#!/usr/bin/env python3
"""Unrestricted interior H=3 search for the exact 19-bit pure-C candidate.

The nonlinear variables are the 57 positive pole slopes.  For fixed poles the
numerators (and the absorbable readout bias) are fitted by a hinge LP on an
active set.  The complete 2^19 cube is only scanned in chunks to add the worst
cutting planes.  A numerical hit is never promoted to a theorem by this file;
it is saved for a separate rational/exact verifier.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import time

import numpy as np
from scipy import sparse
from scipy.optimize import linprog, minimize


SELECTORS = (0, 3, 8, 18, 24, 25, 26, 30, 42, 48, 71, 84)
N = 19
H = 3
NPTS = 1 << N
CELLS = ((1, 1, 1), (1, 1, -1), (1, -1, -1), (-1, -1, -1))


def load_instance(source: Path):
    data = json.loads(source.read_text())
    ax = np.asarray([data["ax"][s] for s in SELECTORS] + data["ay"], dtype=np.int64)
    bx = np.asarray([data["bx"][s] for s in SELECTORS] + data["by"], dtype=np.int64)
    ids = np.arange(NPTS, dtype=np.uint32)[:, None]
    x = ((ids >> np.arange(N, dtype=np.uint32)) & 1).astype(np.uint8)
    xi = x.astype(np.int64, copy=False)
    a = xi @ ax
    b = 1 + xi @ bx
    if int(b.min()) <= 0:
        raise RuntimeError("source pole is not positive")
    twice = 2 * np.sum(a * b, axis=1) + b[:, 0]
    if np.any(twice == 0):
        raise RuntimeError("target has a zero cleared score")
    y = np.where(twice > 0, 1, -1).astype(np.int8)
    sha = hashlib.sha256(np.packbits(y > 0).tobytes()).hexdigest()
    return data, ax, bx, x, y, sha


def initial_active(x: np.ndarray, y: np.ndarray, rng: np.random.Generator, gordan_file: Path):
    ids: set[int] = {0, NPTS - 1}
    for j in range(N):
        ids.add(1 << j)
        ids.add((NPTS - 1) ^ (1 << j))

    # Preserve a broad part of the exact selector obstruction: random complete
    # seven-column fibres over 160 selector assignments.
    selector_assignments = rng.choice(1 << 12, size=160, replace=False)
    for s in selector_assignments:
        for j in range(7):
            ids.add(int(s) | (1 << (12 + j)))

    # Include the supports of the four exceptional exact Gordan circuits.
    if gordan_file.exists():
        spec = importlib.util.spec_from_file_location("purec19_gordan", gordan_file)
        module = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(module)
        for _fixed, _values, vertices, _weights in module.CERTIFICATES:
            ids.update(int(v) for v in vertices)

    # Balanced random bulk.
    for sign in (-1, 1):
        pool = np.flatnonzero(y == sign)
        take = min(650, len(pool))
        ids.update(int(v) for v in rng.choice(pool, size=take, replace=False))
    return np.asarray(sorted(ids), dtype=np.int64)


def pole_weights(logw: np.ndarray) -> np.ndarray:
    return np.exp(np.clip(logw, -18.0, 16.0)).reshape(H, N)


def feature_matrix(xa: np.ndarray, orients: tuple[int, int, int], w: np.ndarray):
    xx = xa.astype(np.float64, copy=False)
    cols = [np.ones((len(xx), 1), dtype=np.float64)]
    for h, orient in enumerate(orients):
        z = xx if orient > 0 else 1.0 - xx
        d = 1.0 + z @ w[h]
        cols.append((1.0 / d)[:, None])
        cols.append(xx / d[:, None])
    return np.hstack(cols)


def hinge_lp(cols: np.ndarray, y: np.ndarray):
    """Minimise sum of unit-margin hinge slacks; return normalised loss, theta."""
    signed = cols * y[:, None]
    rows, nc = signed.shape
    aub = sparse.hstack(
        [sparse.csr_matrix(-signed), -sparse.eye(rows, format="csr")],
        format="csr",
    )
    c = np.concatenate([np.zeros(nc), np.ones(rows)])
    bounds = [(None, None)] * nc + [(0.0, None)] * rows
    result = linprog(c, A_ub=aub, b_ub=-np.ones(rows), bounds=bounds, method="highs")
    if result.status != 0:
        return math.inf, None
    return float(result.fun) / rows, result.x[:nc]


def max_margin_lp(cols: np.ndarray, y: np.ndarray):
    """L1-normalised maximum margin, used only after hinge feasibility."""
    signed = cols * y[:, None]
    rows, nc = signed.shape
    # theta = plus - minus, both nonnegative; final variable is gamma.
    a_margin = np.hstack([-signed, signed, np.ones((rows, 1))])
    a_norm = np.concatenate([np.ones(2 * nc), [0.0]])[None, :]
    aub = sparse.csr_matrix(np.vstack([a_margin, a_norm]))
    bub = np.concatenate([np.zeros(rows), [1.0]])
    c = np.zeros(2 * nc + 1)
    c[-1] = -1.0
    bounds = [(0.0, None)] * (2 * nc) + [(None, None)]
    result = linprog(c, A_ub=aub, b_ub=bub, bounds=bounds, method="highs")
    if result.status != 0:
        return -math.inf, None
    theta = result.x[:nc] - result.x[nc : 2 * nc]
    return float(result.x[-1]), theta


def fit_active(x, y, active, orients, logw, robust=False):
    w = pole_weights(logw)
    cols = feature_matrix(x[active], orients, w)
    loss, theta = hinge_lp(cols, y[active].astype(np.float64))
    if robust and theta is not None and loss < 1e-10:
        margin, theta2 = max_margin_lp(cols, y[active].astype(np.float64))
        if theta2 is not None and margin > 0:
            theta = theta2
    return loss, theta, w


def scan_full(x, y, orients, w, theta, chunk=32768, keep=768):
    worst_ids = np.empty(0, dtype=np.int64)
    worst_margins = np.empty(0, dtype=np.float64)
    wrong = 0
    below_one = 0
    min_margin = math.inf
    hinge_sum = 0.0
    for start in range(0, len(y), chunk):
        stop = min(start + chunk, len(y))
        xx = x[start:stop].astype(np.float64, copy=False)
        score = np.full(stop - start, theta[0], dtype=np.float64)
        k = 1
        for h, orient in enumerate(orients):
            z = xx if orient > 0 else 1.0 - xx
            d = 1.0 + z @ w[h]
            numerator = theta[k] + xx @ theta[k + 1 : k + 1 + N]
            score += numerator / d
            k += N + 1
        margins = y[start:stop] * score
        wrong += int(np.count_nonzero(margins <= 0.0))
        below_one += int(np.count_nonzero(margins < 1.0))
        min_margin = min(min_margin, float(margins.min()))
        hinge_sum += float(np.maximum(0.0, 1.0 - margins).sum())
        local_keep = min(keep, len(margins))
        loc = np.argpartition(margins, local_keep - 1)[:local_keep]
        ids = loc.astype(np.int64) + start
        vals = margins[loc]
        worst_ids = np.concatenate([worst_ids, ids])
        worst_margins = np.concatenate([worst_margins, vals])
        if len(worst_ids) > 2 * keep:
            take = np.argpartition(worst_margins, keep - 1)[:keep]
            worst_ids, worst_margins = worst_ids[take], worst_margins[take]
    order = np.argsort(worst_margins)
    return {
        "wrong": wrong,
        "below_one": below_one,
        "min_margin": min_margin,
        "hinge_per_vertex": hinge_sum / len(y),
        "worst_ids": worst_ids[order][:keep],
        "worst_margins": worst_margins[order][:keep],
    }


def warm_population(data, bx, orients, rng, pop_size, selector_cert: Path):
    starts: list[np.ndarray] = []
    source = np.maximum(bx.T.astype(np.float64), 1e-8)
    for scale in (1e-5, 1e-3, 1e-1, 1.0, 10.0):
        starts.append(np.log(source * scale))

    if selector_cert.exists():
        cert = json.loads(selector_cert.read_text())
        scale = float(cert["scale"])
        bw = np.asarray(cert["B"], dtype=np.float64) / scale
        qw = np.asarray(cert["Q"], dtype=np.float64) / scale
        restricted = np.vstack([bw[list(SELECTORS)], qw]).T
        if restricted.shape == (H, N) and np.all(restricted > 0):
            # Original fit used d0=1e-6; rescale to the D=1+z.W chart.
            starts.append(np.log(restricted / 1e-6))
            starts.append(np.log(restricted / 1e-5))

    for level in (-5.0, -2.0, 0.0, 3.0, 7.0, 11.0):
        starts.append(np.full((H, N), level))
    while len(starts) < pop_size:
        centre = rng.choice([-4.0, -1.0, 2.0, 6.0, 10.0])
        starts.append(rng.normal(centre, 1.6, size=(H, N)))
    rng.shuffle(starts)
    return [np.asarray(p, dtype=np.float64).reshape(-1) for p in starts[:pop_size]]


class Logger:
    def __init__(self, path: Path):
        path.parent.mkdir(parents=True, exist_ok=True)
        self.handle = path.open("a", buffering=1)

    def __call__(self, message: str):
        stamp = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        line = f"[{stamp}] {message}"
        print(line, flush=True)
        self.handle.write(line + "\n")

    def close(self):
        self.handle.close()


def checkpoint(outdir, cell_name, orients, seed, elapsed, logw, theta, active, metrics, sha):
    np.savez_compressed(
        outdir / f"checkpoint_{cell_name}.npz",
        orients=np.asarray(orients, dtype=np.int8),
        seed=np.asarray(seed),
        elapsed=np.asarray(elapsed),
        logw=logw,
        theta=theta,
        active=active,
        wrong=np.asarray(metrics["wrong"]),
        below_one=np.asarray(metrics["below_one"]),
        min_margin=np.asarray(metrics["min_margin"]),
        hinge_per_vertex=np.asarray(metrics["hinge_per_vertex"]),
        target_sha=np.asarray(sha),
    )


def seed_from_checkpoint(path, orients, sha, active, population, rng, population_size, max_active):
    """Warm-restart from a compatible best-candidate checkpoint."""
    with np.load(path, allow_pickle=False) as saved:
        saved_orients = tuple(int(v) for v in np.asarray(saved["orients"]).reshape(-1))
        raw_sha = np.asarray(saved["target_sha"]).item()
        saved_sha = raw_sha.decode() if isinstance(raw_sha, bytes) else str(raw_sha)
        saved_logw = np.asarray(saved["logw"], dtype=np.float64).reshape(-1)
        saved_active = np.asarray(saved["active"], dtype=np.int64).reshape(-1)
        saved_elapsed = float(np.asarray(saved["elapsed"]).item()) if "elapsed" in saved else 0.0

    if saved_orients != tuple(orients):
        raise ValueError(
            f"resume orientation mismatch: checkpoint={saved_orients}, requested={tuple(orients)}"
        )
    if saved_sha != sha:
        raise ValueError(f"resume target SHA mismatch: checkpoint={saved_sha}, current={sha}")
    if saved_logw.shape != (H * N,) or not np.all(np.isfinite(saved_logw)):
        raise ValueError(f"resume logw must be a finite vector of length {H * N}")
    if np.any(saved_active < 0) or np.any(saved_active >= NPTS):
        raise ValueError("resume active set contains an out-of-range vertex")

    # Keep discovered hard rows first, then fill spare capacity with fresh anchors.
    saved_active = np.unique(saved_active)
    fresh_active = np.unique(np.asarray(active, dtype=np.int64))
    fresh_only = fresh_active[~np.isin(fresh_active, saved_active, assume_unique=True)]
    merged_active = np.sort(
        np.concatenate([saved_active, fresh_only])[:max_active]
    )

    centre = saved_logw.copy()
    resume_population = [centre.copy()]
    for scale in (0.03, 0.1, 0.3, 0.7, 1.3):
        resume_population.append(
            np.clip(centre + rng.normal(0.0, scale, H * N), -18.0, 16.0)
        )
    keep = max(population_size, len(resume_population))
    merged_population = (resume_population + population)[:keep]
    return merged_active, merged_population, saved_elapsed


def search_cell(args, data, bx, x, y, sha, orients):
    cell_name = "".join("p" if o > 0 else "m" for o in orients)
    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)
    log = Logger(outdir / f"search_{cell_name}_seed{args.seed}.log")
    rng = np.random.default_rng(args.seed + sum((i + 1) * (o < 0) for i, o in enumerate(orients)) * 10007)
    gordan = Path("/home/lesha/rs-takehome-results/notes/agents/poic2-separation-existence-2026-08-26/purec19-h3-audit/verify_purec19_four_face_gordan_exact.py")
    selector_cert = Path("/home/lesha/rs-takehome-results/notes/purec_signrank8_h3_selector_exact.json")
    active = initial_active(x, y, rng, gordan)
    population = warm_population(data, bx, orients, rng, args.population, selector_cert)
    if args.resume is not None:
        active, population, saved_elapsed = seed_from_checkpoint(
            args.resume, orients, sha, active, population, rng,
            args.population, args.max_active,
        )
        log(
            f"RESUME path={args.resume} saved_elapsed={saved_elapsed:.1f}s "
            f"active={len(active)} population={len(population)}"
        )
    values = []
    thetas = []
    log(f"START cell={orients} seed={args.seed} seconds={args.seconds} npts={len(y)} active={len(active)} sha={sha[:20]}")
    t0 = time.monotonic()
    for i, p in enumerate(population):
        if time.monotonic() - t0 >= args.seconds:
            break
        loss, theta, _w = fit_active(x, y, active, orients, p)
        values.append(loss)
        thetas.append(theta)
        if i % 4 == 0:
            log(f"initial {i+1}/{len(population)} active_hinge={loss:.8g}")
    population = population[: len(values)]
    if not population:
        log("NO EVALUATIONS"); log.close(); return 3

    best_key = (NPTS + 1, -math.inf, math.inf)
    best_record = None
    generation = 0
    last_scan = -1
    while time.monotonic() - t0 < args.seconds:
        generation += 1
        for i in range(len(population)):
            if time.monotonic() - t0 >= args.seconds:
                break
            choices = [j for j in range(len(population)) if j != i]
            if len(choices) < 3:
                break
            a, b, c = rng.choice(choices, 3, replace=False)
            trial = population[a] + args.de_weight * (population[b] - population[c])
            mask = rng.random(H * N) < args.crossover
            mask[rng.integers(0, H * N)] = True
            trial = np.where(mask, trial, population[i])
            trial = np.clip(trial, -18.0, 16.0)
            loss, theta, _w = fit_active(x, y, active, orients, trial)
            if loss < values[i]:
                population[i], values[i], thetas[i] = trial, loss, theta

        ib = int(np.argmin(values))
        need_scan = generation - last_scan >= args.scan_every or values[ib] < 1e-9
        if need_scan and thetas[ib] is not None:
            # Refit robustly once active separation has been achieved.
            loss, theta, w = fit_active(x, y, active, orients, population[ib], robust=True)
            values[ib], thetas[ib] = loss, theta
            metrics = scan_full(x, y, orients, w, theta, args.chunk, args.add_worst * 3)
            elapsed = time.monotonic() - t0
            key = (metrics["wrong"], -metrics["min_margin"], metrics["hinge_per_vertex"])
            log(
                f"gen={generation} elapsed={elapsed:.1f}s active={len(active)} "
                f"sub={loss:.8g} wrong={metrics['wrong']} below1={metrics['below_one']} "
                f"min={metrics['min_margin']:.8g} fullhinge/v={metrics['hinge_per_vertex']:.8g}"
            )
            if key < best_key:
                best_key = key
                best_record = (population[ib].copy(), theta.copy(), active.copy(), dict(metrics))
                checkpoint(outdir, cell_name, orients, args.seed, elapsed, population[ib], theta, active, metrics, sha)
            if metrics["min_margin"] > args.hit_margin:
                np.savez_compressed(
                    outdir / f"NUMERICAL_HIT_{cell_name}_seed{args.seed}.npz",
                    orients=np.asarray(orients), logw=population[ib], w=w, theta=theta,
                    active=active, min_margin=metrics["min_margin"], target_sha=sha,
                )
                log(f"NUMERICAL HIT min_margin={metrics['min_margin']:.12g}; exactification required")
                summary = {"status": "NUMERICAL_HIT", "cell": cell_name, "seed": args.seed,
                           "elapsed": elapsed, "min_margin": metrics["min_margin"], "wrong": 0,
                           "target_sha": sha}
                (outdir / f"summary_{cell_name}_seed{args.seed}.json").write_text(json.dumps(summary, indent=2))
                log.close(); return 0

            # Add the worst not-yet-active rows.  A Python set is cheap at this scale.
            active_set = set(int(v) for v in active)
            additions = [int(v) for v in metrics["worst_ids"] if int(v) not in active_set]
            additions = additions[: args.add_worst]
            if additions:
                active = np.asarray(sorted(active_set.union(additions)), dtype=np.int64)
                if len(active) > args.max_active:
                    anchors = set(int(v) for v in initial_active(x, y, rng, gordan))
                    keep_bad = [int(v) for v in metrics["worst_ids"][: max(0, args.max_active - len(anchors))]]
                    active = np.asarray(sorted(anchors.union(keep_bad)), dtype=np.int64)
                values, thetas = [], []
                for p in population:
                    lv, tv, _ = fit_active(x, y, active, orients, p)
                    values.append(lv); thetas.append(tv)
            last_scan = generation

        if generation % args.polish_every == 0 and time.monotonic() - t0 < args.seconds - 10:
            ib = int(np.argmin(values))
            def objective(p):
                return fit_active(x, y, active, orients, p)[0]
            result = minimize(
                objective, population[ib], method="Nelder-Mead",
                options={"maxfev": args.polish_evals, "xatol": 2e-3, "fatol": 1e-9},
            )
            if result.fun < values[ib]:
                population[ib] = np.clip(result.x, -18.0, 16.0)
                values[ib], thetas[ib], _ = fit_active(x, y, active, orients, population[ib])

    elapsed = time.monotonic() - t0
    if best_record is None:
        status = {"status": "NO_FULL_SCAN", "cell": cell_name, "seed": args.seed,
                  "elapsed": elapsed, "target_sha": sha}
    else:
        _p, _t, _a, metrics = best_record
        status = {"status": "NO_HIT", "cell": cell_name, "seed": args.seed,
                  "elapsed": elapsed, "wrong": metrics["wrong"],
                  "min_margin": metrics["min_margin"],
                  "hinge_per_vertex": metrics["hinge_per_vertex"], "target_sha": sha}
    (outdir / f"summary_{cell_name}_seed{args.seed}.json").write_text(json.dumps(status, indent=2))
    log(f"END {json.dumps(status, sort_keys=True)}")
    log.close()
    return 1


def parse_cell(text: str):
    aliases = {"ppp": (1, 1, 1), "ppm": (1, 1, -1),
               "pmm": (1, -1, -1), "mmm": (-1, -1, -1)}
    if text in aliases:
        return aliases[text]
    parts = tuple(int(v) for v in text.split(","))
    if len(parts) != 3 or any(v not in (-1, 1) for v in parts):
        raise argparse.ArgumentTypeError("cell must be ppp/ppm/pmm/mmm or three +/-1 values")
    return parts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=Path("/home/lesha/rs-takehome-results/notes/purec_shatter7_exact.json"))
    parser.add_argument("--outdir", type=Path, default=Path("/home/lesha/rs-takehome-results/notes/agents/purec19-h3-search-2026-08-26"))
    parser.add_argument("--resume", type=Path,
                        help="warm-restart from a compatible checkpoint NPZ")
    parser.add_argument("--cell", type=parse_cell, default=(1, 1, 1))
    parser.add_argument("--seconds", type=float, default=300.0)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--population", type=int, default=18)
    parser.add_argument("--scan-every", type=int, default=4)
    parser.add_argument("--add-worst", type=int, default=192)
    parser.add_argument("--max-active", type=int, default=6000)
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--de-weight", type=float, default=0.72)
    parser.add_argument("--crossover", type=float, default=0.88)
    parser.add_argument("--polish-every", type=int, default=24)
    parser.add_argument("--polish-evals", type=int, default=300)
    parser.add_argument("--hit-margin", type=float, default=1e-9)
    args = parser.parse_args()

    os.environ.setdefault("OMP_NUM_THREADS", "1")
    os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
    data, _ax, bx, x, y, sha = load_instance(args.source)
    return search_cell(args, data, bx, x, y, sha, args.cell)


if __name__ == "__main__":
    raise SystemExit(main())
