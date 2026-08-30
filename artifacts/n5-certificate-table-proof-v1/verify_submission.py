#!/usr/bin/env python3
"""Standard-library verifier for the complete n=5 certificate proof table."""
from __future__ import annotations
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction
import hashlib
import itertools
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from typing import Any, Sequence

N = 5
VERTICES = 1 << N
EXPECTED_ORBITS = 9_340_584
ROW_FORMAT = "n5-simple-certificate-row-v1"
MANIFEST_FORMAT = "n5-simple-certificate-table-v1"
CHECKPOINT_FORMAT = "n5-submission-shard-checkpoint-v1"
REPORT_FORMAT = "n5-submission-verification-report-v1"

class VerificationError(RuntimeError):
    pass

def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))

def atomic_text(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, raw = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=path.parent)
    temporary = Path(raw)
    try:
        with os.fdopen(fd, "w", encoding="ascii") as handle:
            handle.write(value); handle.flush(); os.fsync(handle.fileno())
        os.replace(temporary, path)
    except BaseException:
        try: temporary.unlink()
        except FileNotFoundError: pass
        raise

def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024): digest.update(block)
    return digest.hexdigest()

def exact_keys(value: dict[str, Any], required: set[str], optional: set[str], label: str) -> None:
    missing, extra = required - set(value), set(value) - required - optional
    if missing or extra:
        raise VerificationError(f"{label}: missing={sorted(missing)}, extra={sorted(extra)}")

def q_json(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]

def parse_q(value: Any, label: str) -> Fraction:
    if (not isinstance(value, list) or len(value) != 2 or
        any(not isinstance(x, int) or isinstance(x, bool) for x in value) or value[1] <= 0):
        raise VerificationError(f"{label}: expected reduced [numerator, positive denominator]")
    result = Fraction(value[0], value[1])
    if q_json(result) != value: raise VerificationError(f"{label}: rational is not reduced")
    return result

def vertex_bits(vertex: int) -> list[int]:
    return [(vertex >> i) & 1 for i in range(N)]

def verify_upper(target: int, degree: int, upper: Any) -> Fraction:
    if not isinstance(upper, dict): raise VerificationError("upper: expected object")
    exact_keys(upper, {"orientations", "weights", "theta"}, set(), "upper")
    orientations = upper["orientations"]
    if (not isinstance(orientations, list) or len(orientations) != degree or
        any(value not in (-1, 1) for value in orientations)):
        raise VerificationError("upper.orientations: bad length or value")
    raw_weights = upper["weights"]
    if not isinstance(raw_weights, list) or len(raw_weights) != degree:
        raise VerificationError("upper.weights: bad head count")
    weights = []
    for head, raw in enumerate(raw_weights):
        if not isinstance(raw, list) or len(raw) != N:
            raise VerificationError(f"upper.weights[{head}]: expected five entries")
        row = [parse_q(v, f"upper.weights[{head}][{i}]") for i, v in enumerate(raw)]
        if any(value <= 0 for value in row):
            raise VerificationError(f"upper.weights[{head}]: nonpositive weight")
        weights.append(row)
    raw_theta = upper["theta"]
    if not isinstance(raw_theta, list) or len(raw_theta) != 1 + degree * (N + 1):
        raise VerificationError("upper.theta: bad coefficient count")
    theta = [parse_q(v, f"upper.theta[{i}]") for i, v in enumerate(raw_theta)]
    minimum = None
    for vertex in range(VERTICES):
        bits = [Fraction(bit) for bit in vertex_bits(vertex)]
        score, cursor = theta[0], 1
        for head in range(degree):
            oriented = bits if orientations[head] > 0 else [1 - bit for bit in bits]
            denominator = 1 + sum((weights[head][i] * oriented[i] for i in range(N)), Fraction())
            if denominator <= 0:
                raise VerificationError(f"upper: nonpositive denominator at vertex {vertex}")
            numerator = theta[cursor] + sum(
                (theta[cursor + 1 + i] * bits[i] for i in range(N)), Fraction())
            score += numerator / denominator
            cursor += N + 1
        wanted = bool((target >> vertex) & 1)
        if score == 0 or (score > 0) != wanted:
            raise VerificationError(f"upper: wrong exact sign at vertex {vertex}")
        minimum = abs(score) if minimum is None else min(minimum, abs(score))
    assert minimum is not None
    return minimum

def verify_lower(target: int, degree: int, lower: Any) -> int:
    if not isinstance(lower, dict): raise VerificationError("lower: expected object")
    exact_keys(lower, {"predecessor_degree", "anchor", "weights"}, set(), "lower")
    predecessor, anchor, entries = lower["predecessor_degree"], lower["anchor"], lower["weights"]
    if degree == 0:
        if target != 0 or predecessor != -1 or anchor != 0 or entries != []:
            raise VerificationError("lower: bad canonical constant witness")
        return 0
    if predecessor != degree - 1: raise VerificationError("lower predecessor mismatch")
    if not isinstance(anchor, int) or isinstance(anchor, bool) or not 0 <= anchor < VERTICES:
        raise VerificationError("lower.anchor: bad vertex")
    if not isinstance(entries, list): raise VerificationError("lower.weights: expected list")
    dense, previous = [0] * VERTICES, -1
    for index, entry in enumerate(entries):
        if (not isinstance(entry, list) or len(entry) != 2 or
            any(not isinstance(x, int) or isinstance(x, bool) for x in entry)):
            raise VerificationError(f"lower.weights[{index}]: malformed")
        vertex, weight = entry
        if not previous < vertex < VERTICES or weight <= 0:
            raise VerificationError("lower.weights: order, range, or positivity failure")
        previous, dense[vertex] = vertex, weight
    if dense[anchor] <= 0 or not ((target >> anchor) & 1):
        raise VerificationError("lower.anchor is not a positive-weight true vertex")
    for subset in range(1 << N):
        if subset.bit_count() > predecessor: continue
        moment = sum(
            (1 if (target >> vertex) & 1 else -1) * weight
            for vertex, weight in enumerate(dense) if (vertex & subset) == subset)
        if moment != 0:
            raise VerificationError(f"lower: nonzero signed moment for subset {subset}")
    return len(entries)

def verify_row(row: Any) -> dict[str, Any]:
    if not isinstance(row, dict): raise VerificationError("row: expected object")
    exact_keys(row, {"format","n","truth_table","degree","upper","lower","source"}, set(), "row")
    if row["format"] != ROW_FORMAT or row["n"] != N:
        raise VerificationError("row: unsupported format or arity")
    target, degree = row["truth_table"], row["degree"]
    if (not isinstance(target, int) or isinstance(target, bool) or not 0 <= target < 1 << VERTICES or
        not isinstance(degree, int) or isinstance(degree, bool) or not 0 <= degree <= N):
        raise VerificationError("row: bad truth table or degree")
    if degree == 0 and target != 0: raise VerificationError("degree zero reserved for false")
    minimum = verify_upper(target, degree, row["upper"])
    support = verify_lower(target, degree, row["lower"])
    return {"truth_table": target, "minimum_abs_score": q_json(minimum), "lower_support": support}

def checkpoint_identity(shard: dict[str, Any], verifier_sha256: str) -> dict[str, Any]:
    return {"format": CHECKPOINT_FORMAT, "verifier_sha256": verifier_sha256,
            "path": shard["path"], "bytes": shard["bytes"], "sha256": shard["sha256"],
            "rows": shard["rows"], "first_truth_table": shard.get("first_truth_table"),
            "last_truth_table": shard.get("last_truth_table")}

def verify_shard(root_raw: str, shard: dict[str, Any], checkpoint_raw: str,
                 verifier_sha256: str, resume: bool) -> dict[str, Any]:
    root, checkpoint_root = Path(root_raw), Path(checkpoint_raw)
    checkpoint = checkpoint_root / (Path(shard["path"]).name + ".ok.json")
    identity = checkpoint_identity(shard, verifier_sha256)
    if resume and checkpoint.is_file():
        saved = json.loads(checkpoint.read_text(encoding="ascii"))
        for key, value in identity.items():
            if saved.get(key) != value: raise VerificationError(f"stale checkpoint {checkpoint}: {key}")
        result = saved.get("result")
        if not isinstance(result, dict): raise VerificationError(f"bad checkpoint {checkpoint}")
        return {**result, "resumed": True}
    path = (root / shard["path"]).resolve(strict=True)
    path.relative_to(root)
    if path.stat().st_size != shard["bytes"] or sha256_file(path) != shard["sha256"]:
        raise VerificationError(f"{path}: manifest file lock failure")
    count, first, last, maximum_support = 0, -1, -1, 0
    with path.open("r", encoding="ascii") as handle:
        for line_number, line in enumerate(handle, start=1):
            try: check = verify_row(json.loads(line))
            except (json.JSONDecodeError, VerificationError) as error:
                raise VerificationError(f"{path}:{line_number}: {error}") from error
            target = check["truth_table"]
            if count and target <= last: raise VerificationError(f"{path}:{line_number}: local order")
            if count == 0: first = target
            last, count = target, count + 1
            maximum_support = max(maximum_support, check["lower_support"])
    if count != shard["rows"] or first != shard.get("first_truth_table") or last != shard.get("last_truth_table"):
        raise VerificationError(f"{path}: manifest row metadata failure")
    result = {"count": count, "first": first, "last": last, "maximum_support": maximum_support}
    atomic_text(checkpoint, canonical_json({**identity, "result": result}) + "\n")
    return {**result, "resumed": False}

def permutation_map(permutation: tuple[int, ...], input_flip: bool) -> list[int]:
    result = []
    for vertex in range(VERTICES):
        mapped = 0
        for coordinate in range(N):
            bit = ((vertex >> permutation[coordinate]) & 1) ^ int(input_flip)
            mapped |= bit << coordinate
        result.append(mapped)
    return result

def cycle_lengths(mapping: list[int]) -> list[int]:
    seen, result = [False] * len(mapping), []
    for start in range(len(mapping)):
        if seen[start]: continue
        current, length = start, 0
        while not seen[current]:
            seen[current] = True; current = mapping[current]; length += 1
        if current != start: raise VerificationError("Burnside action is not a permutation")
        result.append(length)
    return result

def burnside_orbit_count() -> dict[str, int]:
    fixed_sum = group_size = 0
    for permutation in itertools.permutations(range(N)):
        for input_flip in (False, True):
            lengths = cycle_lengths(permutation_map(permutation, input_flip))
            for output_flip in (False, True):
                group_size += 1
                if not output_flip: fixed_sum += 1 << len(lengths)
                elif all(length % 2 == 0 for length in lengths): fixed_sum += 1 << len(lengths)
    if group_size != 480 or fixed_sum % group_size:
        raise VerificationError("Burnside arithmetic failure")
    return {"group_size": group_size, "fixed_sum": fixed_sum, "orbits": fixed_sum // group_size}

def compile_coverage(source: Path, binary: Path, compiler: str) -> dict[str, str]:
    source_sha = sha256_file(source)
    stamp = binary.with_suffix(binary.suffix + ".source-sha256")
    current = stamp.read_text(encoding="ascii").strip() if stamp.is_file() else ""
    if not binary.is_file() or current != source_sha:
        executable = shutil.which(compiler)
        if executable is None: raise VerificationError(f"C compiler not found: {compiler}")
        binary.parent.mkdir(parents=True, exist_ok=True)
        temporary = binary.with_suffix(binary.suffix + ".tmp")
        subprocess.run([executable, "-O3", "-std=c11", "-Wall", "-Wextra", "-Werror",
                        "-fopenmp", str(source), "-o", str(temporary)], check=True)
        os.replace(temporary, binary)
        atomic_text(stamp, source_sha + "\n")
    return {"source_sha256": source_sha, "binary_sha256": sha256_file(binary)}

def build_codes_and_digest(root: Path, shards: list[dict[str, Any]], destination: Path) -> dict[str, Any]:
    destination.parent.mkdir(parents=True, exist_ok=True)
    fd, raw = tempfile.mkstemp(prefix=destination.name + ".", suffix=".tmp", dir=destination.parent)
    temporary, digest, count, previous = Path(raw), hashlib.sha256(), 0, -1
    try:
        with os.fdopen(fd, "wb") as output:
            for shard in shards:
                path = root / shard["path"]
                with path.open("r", encoding="ascii") as handle:
                    for line_number, line in enumerate(handle, start=1):
                        try: target = int(json.loads(line)["truth_table"])
                        except (json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
                            raise VerificationError(f"{path}:{line_number}: bad truth table") from error
                        if not previous < target: raise VerificationError(f"{path}:{line_number}: global order")
                        previous, count = target, count + 1
                        digest.update(f"{target}\n".encode("ascii"))
                        output.write(struct.pack("<I", target))
            output.flush(); os.fsync(output.fileno())
        os.replace(temporary, destination)
    except BaseException:
        try: temporary.unlink()
        except FileNotFoundError: pass
        raise
    return {"rows": count, "truth_tables_sha256": digest.hexdigest(),
            "codes_u32le_sha256": sha256_file(destination), "last_truth_table": previous}

def run(args: argparse.Namespace) -> int:
    started = time.monotonic()
    root = args.table.resolve(strict=True)
    manifest_path = root / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="ascii"))
    if manifest.get("format") != MANIFEST_FORMAT or manifest.get("n") != N:
        raise VerificationError("bad manifest format or arity")
    shards = manifest.get("shards")
    if not isinstance(shards, list) or not shards: raise VerificationError("manifest has no shards")
    if manifest.get("row_count") != EXPECTED_ORBITS: raise VerificationError("wrong manifest orbit count")
    verifier_sha = sha256_file(Path(__file__).resolve())
    checkpoints = args.checkpoints.resolve(); checkpoints.mkdir(parents=True, exist_ok=True)
    results: list[dict[str, Any] | None] = [None] * len(shards)
    verified_rows = resumed_shards = 0
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(verify_shard, str(root), shard, str(checkpoints),
                               verifier_sha, args.resume): index
                   for index, shard in enumerate(shards)}
        for completed, future in enumerate(as_completed(futures), start=1):
            index, result = futures[future], future.result()
            results[index] = result
            verified_rows += result["count"]; resumed_shards += int(result["resumed"])
            print(f"[{completed}/{len(shards)}] exact={shards[index]['path']} rows={result['count']} "
                  f"completed_rows={verified_rows} resumed={str(result['resumed']).lower()}", flush=True)
    previous = count_all = maximum_support = 0
    previous = -1
    for shard, result in zip(shards, results):
        assert result is not None
        if result["first"] <= previous: raise VerificationError(f"{shard['path']}: global shard order")
        previous = result["last"]; count_all += result["count"]
        maximum_support = max(maximum_support, result["maximum_support"])
    if count_all != manifest["row_count"]: raise VerificationError("manifest row count mismatch")
    codes_path = args.codes.resolve()
    code_summary = build_codes_and_digest(root, shards, codes_path)
    if code_summary["rows"] != count_all or code_summary["truth_tables_sha256"] != manifest["truth_tables_sha256"]:
        raise VerificationError("truth-table digest pass mismatch")
    burnside = burnside_orbit_count()
    if burnside["orbits"] != EXPECTED_ORBITS: raise VerificationError("Burnside orbit count mismatch")
    coverage_source, coverage_binary = args.coverage_source.resolve(strict=True), args.coverage_binary.resolve()
    compiler = compile_coverage(coverage_source, coverage_binary, args.compiler)
    process = subprocess.run([str(coverage_binary), str(codes_path), str(count_all),
                              str(args.coverage_workers)], text=True, capture_output=True)
    if process.returncode:
        raise VerificationError("coverage checker failed: " + process.stdout + process.stderr)
    coverage = json.loads(process.stdout)
    if coverage.get("ok") is not True or coverage.get("rows") != count_all:
        raise VerificationError("coverage checker did not certify every row")
    report = {"format": REPORT_FORMAT, "ok": True, "table": str(root),
              "manifest_sha256": sha256_file(manifest_path), "verifier_sha256": verifier_sha,
              "coverage_source_sha256": compiler["source_sha256"],
              "coverage_binary_sha256": compiler["binary_sha256"],
              "rows": count_all, "shards": len(shards), "vertices_checked": count_all * VERTICES,
              "maximum_lower_support": maximum_support,
              "truth_tables_sha256": code_summary["truth_tables_sha256"],
              "codes_u32le_sha256": code_summary["codes_u32le_sha256"],
              "strictly_increasing_codes": True, "burnside": burnside, "coverage": coverage,
              "exact_workers": args.workers, "coverage_workers": args.coverage_workers,
              "resumed_shards": resumed_shards, "fresh_shards": len(shards) - resumed_shards,
              "elapsed_seconds": time.monotonic() - started}
    atomic_text(args.report.resolve(), canonical_json(report) + "\n")
    print(canonical_json(report), flush=True)
    return 0

def parser() -> argparse.ArgumentParser:
    directory = Path(__file__).resolve().parent
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("table", type=Path)
    result.add_argument("--workers", type=int, default=6)
    result.add_argument("--coverage-workers", type=int, default=6)
    result.add_argument("--checkpoints", type=Path, default=directory / "reports/checkpoints")
    result.add_argument("--codes", type=Path, default=directory / "reports/codes.u32le")
    result.add_argument("--report", type=Path, default=directory / "reports/verification-summary.json")
    result.add_argument("--coverage-source", type=Path, default=directory / "coverage_fast.c")
    result.add_argument("--coverage-binary", type=Path, default=directory / "reports/coverage_fast")
    result.add_argument("--compiler", default="cc")
    result.add_argument("--resume", action="store_true")
    return result

def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    if args.workers < 1 or args.coverage_workers < 1: raise SystemExit("workers must be positive")
    try: return run(args)
    except (OSError, VerificationError, ValueError, subprocess.SubprocessError,
            json.JSONDecodeError) as error:
        print(f"verify_submission: ERROR: {error}", file=sys.stderr)
        return 2

if __name__ == "__main__":
    raise SystemExit(main())
