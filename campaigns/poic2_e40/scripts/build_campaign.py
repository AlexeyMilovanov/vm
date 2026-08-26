#!/usr/bin/env python3
"""Build the immutable 40-case E-profile Jules campaign from exact archive data."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
from pathlib import Path


def canonical(obj) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()


def write_json(path: Path, obj) -> None:
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


VALIDATOR = r'''#!/usr/bin/env python3
"""Validate an immutable case input and the basic result envelope."""
import hashlib, json, sys
from pathlib import Path

case = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
data = json.loads((case / "input.json").read_text())
claimed = data.pop("input_sha256")
raw = json.dumps(data, sort_keys=True, separators=(",", ":")).encode()
assert hashlib.sha256(raw).hexdigest() == claimed
assert data["schema"] == "poic2-e40-case-v1"
assert data["grid"] == [6, 5] and data["block_sizes"] == [5, 4]
table = data["weight_table_pm"]
assert len(table) == 6 and all(len(row) == 5 for row in table)
assert all(x in (-1, 1) for row in table for x in row)
truth = data["truth_table_pm"]
assert len(truth) == 512 and all(x in (-1, 1) for x in truth)
for mask, value in enumerate(truth):
    r = sum((mask >> i) & 1 for i in range(5))
    s = sum((mask >> i) & 1 for i in range(5, 9))
    assert value == table[r][s]
result = case / "result.json"
if result.exists():
    out = json.loads(result.read_text())
    assert out["case_id"] == data["case_id"]
    assert out["input_sha256"] == claimed
    assert out["status"] in {
        "UNRESOLVED", "POIC2_LE_3_NUMERICAL", "POIC2_EQ_3_EXACT",
        "H3_NUMERICAL_FOUND", "H3_EXACT_FOUND", "INVALID_TARGET"
    }
print("PASS", data["case_id"], claimed)
'''


BASELINE = r'''#!/usr/bin/env python3
"""Load a case as the 9-bit Boolean truth table expected by the common solvers."""
import json, sys
from pathlib import Path
import numpy as np

case = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
data = json.loads((case / "input.json").read_text())
X = ((np.arange(512)[:, None] >> np.arange(9)) & 1).astype(float)
f = ((np.asarray(data["truth_table_pm"], dtype=float) + 1.0) / 2.0)
assert np.all((f == 0) | (f == 1))
print(data["case_id"], "n=9", "ones=", int(f.sum()), "of", len(f))
'''


README = """# POIC2 E40 Jules campaign

This campaign freezes the forty exact `6 x 5` E tables from the axis-GES
census.  There are ten reflection/global-sign orbits, four tables per orbit.

Important: `E` means only that every strict profile cubic has no split legal
section on the four extreme axis lines (and the representatives also have an
exact obstruction at infinity).  It does **not** mean `POIC_2 <= 3`, `H* > 3`,
or a counterexample.  No budget-three POIC source is presently known for these
tables.

Each `cases/E##_key_<key>/` directory is owned by one Jules session.  Common
inputs and references are read-only.  A session first searches for an exact
`POIC_2 <= 3` certificate; only after finding and independently verifying one
does it search for an exact three-head certificate.  Numerical failure never
proves a lower bound.

Run `python3 common/validate_case.py cases/<case>` to validate a case envelope.
"""


TASK = """# Jules research task: {case_id}

You own only this directory.  Read `../../README.md`, `../../common/`, and the
immutable `input.json`.  Do not edit common files or another case.

Use up to two hours as an autonomous experimental mathematician/programmer.
You may install `numpy`, `scipy`, or `sympy` if absent.  Start from the supplied
solvers but inspect and improve them locally when the diagnostics justify it.

## Ordered objectives

1. Revalidate the target with `../../common/validate_case.py .`.
2. Search for a legal budget-three `POIC_2` representation.  Explore genuinely
   different budget-three topologies/orientation cells, not just random seeds.
3. A numerical hit is only provisional.  Save all coefficients, legality
   margins and full-cube sign margins, rationalize them, and write an
   independent exact-arithmetic verifier in this directory.
4. If an exact `POIC_2 <= 3` certificate is obtained, seek an exact lower bound
   excluding budgets 1 and 2 (for example threshold-degree or an exact
   Gordan/Farkas witness).  Only then report `POIC2_EQ_3_EXACT`.
5. After an exact budget-three source exists, search adaptively for three legal
   heads.  If a numerical H3 hit appears, exactify and check all 512 vertices.
6. Do not infer `POIC_2 > 3` or `H* > 3` from timeout or solver failure.

## Persistence and deliverables

- Append a timestamped entry to `research_log.md` after every substantial
  attempt.  Preserve intermediate scripts, diagnostics and best checkpoints.
- Update `result.json` using the allowed status values checked by the common
  validator.  Include `case_id={case_id}` and the exact `input_sha256` from
  `input.json`.
- Commit useful partial work even without a certificate.  In the final report,
  distinguish exact facts, numerical evidence, and untested ideas.
- If a common solver improvement is broadly useful, save it as
  `proposed_common.patch` here rather than editing `../../common/`.
"""


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--archive", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ns = ap.parse_args()

    archive = ns.archive.resolve()
    notes = archive / "notes"
    sys.path.insert(0, str(notes))
    import verify_exact_6x5_full_ges as v

    orbit_path = notes / "exact_6x5_final_orbit_records.json"
    orbit = json.loads(orbit_path.read_text())
    records = [(int(k), rec) for k, rec in orbit["records"] if rec["k"] == "E"]
    assert len(records) == 40
    assert len({k for k, _ in records}) == 40
    rep_counts = {}
    for _, rec in records:
        rep_counts[rec["rep"]] = rep_counts.get(rec["rep"], 0) + 1
    assert len(rep_counts) == 10 and set(rep_counts.values()) == {4}

    out = ns.out.resolve()
    if out.exists():
        raise SystemExit(f"refusing to overwrite {out}")
    common = out / "common"
    cases = out / "cases"
    common.mkdir(parents=True)
    cases.mkdir()

    (out / "README.md").write_text(README)
    (common / "validate_case.py").write_text(VALIDATOR)
    (common / "load_case.py").write_text(BASELINE)

    assets = {
        notes / "exact_6x5_final_orbit_records.json": common / "exact_6x5_final_orbit_records.json",
        notes / "verify_exact_6x5_full_ges.py": common / "verify_exact_6x5_full_ges.py",
        notes / "build_exact_6x5_final_orbit_classification.py": common / "build_exact_6x5_final_orbit_classification.py",
        notes / "POIC2_6X5_E_INFINITY_EXACT_2026-08-26.md": common / "E_INFINITY_EXACT.md",
        notes / "POLY_CLOSENESS_MODEL_AUDIT.md": common / "MODEL_AUDIT.md",
        notes / "THEOREM_MAP.md": common / "THEOREM_MAP.md",
        archive / "code" / "gap25_h3.py": common / "gap25_h3.py",
        notes / "agents" / "purec19-h3-search-2026-08-26" / "purec19_h3_search.py": common / "purec19_h3_search_reference.py",
        notes / "agents" / "purec19-h3-search-2026-08-26" / "ENGINE_AUDIT.md": common / "H3_ENGINE_AUDIT.md",
    }
    for src, dst in assets.items():
        assert src.exists(), src
        shutil.copy2(src, dst)

    bds = v.quiet_boundaries()
    manifest_cases = []
    for ordinal, (key, rec) in enumerate(sorted(records)):
        bi, mask = divmod(key, 1 << len(v.INTERIOR))
        y = v.labels(bds[bi], mask)
        weight_table = [[int(y[v.NID[(r, s)]]) for s in range(5)] for r in range(6)]
        truth = []
        for word in range(512):
            r = sum((word >> i) & 1 for i in range(5))
            s = sum((word >> i) & 1 for i in range(5, 9))
            truth.append(weight_table[r][s])
        case_id = f"E{ordinal:02d}_key_{key}"
        payload = {
            "schema": "poic2-e40-case-v1",
            "case_id": case_id,
            "key": key,
            "representative": int(rec["rep"]),
            "orbit_transport": {"rr": rec["rr"], "ss": rec["ss"], "sg": rec["sg"]},
            "grid": [6, 5],
            "block_sizes": [5, 4],
            "weight_table_pm": weight_table,
            "truth_table_pm": truth,
            "axis_ges_record": rec,
            "known_exact": [
                "strict cubic profile representative exists",
                "no split legal section on any of four extreme axis lines",
            ],
            "not_known": ["POIC_2 <= 3", "POIC_2 = 3", "H* <= 3", "H* > 3"],
        }
        sha = hashlib.sha256(canonical(payload)).hexdigest()
        data = dict(payload)
        data["input_sha256"] = sha
        cdir = cases / case_id
        (cdir / "results").mkdir(parents=True)
        write_json(cdir / "input.json", data)
        (cdir / "TASK.md").write_text(TASK.format(case_id=case_id))
        (cdir / "research_log.md").write_text(f"# Research log: {case_id}\n\n")
        write_json(cdir / "result.json", {
            "case_id": case_id,
            "input_sha256": sha,
            "status": "UNRESOLVED",
            "exact_facts": [],
            "numerical_evidence": [],
            "artifacts": [],
        })
        manifest_cases.append({
            "case_id": case_id, "key": key, "representative": int(rec["rep"]),
            "input_sha256": sha, "path": f"cases/{case_id}",
        })

    manifest = {
        "schema": "poic2-e40-manifest-v1",
        "source": "exact_6x5_final_orbit_records.json",
        "case_count": 40,
        "orbit_count": 10,
        "cases": manifest_cases,
    }
    manifest["manifest_sha256"] = hashlib.sha256(canonical(manifest)).hexdigest()
    write_json(out / "manifest.json", manifest)
    print(out)
    print("cases=40 orbits=10 manifest_sha256=" + manifest["manifest_sha256"])


if __name__ == "__main__":
    main()
