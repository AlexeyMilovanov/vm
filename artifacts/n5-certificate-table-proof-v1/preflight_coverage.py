#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import subprocess
import time


HERE = Path(__file__).resolve().parent
TABLE = Path("/home/lesha/n5-certificate-table-build/candidate-v2/merged-complete-v1")
REPORTS = HERE / "reports"
SPEC = importlib.util.spec_from_file_location("submission_verifier", HERE / "verify_submission.py")
assert SPEC is not None and SPEC.loader is not None
VERIFIER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFIER)


def main() -> int:
    started = time.monotonic()
    manifest = json.loads((TABLE / "manifest.json").read_text(encoding="ascii"))
    shards = manifest["shards"]
    REPORTS.mkdir(parents=True, exist_ok=True)
    codes = REPORTS / "codes.u32le"
    code_summary = VERIFIER.build_codes_and_digest(TABLE, shards, codes)
    if code_summary["rows"] != manifest["row_count"]:
        raise RuntimeError("preflight row count mismatch")
    if code_summary["truth_tables_sha256"] != manifest["truth_tables_sha256"]:
        raise RuntimeError("preflight truth-table digest mismatch")
    burnside = VERIFIER.burnside_orbit_count()
    if burnside["orbits"] != manifest["row_count"]:
        raise RuntimeError("preflight Burnside count mismatch")
    binary = REPORTS / "coverage_fast"
    compiler = VERIFIER.compile_coverage(HERE / "coverage_fast.c", binary, "cc")
    process = subprocess.run(
        [str(binary), str(codes), str(manifest["row_count"]), "6"],
        text=True,
        capture_output=True,
    )
    if process.returncode:
        raise RuntimeError(process.stdout + process.stderr)
    coverage = json.loads(process.stdout)
    result = {
        "ok": True,
        "code_summary": code_summary,
        "burnside": burnside,
        "coverage": coverage,
        "compiler": compiler,
        "elapsed_seconds": time.monotonic() - started,
    }
    VERIFIER.atomic_text(
        REPORTS / "coverage-preflight.json",
        VERIFIER.canonical_json(result) + "\n",
    )
    print(VERIFIER.canonical_json(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
