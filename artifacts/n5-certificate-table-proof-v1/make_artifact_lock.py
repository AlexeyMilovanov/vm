#!/usr/bin/env python3
"""Freeze a successful table-verification result and its checking sources."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
from typing import Any


FORMAT = "n5-certificate-table-artifact-lock-v1"
SOURCE_NAMES = [
    "README.md",
    "COVERAGE_ARGUMENT.md",
    "ENVIRONMENT.md",
    "table-manifest.json",
    "verify_submission.py",
    "coverage_fast.c",
    "verify.sh",
    "run_full_verification.sh",
    "test_submission_verifier.py",
    "preflight_coverage.py",
    "make_artifact_lock.py",
]
REPORT_NAMES = [
    "unit-tests.txt",
    "coverage-preflight.json",
    "verification-summary.json",
    "verification.log",
    "exit-code.txt",
    "started-utc.txt",
    "finished-utc.txt",
]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def locked(path: Path, relative_to: Path) -> dict[str, Any]:
    stat = path.stat()
    return {
        "path": str(path.relative_to(relative_to)),
        "bytes": stat.st_size,
        "sha256": sha256_file(path),
    }


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, raw = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=path.parent)
    temporary = Path(raw)
    try:
        with os.fdopen(fd, "w", encoding="ascii") as handle:
            json.dump(value, handle, sort_keys=True, separators=(",", ":"))
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path)
    parser.add_argument("--artifact", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    artifact = args.artifact.resolve(strict=True)
    table = args.table.resolve(strict=True)
    reports = artifact / "reports"
    summary_path = reports / "verification-summary.json"
    exit_path = reports / "exit-code.txt"
    summary = json.loads(summary_path.read_text(encoding="ascii"))
    if summary.get("ok") is not True:
        raise SystemExit("verification summary is not successful")
    if exit_path.read_text(encoding="ascii").strip() != "0":
        raise SystemExit("archived verifier exit code is not zero")

    manifest_path = table / "manifest.json"
    manifest_sha = sha256_file(manifest_path)
    if summary.get("manifest_sha256") != manifest_sha:
        raise SystemExit("successful report does not lock the current table manifest")
    archived_manifest = artifact / "table-manifest.json"
    if sha256_file(archived_manifest) != manifest_sha:
        raise SystemExit("archived table-manifest.json differs from the verified table")

    verifier_sha = sha256_file(artifact / "verify_submission.py")
    coverage_source_sha = sha256_file(artifact / "coverage_fast.c")
    if summary.get("verifier_sha256") != verifier_sha:
        raise SystemExit("successful report does not match the current verifier")
    if summary.get("coverage_source_sha256") != coverage_source_sha:
        raise SystemExit("successful report does not match the current coverage source")

    proof_files = []
    for name in SOURCE_NAMES:
        proof_files.append(locked(artifact / name, artifact))
    for name in REPORT_NAMES:
        proof_files.append(locked(reports / name, artifact))

    manifest = json.loads(manifest_path.read_text(encoding="ascii"))
    expected_rows = manifest.get("row_count")
    if (
        summary.get("rows") != expected_rows
        or summary.get("shards") != len(manifest.get("shards", []))
        or summary.get("truth_tables_sha256") != manifest.get("truth_tables_sha256")
        or summary.get("vertices_checked") != 32 * expected_rows
        or summary.get("fresh_shards") != summary.get("shards")
        or summary.get("resumed_shards") != 0
        or summary.get("burnside", {}).get("orbits") != expected_rows
        or summary.get("coverage", {}).get("ok") is not True
        or summary.get("coverage", {}).get("noncanonical") != 0
        or summary.get("coverage", {}).get("rows") != expected_rows
    ):
        raise SystemExit("successful report is not a fresh complete proof run")
    value = {
        "format": FORMAT,
        "claim": "For every Boolean f on at most five variables, deg_pm(f)=POIC_2(f)=H*(f).",
        "artifact_root": str(artifact),
        "table_root": str(table),
        "table_manifest": {
            "bytes": manifest_path.stat().st_size,
            "sha256": manifest_sha,
            "format": manifest.get("format"),
            "row_count": manifest.get("row_count"),
            "truth_tables_sha256": manifest.get("truth_tables_sha256"),
            "shards": len(manifest.get("shards", [])),
            "shard_bytes": sum(item.get("bytes", 0) for item in manifest.get("shards", [])),
        },
        "successful_report": summary,
        "proof_files": proof_files,
    }
    output = (args.output or (artifact / "ARTIFACT_LOCK.json")).resolve()
    atomic_json(output, value)
    print(json.dumps({"ok": True, "output": str(output), "sha256": sha256_file(output)},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
