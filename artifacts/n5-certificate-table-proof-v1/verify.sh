#!/usr/bin/env bash
set -uo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: bash verify.sh TABLE_DIRECTORY [RUN_DIRECTORY]" >&2
  exit 2
fi

artifact_root="$(cd "$(dirname "$0")" && pwd)"
table_root="$(cd "$1" && pwd)"
run_root="${2:-$artifact_root/verification-run}"
exact_workers="${EXACT_WORKERS:-4}"
coverage_workers="${COVERAGE_WORKERS:-$exact_workers}"

mkdir -p "$run_root/checkpoints"
coverage_build="$(mktemp -d "$run_root/coverage-build.XXXXXX")"
resume_args=()
if [[ "${RESUME:-0}" == "1" ]]; then
  resume_args=(--resume)
fi
date -u +%Y-%m-%dT%H:%M:%SZ > "$run_root/started-utc.txt"
python3 "$artifact_root/verify_submission.py" "$table_root" \
  --workers "$exact_workers" \
  --coverage-workers "$coverage_workers" \
  --checkpoints "$run_root/checkpoints" \
  --codes "$run_root/codes.u32le" \
  --coverage-binary "$coverage_build/coverage_fast" \
  --report "$run_root/verification-summary.json" \
  "${resume_args[@]}" \
  2>&1 | tee "$run_root/verification.log"
status="${PIPESTATUS[0]}"
printf '%s\n' "$status" > "$run_root/exit-code.txt.tmp"
mv "$run_root/exit-code.txt.tmp" "$run_root/exit-code.txt"
date -u +%Y-%m-%dT%H:%M:%SZ > "$run_root/finished-utc.txt"
exit "$status"
