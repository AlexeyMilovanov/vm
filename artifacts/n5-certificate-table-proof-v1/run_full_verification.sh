#!/usr/bin/env bash
set -uo pipefail
artifact_root=/home/lesha/rs-takehome-results/artifacts/n5-certificate-table-proof-v1
table_root=/home/lesha/n5-certificate-table-build/candidate-v2/merged-complete-v1
report_root="$artifact_root/reports"
mkdir -p "$report_root/checkpoints"
date -u +%Y-%m-%dT%H:%M:%SZ > "$report_root/started-utc.txt"
taskset -c 4,6,8,10,12,14 nice -n 15 \
  python3 "$artifact_root/verify_submission.py" "$table_root" \
    --workers 6 --coverage-workers 6 \
    --checkpoints "$report_root/checkpoints" \
    --codes "$report_root/codes.u32le" \
    --report "$report_root/verification-summary.json" \
  2>&1 | tee "$report_root/verification.log"
status="${PIPESTATUS[0]}"
printf '%s\n' "$status" > "$report_root/exit-code.txt.tmp"
mv "$report_root/exit-code.txt.tmp" "$report_root/exit-code.txt"
date -u +%Y-%m-%dT%H:%M:%SZ > "$report_root/finished-utc.txt"
exit "$status"
