#!/usr/bin/env bash

set -euo pipefail

script_dir="$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repository_dir="$(dirname -- "$script_dir")"
axiom_check="$script_dir/AxiomCheck.lean"
placeholder_check="$script_dir/check_lean_placeholders.py"
fetch_cache=false

if [ "${1:-}" = "--fetch-cache" ]; then
  fetch_cache=true
  shift
fi
if [ "$#" -ne 0 ]; then
  echo "Usage: $0 [--fetch-cache]" >&2
  exit 2
fi

for command_name in git lake python3; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "Required command not found: $command_name" >&2
    exit 127
  fi
done

cd "$repository_dir"
if [ ! -f lakefile.toml ]; then
  echo "Lean package not found at repository root: $repository_dir" >&2
  exit 1
fi
if [ ! -f "$axiom_check" ] || [ ! -f "$placeholder_check" ]; then
  echo "Validation helper is missing under scripts/." >&2
  exit 1
fi

if $fetch_cache; then
  echo "=== Fetching the pinned mathlib cache ==="
  lake exe cache get
  echo "CACHE_RC=0"
fi

tracked_lean_files=()
while IFS= read -r -d '' source_file; do
  if [ "$source_file" != "scripts/AxiomCheck.lean" ] &&
      [ "$source_file" != "scripts/smoke/FrozenStatements.lean" ]; then
    tracked_lean_files+=("$source_file")
  fi
done < <(git ls-files -z -- '*.lean')

if [ "${#tracked_lean_files[@]}" -eq 0 ]; then
  echo "No tracked Lean sources found." >&2
  exit 1
fi

library_targets=()
for source_file in "${tracked_lean_files[@]}"; do
  library_targets+=("./$source_file")
done

echo "=== Building ${#library_targets[@]} tracked Lean sources ==="
lake build "${library_targets[@]}"
echo "BUILD_RC=0"

echo "=== Elaborating the frozen-statement smoke test ==="
lake env lean scripts/smoke/FrozenStatements.lean
echo "SMOKE_RC=0"

echo "=== Rejecting proof placeholders and extra trust primitives ==="
python3 "$placeholder_check"
echo "PLACEHOLDER_RC=0"

echo "=== Auditing every theorem in ${#tracked_lean_files[@]} modules ==="
lake env lean --run "$axiom_check" "${tracked_lean_files[@]}"
echo "AXIOM_RC=0"

echo "VALIDATION_RC=0"
echo "Validation completed successfully."
