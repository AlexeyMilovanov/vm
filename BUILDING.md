# Building and verifying the Lean proofs

This repository is a Lean package; `lakefile.toml` is at the repository root.
The commands below are the release commands actually exercised on the
submission commit.

## Pinned environment

| Component | Version |
|---|---|
| Lean | `leanprover/lean4:v4.31.0` |
| Lake | the version shipped with Lean 4.31 |
| mathlib | `v4.31.0`, pinned by `lake-manifest.json` |

Install a recent `elan`; the checked-in `lean-toolchain` selects the exact Lean
version.  The validator additionally requires Git, Python 3, and ripgrep.

## One-command validation

From a clean clone:

```bash
bash scripts/validate.sh --fetch-cache
```

The `--fetch-cache` flag downloads the pinned mathlib cache on the first run.
After the cache is present, use:

```bash
bash scripts/validate.sh
```

The validator performs three independent gates:

1. builds every tracked Lean library source, including the statement-lock
   modules, and separately elaborates every import wrapper under
   `scripts/smoke/`; the metaprogram used by the axiom audit is not treated as
   library code;
2. runs a comment-aware hygiene scan over every tracked Lean source,
   rejecting `sorry`, `sorryAx`, `admit`, `native_decide`, `Lean.ofReduceBool`,
   project `axiom`, and `unsafe` declarations;
3. imports every tracked library module, including the statement locks, and
   uses `Lean.collectAxioms` to reject any theorem depending on an axiom other
   than `propext`, `Classical.choice`, or `Quot.sound`.

Successful output ends with:

```text
BUILD_RC=0
SMOKE_RC=0
PLACEHOLDER_RC=0
AXIOM_RC=0
VALIDATION_RC=0
```

The axiom checker is a build-time metaprogram.  Its own `unsafe main` is not a
mathematical theorem and is excluded from the library-source scan and audit.

## Individual commands

Build the complete public library:

```bash
lake build
```

Build the result and separation umbrellas explicitly:

```bash
lake build HeadComplexity.Results.All
lake build HeadComplexity.Separations.All
lake build HeadComplexity.TypicalLogCloseness
```

Build and elaborate the one-marked-bit exact theorem and its statement lock:

```bash
lake build HeadComplexity.TypicalLogCloseness.MarkedBit
lake build HeadComplexity.StatementLocks.MarkedBit
lake env lean scripts/smoke/FrozenMarkedBit.lean
```

Run the frozen separation statement smoke test:

```bash
lake build HeadComplexity.StatementLocks.Separations
lake env lean scripts/smoke/FrozenStatements.lean
```

Run only the placeholder scan:

```bash
python3 scripts/check_lean_placeholders.py
```

Run the all-theorem axiom audit after building:

```bash
files=()
while IFS= read -r -d '' file; do
  case "$file" in
    scripts/AxiomCheck.lean|scripts/smoke/*.lean) ;;
    *) files+=("$file") ;;
  esac
done < <(git ls-files -z -- '*.lean')
lake env lean --run scripts/AxiomCheck.lean "${files[@]}"
```

## Clean-clone release check

For an adversarial reproduction, do not reuse an existing `.lake` directory:

```bash
git clone https://github.com/AlexeyMilovanov/vm.git vm-clean
cd vm-clean
git checkout takehome-submission-2026-08-30-v2
bash scripts/validate.sh --fetch-cache
```

The first run is dominated by downloading the mathlib cache.  With the cache
available, the full build and audit ordinarily take a few minutes on a modern
multi-core machine.  `LEAN_NUM_THREADS` may be set to cap parallelism.

## Rechecking the five-bit certificate table

The 12 GB census is distributed as assets of the
[`n5-certificate-table-v1` GitHub release](https://github.com/AlexeyMilovanov/vm/releases/tag/n5-certificate-table-v1),
not as objects in Git history.  With the GitHub CLI installed, download and
verify it as follows:

```bash
mkdir -p merged-complete-v1
gh release download n5-certificate-table-v1 \
  --repo AlexeyMilovanov/vm \
  --pattern 'manifest.json' \
  --pattern 'shard-*.jsonl' \
  --dir merged-complete-v1
bash artifacts/n5-certificate-table-proof-v1/verify.sh \
  merged-complete-v1 \
  fresh-verification-run
```

The view-only Google Drive location in [SUBMISSION.md](SUBMISSION.md) remains
available as a mirror.

The successful report must contain `"ok": true`, exactly `9,340,584` rows,
`298,898,688` vertex evaluations, and zero noncanonical truth tables.  The
manifest in the proof package fixes the SHA-256, size, row count, and endpoints
of every shard.

This external check has a different trust boundary from Lean: it trusts the
small Python/C checker, Python exact integer/rational arithmetic, the C
compiler/runtime, and the rerun machine.  It is never imported by a Lean
theorem in the default library.
