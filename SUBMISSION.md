# Take-home submission map

This file separates the supplied autoresearch results, the new mathematical
results, and the trust boundary of each verification artifact.

## Selected results from the supplied run (Part One)

The writeup highlights the linear-fractional normal form, the general
threshold-degree lower bound, exact symmetric complexity, the counting lower
bound, and the eight-bit Hamming-threshold separation.  The mathematical
statement of the eight-bit theorem belongs to the supplied run; this
repository adds its complete Lean formalization.

## New results (Part Two)

### Explicit asymptotic separation

For `m >= 2`, the kernel-checked theorem `ndisj_separation_full` gives

```text
thresholdDeg (NDISJ_m) = 2,
m / (4 log_2(8m)) <= HStar (NDISJ_m),
HStar (NDISJ_m) <= m.
```

The split-shattering/Warren proof turns the finite separation in the supplied
run into an explicit family of constant threshold degree and growing head
complexity.  The distance-threshold/XOR-tensor results provide an independent
formalized separation route.

### Typical logarithmic closeness

For `n >= 64`, the kernel-checked `typical_log_closeness` theorem bounds the
number of truth tables violating

```text
HStar <= 512 * POIC2 * (floor(log_2 POIC2) + 1)
```

by `2^(2^(n-1))`.  Out of `2^(2^n)` functions, this is a fraction at most
`2^(-2^(n-1))`.

### Exact equality with one marked bit

For every Boolean function of the form

```text
f(z,y) = F(z, |y|),
```

with one marked bit and one fully symmetric block, the kernel-checked theorem
`markedBit_exact` proves

```text
thresholdDeg(f) = RelaxedPOIC2(f) = POIC2(f) = HStar(f).
```

This is an infinite-class exact theorem, not a finite census or a numerical
observation.  Its implementation is
`HeadComplexity/TypicalLogCloseness/MarkedBit.lean`, and its frozen public
statement is in `HeadComplexity/StatementLocks/MarkedBit.lean`.

### Exact five-bit frontier

The external exact certificate table proves

```text
thresholdDeg(f) = POIC2(f) = HStar(f)
```

for every Boolean function on at most five variables.  Consequently the
smallest arity admitting `thresholdDeg < HStar` lies in `{6,7,8}`.

The table contains `9,340,584` canonical rows in `77` JSONL shards and
`12,200,404,894` shard bytes.  Its copied manifest has SHA-256

```text
9197b62b6836c32e0ae0a872343f62a8fcbda7dcfdbdca1021b5bfee2f8c993a
```

Primary data release:

```text
https://github.com/AlexeyMilovanov/vm/releases/tag/n5-certificate-table-v1
```

Google Drive mirror:

```text
https://drive.google.com/open?id=1IeW5qqoim6V4Pdp34xziR6r-qoAaATU9
```

The Git repository contains the verifier, complete per-shard manifest, hashes,
and archived fresh-run report.  The 12 GB table is attached as release assets
rather than stored in Git history.

## Reproduction

The audited repository snapshot is the immutable tag
`takehome-submission-2026-08-30-v2`.

Lean release validation:

```bash
bash scripts/validate.sh --fetch-cache
```

Download and verify the five-bit table:

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

## Trust boundaries

* The Lean theorems, including `markedBit_exact`, contain no proof placeholders or native decision
  procedures and depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
* The full census is an exact computer-checked proof, not a Lean theorem.  A
  rerun trusts the small Python/C checker, Python integer/rational arithmetic,
  the compiler/runtime, and the machine.
* Failed numerical searches are not used as lower bounds.
* The general statements `POIC2 = HStar` and
  `HStar <= poly(POIC2)` remain open.

## Tool disclosure

OpenAI Codex was the primary research, implementation, proof-integration, and
verification agent.  Gemini, Claude/Opus/Fable, and Jules were used for idea
generation, independent criticism, Lean proof attempts, and bounded numerical
search.  Search outputs were promoted to mathematical claims only after exact
certificate checking; the final Lean and census audits were run independently
of the search programs.  The accompanying submission form contains the same
disclosure in concise form.
