# Complete exact certificate table for all Boolean functions on at most five bits

Date: 2026-08-30. Status: **VERIFIED / COMPLETE**.

## Theorem

For every Boolean function `f` on at most five variables,

    deg_pm(f) = POIC_2(f) = H*(f).

Consequently the least arity `n_sep` at which threshold degree can be
strictly smaller than head complexity satisfies

    n_sep in {6, 7, 8}.

The upper endpoint follows from the archived eight-bit separation. This note
records the new, search-independent computational proof of the lower endpoint.

## Complete table

The table is

    /home/lesha/n5-certificate-table-build/candidate-v2/merged-complete-v1

It contains 77 plain JSONL shards, 9,340,584 rows, and 12,200,404,894 shard
bytes. Its manifest SHA-256 is

    9197b62b6836c32e0ae0a872343f62a8fcbda7dcfdbdca1021b5bfee2f8c993a.

The copied manifest in the proof package lists the byte size, row count,
endpoint truth tables, and SHA-256 digest of every shard.

## What each row proves

For its canonical truth table and integer `d`, a row contains:

1. an exact rational legal `d`-head sign representation, proving
   `H*(f) <= d`;
2. a nonzero positive integral signed-moment/Farkas witness orthogonal to every
   multilinear monomial of degree at most `d-1`, proving
   `deg_pm(f) >= d`.

The general inequality `deg_pm <= H*` closes
`deg_pm(f)=H*(f)=d`. The standard sandwich
`deg_pm <= POIC_2 <= H*` gives the three-way equality. Every rational sign,
denominator-legality condition, and every integral moment is checked from
scratch; source/search metadata is not trusted.

## Coverage proof

The legal symmetry group consists of coordinate permutations, simultaneous
complementation of all five input bits, and output complementation. Its order
is 480. An independent integer Burnside computation gives

    fixed-point sum = 4,483,480,320
    orbit count     = 4,483,480,320 / 480 = 9,340,584.

The table codes are strictly increasing. The coverage checker compared every
stored code against all 480 transforms and found zero noncanonical codes.
Thus the table contains 9,340,584 distinct orbit minima, exactly the Burnside
number, and hence exactly one representative of every orbit.

The detailed proof is in
`artifacts/n5-certificate-table-proof-v1/COVERAGE_ARGUMENT.md`.

## Fresh independent verification

The small verifier in
`artifacts/n5-certificate-table-proof-v1/verify_submission.py` uses only the
Python standard library for all certificate arithmetic. It does not import
the builders, search programs, NumPy, SciPy, pickle files, or numerical
margins. A short C/OpenMP program accelerates only the finite symmetry
comparisons.

The archived run was fresh: no exact-shard checkpoint was reused.

    start                    2026-08-30T07:58:52Z
    finish                   2026-08-30T09:20:41Z
    verifier elapsed         4909.376218991994 s
    fresh/resumed shards     77 / 0
    rows                     9,340,584
    exact vertex checks      298,898,688
    noncanonical codes       0
    maximum lower support    32
    exit code                0

The final report has `"ok":true`. Its important digests are:

    truth-table stream  ce9b36b73f9b088e62a294ce3b77204c37bc28fc16cfbee221e9208c8897e270
    UInt32 code list    505407f6752185790eeff297b0a3a0e2d586063abe45d2e228c95d3d30572e91
    verifier source     54befda7dd212f720dc9df29b368763639327c27bbc9bedf48f869ec09073566
    coverage source     d8fe8d4f45fa3457f69d618fb6dcc9015a4fc3af8a59bedddcf5f058b8a8a2d3

## Reproduce and trust boundary

Navigation:

* `artifacts/n5-certificate-table-proof-v1/README.md` -- proof and command;
* `artifacts/n5-certificate-table-proof-v1/table-manifest.json` -- all shard
  hashes;
* `artifacts/n5-certificate-table-proof-v1/reports/verification-summary.json`
  -- authoritative machine-readable result;
* `artifacts/n5-certificate-table-proof-v1/reports/verification.log` -- full
  run transcript.

Reproduce with a fresh run directory:

    EXACT_WORKERS=6 COVERAGE_WORKERS=6 \
      bash artifacts/n5-certificate-table-proof-v1/verify.sh \
      /path/to/merged-complete-v1 /path/to/fresh-verification-run

This is an exact computer-checked proof whose small verifier is auditable and
rerunnable. It is not yet a Lean-kernel proof: the full 9.34-million-row table
has not been imported into Lean. Thus the external theorem is complete,
while the separate Lean census layer remains conditional on its row-import
and coverage interfaces.

