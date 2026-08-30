# Complete five-bit certificate table: reproducible verifier

This directory is the small, search-independent checking package for the
12 GB certificate table at

    /home/lesha/n5-certificate-table-build/candidate-v2/merged-complete-v1

The intended mathematical conclusion is

    deg_pm(f) = POIC_2(f) = H*(f)

for every Boolean function on at most five variables.

The proof is computational but exact.  The checker does not import the search
programs, NumPy, SciPy, pickle files, floating-point margins, or the historical
campaign logs.  It uses Python's standard library for rational/integer
arithmetic and a short C/OpenMP program for the 4.48-billion finite symmetry
comparisons.

The `source` object retained in each row is provenance metadata only.  The
proof does not trust it: correctness is re-established from the truth table
and the two self-contained certificates.

## What one row proves

A row names a canonical five-bit truth table and an integer `d`.

The upper certificate gives exact rational coefficients for

    theta_0 + sum_{h=1}^d
        (a_{h,0} + sum_i a_{h,i} x_i)
        / (1 + sum_i w_{h,i} z_{h,i}),

where every `w_{h,i}` is positive and, for each head, either all
`z_{h,i}=x_i` or all `z_{h,i}=1-x_i`.  The verifier evaluates this expression
exactly at all 32 vertices, rejects zero values, and checks the requested sign.
This proves `H*(f) <= d`.

The lower certificate is a nonzero positive integral weight vector
`lambda_x` satisfying

    sum_x lambda_x sign(f(x)) product_{i in S} x_i = 0

for every `|S| <= d-1`.  If a polynomial of degree at most `d-1` strictly
sign-represented `f`, its positive weighted signed sum would be both zero
(by these moment equations) and strictly positive (pointwise), a
contradiction.  Hence `deg_pm(f) >= d`.

The standard clearing-denominators inequality gives
`deg_pm(f) <= H*(f)`, so the two certificates prove
`deg_pm(f)=H*(f)=d`.  The sandwich
`deg_pm <= POIC_2 <= H*` then gives the three-way equality.

## Why the rows cover every function

The table has one row for each orbit under coordinate permutation, global
input complementation, and output complementation.  The verifier independently
recomputes the Burnside count `9,340,584`, proves that the codes are strictly
increasing, and checks that every stored code is minimal in its full
480-element orbit.  See [COVERAGE_ARGUMENT.md](COVERAGE_ARGUMENT.md) for the
short proof that these checks imply exact coverage.

Functions of fewer than five variables are padded by dummy variables and then
the resulting certificate is restricted back.  Threshold degree is unchanged
by padding, and restricting a legal head certificate remains legal.

## Reproduce

Requirements:

* Linux or WSL;
* Python 3.10 or newer;
* a C compiler supporting OpenMP (for example GCC);
* about 12 GB for the table and about 40 MB for the generated code list.

Run the quick positive/negative tests:

    N5_CERTIFICATE_TABLE=/path/to/merged-complete-v1 \
      python3 test_submission_verifier.py

Run the complete exact check:

    EXACT_WORKERS=6 COVERAGE_WORKERS=6 \
      bash verify.sh /path/to/merged-complete-v1 /path/to/verification-run

By default the command performs a fresh exact check even if old checkpoint
files are present, and it always compiles the C accelerator into a fresh
directory.  For recovery after an interrupted run on one's own immutable
copy of the table, set `RESUME=1`.  A checkpoint is then reused only when the
verifier hash and the manifest's shard path, size, hash, row count, and
endpoint metadata all agree.  An adversarial audit should use a new run
directory and leave `RESUME` unset.

Success means all of the following:

* exit code `0`;
* `verification-summary.json` contains `"ok":true`;
* exactly `9,340,584` exact certificate rows and `298,898,688` vertex
  evaluations were checked;
* the truth-table digest equals
  `ce9b36b73f9b088e62a294ce3b77204c37bc28fc16cfbee221e9208c8897e270`;
* the Burnside orbit count and full canonicality pass.

## Archived fresh run

The archived run on 2026-08-30 passed all checks:

* start: `2026-08-30T07:58:52Z`;
* finish: `2026-08-30T09:20:41Z`;
* verifier time: `4909.376218991994` seconds;
* `77/77` fresh shards, `0` resumed shards;
* `9,340,584` rows and `298,898,688` exact vertex evaluations;
* `0` noncanonical rows among all `9,340,584` codes;
* maximum support of an integral lower witness: `32`.
* all five quick positive/negative tests passed, including an independent
  Python-versus-C comparison on fixed pseudorandom truth tables.

Key SHA-256 locks:

    table manifest  9197b62b6836c32e0ae0a872343f62a8fcbda7dcfdbdca1021b5bfee2f8c993a
    verifier        54befda7dd212f720dc9df29b368763639327c27bbc9bedf48f869ec09073566
    coverage source d8fe8d4f45fa3457f69d618fb6dcc9015a4fc3af8a59bedddcf5f058b8a8a2d3
    truth tables    ce9b36b73f9b088e62a294ce3b77204c37bc28fc16cfbee221e9208c8897e270
    UInt32 code list 505407f6752185790eeff297b0a3a0e2d586063abe45d2e228c95d3d30572e91

The authoritative structured result is
`reports/verification-summary.json`; the complete transcript is
`reports/verification.log`.

## Files and trust boundary

* `verify_submission.py`: complete row, manifest, digest, Burnside, and
  coverage orchestration; standard library only.
* `coverage_fast.c`: transparent finite symmetry accelerator.
* `table-manifest.json`: portable copy of the manifest, including the size,
  row count, endpoints, and SHA-256 hash of every one of the 77 table shards.
* `ENVIRONMENT.md`: versions and resource settings of the archived run.
* `verify.sh`: one portable reproducible command.
* `test_submission_verifier.py`: accepts genuine witnesses and rejects
  deliberately corrupted upper, lower, and coverage evidence.
* `make_artifact_lock.py`: freezes the successful report and all checking
  sources into `ARTIFACT_LOCK.json`.
* `reports/verification-summary.json`: authoritative machine-readable result
  of the archived fresh run (present only after that run succeeds).

This is stronger than trusting the search: a reader need only trust and audit
the small checker, Python's exact integer/rational implementation, the C
compiler/runtime, and the machine on which they rerun it.  It is not a
kernel-checked Lean proof; a malicious machine or compiler is outside this
artifact's trust boundary.
