# head-complexity

Lean 4.31 formalization and exact computational artifacts for the head
complexity of Boolean functions in one-layer attention.

For a Boolean function `f : {0,1}^n -> {0,1}`, `HStar n f` is the least
number of attention heads needed by the model from the take-home task.  The
repository contains the formalized algebraic model, explicit separations from
threshold degree, a canonical `POIC2` intermediate measure, and the small
search-independent checker for the complete five-bit census.

## Release status

At the submission release, all tracked Lean library sources:

* build against Lean `v4.31.0` and mathlib `v4.31.0`;
* contain no `sorry`, `admit`, `native_decide`, project axiom, or unsafe proof;
* have their theorem declarations audited to depend only on
  `propext`, `Classical.choice`, and `Quot.sound`.

Run the complete build, placeholder scan, and all-theorem axiom audit with:

```bash
bash scripts/validate.sh --fetch-cache  # first run
bash scripts/validate.sh                # subsequent runs
```

See [BUILDING.md](BUILDING.md) for the exact requirements and individual
commands.

## Headline kernel-checked results

### Algebraic foundation

The inherited L1--L13 foundation is fully formalized.  It includes:

* `HStar_eq_Lfrac`: the linear-fractional normal form `H* = L_frac`;
* `degree_le_of_computableWithHeadsN`: `deg_pm(f) <= H*(f)`;
* `HStar_symmetricFn`: exact head complexity of symmetric functions;
* `HStar_parity`: `H*(XOR_n) = n`;
* `HStar_le_universal_boolean`: the universal `2^n - 1` upper bound;
* `f10_strict_separation`: the original ten-bit strict separation.

The result facade is [HeadComplexity/Results/All.lean](HeadComplexity/Results/All.lean).

### Explicit scalable separations

The complete separation layer is imported by
[HeadComplexity/Separations/All.lean](HeadComplexity/Separations/All.lean).
In particular:

* `theorem189_eight_bit_hamming_threshold` proves exactly
  `thresholdDeg f8 = 2` and `HStar 8 f8 = 3`;
* `theoremA_full` proves an explicit constant-degree distance-threshold
  family with unbounded `H*/deg_pm`;
* `theoremB_full` proves a tensor family with a linear additive gap;
* `ndisj_separation_full` proves, for `m >= 2`,

  ```text
  thresholdDeg (NDISJ_m) = 2,
  m / (4 log_2(8m)) <= HStar (NDISJ_m),
  HStar (NDISJ_m) <= m.
  ```

The chain includes formalized head-to-sign-rank clearing, Forster's bound,
the needed weak Warren sign-pattern theorem, and the split-shattering
argument.

### `POIC2` and typical logarithmic closeness

The canonical hierarchy is kernel checked:

```text
thresholdDeg <= RelaxedPOIC2 <= POIC2 <= HStar.
```

For every `n >= 64`, `typical_log_closeness` proves that the number of Boolean
functions satisfying

```text
HStar f > 512 * POIC2 f * (floor(log_2 (POIC2 f)) + 1)
```

is at most `2^(2^(n-1))`, out of `2^(2^n)` truth tables.  Thus the exceptional
fraction is at most `2^(-2^(n-1))`.  The same layer contains the explicit
counting lower bound and the fixed-pole bank theorems.

See [HeadComplexity/TypicalLogCloseness.lean](HeadComplexity/TypicalLogCloseness.lean).

## Complete five-bit census: exact external artifact

The theorem

```text
thresholdDeg(f) = POIC2(f) = HStar(f)  for every Boolean f on at most five bits
```

is established by an exact, search-independent Python/C checker over
`9,340,584` legal symmetry orbits.  Every row contains an exact rational head
upper certificate and an integral threshold-degree lower witness.  A fresh
run checked all `77` shards and `298,898,688` cube evaluations.

This census is **not** claimed as a Lean-kernel theorem: the 12 GB table is not
imported into Lean.  The checker, complete shard manifest, hashes, and archived
verification report are in
[artifacts/n5-certificate-table-proof-v1](artifacts/n5-certificate-table-proof-v1).
The view-only data location and trust boundary are recorded in
[SUBMISSION.md](SUBMISSION.md).

## Navigation

* [SUBMISSION.md](SUBMISSION.md): paper-facing result map and trust boundaries.
* [PROOF_OVERVIEW.md](PROOF_OVERVIEW.md): proof architecture.
* [SEPARATIONS.md](SEPARATIONS.md): detailed separation endpoint inventory.
* [BUILDING.md](BUILDING.md): clean build and verification.
* [PROOFS.md](PROOFS.md): fine-grained informal proofs used during formalization.
* [PROGRESS.md](PROGRESS.md): historical development log, not a status source.

## Open problems

Neither `POIC2 = HStar` nor a strict example `POIC2 < HStar` is known in
general.  The polynomial-equivalence question

```text
HStar(f) <= poly(POIC2(f))
```

also remains open.  Numerical search failures are not lower bounds.
