# Head complexity: Lean 4 formalization

This repository contains a Lean 4.31 formalization of head complexity for
Boolean functions computed by one-layer attention.  It defines the attention
model, relates it to algebraic complexity measures, and proves explicit exact
results, separations, and counting theorems.

The audited release is tagged `takehome-submission-2026-08-30-v2`.

## Main definitions

For a Boolean function `f : {0,1}^n -> {0,1}`:

* `HStar n f` is the least number of attention heads needed by the formalized
  one-layer model;
* `thresholdDeg f` is the least degree of a real polynomial that strictly
  sign-represents `f` on the Boolean cube;
* `POIC2 n f` is the canonical two-pole intermediate complexity measure;
* `RelaxedPOIC2 n f` is the relaxed version used in the counting argument.

The model definitions are under `HeadComplexity/Model/`, and the algebraic
atoms and conversions are under `HeadComplexity/Atoms/`.

## Formalized results

### Algebraic foundation

The following theorem endpoints are kernel checked:

* `HStar_eq_Lfrac`: head complexity equals linear-fractional complexity;
* `degree_le_of_computableWithHeadsN`: every `H`-head representation gives a
  sign polynomial of degree at most `H`, hence
  `thresholdDeg(f) <= HStar(f)`;
* `HStar_symmetricFn`: exact head complexity of every symmetric Boolean
  function in terms of its profile sign changes;
* `HStar_parity`: `HStar(XOR_n) = n`;
* `HStar_le_universal_boolean`: the universal `2^n - 1` upper bound.

The public facade is
[`HeadComplexity/Results/All.lean`](HeadComplexity/Results/All.lean).

### Explicit strict and asymptotic separations

The separation layer formalizes sign rank, the head-to-sign-rank bridge,
Forster's bound, the required spectral and Kronecker facts, a weak Warren
sign-pattern theorem, and split shattering.  Its main endpoints include:

* `theorem189_eight_bit_hamming_threshold`:
  `thresholdDeg(f8) = 2` and `HStar(f8) = 3`;
* `f10_strict_separation`: a separate ten-bit strict separation;
* `theoremA_full`: an explicit constant-threshold-degree family with
  unbounded ratio `HStar/thresholdDeg`;
* `theoremB_full`: a tensor family with a linear additive gap;
* `ndisj_separation_full`: for every `m >= 2`,

  ```text
  thresholdDeg(NDISJ_m) = 2,
  m / (4 log_2(8m)) <= HStar(NDISJ_m),
  HStar(NDISJ_m) <= m.
  ```

The complete public inventory is
[`HeadComplexity/Separations/All.lean`](HeadComplexity/Separations/All.lean).

### Canonical `POIC2` hierarchy and typical closeness

The formalization proves the hierarchy

```text
thresholdDeg(f) <= RelaxedPOIC2(f) <= POIC2(f) <= HStar(f).
```

For every `n >= 64`, `typical_log_closeness` proves that at most
`2^(2^(n-1))` of the `2^(2^n)` Boolean functions violate

```text
HStar(f) <=
  512 * POIC2(f) * (floor(log_2(POIC2(f))) + 1).
```

Thus the exceptional fraction is at most `2^(-2^(n-1))`.  The same layer
contains the explicit counting lower bound and the fixed-pole universal-bank
theorems.  The umbrella module is
[`HeadComplexity/TypicalLogCloseness.lean`](HeadComplexity/TypicalLogCloseness.lean).

### Exact equality for one marked bit and one symmetric block

Let `z` be one marked Boolean input and let `y` be a fully symmetric block of
arbitrary size.  For every table `F : Bool -> Nat -> Bool`, define

```text
f(z,y) = F(z, |y|).
```

The theorem `markedBit_exact` proves the four-way identity

```text
thresholdDeg(f) = RelaxedPOIC2(f) = POIC2(f) = HStar(f).
```

The proof and reusable interpolation compiler are in
[`HeadComplexity/TypicalLogCloseness/MarkedBit.lean`](HeadComplexity/TypicalLogCloseness/MarkedBit.lean).
Its public, axiom-audited statement lock is
[`HeadComplexity/StatementLocks/MarkedBit.lean`](HeadComplexity/StatementLocks/MarkedBit.lean).

## Building and verification

The repository is pinned to Lean `v4.31.0` and mathlib `v4.31.0`.  From a
clean clone, run:

```bash
bash scripts/validate.sh --fetch-cache
```

On subsequent runs:

```bash
bash scripts/validate.sh
```

The validator:

1. builds every tracked Lean library source, including the statement locks;
2. elaborates the import wrappers under `scripts/smoke/`;
3. performs a hygiene scan for `sorry`, `sorryAx`, `admit`, `native_decide`,
   `Lean.ofReduceBool`, project axioms, and unsafe declarations;
4. audits every theorem in every library module, including the statement-lock
   theorems, with `Lean.collectAxioms`.

The audited release contains no proof placeholders or project-specific trust
extensions.  Its theorems depend only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms.

See [`BUILDING.md`](BUILDING.md) for individual commands and the exact
clean-clone procedure, and [`PROOF_OVERVIEW.md`](PROOF_OVERVIEW.md) for the
proof architecture.
