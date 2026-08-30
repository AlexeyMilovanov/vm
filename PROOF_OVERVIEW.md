# Proof architecture

The repository has four proof layers.  The first three are Lean-kernel checked;
the fourth is a separate exact computational artifact.

## 1. Model and algebraic normal form

`HeadComplexity/Model/Head.lean` defines the one-layer attention model and
`HStar`.  A head's query readout is a linear-fractional atom on the Boolean
cube.  The two conversion directions are formalized in `Atoms/`, yielding

```text
HStar(f) = Lfrac(f).
```

Clearing positive denominators converts an `H`-head score to a degree-at-most
`H` sign polynomial, proving

```text
thresholdDeg(f) <= HStar(f).
```

This is the main lower-bound spine.  Explicit fractional atoms, partial
fractions, and interpolation form the upper-bound spine.  Together they give
the level-zero/one classification, parity, symmetric exactness, and universal
upper bounds collected in `HeadComplexity/Results/All.lean`.

## 2. Explicit separations

The separation layer introduces sign matrices and proves the head-to-sign-rank
bridge

```text
H heads  =>  signRank <= 2^(H+1) - 2.
```

Its proof clears all denominators and groups the resulting matrix by subsets
of heads.  The layer then formalizes the required sign-rank, spectral, Forster,
Kronecker, and Warren machinery.

There are three paper-facing outcomes:

* the exact eight-bit Hamming-threshold theorem
  `thresholdDeg f8 = 2`, `HStar f8 = 3`;
* distance-threshold and XOR-tensor families with unbounded ratio and linear
  additive gap;
* the split-shattering theorem applied to `NDISJ_m`, giving constant threshold
  degree and `Omega(m / log m)` head complexity.

The public inventory is `HeadComplexity/Separations/All.lean`; detailed
dependency notes are in `SEPARATIONS.md` and `PROOFS.md`.

## 3. Canonical `POIC2`, counting, and typicality

`HeadComplexity/TypicalLogCloseness/` defines exact affine denominators,
topologies, relaxed and canonical `POIC2`, and proves

```text
thresholdDeg <= RelaxedPOIC2 <= POIC2 <= HStar.
```

Two independent ingredients produce the typical theorem:

1. a Hamming-code/power-block fixed-pole bank spans every truth table with
   `O(2^n/n)` heads;
2. a Warren count bounds the `POIC2 <= Q` sublevel by `2^(O(n^2 Q))`.

Splitting at `Q` of order `2^n/n^2` proves that, outside a doubly
exponentially small fraction, `HStar = O(POIC2 log POIC2)`.  The explicit
finite endpoint is `typical_log_closeness` in `Headline.lean`.

The same counting infrastructure yields an explicit finite form of the
worst-case `Omega(2^n/n^2)` lower bound and the fixed-pole `Bank` theorems.

The same layer also contains the independent infinite-class theorem
`markedBit_exact`.  For every function `f(z,y) = F(z, |y|)` with one marked
bit and one fully symmetric block, it proves

```text
thresholdDeg(f) = RelaxedPOIC2(f) = POIC2(f) = HStar(f).
```

The proof slices a minimum-degree strict sign polynomial at `z = 0,1`,
symmetrizes the remaining block, and compiles the two univariate slices into
legal fractional atoms with shared interpolation data.  Its implementation is
`HeadComplexity/TypicalLogCloseness/MarkedBit.lean` and its statement lock is
`HeadComplexity/StatementLocks/MarkedBit.lean`.

## 4. Five-bit exact census

The complete theorem for `n <= 5` is not part of the Lean-kernel layer.  Its
proof table has one canonical row per legal symmetry orbit.  Every row has:

* an exact rational legal head certificate, proving `HStar <= d`;
* a positive integral signed-moment witness, proving
  `thresholdDeg >= d`.

The general sandwich closes equality, while an independent Burnside count and
full canonicality scan prove coverage.  The small search-independent checker,
manifest, and archived report are under
`artifacts/n5-certificate-table-proof-v1/`; the table itself is distributed
separately as documented in `SUBMISSION.md`.

## Trust summary

| Layer | Status | Trust boundary |
|---|---|---|
| Algebraic foundation | proved | Lean kernel + standard axioms |
| Separations, Warren, NDISJ | proved | Lean kernel + standard axioms |
| `POIC2` sandwich, marked-bit exactness, and typicality | proved | Lean kernel + standard axioms |
| Full five-bit census | exact external proof | small Python/C verifier + machine |

The general equality and polynomial-equivalence questions between `POIC2` and
`HStar` remain open.
