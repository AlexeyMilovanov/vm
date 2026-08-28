# Eight-bit Hamming threshold: module reconstruction plan

Date: 2026-08-28

## Implementation status

Implemented on 2026-08-28.

- The original 4,817-line compilation unit is now a 50-line public wrapper.
- The proof is split into `Core` (323 lines), `Curvature` (1,119),
  `K4Cone` (1,263), `Normalization` (1,231), `Obstruction` (695), and
  `Certificate` (332).
- Cross-module helpers live in `HeadComplexity.EightBitInternal`; helpers that
  do not cross a boundary remain `private`.
- The old public declaration set and final theorem statements are preserved.
- Every new module and the wrapper compile with no `sorry` or `admit`.
- The reconstructed package itself emits no Lean or strict style-linter
  warnings. Warnings replayed from older imported modules are outside this
  package.
- The cached complete target build takes about eight seconds; the wrapper
  itself elaborates in roughly 2.5 seconds.

Target:

`HeadComplexity/Separations/EightBitHammingThreshold.lean`

## Current state

- The file is complete: it contains no `sorry`, `admit`, or declaration with an
  intentionally missing proof.
- It has 4,817 physical lines (about 4,447 code lines).
- The ordinary Lean warnings found during the final proof-closing pass have been
  removed.
- A cold rebuild of the single module took about 215 seconds while the low-priority
  N5 census was using six CPU workers.
- The cold Lean process reached roughly 4.7 GiB RSS. This is module elaboration and
  code-generation memory, not a heartbeat failure.
- After refreshing the `.olean`, the unchanged target rebuild took about 8 seconds
  and under 0.9 GiB for the Lake process.
- A full exported `trace.profiler` run is not a useful diagnostic for this module:
  retaining the nested trace made the diagnostic itself slower and more
  memory-hungry than the normal build. It was stopped after five minutes.

There is therefore no evidence of one theorem that is stuck or close to a
heartbeat limit. The practical problem is the size of the compilation unit and
the fact that every edit invalidates the whole unit.

Lake's strict Mathlib style pass additionally reports formatting-only findings
(long lines, blank lines inside tactic sequences, and a few flexible
`simp`/`simp_all` calls). These findings are not responsible for the memory
profile. They should be removed module by module during extraction, so that the
large move is not mixed with one monolithic formatting diff.

## Semantic blocks in the current file

The file already has good mathematical boundaries, but they are interleaved in
one Lean module:

1. Lines 24--268: `f8`, bit helpers, the degree-two upper bound, and basic
   matrix/quadratic-form vocabulary.
2. Lines 269--1,343: checkerboard curvature, signed permutations, the explicit
   curvature certificate, and `f8_quadratic_mixed_negative`.
3. Lines 1,344--1,815: `F8NormalizedSystem`, factor data, and normalization
   primitives.
4. Lines 1,816--3,070: generic column-max, K4 allocation, choice-cone, and
   spectral machinery.
5. Lines 3,071--3,790: the cleared two-atom polynomial, factorization defects,
   and construction of an `F8NormalizedSystem`.
6. Lines 3,802--4,472: nonexistence of the normalized system, including the
   nonzero and perturbative cases, and the lower bound.
7. Lines 4,473--4,816: the explicit integral three-head certificate and the
   final exact theorem.

The main structural defect is that blocks 3 and 5 belong together but are
separated by the independent K4 block.

## Proposed module graph

```text
EightBitHammingThreshold/Core
        |                 \
        v                  v
    Curvature            K4Cone
        |
        v
   Normalization ---------+
        |                 |
        +--------+--------+
                 v
            Obstruction

Core ----------------> Certificate

Obstruction + Certificate
              |
              v
EightBitHammingThreshold (small public wrapper)
```

No edge points back toward `Core`, and `K4Cone` does not import the
two-head normalization layer.

## Proposed files

### 1. `EightBitHammingThreshold/Core.lean`

Expected size: 250--350 code lines.

Keep:

- `f8` and its elementary Boolean/bit lemmas;
- `mixedMatrix4`, `quadraticForm4`, and the spectral predicates used by
  more than one later module;
- the data-only declaration of `F8NormalizedSystem`;
- genuinely generic small `Fin 4` utilities shared across blocks.

This module must not import the two-head bridge or K4 proofs.

### 2. `EightBitHammingThreshold/Curvature.lean`

Expected size: 1,050--1,150 code lines.

Move the signed-permutation/checkerboard development and end at
`f8_quadratic_mixed_negative`. This is the reusable finite certificate that
the normalization reduction consumes.

### 3. `EightBitHammingThreshold/K4Cone.lean`

Expected size: 1,200--1,350 code lines.

Move the column-max picker, K4 edge allocation, probabilistic choice-cone
construction, normalized capacity proof, and spectral inequality. This block is
mathematically independent of the two-head factorization once its small matrix
vocabulary comes from `Core`.

### 4. `EightBitHammingThreshold/Normalization.lean`

Expected size: 1,100--1,250 code lines.

Join the currently separated normalization blocks:

- factor data and legal normalization;
- the cleared two-atom polynomial;
- factor curvature and defects;
- `two_heads_yield_f8NormalizedSystem`.

This is the exact bridge from the POIC/two-head representation to the finite
normalized obstruction.

### 5. `EightBitHammingThreshold/Obstruction.lean`

Expected size: 600--750 code lines.

Import `Normalization` and `K4Cone`. Keep the normalized-system
nonexistence proof, the nonzero case, perturbation/closure, and the lower-bound
theorem.

### 6. `EightBitHammingThreshold/Certificate.lean`

Expected size: 300--400 code lines.

Move the explicit integer three-head representation and its verification here.
It is a leaf over `Core` and can be rebuilt independently of all lower-bound
geometry.

### 7. Public wrapper

`HeadComplexity/Separations/EightBitHammingThreshold.lean` should become a
small wrapper importing `Obstruction` and `Certificate`, then exposing only
the final exact value and theorem-189-facing API.

## Visibility rule

Lean's `private` declarations cannot be referenced from another module. The
split must therefore not mechanically turn every helper into a root-level
public name.

Use an internal namespace such as:

```lean
namespace HeadComplexity.EightBit
```

Cross-module implementation lemmas become ordinary declarations inside that
namespace. Helpers that remain within one file stay `private`. Only the
existing intended external API is re-exposed in `HeadComplexity`.
