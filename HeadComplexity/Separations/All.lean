import HeadComplexity.Separations.TwoBlock
import HeadComplexity.Separations.SignRank
import HeadComplexity.Separations.SignRankBridge
import HeadComplexity.Separations.Warren
import HeadComplexity.Separations.Forster
import HeadComplexity.Separations.DistanceThreshold
import HeadComplexity.Separations.Tensor
import HeadComplexity.Separations.NDISJ

set_option linter.style.header false

/-!
# Separations layer: table of contents

Asymptotic separations between head complexity `H*` and threshold degree
`deg±`, from `audit/sources/EXPLICIT_GAP.md` and `audit/sources/STRENGTHENING.md`.  Unlike
`Results/All.lean`, this layer is **work in progress**: statements are final
(treat them as frozen; see `SEPARATIONS.md`), proofs may contain `sorry`.

External inputs stated as targets:
* `warren_sign_patterns` — Warren 1968 on sign patterns of polynomials;
* `forster` — Forster 2002 sign-rank lower bound;
* `specNorm_kronecker` — spectral norm multiplicativity.

Own results:
* `signRank_le_of_computableWithHeadsN` — the 028 bridge
  `H ≥ 1` heads → sign-rank ≤ `2^(H+1) - 2`;
* `signRank_le_of_thresholdDegLE` + `signRank_le_two_pow_min` — Theorem C,
  the route's degree and dimension ceilings;
* `theoremA` (+ `four_le_HStar_distThreshold_127`) — constant degree,
  `H* ≥ (1/2)·log₂ m - O(1)`;
* `theoremB_HStar` / `theoremB_gap` — explicit linear additive gap;
* `pow_le_of_leftShatters` + `ndisj_separation` — `Ω(m / log m)` heads at
  degree 2 for `NDISJ`;
* `SharpShatteringUpperBound` — the upper-bound half of the `VC = 2H`
  conjecture (a `Prop`, not asserted).
-/
