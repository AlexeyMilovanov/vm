import HeadComplexity.Separations.SignRankBridge
import HeadComplexity.Separations.Forster
import HeadComplexity.Polynomial.ParityThresholdDegree
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.header false

/-!
# Theorem A: constant degree, unboundedly many heads

The base family of `audit/sources/EXPLICIT_GAP.md`: for odd `m`, on `m + m` bits,

  `F_m(x, y) = 1 [ Δ(x, y) ≥ (m + 1) / 2 ]`

(majority of disagreements).  Its threshold degree is exactly `2`, while its
two-block sign matrix is the XOR-pattern of `MAJ_m`, whose spectral norm is
`2 · C(m-1, (m-1)/2)`.  Forster then gives sign-rank at least
`γ_m = 2^(m-1) / C(m-1, (m-1)/2) ~ √(πm/2)`, so by the sign-rank bridge
`H*(F_m) ≥ log₂(γ_m + 2) - 1 → ∞` at constant degree.  First explicit point
beating the corpus's 3-head ceiling: `m = 127`, where `γ > 14` forces
`H* ≥ 4`.
-/

namespace HeadComplexity

/-- The distance-majority function `F_m` on `m + m` bits. -/
def distThreshold (m : ℕ) : (Fin (m + m) → Bool) → Bool :=
  fun z => decide ((m + 1) / 2 ≤ hammingDist (leftBits m m z) (rightBits m m z))

/-- The Forster ratio `γ_m = 2^(m-1) / C(m-1, (m-1)/2)` of the family:
`2^m / specNorm` of its sign matrix.  Asymptotically `√(π m / 2)`. -/
noncomputable def forsterRatio (m : ℕ) : ℝ :=
  2 ^ (m - 1) / ((m - 1).choose ((m - 1) / 2))

/-- Upper half of the degree computation: `Δ(x,y) - m/2` is a quadratic sign
polynomial for `F_m` (never zero since `m` is odd). -/
theorem thresholdDegLE_distThreshold {m : ℕ} (hm : Odd m) :
    ThresholdDegLE (distThreshold m) 2 := by
  sorry

/-- Exact degree: restricting all but one disagreement pair to fixed
disagreement leaves a 2-bit XOR, so degree `2` is also necessary. -/
theorem thresholdDeg_distThreshold {m : ℕ} (hm : Odd m) :
    thresholdDeg (distThreshold m) = 2 := by
  sorry

/-- The two-block sign matrix of `F_m` is the XOR-pattern of `MAJ_m`; the
characters diagonalize it, the top eigenvalue sits at Fourier level `1`, and
equals `2 · C(m-1, (m-1)/2)`. -/
theorem specNorm_signMatrix_distThreshold {m : ℕ} (hm : Odd m) :
    specNorm (signMatrix m m (distThreshold m)) =
      2 * ((m - 1).choose ((m - 1) / 2)) := by
  sorry

/-- Forster's lower bound instantiated on the family: `γ_m ≤ signRank`. -/
theorem forsterRatio_le_signRank {m : ℕ} (hm : Odd m) :
    forsterRatio m ≤ (signRank (signMatrix m m (distThreshold m)) : ℝ) := by
  sorry

/-- **Theorem A** (`audit/sources/EXPLICIT_GAP.md`): the family `F_m` has threshold
degree `2` while `γ_m ≤ 2 ^ (H* + 1) - 2`, hence
`H*(F_m) ≥ log₂(γ_m + 2) - 1 = (1/2) log₂ m - O(1)` grows without bound at
constant degree. -/
theorem theoremA {m : ℕ} (hm : Odd m) :
    thresholdDeg (distThreshold m) = 2 ∧
      forsterRatio m ≤ (2 : ℝ) ^ (HStar (m + m) (distThreshold m) + 1) - 2 := by
  sorry

/-- Quantitative growth of the Forster ratio: `γ_m ≥ √(m - 1)` for odd
`m ≥ 3` (central binomial estimate). -/
theorem sqrt_le_forsterRatio {m : ℕ} (hm : Odd m) (h3 : 3 ≤ m) :
    Real.sqrt ((m : ℝ) - 1) ≤ forsterRatio m := by
  sorry

/-- **Theorem A, explicit point**: at `m = 127` (254 input bits) the Forster
ratio exceeds `14 = 2^4 - 2`, so four heads are necessary — the first explicit
bound beyond the corpus's 3-head frontier.  (`m = 125` gives only `13.98`;
`127` is minimal for this route.) -/
theorem four_le_HStar_distThreshold_127 :
    4 ≤ HStar (127 + 127) (distThreshold 127) := by
  sorry

end HeadComplexity
