import HeadComplexity.Polynomial.ThresholdDegree
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Set.Card

set_option linter.style.header false

/-!
# Warren's theorem on sign patterns of real polynomials

Statement of Warren (1968): `k` real polynomials of degree at most `d` in `m`
variables realize at most `(4 e d k / m) ^ m` strict sign patterns.  This is
the analytic engine behind the split-shattering head lower bound
(`audit/sources/STRENGTHENING.md` §1) and the corpus counting bound (theorem 026).
Not in mathlib; stated here as a proof target.
-/

namespace HeadComplexity

open MvPolynomial

/-- The set of strict sign patterns realized by the family `P` at points where
no member vanishes: `s i = true` iff `P i` is positive there. -/
def signPatterns {m k : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ) :
    Set (Fin k → Bool) :=
  {s | ∃ x : Fin m → ℝ, (∀ i, eval x (P i) ≠ 0) ∧
        ∀ i, s i = decide (0 < eval x (P i))}

/-- **Warren's theorem** (Warren 1968, Theorem 3).  `k ≥ m ≥ 1` polynomials of
degree at most `d ≥ 1` in `m` real variables realize at most
`(4 e d k / m) ^ m` strict sign patterns. -/
theorem warren_sign_patterns {m k d : ℕ} (hm : 1 ≤ m) (hk : m ≤ k) (hd : 1 ≤ d)
    (P : Fin k → MvPolynomial (Fin m) ℝ)
    (hdeg : ∀ i, (P i).totalDegree ≤ d) :
    ((signPatterns P).ncard : ℝ) ≤ (4 * Real.exp 1 * d * k / m) ^ m := by
  sorry

end HeadComplexity
