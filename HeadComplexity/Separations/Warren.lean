import HeadComplexity.Polynomial.ThresholdDegree
import Warren.Statements
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Set.Card

set_option linter.style.header false

/-!
# A weak Warren-type bound on sign patterns of real polynomials

The integrated Lean 4.31 `Warren` library proves the deliberately
generous, hypothesis-free bound `(8 * (d*k + 1))^m`.  This is weaker than
Warren's sharp `(4 e d k / m)^m`, but it is sufficient for the downstream
split-shattering lower bound after replacing the numerical endpoint by
`(8k)^(4H)`.  The theorem below preserves the frozen `HeadComplexity`
interface and transports the integrated producer theorem definitionally.
-/

namespace HeadComplexity

open MvPolynomial

/-- The set of strict sign patterns realized by the family `P` at points where
no member vanishes: `s i = true` iff `P i` is positive there. -/
def signPatterns {m k : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ) :
    Set (Fin k → Bool) :=
  {s | ∃ x : Fin m → ℝ, (∀ i, eval x (P i) ≠ 0) ∧
        ∀ i, s i = decide (0 < eval x (P i))}

/-- Weak Warren-type bound, matching the frozen Lean 4.28 producer endpoint.
All degenerate cases are included. -/
theorem warren_sign_patterns_weak {m k d : ℕ}
    (P : Fin k → MvPolynomial (Fin m) ℝ)
    (hdeg : ∀ i, (P i).totalDegree ≤ d) :
    ((signPatterns P).ncard : ℝ) ≤ (8 * ((d : ℝ) * k + 1)) ^ m := by
  simpa only [HeadComplexity.signPatterns, _root_.signPatterns] using
    (_root_.warren_sign_patterns_weak P hdeg)

/-- Diagonal consumer bridge used by the H*/NDISJ argument. -/
theorem warren_sign_patterns_diag {H k : ℕ}
    (P : Fin k → MvPolynomial (Fin (2 * H)) ℝ)
    (hdeg : ∀ i, (P i).totalDegree ≤ H) :
    ((signPatterns P).ncard : ℝ) ≤ (8 * ((H : ℝ) * k + 1)) ^ (2 * H) :=
  warren_sign_patterns_weak P hdeg

end HeadComplexity
