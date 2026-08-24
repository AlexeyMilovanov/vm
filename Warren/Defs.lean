import Mathlib

/-!
# Strict sign patterns of a family of real multivariate polynomials

FROZEN DEFINITION. `signPatterns` is copied verbatim from
`hstar-separations-lean/HeadComplexity/Separations/Warren.lean` (Lean 4.31);
the eventual migration back to that project depends on this definition staying
byte-compatible. It is `rfl`-locked by `scripts/smoke/FrozenGoals.lean`.
Do not rename, re-quantify, or "clean it up".
-/

/-- The set of strict sign patterns realized by the family `P` at points where
no member vanishes: `s i = true` iff `P i` is positive there. -/
def signPatterns {m k : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ) :
    Set (Fin k → Bool) :=
  {s | ∃ x : Fin m → ℝ, (∀ i, MvPolynomial.eval x (P i) ≠ 0) ∧
        ∀ i, s i = decide (0 < MvPolynomial.eval x (P i))}
