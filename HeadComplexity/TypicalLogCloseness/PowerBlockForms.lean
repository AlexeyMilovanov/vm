import HeadComplexity.TypicalLogCloseness.PowerBlockEquiv

set_option linter.style.header false

/-!
# Affine forms and evaluation identities for power-block localization

This module defines the affine forms (suffix penalty forms and Lagrange delta basis)
on each power-block and proves their evaluation properties.
-/

namespace HeadComplexity.TypicalLogCloseness

/-- Affine form detecting whether coordinate `k` differs from bit `b`. -/
def coordMismatchForm (n : ℕ) (k : Fin n) (b : Bool) : AffineForm n where
  constant := if b = true then 1 else 0
  linear j := if j = k then (if b = true then -1 else 1) else 0

/-- Evaluation identity for `coordMismatchForm`. -/
@[simp] theorem coordMismatchForm_eval (n : ℕ) (k : Fin n) (b : Bool)
    (x : Cube n) :
    (coordMismatchForm n k b).eval x = if x k = b then 0 else 1 := by
  sorry

/-- The suffix penalty affine form `ell g` for a group index `g`. -/
noncomputable def powerBlockEll (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n)) : AffineForm n := by
  sorry

/-- The suffix penalty `ell g` vanishes on vertex `z` if and only if `g = z.1`. -/
theorem powerBlockEll_zero_iff (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n))
    (z : Fin (2 ^ n / powerBlockSize n) × Fin (powerBlockSize n)) :
    (powerBlockEll n hn g).eval ((powerBlockPartition n hn).vertex z) = 0 ↔
      g = z.1 := by
  sorry

/-- The Lagrange delta affine form on block `g` for index `i`. -/
noncomputable def powerBlockLagrange (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n))
    (i : Fin (powerBlockSize n)) : AffineForm n := by
  sorry

/-- Evaluation identity for `powerBlockLagrange` matching delta basis. -/
theorem powerBlockLagrange_delta (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n))
    (i k : Fin (powerBlockSize n)) :
    (powerBlockLagrange n hn g i).eval
        ((powerBlockPartition n hn).vertex (g, k)) =
      if i = k then 1 else 0 := by
  sorry

end HeadComplexity.TypicalLogCloseness
