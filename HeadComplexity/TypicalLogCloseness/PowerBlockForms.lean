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
  dsimp [coordMismatchForm, AffineForm.eval]
  rw [Finset.sum_eq_single k]
  · cases b <;> cases x k <;> simp [bitReal]
  · intro j _ hj
    simp [hj]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

open Finset
open scoped BigOperators

/-- The suffix penalty affine form `ell g` for a group index `g`. -/
noncomputable def powerBlockEll (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n)) : AffineForm n :=
  let m := Nat.log 2 n
  let p := powerBlockSize n
  let hp : p ≤ n := powerBlockSize_le_self n hn
  let cs := powerBlockGroupEquiv n hn g
  let c := cs.1
  let s := cs.2
  { constant :=
      (∑ k : Fin p, if c.1 (starCoordEquiv m k) = true then (1 : ℝ) else 0) - 1 +
      2 * (∑ j : Fin (n - p), if s j = true then (1 : ℝ) else 0)
    linear := fun i =>
      if hi : i.1 < p then
        if c.1 (starCoordEquiv m ⟨i.1, hi⟩) = true then -1 else 1
      else
        have hj : i.1 - p < n - p := by omega
        2 * (if s ⟨i.1 - p, hj⟩ = true then -1 else 1) }

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
    (i : Fin (powerBlockSize n)) : AffineForm n :=
  let m := Nat.log 2 n
  let c := (powerBlockGroupEquiv n hn g).1
  let b := c.1 (starCoordEquiv m i)
  let k : Fin n := ⟨i.1, lt_of_lt_of_le i.2 (powerBlockSize_le_self n hn)⟩
  coordMismatchForm n k b

/-- Evaluation identity for `powerBlockLagrange` matching delta basis. -/
theorem powerBlockLagrange_delta (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n))
    (i k : Fin (powerBlockSize n)) :
    (powerBlockLagrange n hn g i).eval
        ((powerBlockPartition n hn).vertex (g, k)) =
      if i = k then 1 else 0 := by
  sorry

end HeadComplexity.TypicalLogCloseness
