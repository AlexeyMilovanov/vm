import HeadComplexity.Atoms.FracAtom

set_option linter.style.header false

/-!
# Affine forms for the POIC₂ / typical-closeness development

This module freezes the elementary affine-function convention used by the
counting and universal-bank arguments.  The canonical POIC₂ model has no
free global bias; constants are handled separately at complexity zero.
-/

namespace HeadComplexity.TypicalLogCloseness

open Finset
open scoped BigOperators

/-- The Boolean cube and Boolean functions on it. -/
abbrev Cube (n : ℕ) := Fin n → Bool
abbrev BoolFn (n : ℕ) := Cube n → Bool

/-- The real indicator of a Boolean value. -/
def bitReal (b : Bool) : ℝ := if b = true then 1 else 0

@[simp] theorem bitReal_false : bitReal false = 0 := rfl
@[simp] theorem bitReal_true : bitReal true = 1 := rfl

theorem bitReal_nonneg (b : Bool) : 0 ≤ bitReal b := by
  cases b <;> simp

/-- An affine real-valued function on the Boolean cube. -/
structure AffineForm (n : ℕ) where
  constant : ℝ
  linear : Fin n → ℝ

namespace AffineForm

@[ext] theorem ext {L K : AffineForm n}
    (hconstant : L.constant = K.constant)
    (hlinear : ∀ i, L.linear i = K.linear i) : L = K := by
  cases L with
  | mk lc ll =>
      cases K with
      | mk kc kl =>
          change lc = kc at hconstant
          change ∀ i, ll i = kl i at hlinear
          subst kc
          have hfun : ll = kl := funext hlinear
          subst kl
          rfl

/-- Evaluation of an affine form on a Boolean vertex. -/
noncomputable def eval (L : AffineForm n) (x : Cube n) : ℝ :=
  L.constant + ∑ i, L.linear i * bitReal (x i)

/-- Strict legality: the affine denominator is positive on every cube vertex. -/
def StrictLegal (B : AffineForm n) : Prop :=
  ∀ x, 0 < B.eval x

theorem eval_pos (B : AffineForm n) (hB : B.StrictLegal) (x : Cube n) :
    0 < B.eval x := hB x

theorem eval_ne_zero (B : AffineForm n) (hB : B.StrictLegal) (x : Cube n) :
    B.eval x ≠ 0 := (B.eval_pos hB x).ne'

/-- Strong coefficientwise positivity used by the universal H* bank.  It is
stronger than certificate legality and makes an affine quotient realizable by
one fractional atom. -/
def PositiveCoefficients (B : AffineForm n) : Prop :=
  0 < B.constant ∧ ∀ i, 0 < B.linear i

theorem PositiveCoefficients.strictLegal {B : AffineForm n}
    (hB : B.PositiveCoefficients) : B.StrictLegal := by
  intro x
  unfold eval
  exact add_pos_of_pos_of_nonneg hB.1
    (Finset.sum_nonneg fun i _ =>
      mul_nonneg (hB.2 i).le (bitReal_nonneg _))

/-- Pointwise addition, used by the legal one-parameter deformation. -/
def add (L K : AffineForm n) : AffineForm n where
  constant := L.constant + K.constant
  linear i := L.linear i + K.linear i

/-- Scalar multiplication of an affine form. -/
def smul (a : ℝ) (L : AffineForm n) : AffineForm n where
  constant := a * L.constant
  linear i := a * L.linear i

@[simp] theorem eval_add (L K : AffineForm n) (x : Cube n) :
    (L.add K).eval x = L.eval x + K.eval x := by
  simp only [eval, add]
  simp_rw [add_mul, Finset.sum_add_distrib]
  ring

@[simp] theorem eval_smul (a : ℝ) (L : AffineForm n) (x : Cube n) :
    (L.smul a).eval x = a * L.eval x := by
  simp only [eval, smul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The fixed positive-slope form `1 + ∑ xᵢ` used in the legal path. -/
def positiveDirection (n : ℕ) : AffineForm n where
  constant := 1
  linear _ := 1

theorem positiveDirection_positiveCoefficients :
    (positiveDirection n).PositiveCoefficients := by
  constructor <;> simp [positiveDirection]

theorem positiveDirection_strictLegal : (positiveDirection n).StrictLegal :=
  positiveDirection_positiveCoefficients.strictLegal

end AffineForm

end HeadComplexity.TypicalLogCloseness
