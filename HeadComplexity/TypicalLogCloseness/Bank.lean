import HeadComplexity.TypicalLogCloseness.Headline

set_option linter.style.header false

/-!
# P19: fixed-pole spanning banks

`Bank n` is the least number of fixed native denominators whose
affine-numerator quotient spaces span every real-valued table on the Boolean
cube.  This is not the older calibration or 0/1 bank invariant.
-/

namespace HeadComplexity.TypicalLogCloseness

open Finset
open scoped BigOperators

/-- A fixed denominator family spans every real table when the affine
numerators may depend on the target table. -/
def FixedBankSpans (B : Fin H → AffineForm n) : Prop :=
  ∀ v : Cube n → ℝ, ∃ A : Fin H → AffineForm n,
    ∀ x, v x = ∑ h, (A h).eval x / (B h).eval x

/-- A native fixed-pole bank: every denominator is strictly positive on the
cube, has one nonzero slope orientation, and the quotient spaces span all
tables. -/
def IsSpanningBank (B : Fin H → AffineForm n) : Prop :=
  (∀ h, (B h).StrictAdmissible) ∧ FixedBankSpans B

/-- Existence of a spanning bank with exactly `H` fixed poles. -/
def HasSpanningBank (n H : ℕ) : Prop :=
  ∃ B : Fin H → AffineForm n, IsSpanningBank B

/-- Totality follows from the power-block localization construction (with the
small arities handled separately). -/
theorem exists_spanningBank (n : ℕ) : ∃ H, HasSpanningBank n H := by
  sorry

/-- Fixed-pole span complexity. -/
noncomputable def Bank (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_spanningBank n)

theorem hasSpanningBank_bank (n : ℕ) : HasSpanningBank n (Bank n) := by
  classical
  exact Nat.find_spec (exists_spanningBank n)

theorem Bank_le_of_hasSpanningBank {n H : ℕ} (h : HasSpanningBank n H) :
    Bank n ≤ H := by
  classical
  exact Nat.find_min' (exists_spanningBank n) h

/-- One spanning bank works for every Boolean target, hence bounds H*. -/
theorem HStar_le_Bank (f : BoolFn n) :
    HeadComplexity.HStar n f ≤ Bank n := by
  sorry

/-- Shared-constant dimension bound. Each head space has affine dimension
`n + 1`, but all head spaces contain the same constant function
`1 = B_h / B_h`; therefore `H` poles span at most `1 + nH` dimensions. -/
theorem spanningBank_dimension_bound {n H : ℕ}
    (h : HasSpanningBank n H) :
    2 ^ n ≤ 1 + n * H := by
  sorry

theorem bank_dimension_bound (n : ℕ) :
    2 ^ n ≤ 1 + n * Bank n :=
  spanningBank_dimension_bound (hasSpanningBank_bank n)

/-- P19 lower bound in explicit natural-number ceiling form. -/
theorem bank_lower_bound {n : ℕ} (hn : 1 ≤ n) :
    ((2 ^ n - 1) + (n - 1)) / n ≤ Bank n := by
  sorry

/-- The already-formalized power-block localization is a spanning bank, not
only a per-function upper bound. -/
theorem bank_le_powerBlock_groupCount {n : ℕ} (hn : 2 ≤ n) :
    Bank n ≤ (powerBlockLocalization n hn).groupCount := by
  sorry

/-- Exact P19 value on power-of-two arities. -/
theorem bank_pow_two (m : ℕ) (hm : 1 ≤ m) :
    Bank (2 ^ m) = 2 ^ (2 ^ m) / 2 ^ m := by
  sorry

/-- The one-bit endpoint. -/
theorem bank_one : Bank 1 = 1 := by
  sorry

end HeadComplexity.TypicalLogCloseness
