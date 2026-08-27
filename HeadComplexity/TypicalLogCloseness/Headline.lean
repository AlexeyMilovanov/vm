import HeadComplexity.TypicalLogCloseness.AbstractCounting
import HeadComplexity.TypicalLogCloseness.LocalizationMatrix
import HeadComplexity.TypicalLogCloseness.CanonicalCounting
import HeadComplexity.Results.FractionalNormalForm

set_option linter.style.header false

/-!
# Explicit finite typical logarithmic-closeness theorem
-/

namespace HeadComplexity.TypicalLogCloseness

/-- The elementary numerical inequality needed at the explicit cutoff. -/
theorem growth_condition_of_64_le {n : ℕ} (hn : 64 ≤ n) :
    128 * n ^ 2 ≤ 2 ^ (n / 2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h64 : n = 64
      · subst n
        norm_num
      by_cases h65 : n = 65
      · subst n
        norm_num
      have hn66 : 66 ≤ n := by omega
      have hprev : 128 * (n - 2) ^ 2 ≤ 2 ^ ((n - 2) / 2) :=
        ih (n - 2) (by omega) (by omega)
      have hsquare : n ^ 2 ≤ 2 * (n - 2) ^ 2 := by
        calc
          n ^ 2 = ((n - 2) + 2) ^ 2 := by congr 1 <;> omega
          _ ≤ 2 * (n - 2) ^ 2 := by
            have hk : 64 ≤ n - 2 := by omega
            nlinarith
      calc
        128 * n ^ 2 ≤ 2 * (128 * (n - 2) ^ 2) := by nlinarith
        _ ≤ 2 * 2 ^ ((n - 2) / 2) := Nat.mul_le_mul_left 2 hprev
        _ = 2 ^ (n / 2) := by
          rw [show n / 2 = (n - 2) / 2 + 1 by omega, pow_succ]
          ring

/-- The localization matrix gives a bank with one fractional atom per block. -/
theorem HStar_le_powerBlock_groupCount {n : ℕ} (hn : 2 ≤ n)
    (f : BoolFn n) :
    HStar n f ≤ (powerBlockLocalization n hn).groupCount := by
  classical
  let L := powerBlockLocalization n hn
  obtain ⟨T, hpositive, hcleared⟩ := exists_legal_fullRank_bank L
  let B : Fin L.groupCount → AffineForm n := legalPath L T
  have hlegal : ∀ g, (B g).StrictLegal :=
    fun g => (hpositive g).strictLegal
  have hfractional : Matrix.det (fractionalMatrix L B) ≠ 0 :=
    fractional_det_ne_zero L B hlegal hcleared
  let v : Cube n → ℝ := fun x => if f x then 1 else -1
  obtain ⟨A, hspan⟩ := fixedBank_spans L B hlegal hfractional v
  choose φ hφ using fun g => exists_fracAtom_eval_eq (A g) (B g) (hpositive g)
  apply HStar_le_of_fracComputable
  refine ⟨φ, 0, fun x => ?_⟩
  simp_rw [hφ]
  rw [zero_add, ← hspan x]
  cases hx : f x <;> simp [v, hx]

/-- The universal Hamming-star bank bound in the exact multiplicative form
consumed by the abstract counting theorem. -/
theorem universal_bank_bound {n : ℕ} (hn : 2 ≤ n) (f : BoolFn n) :
    (n + 1) * HStar n f ≤ 2 * (2 ^ n) := by
  have hH := HStar_le_powerBlock_groupCount hn f
  have hsize := powerBlockSize_lower_bound n hn
  have hgroups := powerBlockLocalization_groupCount n hn
  have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hdiv : powerBlockSize n ∣ 2 ^ n := by
    exact pow_dvd_pow 2 hlog
  calc
    (n + 1) * HStar n f
        ≤ (n + 1) * (powerBlockLocalization n hn).groupCount :=
      Nat.mul_le_mul_left (n + 1) hH
    _ ≤ (2 * powerBlockSize n) *
          (powerBlockLocalization n hn).groupCount :=
      Nat.mul_le_mul_right _ hsize
    _ = 2 * (2 ^ n) := by
      rw [hgroups]
      rw [Nat.mul_assoc, Nat.mul_div_cancel' hdiv]

/-- Primary finite endpoint. -/
theorem typical_log_closeness {n : ℕ} (hn : 64 ≤ n) :
    (badLog (POIC2 n) (HStar n) 512).card ≤ 2 ^ (2 ^ (n - 1)) := by
  have hn2 : 2 ≤ n := by omega
  have hmain := typical_from_bank_and_warren
    (F := BoolFn n) n 64 hn2 (by norm_num)
    (POIC2 n) (HStar n)
    (universal_bank_bound hn2)
    (fun Q hQ0 hQN => poic2_sublevel_card_le n Q hn2 hQ0 hQN)
    (by simpa using growth_condition_of_64_le hn)
  have hexp : (2 ^ n) / 2 = 2 ^ (n - 1) := by
    exact (Nat.pow_sub_one (by norm_num : (2 : ℕ) ≠ 0) (by omega : n ≠ 0)).symm
  simpa [hexp] using hmain

end HeadComplexity.TypicalLogCloseness
