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
open Module

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

/-- The zero-dimensional cube is spanned by one positive pole. -/
private theorem hasSpanningBank_zero : HasSpanningBank 0 1 := by
  refine ⟨fun _ => AffineForm.positiveDirection 0, ?_, ?_⟩
  · intro h
    exact AffineForm.positiveDirection_positiveCoefficients.strictAdmissible
  · intro v
    refine ⟨fun _ => ⟨v (fun _ => false), fun _ => 0⟩, fun x => ?_⟩
    rw [Fin.sum_univ_one]
    have hx : x = fun _ => false := funext (fun i => i.elim0)
    have hB : (AffineForm.positiveDirection 0).eval x = 1 := by
      simp [AffineForm.eval, AffineForm.positiveDirection]
    have hA :
        (AffineForm.mk (v (fun _ => false)) (fun _ => 0)).eval x = v x := by
      simp [AffineForm.eval, hx]
    rw [hA, hB, div_one]

/-- Every table on the one-dimensional cube is one affine numerator divided
by the fixed positive direction. -/
private theorem hasSpanningBank_one_totality : HasSpanningBank 1 1 := by
  let B0 : AffineForm 1 := ⟨2, fun _ => 1⟩
  use fun _ => B0
  constructor
  · intro h
    constructor
    · intro x
      dsimp [B0, AffineForm.eval]
      have hnonneg : 0 ≤ ∑ i : Fin 1, (1 : ℝ) * bitReal (x i) := by
        apply Finset.sum_nonneg
        intro i _
        exact mul_nonneg zero_le_one (bitReal_nonneg _)
      linarith
    · left
      intro i
      exact zero_lt_one
  · intro v
    let v0 := v (fun _ => false)
    let v1 := v (fun _ => true)
    let A0 : AffineForm 1 := ⟨2 * v0, fun _ => 3 * v1 - 2 * v0⟩
    use fun _ => A0
    intro x
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    have hx : x = (fun _ => false) ∨ x = (fun _ => true) := by
      cases h : x 0
      · left; ext i; fin_cases i; exact h
      · right; ext i; fin_cases i; exact h
    rcases hx with rfl | rfl
    · dsimp [A0, B0, AffineForm.eval]
      simp only [Finset.univ_unique, Fin.default_eq_zero,
        Finset.sum_singleton, mul_zero, add_zero]
      ring
    · dsimp [A0, B0, AffineForm.eval]
      simp only [Finset.univ_unique, Fin.default_eq_zero,
        Finset.sum_singleton, mul_one]
      ring

/-- For arity at least two, the localization matrix supplies a spanning bank. -/
private theorem hasSpanningBank_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    HasSpanningBank n (powerBlockLocalization n hn).groupCount := by
  let L := powerBlockLocalization n hn
  obtain ⟨T, hpositive, hcleared⟩ := exists_legal_fullRank_bank L
  let B : Fin L.groupCount → AffineForm n := legalPath L T
  refine ⟨B, ?_, ?_⟩
  · intro g
    exact (hpositive g).strictAdmissible
  · intro v
    have hlegal : ∀ g, (B g).StrictLegal :=
      fun g => (hpositive g).strictLegal
    have hdet : Matrix.det (fractionalMatrix L B) ≠ 0 :=
      fractional_det_ne_zero L B hlegal hcleared
    exact fixedBank_spans L B hlegal hdet v

/-- Totality follows from the power-block localization construction (with the
small arities handled separately). -/
theorem exists_spanningBank (n : ℕ) : ∃ H, HasSpanningBank n H := by
  rcases n with _ | _ | n
  · exact ⟨1, hasSpanningBank_zero⟩
  · exact ⟨1, hasSpanningBank_one_totality⟩
  · have hn2 : 2 ≤ n + 2 := by omega
    exact ⟨(powerBlockLocalization (n + 2) hn2).groupCount,
      hasSpanningBank_of_two_le hn2⟩

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

/-- Every quotient by a strictly admissible pole is one native fractional
atom, including the negative-slope orientation. -/
private theorem exists_fracAtom_eval_eq_of_strictAdmissible
    (A B : AffineForm n) (hB : B.StrictAdmissible) :
    ∃ φ : HeadComplexity.FracAtom n,
      ∀ x, φ.eval x = A.eval x / B.eval x := by
  rcases hB.2 with hpos | hneg
  · have hbc : 0 < B.constant := by
      have h0 := hB.1 (fun _ => false)
      simpa [AffineForm.eval] using h0
    exact exists_fracAtom_eval_eq A B ⟨hbc, hpos⟩
  · classical
    let all_false : Cube n := fun _ => false
    let all_true : Cube n := fun _ => true
    have hbc : 0 < B.constant := by
      have h0 := hB.1 all_false
      simpa [AffineForm.eval, all_false] using h0
    have hsum_pos : 0 < B.constant + ∑ i, B.linear i := by
      have h1 := hB.1 all_true
      simpa [AffineForm.eval, all_true] using h1
    let S : ℝ := ∑ i, B.linear i
    have hS : S ≤ 0 := Finset.sum_nonpos fun i _ => (hneg i).le
    have hS_lt : -S < B.constant := by linarith [hsum_pos]
    let d : ℝ := (1 + (-S / B.constant)) / 2
    have hd_lt1 : -S / B.constant < 1 := (div_lt_one hbc).mpr hS_lt
    have hd_pos0 : 0 ≤ -S / B.constant := div_nonneg (by linarith) hbc.le
    have hd_pos : 0 < d := by dsimp [d]; linarith
    have hd_lt : d < 1 := by dsimp [d]; linarith
    have hd_gt : -S / B.constant < d := by dsimp [d]; linarith
    have hγ : 0 < B.constant + S / d := by
      have h1 : -S / d < B.constant := by
        have h1' : -S < d * B.constant := (div_lt_iff₀ hbc).mp hd_gt
        exact (div_lt_iff₀' hd_pos).mpr h1'
      rw [neg_div] at h1
      linarith
    have hα : 0 < 1 - d := sub_pos.mpr hd_lt
    have hρ : ∀ i, 0 < -B.linear i / d := fun i => div_pos (neg_pos.mpr (hneg i)) hd_pos
    let φ : HeadComplexity.FracAtom n := {
      η := A.constant + ∑ i, A.linear i / d
      δ := 0
      γ := B.constant + S / d
      α := 1 - d
      ρ i := -B.linear i / d
      m i := A.linear i / B.linear i
      hγ := hγ
      hα := hα
      hρ := hρ
    }
    have hden : fracDenominator φ = B := by
      ext
      · dsimp [fracDenominator, φ]
        have hli : ∀ j, -B.linear j / d = -(B.linear j / d) := fun _ => neg_div _ _
        simp_rw [hli, Finset.sum_neg_distrib, ← Finset.sum_div, show (∑ j, B.linear j) = S from rfl]
        ring
      · rename_i j
        dsimp [fracDenominator, φ]
        have hdn : d ≠ 0 := hd_pos.ne'
        field_simp
        ring
    have hnum : fracNumerator φ = A := by
      ext
      · dsimp [fracNumerator, φ]
        have hli : ∀ j, -B.linear j / d * (A.linear j / B.linear j) = -(A.linear j / d) := by
          intro j
          have hneq : B.linear j ≠ 0 := (hneg j).ne
          have hdn : d ≠ 0 := hd_pos.ne'
          field_simp
        simp_rw [hli, Finset.sum_neg_distrib]
        rw [add_neg_cancel_right]
      · rename_i j
        dsimp [fracNumerator, φ]
        have hdn : d ≠ 0 := hd_pos.ne'
        have hli2 : B.linear j ≠ 0 := (hneg j).ne
        field_simp [hli2, hdn]
        ring
    refine ⟨φ, fun x => ?_⟩
    rw [fracAtom_eval_eq_affine, hden, hnum]

/-- One spanning bank works for every Boolean target, hence bounds H*. -/
theorem HStar_le_Bank (f : BoolFn n) :
    HeadComplexity.HStar n f ≤ Bank n := by
  classical
  obtain ⟨B, hB_spans⟩ := hasSpanningBank_bank n
  rcases hB_spans with ⟨hB_adm, hB_span⟩
  let v : Cube n → ℝ := fun x => if f x then 1 else -1
  obtain ⟨A, hA⟩ := hB_span v
  choose φ hφ using fun h =>
    exists_fracAtom_eval_eq_of_strictAdmissible (A h) (B h) (hB_adm h)
  apply HStar_le_of_fracComputable
  refine ⟨φ, 0, fun x => ?_⟩
  simp_rw [hφ]
  rw [zero_add, ← hA x]
  cases hx : f x <;> simp [v, hx]

private noncomputable def affineEvalLinearMap (n : ℕ) :
    (ℝ × (Fin n → ℝ)) →ₗ[ℝ] (Cube n → ℝ) where
  toFun := fun (c, l) x => c + ∑ i, l i * bitReal (x i)
  map_add' := fun (c1, l1) (c2, l2) => by
    ext x
    simp only [Pi.add_apply, add_mul]
    rw [Finset.sum_add_distrib]
    ring
  map_smul' := fun a (c, l) => by
    ext x
    simp only [Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

private noncomputable def divByB (n : ℕ) (B : AffineForm n) :
    (Cube n → ℝ) →ₗ[ℝ] (Cube n → ℝ) where
  toFun := fun v x => v x / B.eval x
  map_add' := fun v w => by ext x; simp only [Pi.add_apply, add_div]
  map_smul' := fun a v => by
    ext x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

private noncomputable def headSpace (n : ℕ) (B : AffineForm n) : Submodule ℝ (Cube n → ℝ) :=
  ((divByB n B).comp (affineEvalLinearMap n)).range

private lemma finrank_affineEval (n : ℕ) : finrank ℝ (affineEvalLinearMap n).range ≤ n + 1 := by
  have h := LinearMap.finrank_range_le (affineEvalLinearMap n)
  rw [finrank_prod, finrank_self, finrank_pi, Fintype.card_fin] at h
  omega

private lemma finrank_headSpace (n : ℕ) (B : AffineForm n) :
    finrank ℝ (headSpace n B) ≤ n + 1 := by
  have h1 : headSpace n B = ((divByB n B).comp (affineEvalLinearMap n)).range := rfl
  rw [h1, LinearMap.range_comp]
  have h2 := Submodule.finrank_map_le (divByB n B) (affineEvalLinearMap n).range
  have h3 := finrank_affineEval n
  omega

private lemma one_mem_headSpace (n : ℕ) (B : AffineForm n) (hB : ∀ x, B.eval x ≠ 0) :
    (fun (_ : Cube n) => (1 : ℝ)) ∈ headSpace n B := by
  use (B.constant, B.linear)
  ext x
  change B.eval x / B.eval x = 1
  exact div_self (hB x)

private lemma finrank_sup_le_of_mem_inter {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] (S T : Submodule K V) [FiniteDimensional K ↥S] [FiniteDimensional K ↥T]
    (c : V) (hcS : c ∈ S) (hcT : c ∈ T) (hc0 : c ≠ 0) :
    finrank K ↥(S ⊔ T) ≤ finrank K ↥S + finrank K ↥T - 1 := by
  have h_inf : c ∈ S ⊓ T := Submodule.mem_inf.mpr ⟨hcS, hcT⟩
  have h_ne : S ⊓ T ≠ ⊥ := fun h => hc0 (by
    have : c ∈ (⊥ : Submodule K V) := h ▸ h_inf
    rwa [Submodule.mem_bot] at this)
  have h_pos : 1 ≤ finrank K ↥(S ⊓ T) := by
    by_contra h0
    have h1 : finrank K ↥(S ⊓ T) = 0 := by omega
    have h2 := Submodule.finrank_eq_zero.mp h1
    exact h_ne h2
  have h_eq := Submodule.finrank_sup_add_finrank_inf_eq S T
  omega

private lemma iSup_fin_succ' {α : Type*} [CompleteLattice α] {n : ℕ} (f : Fin (n + 1) → α) :
    (⨆ i, f i) = (⨆ i : Fin n, f i.castSucc) ⊔ f (Fin.last n) := by
  refine le_antisymm (iSup_le fun i => ?_)
    (sup_le (iSup_le fun i => le_iSup f i.castSucc) (le_iSup f (Fin.last n)))
  rcases i.le_last.eq_or_lt with h | h
  · rw [h]
    exact le_sup_right
  · have : i = Fin.castSucc ⟨i.val, h⟩ := by ext; rfl
    rw [this]
    exact le_trans (le_iSup (fun i : Fin n => f i.castSucc) ⟨i.val, h⟩) le_sup_left

private lemma finrank_sum_le_of_mem_inter {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] (c : V) (hc0 : c ≠ 0) :
    ∀ (H : ℕ) (S : Fin H → Submodule K V) [∀ h, FiniteDimensional K ↥(S h)] (_ : ∀ h, c ∈ S h),
      finrank K ↥(⨆ h, S h) ≤ 1 + ∑ h, (finrank K ↥(S h) - 1)
  | 0, S, _, _ => by
      have : (⨆ h : Fin 0, S h) = ⊥ := iSup_of_empty S
      rw [this, finrank_bot]
      omega
  | H + 1, S, _, hcS => by
      rw [iSup_fin_succ', Fin.sum_univ_castSucc]
      have ih := finrank_sum_le_of_mem_inter c hc0 H (fun h => S h.castSucc)
        (fun h => hcS h.castSucc)
      cases H with
      | zero =>
          have h_bot : (⨆ h : Fin 0, S (Fin.castSucc h)) = ⊥ := iSup_of_empty _
          rw [h_bot, bot_sup_eq]
          have h0 : ∑ i : Fin 0, (finrank K ↥(S i.castSucc) - 1) = 0 := rfl
          rw [h0, zero_add]
          have : c ∈ S (Fin.last 0) := hcS (Fin.last 0)
          have h_ne : S (Fin.last 0) ≠ ⊥ := fun h => hc0 (by rwa [h, Submodule.mem_bot] at this)
          have h1 : 1 ≤ finrank K ↥(S (Fin.last 0)) := by
            by_contra h0
            have h2 : finrank K ↥(S (Fin.last 0)) = 0 := by omega
            exact h_ne (Submodule.finrank_eq_zero.mp h2)
          omega
      | succ H' =>
          let i0 : Fin (H' + 1) := ⟨0, Nat.succ_pos H'⟩
          have hc_iSup : c ∈ ⨆ h : Fin (H' + 1), S h.castSucc :=
            le_iSup (fun h => S h.castSucc) i0 (hcS i0.castSucc)
          have hc_last : c ∈ S (Fin.last (H' + 1)) := hcS (Fin.last (H' + 1))
          have h_bound := finrank_sup_le_of_mem_inter (⨆ h : Fin (H' + 1), S h.castSucc)
            (S (Fin.last (H' + 1))) c hc_iSup hc_last hc0
          have h_last_pos : 1 ≤ finrank K ↥(S (Fin.last (H' + 1))) := by
            have : c ∈ S (Fin.last (H' + 1)) := hcS (Fin.last (H' + 1))
            have h_ne : S (Fin.last (H' + 1)) ≠ ⊥ :=
              fun h => hc0 (by rwa [h, Submodule.mem_bot] at this)
            by_contra h0
            have h2 : finrank K ↥(S (Fin.last (H' + 1))) = 0 := by omega
            exact h_ne (Submodule.finrank_eq_zero.mp h2)
          omega

/-- Shared-constant dimension bound. Each head space has affine dimension
`n + 1`, but all head spaces contain the same constant function
`1 = B_h / B_h`; therefore `H` poles span at most `1 + nH` dimensions. -/
theorem spanningBank_dimension_bound {n H : ℕ}
    (h : HasSpanningBank n H) :
    2 ^ n ≤ 1 + n * H := by
  rcases h with ⟨B, hB_adm, hB_spans⟩
  have hB_ne0 : ∀ h x, (B h).eval x ≠ 0 := fun h x => (B h).eval_ne_zero (hB_adm h).1 x
  let S : Fin H → Submodule ℝ (Cube n → ℝ) := fun h => headSpace n (B h)
  have hcS : ∀ h, (fun (_ : Cube n) => (1 : ℝ)) ∈ S h :=
    fun h => one_mem_headSpace n (B h) (hB_ne0 h)
  have hc0 : (fun (_ : Cube n) => (1 : ℝ)) ≠ 0 := by
    intro h_zero
    have h1 := congr_fun h_zero (fun _ => true)
    norm_num at h1
  have h_top : (⨆ h, S h) = ⊤ := by
    ext v
    simp only [Submodule.mem_top, iff_true]
    rcases hB_spans v with ⟨A, hA⟩
    have : v = ∑ h, ((divByB n (B h)).comp (affineEvalLinearMap n))
        ((A h).constant, (A h).linear) := by
      ext x
      simp only [Finset.sum_apply, LinearMap.comp_apply, divByB, affineEvalLinearMap,
        LinearMap.coe_mk, AddHom.coe_mk, AffineForm.eval]
      exact hA x
    rw [this]
    exact Submodule.sum_mem _ (fun h _ => Submodule.mem_iSup_of_mem h
      ⟨((A h).constant, (A h).linear), rfl⟩)
  have h_bound := finrank_sum_le_of_mem_inter (fun (_ : Cube n) => (1 : ℝ)) hc0 H S hcS
  rw [h_top, finrank_top] at h_bound
  have h_cube : finrank ℝ (Cube n → ℝ) = 2 ^ n := by
    rw [finrank_pi, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [h_cube] at h_bound
  have h_sum : ∑ h : Fin H, (finrank ℝ ↥(S h) - 1) ≤ ∑ h : Fin H, n := by
    apply Finset.sum_le_sum
    intro h _
    change finrank ℝ ↥(headSpace n (B h)) - 1 ≤ n
    have hhs := finrank_headSpace n (B h)
    omega
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h_sum
  have h_mn : H * n = n * H := mul_comm H n
  omega

theorem bank_dimension_bound (n : ℕ) :
    2 ^ n ≤ 1 + n * Bank n :=
  spanningBank_dimension_bound (hasSpanningBank_bank n)

/-- P19 lower bound in explicit natural-number ceiling form. -/
theorem bank_lower_bound {n : ℕ} (hn : 1 ≤ n) :
    ((2 ^ n - 1) + (n - 1)) / n ≤ Bank n := by
  have hdim := bank_dimension_bound n
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h1 : (2 ^ n - 1) + (n - 1) < n * (Bank n + 1) := by
    calc (2 ^ n - 1) + (n - 1) ≤ n * Bank n + (n - 1) := by omega
    _ < n * Bank n + n := by omega
    _ = n * (Bank n + 1) := by ring
  exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul h1)

/-- The already-formalized power-block localization is a spanning bank, not
only a per-function upper bound. -/
theorem bank_le_powerBlock_groupCount {n : ℕ} (hn : 2 ≤ n) :
    Bank n ≤ (powerBlockLocalization n hn).groupCount := by
  classical
  let L := powerBlockLocalization n hn
  obtain ⟨T, hpositive, hcleared⟩ := exists_legal_fullRank_bank L
  let B : Fin L.groupCount → AffineForm n := legalPath L T
  have hlegal : ∀ g, (B g).StrictLegal :=
    fun g => (hpositive g).strictLegal
  have hfractional : Matrix.det (fractionalMatrix L B) ≠ 0 :=
    fractional_det_ne_zero L B hlegal hcleared
  have hspan : FixedBankSpans B :=
    fun v => fixedBank_spans L B hlegal hfractional v
  have hB : IsSpanningBank B :=
    ⟨fun g => (hpositive g).strictAdmissible, hspan⟩
  exact Bank_le_of_hasSpanningBank ⟨B, hB⟩

private theorem bank_pow_two_arith_lemma (K q : ℕ) (hK : 2 ≤ K) (hq : 1 ≤ q) :
    (K * q - 1 + (K - 1)) / K = q := by
  have hK_pos : 0 < K := by omega
  have h_eq : K * q - 1 + (K - 1) = K * (q - 1) + (K + (K - 2)) := by
    have hq_eq : q = (q - 1) + 1 := (Nat.sub_add_cancel hq).symm
    nth_rw 1 [hq_eq]
    rw [mul_add, mul_one]
    omega
  rw [h_eq]
  have h_eq2 : K * (q - 1) + (K + (K - 2)) = (K - 2) + (q - 1 + 1) * K := by
    ring
  rw [h_eq2]
  rw [Nat.add_mul_div_right (K - 2) (q - 1 + 1) hK_pos]
  have h_small : (K - 2) / K = 0 := Nat.div_eq_of_lt (by omega)
  rw [h_small, zero_add]
  omega

/-- Exact P19 value on power-of-two arities. -/
theorem bank_pow_two (m : ℕ) (hm : 1 ≤ m) :
    Bank (2 ^ m) = 2 ^ (2 ^ m) / 2 ^ m := by
  have hn2 : 2 ≤ 2 ^ m := by
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    exact this
  have hn1 : 1 ≤ 2 ^ m := by omega
  have h_le := bank_le_powerBlock_groupCount hn2
  rw [powerBlockLocalization_groupCount (2 ^ m) hn2] at h_le
  have h_pbs : powerBlockSize (2 ^ m) = 2 ^ m := by
    dsimp [powerBlockSize]
    rw [Nat.log_pow Nat.one_lt_two m]
  rw [h_pbs] at h_le
  have h_ge := bank_lower_bound (n := 2 ^ m) hn1
  have h_m_le : m ≤ 2 ^ m := (Nat.lt_pow_self Nat.one_lt_two).le
  have h_div : 2 ^ m ∣ 2 ^ (2 ^ m) := pow_dvd_pow 2 h_m_le
  rcases h_div with ⟨q, hq⟩
  have h_2m_pos : 0 < 2 ^ m := Nat.pow_pos (by omega)
  have h_q_pos : 1 ≤ q := by
    rcases q with _ | q'
    · rw [mul_zero] at hq
      have : 0 < 2 ^ (2 ^ m) := Nat.pow_pos (by omega)
      omega
    · omega
  have h_arith := bank_pow_two_arith_lemma (2 ^ m) q hn2 h_q_pos
  rw [hq] at h_ge
  rw [h_arith] at h_ge
  have h_div_cancel : 2 ^ (2 ^ m) / 2 ^ m = q := by
    rw [hq, Nat.mul_div_cancel_left q h_2m_pos]
  omega

/-- Explicit spanning bank for `n = 1` with 1 pole. -/
private theorem hasSpanningBank_one : HasSpanningBank 1 1 := by
  let B0 : AffineForm 1 := ⟨2, fun _ => 1⟩
  use fun _ => B0
  constructor
  · intro h
    constructor
    · intro x
      dsimp [B0, AffineForm.eval]
      have hnonneg : 0 ≤ ∑ i : Fin 1, (1 : ℝ) * bitReal (x i) := by
        apply Finset.sum_nonneg
        intro i _
        exact mul_nonneg zero_le_one (bitReal_nonneg _)
      linarith
    · left
      intro i
      exact zero_lt_one
  · intro v
    let v0 := v (fun _ => false)
    let v1 := v (fun _ => true)
    let A0 : AffineForm 1 := ⟨2 * v0, fun _ => 3 * v1 - 2 * v0⟩
    use fun _ => A0
    intro x
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    have hx : x = (fun _ => false) ∨ x = (fun _ => true) := by
      cases h : x 0
      · left; ext i; fin_cases i; exact h
      · right; ext i; fin_cases i; exact h
    rcases hx with rfl | rfl
    · dsimp [A0, B0, AffineForm.eval]
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, mul_zero, add_zero]
      ring
    · dsimp [A0, B0, AffineForm.eval]
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, mul_one]
      ring

/-- The one-bit endpoint. -/
theorem bank_one : Bank 1 = 1 := by
  have h1 : 1 ≤ Bank 1 := by
    have hbound := bank_dimension_bound 1
    linarith
  have h2 : Bank 1 ≤ 1 := Bank_le_of_hasSpanningBank hasSpanningBank_one
  exact le_antisymm h2 h1

end HeadComplexity.TypicalLogCloseness
