import HeadComplexity.Separations.EightBitHammingThreshold.Normalization
import HeadComplexity.Separations.EightBitHammingThreshold.K4Cone

set_option linter.style.header false

/-!
# Eight-bit Hamming threshold: normalized-system contradiction
-/

namespace HeadComplexity

open Finset
open scoped BigOperators
open TypicalLogCloseness
open MvPolynomial
open EightBitInternal

private theorem trace_plus_two_sum_eq_sum_univ
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (pick : Fin 4 → Fin 4) :
    Matrix.trace M + 2 * ∑ j, M (pick j) j =
      ∑ j, (M j j + 2 * M (pick j) j) := by
  unfold Matrix.trace Matrix.diag
  rw [mul_sum, ← sum_add_distrib]


private lemma neg_abs_sub_le (X Y t : ℝ) (ht : t = 1 ∨ t = -1) :
    -|X - Y| ≤ -t * X + t * Y := by
  rcases ht with rfl | rfl
  · linarith [le_abs_self (X - Y)]
  · linarith [neg_le_abs (X - Y)]

private lemma neg_abs_add_le (X Y t : ℝ) (ht : t = 1 ∨ t = -1) :
    -|X + Y| ≤ -t * X - t * Y := by
  rcases ht with rfl | rfl
  · linarith [le_abs_self (X + Y)]
  · linarith [neg_le_abs (X + Y)]

private lemma signed_contraction_fin4
    (s U V : Fin 4 → ℝ) (w : ℝ) (j i : Fin 4) (hij : i ≠ j)
    (hsign : s j = 1 ∨ s j = -1)
    (hc : |w| + |U i - V i| +
      ∑ k with k ≠ i ∧ k ≠ j, |U k + V k| < U j)
    (hw : s j * w ≤ |w|)
    (hsub : s j * s i * (-(U i - V i)) ≤ |U i - V i|)
    (hadd : ∀ k, s j * s k * (-(U k + V k)) ≤ |U k + V k|) :
    s j * (w - ∑ k, s k * U k) <
      s j * (∑ k ∈ offDiagSet j, s k * V k) -
        2 * s j * s i * V i := by
  fin_cases j <;> fin_cases i <;>
    simp_all only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      neg_add_rev, ne_eq, zero_ne_one, one_ne_zero, Fin.reduceEq,
      not_false_eq_true, not_true_eq_false, sum_filter, Fin.sum_univ_four,
      and_false, and_true, and_self, ↓reduceIte, add_zero, zero_add,
      neg_sub, offDiagSet, ite_not]
  all_goals rcases hsign with hs | hs
  all_goals simp only [Fin.isValue, hs, neg_mul, one_mul, neg_sub,
    neg_add_rev, mul_neg, mul_one, sub_neg_eq_add] at *
  all_goals
    have hk0 := hadd 0
    have hk1 := hadd 1
    have hk2 := hadd 2
    have hk3 := hadd 3
    ring_nf at ⊢
    linarith only [hc, hw, hsub, hk0, hk1, hk2, hk3]

/-- The algebraic part of paper Lemma 6. Once every null-vector coordinate is
nonzero, rowwise contraction and the column-max spectral inequality contradict
the strict intercept inequality. -/
private theorem f8NormalizedSystem_false_of_mu_ne_zero
    (sys : F8NormalizedSystem) (hμ : ∀ i, sys.μ i ≠ 0) : False := by
  set r : Fin 4 → ℝ := fun i => |sys.μ i|
  have hr : ∀ i, 0 < r i := fun i => abs_pos.mpr (hμ i)
  set s : Fin 4 → ℝ := fun i => sys.μ i / r i
  have hs_sq : ∀ i, s i ^ 2 = 1 := by
    intro i
    dsimp [s, r]
    rw [div_pow, sq_abs, div_self (pow_ne_zero 2 (hμ i))]
  have hs_mul_r : ∀ i, s i * r i = sys.μ i := by
    intro i
    dsimp [s, r]
    exact div_mul_cancel₀ (sys.μ i) (hr i).ne'
  have hs_mul_mu : ∀ i, s i * sys.μ i = r i := by
    intro i
    calc
      s i * sys.μ i = s i * (s i * r i) := by rw [← hs_mul_r i]
      _ = (s i ^ 2) * r i := by ring
      _ = 1 * r i := by rw [hs_sq i]
      _ = r i := by ring
  set q : Fin 4 → ℝ := fun i => 1 / r i
  have hq : ∀ i, 0 < q i := fun i => one_div_pos.mpr (hr i)
  set H : Matrix (Fin 4) (Fin 4) ℝ := (Matrix.diagonal sys.μ) * sys.V * (Matrix.diagonal sys.μ)
  have hH_apply (i j : Fin 4) : H i j = sys.μ i * sys.V i j * sys.μ j := by
    change ((Matrix.diagonal sys.μ) * sys.V * (Matrix.diagonal sys.μ)) i j = _
    rw [Matrix.mul_apply, sum_fin4]
    simp only [diag_mul_apply]
    fin_cases i <;> fin_cases j <;> simp
  set g : Fin 4 → ℝ := H.mulVec 1
  have hg_apply (i : Fin 4) : g i = sys.μ i * (sys.V.mulVec sys.μ) i := by
    dsimp [g, Matrix.mulVec, dotProduct]
    rw [sum_fin4]
    rw [hH_apply i 0, hH_apply i 1, hH_apply i 2, hH_apply i 3]
    rw [sum_fin4]
    ring
  have hg_H (i : Fin 4) : g i = H i 0 + H i 1 + H i 2 + H i 3 := by
    change H.mulVec 1 i = H i 0 + H i 1 + H i 2 + H i 3
    dsimp [Matrix.mulVec, dotProduct]
    rw [sum_fin4]
    ring
  have hs_g : ∀ i, 0 < s i * g i := by
    intro i
    rw [hg_apply i]
    have h1 : s i * (sys.μ i * (sys.V.mulVec sys.μ) i) = (s i * sys.μ i) * (sys.V.mulVec sys.μ)
        i := by ring
    rw [h1, hs_mul_mu i]
    exact mul_pos (hr i) (sys.rightSlope_pos i)
  have habs_g : ∀ i, |g i| = s i * g i := by
    intro i
    have hpos := hs_g i
    have h_or : s i = 1 ∨ s i = -1 := by
      have hsq := hs_sq i
      have h_factor : (s i - 1) * (s i + 1) = 0 := by linarith [hsq]
      cases mul_eq_zero.mp h_factor with
      | inl h1 => left; linarith
      | inr h2 => right; linarith
    rcases h_or with h1 | h1
    · rw [h1] at hpos ⊢
      rw [one_mul] at hpos ⊢
      exact abs_of_pos hpos
    · rw [h1] at hpos ⊢
      have hg_neg : g i < 0 := by linarith [hpos]
      rw [neg_mul, one_mul] at hpos ⊢
      exact abs_of_neg hg_neg
  set C : Matrix (Fin 4) (Fin 4) ℝ := H + Matrix.diagonal (fun i => |g i| - g i)
  have hC_apply (i j : Fin 4) : C i j = H i j + if i = j then |g i| - g i else 0 := by
    change (H + Matrix.diagonal (fun k => |g k| - g k)) i j = _
    rw [Matrix.add_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, Matrix.diagonal_apply_eq]
    · rw [if_neg hij, Matrix.diagonal_apply_ne _ hij, add_zero]
  set M : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal q * C
  have hM_apply (i j : Fin 4) : M i j = q i * C i j := by
    change ((Matrix.diagonal q) * C) i j = _
    rw [diag_mul_apply]
  have hrow : ∀ i, 0 < (M.mulVec (fun _ => 1)) i := by
    intro i
    have h_sum_C : C i 0 + C i 1 + C i 2 + C i 3 = |g i| := by
      rw [hC_apply i 0, hC_apply i 1, hC_apply i 2, hC_apply i 3]
      rw [hg_H i]
      fin_cases i <;> simp <;> linarith
    have h_g_pos : 0 < |g i| := by rw [habs_g i]; exact hs_g i
    calc (M.mulVec (fun _ => 1)) i
        = q i * C i 0 * 1 + q i * C i 1 * 1 + q i * C i 2 * 1 + q i * C i 3 * 1 := by
          dsimp [Matrix.mulVec, dotProduct]
          rw [sum_fin4]
          rw [hM_apply i 0, hM_apply i 1, hM_apply i 2, hM_apply i 3]
      _ = q i * (C i 0 + C i 1 + C i 2 + C i 3) := by ring
      _ = q i * |g i| := by rw [h_sum_C]
      _ > 0 := mul_pos (hq i) h_g_pos
  have hC_symm : C.IsSymm := by
    ext i j
    dsimp [Matrix.transpose]
    rw [hC_apply i j, hC_apply j i]
    have hV_symm := congr_fun (congr_fun sys.V_inertia.1 i) j
    dsimp [Matrix.transpose] at hV_symm
    by_cases hij : i = j
    · rw [hij]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
      rw [hH_apply i j, hH_apply j i]
      rw [hV_symm]
      ring
  have h_rM (i j : Fin 4) : ((Matrix.diagonal r) * M) i j = C i j := by
    change (Matrix.diagonal r * (Matrix.diagonal q * C)) i j = C i j
    rw [diag_mul_apply, diag_mul_apply]
    have h_rq : r i * q i = 1 := by
      dsimp [q]
      exact mul_one_div_cancel (hr i).ne'
    rw [← mul_assoc, h_rq, one_mul]
  have h_rM_mulVec (z : Fin 4 → ℝ) : ((Matrix.diagonal r) * M).mulVec z = C.mulVec z := by
    ext i
    dsimp [Matrix.mulVec, dotProduct]
    rw [sum_fin4, sum_fin4]
    rw [h_rM i 0, h_rM i 1, h_rM i 2, h_rM i 3]
  have hspectral : DiagonallySymmetrizableWithPositiveIndexTwo4 M := by
    use r
    refine ⟨hr, ?_, ?_⟩
    · ext i j
      dsimp [Matrix.transpose]
      rw [h_rM i j, h_rM j i]
      exact congr_fun (congr_fun hC_symm i) j
    · obtain ⟨u, v, huv⟩ := sys.V_inertia.2.1
      set u' : Fin 4 → ℝ := fun i => u i / sys.μ i
      set v' : Fin 4 → ℝ := fun i => v i / sys.μ i
      use u', v'
      intro a b hab
      have hpos := huv a b hab
      dsimp [quadraticForm4] at hpos ⊢
      have h_C_eq (z : Fin 4 → ℝ) : dotProduct z (C.mulVec z) =
          dotProduct (fun i => sys.μ i * z i) (sys.V.mulVec (fun i => sys.μ i * z i)) +
          ∑ i, (|g i| - g i) * z i ^ 2 := by
        dsimp [dotProduct, Matrix.mulVec]
        rw [sum_fin4]
        rw [sum_fin4, sum_fin4, sum_fin4, sum_fin4]
        rw [hC_apply 0 0, hC_apply 0 1, hC_apply 0 2, hC_apply 0 3]
        rw [hC_apply 1 0, hC_apply 1 1, hC_apply 1 2, hC_apply 1 3]
        rw [hC_apply 2 0, hC_apply 2 1, hC_apply 2 2, hC_apply 2 3]
        rw [hC_apply 3 0, hC_apply 3 1, hC_apply 3 2, hC_apply 3 3]
        rw [hH_apply 0 0, hH_apply 0 1, hH_apply 0 2, hH_apply 0 3]
        rw [hH_apply 1 0, hH_apply 1 1, hH_apply 1 2, hH_apply 1 3]
        rw [hH_apply 2 0, hH_apply 2 1, hH_apply 2 2, hH_apply 2 3]
        rw [hH_apply 3 0, hH_apply 3 1, hH_apply 3 2, hH_apply 3 3]
        dsimp [Matrix.mulVec, dotProduct]
        rw [sum_fin4, sum_fin4, sum_fin4, sum_fin4, sum_fin4, sum_fin4]
        ring
      have h_sub : (fun i => sys.μ i * (a * u' i + b * v' i)) = fun i => a * u i + b * v i := by
        ext i
        dsimp [u', v']
        have h_mu := hμ i
        have h_div1 : sys.μ i * (a * (u i / sys.μ i)) = a * u i := by
          calc sys.μ i * (a * (u i / sys.μ i)) = a * (sys.μ i * (u i / sys.μ i)) := by ring
          _ = a * u i := by rw [mul_div_cancel₀ (u i) h_mu]
        have h_div2 : sys.μ i * (b * (v i / sys.μ i)) = b * v i := by
          calc sys.μ i * (b * (v i / sys.μ i)) = b * (sys.μ i * (v i / sys.μ i)) := by ring
          _ = b * v i := by rw [mul_div_cancel₀ (v i) h_mu]
        linarith [h_div1, h_div2]
      rw [h_rM_mulVec]
      rw [h_C_eq]
      rw [h_sub]
      have h_nonneg : 0 ≤ ∑ i, (|g i| - g i) * (a * u' i + b * v' i) ^ 2 := by
        rw [sum_fin4]
        have h0 : 0 ≤ |g 0| - g 0 := sub_nonneg.mpr (le_abs_self (g 0))
        have h1 : 0 ≤ |g 1| - g 1 := sub_nonneg.mpr (le_abs_self (g 1))
        have h2 : 0 ≤ |g 2| - g 2 := sub_nonneg.mpr (le_abs_self (g 2))
        have h3 : 0 ≤ |g 3| - g 3 := sub_nonneg.mpr (le_abs_self (g 3))
        have sq0 : 0 ≤ (a * u' 0 + b * v' 0) ^ 2 := sq_nonneg _
        have sq1 : 0 ≤ (a * u' 1 + b * v' 1) ^ 2 := sq_nonneg _
        have sq2 : 0 ≤ (a * u' 2 + b * v' 2) ^ 2 := sq_nonneg _
        have sq3 : 0 ≤ (a * u' 3 + b * v' 3) ^ 2 := sq_nonneg _
        nlinarith
      linarith
  obtain ⟨pick, hpick_ne, hspec_pos⟩ := columnMax_spectral_inequality M hspectral hrow
  rw [trace_plus_two_sum_eq_sum_univ] at hspec_pos
  rw [sum_fin4] at hspec_pos
  have h_M_diag (j : Fin 4) : M j j = r j * sys.V j j + (1 - s j) * (sys.V.mulVec sys.μ) j := by
    rw [hM_apply j j, hC_apply j j, if_pos rfl, hH_apply j j, habs_g j, hg_apply j]
    have h_mu : sys.μ j = s j * r j := (hs_mul_r j).symm
    have hsq : s j ^ 2 = 1 := hs_sq j
    have hr_ne : r j ≠ 0 := (hr j).ne'
    dsimp [q]
    rw [h_mu]
    have hC_eq : (s j * r j) * sys.V j j * (s j * r j) +
        (s j * ((s j * r j) * (sys.V.mulVec sys.μ) j) - (s j * r j) * (sys.V.mulVec sys.μ) j) =
        r j * (r j * sys.V j j + (1 - s j) * (sys.V.mulVec sys.μ) j) := by
      calc
        (s j * r j) * sys.V j j * (s j * r j) + (s j * ((s j * r j) * (sys.V.mulVec sys.μ) j) -
            (s j * r j) * (sys.V.mulVec sys.μ) j)
          = (s j ^ 2 * r j) * r j * sys.V j j + (s j ^ 2 * r j - s j * r j) * (sys.V.mulVec
              sys.μ) j := by ring
        _ = (1 * r j) * r j * sys.V j j + (1 * r j - s j * r j) * (sys.V.mulVec sys.μ) j := by
            rw [hsq]
        _ = r j * (r j * sys.V j j + (1 - s j) * (sys.V.mulVec sys.μ) j) := by ring
    rw [hC_eq]
    rw [← mul_assoc, one_div_mul_cancel hr_ne, one_mul]
  have h_M_off (i j : Fin 4) (hij : i ≠ j) : M i j = s i * s j * r j * sys.V i j := by
    rw [hM_apply i j, hC_apply i j, if_neg hij, add_zero, hH_apply i j]
    have hmi : sys.μ i = s i * r i := (hs_mul_r i).symm
    have hmj : sys.μ j = s j * r j := (hs_mul_r j).symm
    have hri := (hr i).ne'
    dsimp [q]
    rw [hmi, hmj]
    calc (1 / r i) * (s i * r i * sys.V i j * (s j * r j))
        = (1 / r i * r i) * (s i * s j * r j * sys.V i j) := by ring
      _ = 1 * (s i * s j * r j * sys.V i j) := by rw [one_div_mul_cancel hri]
      _ = s i * s j * r j * sys.V i j := by ring
  have hs_or (k : Fin 4) : s k = 1 ∨ s k = -1 := by
    have hsq := hs_sq k
    have h_factor : (s k - 1) * (s k + 1) = 0 := by linarith [hsq]
    cases mul_eq_zero.mp h_factor with
    | inl h1 => left; linarith
    | inr h2 => right; linarith
  have h_s_a (j : Fin 4) : s j * (sys.U.transpose.mulVec sys.μ) j ≤ (sys.U.transpose.mulVec
      sys.μ) j := by
    have ha_pos := sys.leftSlope_pos j
    rcases hs_or j with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, neg_one_mul]
      linarith
  have h_sum_s_a : ∑ j, s j * (sys.U.transpose.mulVec sys.μ) j ≤ ∑ j, (sys.U.transpose.mulVec
      sys.μ) j := by
    rw [sum_fin4, sum_fin4]
    have ha0 := h_s_a 0
    have ha1 := h_s_a 1
    have ha2 := h_s_a 2
    have ha3 := h_s_a 3
    linarith
  have h_signed_le_abs (x t : ℝ) (ht : t = 1 ∨ t = -1) :
      t * x ≤ |x| := by
    rcases ht with rfl | rfl
    · simpa using le_abs_self x
    · simpa using neg_le_abs x
  have hs_prod (i j : Fin 4) : s i * s j = 1 ∨ s i * s j = -1 := by
    rcases hs_or i with hi | hi <;> rcases hs_or j with hj | hj <;>
      simp [hi, hj]
  have h_row_bound (j i : Fin 4) (hij : i ≠ j) :
      sys.μ j * (sys.w j - ∑ k, s k * sys.U j k) <
        sys.μ j * (∑ k ∈ offDiagSet j, s k * sys.V j k) -
          2 * sys.μ j * s i * sys.V j i := by
    have hc := sys.contraction i j hij
    have hw : s j * sys.w j ≤ |sys.w j| :=
      h_signed_le_abs (sys.w j) (s j) (hs_or j)
    have hsub :
        (s j * s i) * (-(sys.U j i - sys.V j i)) ≤
          |sys.U j i - sys.V j i| :=
      by simpa only [abs_neg] using
        h_signed_le_abs (-(sys.U j i - sys.V j i)) (s j * s i) (hs_prod j i)
    have hadd (k : Fin 4) :
        (s j * s k) * (-(sys.U j k + sys.V j k)) ≤
          |sys.U j k + sys.V j k| :=
      by simpa only [abs_neg] using
        h_signed_le_abs (-(sys.U j k + sys.V j k)) (s j * s k) (hs_prod j k)
    have hcore :
        s j * (sys.w j - ∑ k, s k * sys.U j k) <
          s j * (∑ k ∈ offDiagSet j, s k * sys.V j k) -
            2 * s j * s i * sys.V j i := by
      exact signed_contraction_fin4 s (fun k => sys.U j k)
        (fun k => sys.V j k) (sys.w j) j i hij (hs_or j)
        hc hw hsub hadd
    calc
      sys.μ j * (sys.w j - ∑ k, s k * sys.U j k) =
          r j * (s j * (sys.w j - ∑ k, s k * sys.U j k)) := by
            rw [← hs_mul_r j]
            ring
      _ < r j * (s j * (∑ k ∈ offDiagSet j, s k * sys.V j k) -
          2 * s j * s i * sys.V j i) :=
        mul_lt_mul_of_pos_left hcore (hr j)
      _ = sys.μ j * (∑ k ∈ offDiagSet j, s k * sys.V j k) -
          2 * sys.μ j * s i * sys.V j i := by
            rw [← hs_mul_r j]
            ring
  let Rmin : ℝ :=
    ∑ j, (sys.μ j * (∑ k ∈ offDiagSet j, s k * sys.V j k) -
      2 * sys.μ j * s (pick j) * sys.V j (pick j))
  have h_rows :
      dotProduct sys.μ sys.w -
          ∑ i, s i * (sys.U.transpose.mulVec sys.μ) i < Rmin := by
    have h0 := h_row_bound 0 (pick 0) (hpick_ne 0)
    have h1 := h_row_bound 1 (pick 1) (hpick_ne 1)
    have h2 := h_row_bound 2 (pick 2) (hpick_ne 2)
    have h3 := h_row_bound 3 (pick 3) (hpick_ne 3)
    have hleft :
        dotProduct sys.μ sys.w -
            ∑ i, s i * (sys.U.transpose.mulVec sys.μ) i =
          ∑ j, sys.μ j * (sys.w j - ∑ k, s k * sys.U j k) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply,
        Fin.sum_univ_four]
      ring
    rw [hleft]
    dsimp [Rmin]
    simp only [Fin.sum_univ_four]
    simp only [Fin.sum_univ_four] at h0 h1 h2 h3
    have h01 := add_lt_add h0 h1
    have h012 := add_lt_add h01 h2
    exact add_lt_add h012 h3
  have hb_lt_Rmin : ∑ i, (sys.V.mulVec sys.μ) i < Rmin := by
    have hint := sys.intercept
    linarith only [hint, h_rows, h_sum_s_a]
  have hVpick (j : Fin 4) :
      sys.V (pick j) j = sys.V j (pick j) := by
    exact congr_fun (congr_fun sys.V_inertia.1 j) (pick j)
  have hV01 : sys.V 0 1 = sys.V 1 0 :=
    congr_fun (congr_fun sys.V_inertia.1 1) 0
  have hV02 : sys.V 0 2 = sys.V 2 0 :=
    congr_fun (congr_fun sys.V_inertia.1 2) 0
  have hV03 : sys.V 0 3 = sys.V 3 0 :=
    congr_fun (congr_fun sys.V_inertia.1 3) 0
  have hV12 : sys.V 1 2 = sys.V 2 1 :=
    congr_fun (congr_fun sys.V_inertia.1 2) 1
  have hV13 : sys.V 1 3 = sys.V 3 1 :=
    congr_fun (congr_fun sys.V_inertia.1 3) 1
  have hV23 : sys.V 2 3 = sys.V 3 2 :=
    congr_fun (congr_fun sys.V_inertia.1 3) 2
  have h_spectral_sum :
      ∑ j, (M j j + 2 * M (pick j) j) =
        (∑ i, (sys.V.mulVec sys.μ) i) - Rmin := by
    rw [Fin.sum_univ_four]
    rw [h_M_diag 0, h_M_diag 1, h_M_diag 2, h_M_diag 3]
    rw [h_M_off (pick 0) 0 (hpick_ne 0),
      h_M_off (pick 1) 1 (hpick_ne 1),
      h_M_off (pick 2) 2 (hpick_ne 2),
      h_M_off (pick 3) 3 (hpick_ne 3)]
    rw [hVpick 0, hVpick 1, hVpick 2, hVpick 3]
    dsimp [Rmin]
    simp only [Fin.isValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, offDiagSet, ne_eq, sum_filter, ite_not,
      sum_sub_distrib, ↓reduceIte, one_ne_zero, zero_add, Fin.reduceEq,
      zero_ne_one, add_zero]
    rw [← hs_mul_r 0, ← hs_mul_r 1, ← hs_mul_r 2, ← hs_mul_r 3]
    rw [← hV01, ← hV02, ← hV03, ← hV12, ← hV13, ← hV23]
    ring_nf
    rw [hs_sq 0, hs_sq 1, hs_sq 2, hs_sq 3]
    ring
  have h_sum_neg : ∑ j, (M j j + 2 * M (pick j) j) < 0 := by
    rw [h_spectral_sum]
    linarith only [hb_lt_Rmin]
  rw [Fin.sum_univ_four] at h_sum_neg
  linarith only [hspec_pos, h_sum_neg]

private lemma quad_null_expansion (sys : F8NormalizedSystem) (t α : ℝ) (h : Fin 4 → ℝ) (k : Fin 4) :
    quadraticForm4 sys.V (sys.μ + t • h + α • Pi.single k 1) =
      quadraticForm4 sys.V sys.μ +
      2 * t * dotProduct (sys.V.mulVec sys.μ) h +
      2 * α * (sys.V.mulVec sys.μ) k +
      t ^ 2 * quadraticForm4 sys.V h +
      2 * t * α * (sys.V.mulVec h) k +
      α ^ 2 * sys.V k k := by
  have hsymm := sys.V_inertia.1
  dsimp [quadraticForm4, dotProduct, Matrix.mulVec]
  simp only [Fin.sum_univ_four, Pi.single_apply]
  have hS (i j : Fin 4) : sys.V j i = sys.V i j := congr_fun (congr_fun hsymm i) j
  have h01 := hS 0 1; have h02 := hS 0 2; have h03 := hS 0 3
  have h12 := hS 1 2; have h13 := hS 1 3; have h23 := hS 2 3
  fin_cases k
  · dsimp; rw [← h01, ← h02, ← h03, ← h12, ← h13, ← h23]; ring
  · dsimp; rw [← h01, ← h02, ← h03, ← h12, ← h13, ← h23]; ring
  · dsimp; rw [← h01, ← h02, ← h03, ← h12, ← h13, ← h23]; ring
  · dsimp; rw [← h01, ← h02, ← h03, ← h12, ← h13, ← h23]; ring

private lemma quad_root_spec (A B C : ℝ) (hA : A ≠ 0) (hdisc : 0 ≤ B ^ 2 - 4 * A * C) :
    let x := (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A)
    A * x ^ 2 + B * x + C = 0 := by
  intro x
  dsimp [x]
  have h2A : 2 * A ≠ 0 := mul_ne_zero (by norm_num) hA
  have hsq := Real.sq_sqrt hdisc
  have h : A * ((-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A)) ^ 2 +
      B * ((-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A)) + C =
      ((Real.sqrt (B ^ 2 - 4 * A * C)) ^ 2 - (B ^ 2 - 4 * A * C)) / (4 * A) := by
    field_simp; ring
  rw [h, hsq, sub_self, zero_div]

private lemma alpha_tendsto_zero (sys : F8NormalizedSystem) (h : Fin 4 → ℝ) (k : Fin 4)
    (hVk : 0 < (sys.V.mulVec sys.μ) k) :
    let A := sys.V k k
    let B (t : ℝ) := 2 * (sys.V.mulVec sys.μ) k + 2 * t * (sys.V.mulVec h) k
    let C (t : ℝ) := 2 * t * dotProduct (sys.V.mulVec sys.μ) h + t ^ 2 * quadraticForm4 sys.V h
    let Δ (t : ℝ) := B t ^ 2 - 4 * A * C t
    let α (t : ℝ) := if A = 0 then - C t / B t else (- B t + Real.sqrt (Δ t)) / (2 * A)
    Filter.Tendsto α (nhds 0) (nhds 0) ∧ ∀ᶠ t in nhds 0, quadraticForm4 sys.V (sys.μ + t • h +
        (α t) • Pi.single k 1) = 0 := by
  intro A B C Δ α
  have hB0 : B 0 = 2 * (sys.V.mulVec sys.μ) k := by dsimp [B]; ring
  have hB0_pos : 0 < B 0 := by rw [hB0]; linarith
  have hC0 : C 0 = 0 := by dsimp [C]; ring
  have hcontB : Continuous B := by
    dsimp [B]
    exact continuous_const.add ((continuous_const.mul continuous_id).mul continuous_const)
  have hcontC : Continuous C := by
    dsimp [C]
    exact ((continuous_const.mul continuous_id).mul continuous_const).add ((continuous_id.pow
        2).mul continuous_const)
  have hcontΔ : Continuous Δ := by
    dsimp [Δ]
    exact (hcontB.pow 2).sub (continuous_const.mul hcontC)
  have hΔ0 : Δ 0 = (B 0) ^ 2 := by
    dsimp [Δ]
    rw [hC0, mul_zero, sub_zero]
  have hΔ0_pos : 0 < Δ 0 := by rw [hΔ0]; positivity
  have hB_evt : ∀ᶠ t in nhds 0, 0 < B t := hcontB.tendsto 0 (Ioi_mem_nhds hB0_pos)
  have hΔ_evt : ∀ᶠ t in nhds 0, 0 ≤ Δ t := hcontΔ.tendsto 0 (mem_nhds_iff.mpr ⟨Set.Ioi 0,
      Set.Ioi_subset_Ici_self, isOpen_Ioi, hΔ0_pos⟩)
  by_cases hA : A = 0
  · have hα_def : α = fun t => - C t / B t := by ext t; dsimp [α]; rw [if_pos hA]
    rw [hα_def]
    refine ⟨?_, ?_⟩
    · have hC_lim : Filter.Tendsto C (nhds 0) (nhds 0) := by
        have h := hcontC.tendsto 0
        rwa [hC0] at h
      have hB_lim : Filter.Tendsto B (nhds 0) (nhds (B 0)) := hcontB.tendsto 0
      have hdiv := Filter.Tendsto.div hC_lim.neg hB_lim hB0_pos.ne'
      rw [neg_zero, zero_div] at hdiv
      exact hdiv
    · filter_upwards [hB_evt] with t ht
      have hnull_exp := quad_null_expansion sys t (-C t / B t) h k
      rw [hnull_exp, sys.null]
      dsimp [A, B, C] at *
      have hBt_ne : 2 * (sys.V.mulVec sys.μ) k + 2 * t * (sys.V.mulVec h) k ≠ 0 := ht.ne'
      rw [hA]
      have h_alg : 0 + 2 * t * dotProduct (sys.V.mulVec sys.μ) h +
          2 * (- (2 * t * dotProduct (sys.V.mulVec sys.μ) h + t ^ 2 * quadraticForm4 sys.V h) /
            (2 * (sys.V.mulVec sys.μ) k + 2 * t * (sys.V.mulVec h) k)) * (sys.V.mulVec sys.μ) k +
          t ^ 2 * quadraticForm4 sys.V h +
          2 * t * (- (2 * t * dotProduct (sys.V.mulVec sys.μ) h + t ^ 2 * quadraticForm4 sys.V h) /
            (2 * (sys.V.mulVec sys.μ) k + 2 * t * (sys.V.mulVec h) k)) * (sys.V.mulVec h) k +
          (- (2 * t * dotProduct (sys.V.mulVec sys.μ) h + t ^ 2 * quadraticForm4 sys.V h) /
            (2 * (sys.V.mulVec sys.μ) k + 2 * t * (sys.V.mulVec h) k)) ^ 2 * 0 =
          (2 * t * dotProduct (sys.V.mulVec sys.μ) h + t ^ 2 * quadraticForm4 sys.V h) *
          (1 - (2 * (sys.V.mulVec sys.μ) k + 2 * t * (sys.V.mulVec h) k) /
            (2 * (sys.V.mulVec sys.μ) k + 2 * t * (sys.V.mulVec h) k)) := by
        field_simp
        ring
      rw [h_alg, div_self hBt_ne, sub_self, mul_zero]
  · have hα_def : α = fun t => (- B t + Real.sqrt (Δ t)) / (2 * A) := by
      ext t; dsimp [α]; rw [if_neg hA]
    rw [hα_def]
    refine ⟨?_, ?_⟩
    · have hB_lim : Filter.Tendsto B (nhds 0) (nhds (B 0)) := hcontB.tendsto 0
      have hΔ_lim : Filter.Tendsto Δ (nhds 0) (nhds (Δ 0)) := hcontΔ.tendsto 0
      have hsqrt : Filter.Tendsto (fun t => Real.sqrt (Δ t)) (nhds 0) (nhds (Real.sqrt (Δ 0))) :=
        Continuous.tendsto (Real.continuous_sqrt) _ |>.comp hΔ_lim
      rw [hΔ0, Real.sqrt_sq hB0_pos.le] at hsqrt
      have hnum : Filter.Tendsto (fun t => - B t + Real.sqrt (Δ t)) (nhds 0) (nhds (- B 0 + B 0)) :=
        hB_lim.neg.add hsqrt
      rw [neg_add_cancel] at hnum
      have hdiv2 : Filter.Tendsto (fun t => (- B t + Real.sqrt (Δ t)) * (1 / (2 * A))) (nhds 0)
          (nhds (0 * (1 / (2 * A)))) :=
        Filter.Tendsto.mul_const (1 / (2 * A)) hnum
      rw [zero_mul] at hdiv2
      have h_eq : (fun t => (- B t + Real.sqrt (Δ t)) / (2 * A)) = (fun t => (- B t + Real.sqrt
          (Δ t)) * (1 / (2 * A))) := by
        ext t; ring
      rwa [h_eq]
    · filter_upwards [hΔ_evt] with t ht
      have hnull_exp := quad_null_expansion sys t ((- B t + Real.sqrt (Δ t)) / (2 * A)) h k
      rw [hnull_exp, sys.null]
      have hspec := quad_root_spec A (B t) (C t) hA ht
      dsimp [A, B, C] at *
      linarith [hspec]

/-- The perturbative part of paper Lemma 6. The null cone is smooth at `μ`
because `V μ` is coordinatewise positive. Hence one can remove zero
coordinates while preserving the four strict open conditions. -/
private theorem exists_nonzero_null_perturbation
    (sys : F8NormalizedSystem) :
    ∃ ν : Fin 4 → ℝ,
      (∀ i, ν i ≠ 0) ∧
      (∀ i, 0 < (sys.U.transpose.mulVec ν) i) ∧
      (∀ i, 0 < (sys.V.mulVec ν) i) ∧
      quadraticForm4 sys.V ν = 0 ∧
      (∑ i, (sys.U.transpose.mulVec ν) i) +
        (∑ i, (sys.V.mulVec ν) i) < dotProduct ν sys.w := by
  by_cases hμ_all : ∀ i, sys.μ i ≠ 0
  · exact ⟨sys.μ, hμ_all, sys.leftSlope_pos, sys.rightSlope_pos, sys.null, sys.intercept⟩
  · have hμ_not_all : ¬ ∀ i, sys.μ i ≠ 0 := hμ_all
    clear hμ_all
    have hμ_ne_zero : sys.μ ≠ 0 := by
      intro h_zero
      have h_right0 := sys.rightSlope_pos 0
      rw [h_zero, Matrix.mulVec_zero] at h_right0
      dsimp at h_right0
      linarith
    have h_ex_k : ∃ k : Fin 4, sys.μ k ≠ 0 := by
      by_contra h_all_zero
      push Not at h_all_zero
      apply hμ_ne_zero
      ext k
      exact h_all_zero k
    obtain ⟨k, hk⟩ := h_ex_k
    let h : Fin 4 → ℝ := fun i => if sys.μ i = 0 then 1 else 0
    have hVk : 0 < (sys.V.mulVec sys.μ) k := sys.rightSlope_pos k
    set A := sys.V k k
    set B : ℝ → ℝ := fun t => 2 * (sys.V.mulVec sys.μ) k + 2 * t * (sys.V.mulVec h) k
    set C : ℝ → ℝ := fun t => 2 * t * dotProduct (sys.V.mulVec sys.μ) h + t ^ 2 * quadraticForm4
        sys.V h
    set Δ : ℝ → ℝ := fun t => B t ^ 2 - 4 * A * C t
    set α : ℝ → ℝ := fun t => if A = 0 then - C t / B t else (- B t + Real.sqrt (Δ t)) / (2 * A)
    obtain ⟨hα_lim, hα_null⟩ := alpha_tendsto_zero sys h k hVk
    let ν (t : ℝ) : Fin 4 → ℝ := sys.μ + t • h + (α t) • Pi.single k 1
    have hν_lim : Filter.Tendsto ν (nhds 0) (nhds sys.μ) := by
      change Filter.Tendsto (fun t => sys.μ + t • h + α t • Pi.single k 1) (nhds 0) (nhds sys.μ)
      have h1 : Filter.Tendsto (fun t : ℝ => sys.μ + t • h) (nhds 0) (nhds sys.μ) := by
        have h_cont1 : Continuous (fun t : ℝ => sys.μ + t • h) :=
          continuous_const.add (continuous_id.smul continuous_const)
        have h1_sub := h_cont1.tendsto 0
        change Filter.Tendsto (fun t => sys.μ + t • h) (nhds 0) (nhds (sys.μ + (0:ℝ) • h)) at h1_sub
        rw [zero_smul, add_zero] at h1_sub
        exact h1_sub
      have h2 : Filter.Tendsto (fun t : ℝ => (α t) • Pi.single k 1) (nhds 0) (nhds 0) := by
        have h2_sub := Filter.Tendsto.smul hα_lim (tendsto_const_nhds : Filter.Tendsto (fun _ :
            ℝ => Pi.single k (1:ℝ)) (nhds 0) (nhds (Pi.single k 1)))
        change Filter.Tendsto (fun t => (α t) • Pi.single k 1) (nhds 0) (nhds ((0:ℝ) • Pi.single
            k 1)) at h2_sub
        rw [zero_smul] at h2_sub
        exact h2_sub
      have h3 := h1.add h2
      rw [add_zero] at h3
      exact h3
    have h_left_evt : ∀ᶠ t in nhds 0, ∀ i, 0 < (sys.U.transpose.mulVec (ν t)) i := by
      have h_open (i : Fin 4) : ∀ᶠ t in nhds 0, 0 < (sys.U.transpose.mulVec (ν t)) i := by
        have h_cont : Continuous (fun v : Fin 4 → ℝ => (sys.U.transpose.mulVec v) i) := by
          dsimp [Matrix.mulVec, dotProduct]
          exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j))
        exact h_cont.tendsto sys.μ |>.comp hν_lim (Ioi_mem_nhds (sys.leftSlope_pos i))
      exact Filter.eventually_all.mpr h_open
    have h_right_evt : ∀ᶠ t in nhds 0, ∀ i, 0 < (sys.V.mulVec (ν t)) i := by
      have h_open (i : Fin 4) : ∀ᶠ t in nhds 0, 0 < (sys.V.mulVec (ν t)) i := by
        have h_cont : Continuous (fun v : Fin 4 → ℝ => (sys.V.mulVec v) i) := by
          dsimp [Matrix.mulVec, dotProduct]
          exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j))
        exact h_cont.tendsto sys.μ |>.comp hν_lim (Ioi_mem_nhds (sys.rightSlope_pos i))
      exact Filter.eventually_all.mpr h_open
    have h_intercept_evt : ∀ᶠ t in nhds 0,
        (∑ i, (sys.U.transpose.mulVec (ν t)) i) + (∑ i, (sys.V.mulVec (ν t)) i) < dotProduct (ν
            t) sys.w := by
      have h_cont : Continuous (fun v : Fin 4 → ℝ =>
          (∑ i, (sys.U.transpose.mulVec v) i) + (∑ i, (sys.V.mulVec v) i) - dotProduct v sys.w)
              := by
        dsimp [Matrix.mulVec, dotProduct]
        have c1 : Continuous (fun v : Fin 4 → ℝ => ∑ i : Fin 4, ∑ j : Fin 4, sys.U.transpose i j
            * v j) :=
          continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
              continuous_const.mul (continuous_apply j)))
        have c2 : Continuous (fun v : Fin 4 → ℝ => ∑ i : Fin 4, ∑ j : Fin 4, sys.V i j * v j) :=
          continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
              continuous_const.mul (continuous_apply j)))
        have c3 : Continuous (fun v : Fin 4 → ℝ => ∑ i : Fin 4, v i * sys.w i) :=
          continuous_finsetSum _ (fun i _ => (continuous_apply i).mul continuous_const)
        exact (c1.add c2).sub c3
      have h_init : (∑ i, (sys.U.transpose.mulVec sys.μ) i) + (∑ i, (sys.V.mulVec sys.μ) i) -
          dotProduct sys.μ sys.w < 0 :=
        sub_neg.mpr sys.intercept
      have h_evt := h_cont.tendsto sys.μ |>.comp hν_lim (Iio_mem_nhds h_init)
      filter_upwards [h_evt] with t ht
      change (∑ i, (sys.U.transpose.mulVec (ν t)) i) + (∑ i, (sys.V.mulVec (ν t)) i) -
          dotProduct (ν t) sys.w < 0 at ht
      linarith
    have h_ne_k_evt : ∀ᶠ t in nhds 0, (ν t) k ≠ 0 := by
      have h_cont : Continuous (fun v : Fin 4 → ℝ => v k) := continuous_apply k
      exact h_cont.tendsto sys.μ |>.comp hν_lim (isOpen_ne.mem_nhds hk)
    have h_pos_freq : ∃ᶠ t in nhds (0 : ℝ), 0 < t := frequently_gt_nhds 0
    have h_all_evt : ∀ᶠ t in nhds (0 : ℝ),
        quadraticForm4 sys.V (ν t) = 0 ∧
        (∀ i, 0 < (sys.U.transpose.mulVec (ν t)) i) ∧
        (∀ i, 0 < (sys.V.mulVec (ν t)) i) ∧
        ((∑ i, (sys.U.transpose.mulVec (ν t)) i) + (∑ i, (sys.V.mulVec (ν t)) i) < dotProduct (ν
            t) sys.w) ∧
        (ν t) k ≠ 0 :=
      hα_null.and (h_left_evt.and (h_right_evt.and (h_intercept_evt.and h_ne_k_evt)))
    have h_freq_all : ∃ t : ℝ, 0 < t ∧
        quadraticForm4 sys.V (ν t) = 0 ∧
        (∀ i, 0 < (sys.U.transpose.mulVec (ν t)) i) ∧
        (∀ i, 0 < (sys.V.mulVec (ν t)) i) ∧
        ((∑ i, (sys.U.transpose.mulVec (ν t)) i) + (∑ i, (sys.V.mulVec (ν t)) i) < dotProduct (ν
            t) sys.w) ∧
        (ν t) k ≠ 0 :=
      Filter.Frequently.exists (Filter.Frequently.and_eventually h_pos_freq h_all_evt)
    obtain ⟨t, ht_pos, ht_null, ht_left, ht_right, ht_intercept, ht_ne_k⟩ := h_freq_all
    refine ⟨ν t, ?_, ht_left, ht_right, ht_null, ht_intercept⟩
    intro i
    by_cases hk_i : i = k
    · rw [hk_i]; exact ht_ne_k
    · have h_single : (α t * (Pi.single k 1 : Fin 4 → ℝ) i) = 0 := by
        have h1 : (Pi.single k 1 : Fin 4 → ℝ) i = 0 := Pi.single_eq_of_ne hk_i 1
        rw [h1, mul_zero]
      change sys.μ i + t * h i + α t * (Pi.single k 1 : Fin 4 → ℝ) i ≠ 0
      rw [h_single, add_zero]
      by_cases hμ_i : sys.μ i = 0
      · dsimp [h]
        rw [hμ_i, if_pos rfl, mul_one, zero_add]
        exact ht_pos.ne'
      · have h_h_i : h i = 0 := by
          dsimp [h]
          rw [if_neg hμ_i]
        rw [h_h_i, mul_zero, add_zero]
        exact hμ_i

/-- Paper Lemma 6: the normalized system is impossible. -/
theorem not_nonempty_f8NormalizedSystem :
    ¬ Nonempty F8NormalizedSystem := by
  rintro ⟨sys⟩
  obtain ⟨ν, hν, hleft, hright, hnull, hintercept⟩ :=
    exists_nonzero_null_perturbation sys
  let perturbed : F8NormalizedSystem := {
    U := sys.U
    V := sys.V
    w := sys.w
    μ := ν
    U_pos := sys.U_pos
    V_inertia := sys.V_inertia
    diagonal_pos := sys.diagonal_pos
    contraction := sys.contraction
    leftSlope_pos := hleft
    rightSlope_pos := hright
    null := hnull
    intercept := hintercept
  }
  exact f8NormalizedSystem_false_of_mu_ne_zero perturbed hν

theorem f8_not_computableWithHeadsN_two :
    ¬ computableWithHeadsN 8 2 f8 := by
  intro h
  exact not_nonempty_f8NormalizedSystem
    (two_heads_yield_f8NormalizedSystem h)

end HeadComplexity
