import HeadComplexity.Separations.EightBitHammingThreshold.Core

set_option linter.style.header false

/-!
# Eight-bit Hamming threshold: K4 choice-cone obstruction
-/

namespace HeadComplexity

open Finset
open scoped BigOperators
open TypicalLogCloseness
open MvPolynomial
open EightBitInternal

private lemma exists_offDiag_maximizer (M : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    ∃ p ∈ offDiagSet j, ∀ i ∈ offDiagSet j, M i j ≤ M p j :=
  Finset.exists_max_image (offDiagSet j) (fun i => M i j) (offDiagSet_nonempty j)

private noncomputable def columnMaxPicker (M : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) : Fin 4 :=
  Classical.choose (exists_offDiag_maximizer M j)

private lemma columnMaxPicker_ne (M : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    columnMaxPicker M j ≠ j := by
  have h := (Classical.choose_spec (exists_offDiag_maximizer M j)).1
  dsimp [offDiagSet] at h
  rw [Finset.mem_filter] at h
  exact h.2

private lemma columnMaxPicker_le (M : Matrix (Fin 4) (Fin 4) ℝ)
    (j : Fin 4) (i : Fin 4) (hi : i ≠ j) :
    M i j ≤ M (columnMaxPicker M j) j := by
  have hspec := (Classical.choose_spec (exists_offDiag_maximizer M j)).2
  have hi_mem : i ∈ offDiagSet j := by
    dsimp [offDiagSet]
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hi⟩
  exact hspec i hi_mem

private theorem quadraticForm4_zeroRow_eq_edge_sum
    (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hsymm : B.IsSymm) (hzero : B.mulVec (fun _ => 1) = 0) (z : Fin 4 → ℝ) :
    quadraticForm4 B z =
      - B 0 1 * (z 0 - z 1) ^ 2 -
      B 0 2 * (z 0 - z 2) ^ 2 -
      B 0 3 * (z 0 - z 3) ^ 2 -
      B 1 2 * (z 1 - z 2) ^ 2 -
      B 1 3 * (z 1 - z 3) ^ 2 -
      B 2 3 * (z 2 - z 3) ^ 2 := by
  have hz0 : B 0 0 + B 0 1 + B 0 2 + B 0 3 = 0 := by
    have h := congr_fun hzero 0
    dsimp [Matrix.mulVec, dotProduct] at h
    rw [sum_fin4] at h
    linarith
  have hz1 : B 1 0 + B 1 1 + B 1 2 + B 1 3 = 0 := by
    have h := congr_fun hzero 1
    dsimp [Matrix.mulVec, dotProduct] at h
    rw [sum_fin4] at h
    linarith
  have hz2 : B 2 0 + B 2 1 + B 2 2 + B 2 3 = 0 := by
    have h := congr_fun hzero 2
    dsimp [Matrix.mulVec, dotProduct] at h
    rw [sum_fin4] at h
    linarith
  have hz3 : B 3 0 + B 3 1 + B 3 2 + B 3 3 = 0 := by
    have h := congr_fun hzero 3
    dsimp [Matrix.mulVec, dotProduct] at h
    rw [sum_fin4] at h
    linarith
  have h10 : B 1 0 = B 0 1 := congr_fun (congr_fun hsymm 0) 1
  have h20 : B 2 0 = B 0 2 := congr_fun (congr_fun hsymm 0) 2
  have h30 : B 3 0 = B 0 3 := congr_fun (congr_fun hsymm 0) 3
  have h21 : B 2 1 = B 1 2 := congr_fun (congr_fun hsymm 1) 2
  have h31 : B 3 1 = B 1 3 := congr_fun (congr_fun hsymm 1) 3
  have h32 : B 3 2 = B 2 3 := congr_fun (congr_fun hsymm 2) 3
  unfold quadraticForm4 dotProduct
  rw [sum_fin4]
  have hd (i : Fin 4) : B.mulVec z i = B i 0 * z 0 + B i 1 * z 1 + B i 2 * z 2 + B i 3 * z 3 := by
    dsimp [Matrix.mulVec, dotProduct]
    rw [sum_fin4]
  rw [hd 0, hd 1, hd 2, hd 3]
  linear_combination
    z 0 ^ 2 * hz0 + z 1 ^ 2 * hz1 + z 2 ^ 2 * hz2 + z 3 ^ 2 * hz3 +
    (z 0 * z 1 - z 1 ^ 2) * h10 + (z 0 * z 2 - z 2 ^ 2) * h20 + (z 0 * z 3 - z 3 ^ 2) * h30 +
    (z 1 * z 2 - z 2 ^ 2) * h21 + (z 1 * z 3 - z 3 ^ 2) * h31 + (z 2 * z 3 - z 3 ^ 2) * h32

private def choiceFunctional (q : Fin 4 → ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ)
    (pick : Fin 4 → Fin 4) : ℝ :=
  (∑ i, q i * B i i) + 2 * ∑ j, q (pick j) * B (pick j) j

private theorem exists_three_interval_sum
    (l₁ u₁ l₂ u₂ l₃ u₃ s : ℝ)
    (h₁ : l₁ ≤ u₁) (h₂ : l₂ ≤ u₂) (h₃ : l₃ ≤ u₃)
    (hl : l₁ + l₂ + l₃ ≤ s) (hu : s ≤ u₁ + u₂ + u₃) :
    ∃ x₁ x₂ x₃ : ℝ,
      l₁ ≤ x₁ ∧ x₁ ≤ u₁ ∧ l₂ ≤ x₂ ∧ x₂ ≤ u₂ ∧
        l₃ ≤ x₃ ∧ x₃ ≤ u₃ ∧ x₁ + x₂ + x₃ = s := by
  let x₁ := max l₁ (s - u₂ - u₃)
  let x₂ := max l₂ (s - x₁ - u₃)
  let x₃ := s - x₁ - x₂
  have hx₁l : l₁ ≤ x₁ := le_max_left _ _
  have hx₁a : s - u₂ - u₃ ≤ x₁ := le_max_right _ _
  have hx₁u : x₁ ≤ u₁ := by
    apply max_le h₁
    linarith
  have hx₁r : x₁ ≤ s - l₂ - l₃ := by
    apply max_le
    · linarith
    · linarith
  have hx₂l : l₂ ≤ x₂ := le_max_left _ _
  have hx₂a : s - x₁ - u₃ ≤ x₂ := le_max_right _ _
  have hx₂u : x₂ ≤ u₂ := by
    apply max_le h₂
    linarith
  have hx₂r : x₂ ≤ s - x₁ - l₃ := by
    apply max_le
    · linarith
    · linarith
  refine ⟨x₁, x₂, x₃, hx₁l, hx₁u, hx₂l, hx₂u, ?_, ?_, ?_⟩
  · dsimp [x₃]
    linarith
  · dsimp [x₃]
    linarith
  · dsimp [x₃]
    ring

private theorem triangle_edge_allocation
    (c₁₂ c₁₃ c₂₃ r₁ r₂ r₃ : ℝ)
    (hc₁₂ : 0 ≤ c₁₂) (hc₁₃ : 0 ≤ c₁₃) (hc₂₃ : 0 ≤ c₂₃)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hr₃ : 0 ≤ r₃)
    (htotal : r₁ + r₂ + r₃ = c₁₂ + c₁₃ + c₂₃)
    (hinc₁ : r₁ ≤ c₁₂ + c₁₃)
    (hinc₂ : r₂ ≤ c₁₂ + c₂₃)
    (hinc₃ : r₃ ≤ c₁₃ + c₂₃) :
    ∃ a b c : ℝ,
      0 ≤ a ∧ a ≤ c₁₂ ∧ 0 ≤ b ∧ b ≤ c₁₃ ∧ 0 ≤ c ∧ c ≤ c₂₃ ∧
        a + b = r₁ ∧ (c₁₂ - a) + c = r₂ ∧
          (c₁₃ - b) + (c₂₃ - c) = r₃ := by
  let a := max (max 0 (r₁ - c₁₃)) (c₁₂ - r₂)
  have ha0 : 0 ≤ a :=
    le_trans (le_max_left 0 (r₁ - c₁₃))
      (le_max_left (max 0 (r₁ - c₁₃)) (c₁₂ - r₂))
  have haR : r₁ - c₁₃ ≤ a :=
    le_trans (le_max_right 0 (r₁ - c₁₃))
      (le_max_left (max 0 (r₁ - c₁₃)) (c₁₂ - r₂))
  have haC : c₁₂ - r₂ ≤ a := le_max_right _ _
  have ha12 : a ≤ c₁₂ := by
    apply max_le
    · apply max_le hc₁₂
      linarith
    · linarith
  have ha1 : a ≤ r₁ := by
    apply max_le
    · apply max_le hr₁
      linarith
    · linarith
  have ha23 : a ≤ c₁₂ - r₂ + c₂₃ := by
    apply max_le
    · apply max_le
      · linarith
      · linarith
    · linarith
  refine ⟨a, r₁ - a, r₂ - c₁₂ + a, ha0, ha12, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · ring
  · ring
  · linarith

private theorem k4_edge_allocation
    (c₀₁ c₀₂ c₀₃ c₁₂ c₁₃ c₂₃ v₀ v₁ v₂ v₃ : ℝ)
    (hc₀₁ : 0 ≤ c₀₁) (hc₀₂ : 0 ≤ c₀₂) (hc₀₃ : 0 ≤ c₀₃)
    (hc₁₂ : 0 ≤ c₁₂) (hc₁₃ : 0 ≤ c₁₃) (hc₂₃ : 0 ≤ c₂₃)
    (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (htotal : v₀ + v₁ + v₂ + v₃ = c₀₁ + c₀₂ + c₀₃ + c₁₂ + c₁₃ + c₂₃)
    (hp₀₁ : c₀₁ ≤ v₀ + v₁) (hp₀₂ : c₀₂ ≤ v₀ + v₂)
    (hp₀₃ : c₀₃ ≤ v₀ + v₃) (hp₁₂ : c₁₂ ≤ v₁ + v₂)
    (hp₁₃ : c₁₃ ≤ v₁ + v₃) (hp₂₃ : c₂₃ ≤ v₂ + v₃)
    (ht₀₁₂ : c₀₁ + c₀₂ + c₁₂ ≤ v₀ + v₁ + v₂)
    (ht₀₁₃ : c₀₁ + c₀₃ + c₁₃ ≤ v₀ + v₁ + v₃)
    (ht₀₂₃ : c₀₂ + c₀₃ + c₂₃ ≤ v₀ + v₂ + v₃)
    (ht₁₂₃ : c₁₂ + c₁₃ + c₂₃ ≤ v₁ + v₂ + v₃) :
    ∃ A : Matrix (Fin 4) (Fin 4) ℝ,
      (∀ i j, 0 ≤ A i j) ∧
      (∀ i, A i i = 0) ∧
      (∀ i, ∑ j, A i j = ![v₀, v₁, v₂, v₃] i) ∧
      A 0 1 + A 1 0 = c₀₁ ∧ A 0 2 + A 2 0 = c₀₂ ∧
      A 0 3 + A 3 0 = c₀₃ ∧ A 1 2 + A 2 1 = c₁₂ ∧
      A 1 3 + A 3 1 = c₁₃ ∧ A 2 3 + A 3 2 = c₂₃ := by
  let l₁ := max 0 (c₀₁ - v₁)
  let l₂ := max 0 (c₀₂ - v₂)
  let l₃ := max 0 (c₀₃ - v₃)
  let u₁ := min c₀₁ (c₀₁ - v₁ + c₁₂ + c₁₃)
  let u₂ := min c₀₂ (c₀₂ - v₂ + c₁₂ + c₂₃)
  let u₃ := min c₀₃ (c₀₃ - v₃ + c₁₃ + c₂₃)
  have hl₁u₁ : l₁ ≤ u₁ := by
    apply max_le
    · apply le_min hc₀₁
      linarith
    · apply le_min
      · linarith
      · linarith
  have hl₂u₂ : l₂ ≤ u₂ := by
    apply max_le
    · apply le_min hc₀₂
      linarith
    · apply le_min
      · linarith
      · linarith
  have hl₃u₃ : l₃ ≤ u₃ := by
    apply max_le
    · apply le_min hc₀₃
      linarith
    · apply le_min
      · linarith
      · linarith
  have hl₁ : l₁ = 0 ∨ l₁ = c₀₁ - v₁ := by
    dsimp [l₁]
    exact max_choice _ _
  have hl₂ : l₂ = 0 ∨ l₂ = c₀₂ - v₂ := by
    dsimp [l₂]
    exact max_choice _ _
  have hl₃ : l₃ = 0 ∨ l₃ = c₀₃ - v₃ := by
    dsimp [l₃]
    exact max_choice _ _
  have hlsum : l₁ + l₂ + l₃ ≤ v₀ := by
    rcases hl₁ with hl₁ | hl₁ <;> rcases hl₂ with hl₂ | hl₂ <;>
      rcases hl₃ with hl₃ | hl₃ <;> rw [hl₁, hl₂, hl₃]
    all_goals linarith
  have hu₁ : u₁ = c₀₁ ∨ u₁ = c₀₁ - v₁ + c₁₂ + c₁₃ := by
    dsimp [u₁]
    exact min_choice _ _
  have hu₂ : u₂ = c₀₂ ∨ u₂ = c₀₂ - v₂ + c₁₂ + c₂₃ := by
    dsimp [u₂]
    exact min_choice _ _
  have hu₃ : u₃ = c₀₃ ∨ u₃ = c₀₃ - v₃ + c₁₃ + c₂₃ := by
    dsimp [u₃]
    exact min_choice _ _
  have husum : v₀ ≤ u₁ + u₂ + u₃ := by
    rcases hu₁ with hu₁ | hu₁ <;> rcases hu₂ with hu₂ | hu₂ <;>
      rcases hu₃ with hu₃ | hu₃ <;> rw [hu₁, hu₂, hu₃]
    all_goals linarith
  obtain ⟨x₀₁, x₀₂, x₀₃, hx₀₁l, hx₀₁u, hx₀₂l, hx₀₂u,
      hx₀₃l, hx₀₃u, hxsum⟩ :=
    exists_three_interval_sum l₁ u₁ l₂ u₂ l₃ u₃ v₀
      hl₁u₁ hl₂u₂ hl₃u₃ hlsum husum
  have hr₁0 : 0 ≤ v₁ - c₀₁ + x₀₁ := by
    have := le_trans (le_max_right 0 (c₀₁ - v₁)) hx₀₁l
    linarith
  have hr₂0 : 0 ≤ v₂ - c₀₂ + x₀₂ := by
    have := le_trans (le_max_right 0 (c₀₂ - v₂)) hx₀₂l
    linarith
  have hr₃0 : 0 ≤ v₃ - c₀₃ + x₀₃ := by
    have := le_trans (le_max_right 0 (c₀₃ - v₃)) hx₀₃l
    linarith
  have hr₁u : v₁ - c₀₁ + x₀₁ ≤ c₁₂ + c₁₃ := by
    have := le_trans hx₀₁u (min_le_right c₀₁ (c₀₁ - v₁ + c₁₂ + c₁₃))
    linarith
  have hr₂u : v₂ - c₀₂ + x₀₂ ≤ c₁₂ + c₂₃ := by
    have := le_trans hx₀₂u (min_le_right c₀₂ (c₀₂ - v₂ + c₁₂ + c₂₃))
    linarith
  have hr₃u : v₃ - c₀₃ + x₀₃ ≤ c₁₃ + c₂₃ := by
    have := le_trans hx₀₃u (min_le_right c₀₃ (c₀₃ - v₃ + c₁₃ + c₂₃))
    linarith
  have hrtotal :
      (v₁ - c₀₁ + x₀₁) + (v₂ - c₀₂ + x₀₂) + (v₃ - c₀₃ + x₀₃) =
        c₁₂ + c₁₃ + c₂₃ := by
    linarith
  obtain ⟨x₁₂, x₁₃, x₂₃, hx₁₂0, hx₁₂u, hx₁₃0, hx₁₃u,
      hx₂₃0, hx₂₃u, hrow₁, hrow₂, hrow₃⟩ :=
    triangle_edge_allocation c₁₂ c₁₃ c₂₃
      (v₁ - c₀₁ + x₀₁) (v₂ - c₀₂ + x₀₂) (v₃ - c₀₃ + x₀₃)
      hc₁₂ hc₁₃ hc₂₃ hr₁0 hr₂0 hr₃0 hrtotal hr₁u hr₂u hr₃u
  have hx₀₁0 : 0 ≤ x₀₁ :=
    le_trans (le_max_left 0 (c₀₁ - v₁)) hx₀₁l
  have hx₀₂0 : 0 ≤ x₀₂ :=
    le_trans (le_max_left 0 (c₀₂ - v₂)) hx₀₂l
  have hx₀₃0 : 0 ≤ x₀₃ :=
    le_trans (le_max_left 0 (c₀₃ - v₃)) hx₀₃l
  have hx₀₁c : x₀₁ ≤ c₀₁ :=
    le_trans hx₀₁u (min_le_left c₀₁ (c₀₁ - v₁ + c₁₂ + c₁₃))
  have hx₀₂c : x₀₂ ≤ c₀₂ :=
    le_trans hx₀₂u (min_le_left c₀₂ (c₀₂ - v₂ + c₁₂ + c₂₃))
  have hx₀₃c : x₀₃ ≤ c₀₃ :=
    le_trans hx₀₃u (min_le_left c₀₃ (c₀₃ - v₃ + c₁₃ + c₂₃))
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    ![![0, x₀₁, x₀₂, x₀₃],
      ![c₀₁ - x₀₁, 0, x₁₂, x₁₃],
      ![c₀₂ - x₀₂, c₁₂ - x₁₂, 0, x₂₃],
      ![c₀₃ - x₀₃, c₁₃ - x₁₃, c₂₃ - x₂₃, 0]]
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [A] <;> linarith
  · intro i
    fin_cases i <;> simp [A]
  · intro i
    fin_cases i <;> simp [A, Fin.sum_univ_four] <;> linarith
  · simp [A]

private theorem productProbability_mass
    (p : Fin 4 → Fin 4 → ℝ) (hrow : ∀ i, ∑ j, p i j = 1) :
    ∑ pick : Fin 4 → Fin 4, ∏ i, p i (pick i) = 1 := by
  classical
  calc
    (∑ pick : Fin 4 → Fin 4, ∏ i, p i (pick i)) =
        ∏ i, ∑ j, p i j := by
      rw [← Finset.sum_prod_piFinset (s := Finset.univ) p]
      simp [Fintype.piFinset_univ]
    _ = 1 := by simp [hrow]

private theorem productProbability_expect_coordinate
    (p : Fin 4 → Fin 4 → ℝ) (hrow : ∀ i, ∑ j, p i j = 1)
    (j : Fin 4) (r : Fin 4 → ℝ) :
    (∑ pick : Fin 4 → Fin 4, (∏ i, p i (pick i)) * r (pick j)) =
      ∑ a, p j a * r a := by
  classical
  let g : Fin 4 → Fin 4 → ℝ :=
    fun i a => if i = j then p i a * r a else p i a
  have hg (pick : Fin 4 → Fin 4) :
      (∏ i, g i (pick i)) = (∏ i, p i (pick i)) * r (pick j) := by
    fin_cases j <;> simp [g, Fin.prod_univ_four] <;> ring
  calc
    (∑ pick : Fin 4 → Fin 4, (∏ i, p i (pick i)) * r (pick j)) =
        ∑ pick : Fin 4 → Fin 4, ∏ i, g i (pick i) := by
      apply Finset.sum_congr rfl
      intro pick _
      rw [hg]
    _ = ∏ i, ∑ a, g i a := by
      rw [← Finset.sum_prod_piFinset (s := Finset.univ) g]
      simp [Fintype.piFinset_univ]
    _ = ∑ a, p j a * r a := by
      fin_cases j <;> simp [g, hrow]

private theorem productProbability_choiceFunctional
    (p : Fin 4 → Fin 4 → ℝ) (hrow : ∀ i, ∑ j, p i j = 1)
    (q : Fin 4 → ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    (∑ pick : Fin 4 → Fin 4,
      (∏ i, p i (pick i)) * choiceFunctional q B pick) =
      (∑ i, q i * B i i) +
        2 * ∑ j, ∑ i, p j i * (q i * B i j) := by
  classical
  let P : (Fin 4 → Fin 4) → ℝ := fun pick => ∏ i, p i (pick i)
  let D : ℝ := ∑ i, q i * B i i
  let R : (Fin 4 → Fin 4) → Fin 4 → ℝ :=
    fun pick j => q (pick j) * B (pick j) j
  have hmass : ∑ pick, P pick = 1 := productProbability_mass p hrow
  have hexp (j : Fin 4) :
      (∑ pick, P pick * R pick j) =
        ∑ i, p j i * (q i * B i j) := by
    exact productProbability_expect_coordinate p hrow j
      (fun i => q i * B i j)
  have hfirst : (∑ pick, P pick * D) = (∑ pick, P pick) * D :=
    (Finset.sum_mul ..).symm
  have hsecond :
      (∑ pick, P pick * (2 * ∑ j, R pick j)) =
        2 * ∑ j, ∑ pick, P pick * R pick j := by
    calc
      (∑ pick, P pick * (2 * ∑ j, R pick j)) =
          2 * ∑ pick, ∑ j, P pick * R pick j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pick _
        calc
          P pick * (2 * ∑ j, R pick j) =
              2 * (P pick * ∑ j, R pick j) := by ring
          _ = 2 * ∑ j, P pick * R pick j := by rw [Finset.mul_sum]
      _ = 2 * ∑ j, ∑ pick, P pick * R pick j := by
        rw [Finset.sum_comm]
  change (∑ pick, P pick * (D + 2 * ∑ j, R pick j)) =
    D + 2 * ∑ j, ∑ i, p j i * (q i * B i j)
  rw [show (∑ pick, P pick * (D + 2 * ∑ j, R pick j)) =
      (∑ pick, P pick * D) + ∑ pick, P pick * (2 * ∑ j, R pick j) by
        simp_rw [mul_add]
        exact Finset.sum_add_distrib]
  rw [hfirst, hsecond, hmass, one_mul]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact hexp j

private theorem choiceCone_of_probabilities
    (q : Fin 4 → ℝ) (W d₀₁ d₀₂ d₀₃ d₁₂ d₁₃ d₂₃ : ℝ)
    (p : Fin 4 → Fin 4 → ℝ)
    (hW : 0 ≤ W) (hp : ∀ i j, 0 ≤ p i j)
    (hpdiag : ∀ i, p i i = 0) (hrow : ∀ i, ∑ j, p i j = 1)
    (h₀₁ : W * (q 0 + q 1) -
      2 * W * (q 0 * p 1 0 + q 1 * p 0 1) = d₀₁)
    (h₀₂ : W * (q 0 + q 2) -
      2 * W * (q 0 * p 2 0 + q 2 * p 0 2) = d₀₂)
    (h₀₃ : W * (q 0 + q 3) -
      2 * W * (q 0 * p 3 0 + q 3 * p 0 3) = d₀₃)
    (h₁₂ : W * (q 1 + q 2) -
      2 * W * (q 1 * p 2 1 + q 2 * p 1 2) = d₁₂)
    (h₁₃ : W * (q 1 + q 3) -
      2 * W * (q 1 * p 3 1 + q 3 * p 1 3) = d₁₃)
    (h₂₃ : W * (q 2 + q 3) -
      2 * W * (q 2 * p 3 2 + q 3 * p 2 3) = d₂₃) :
    ∃ w : (Fin 4 → Fin 4) → ℝ,
      (∀ pick, 0 ≤ w pick) ∧
      (∀ pick, w pick ≠ 0 → ∀ j, pick j ≠ j) ∧
      ∀ (B : Matrix (Fin 4) (Fin 4) ℝ) (_hsymm : B.IsSymm)
        (_hzero : B.mulVec (fun _ => 1) = 0),
        (∑ pick, w pick * choiceFunctional q B pick) =
          -B 0 1 * d₀₁ - B 0 2 * d₀₂ - B 0 3 * d₀₃ -
          B 1 2 * d₁₂ - B 1 3 * d₁₃ - B 2 3 * d₂₃ := by
  classical
  let w : (Fin 4 → Fin 4) → ℝ := fun pick => W * ∏ i, p i (pick i)
  refine ⟨w, ?_, ?_, ?_⟩
  · intro pick
    apply mul_nonneg hW
    exact Finset.prod_nonneg fun i _ => hp i (pick i)
  · intro pick hwp j hj
    apply hwp
    have hprod : (∏ i, p i (pick i)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hj, hpdiag]
    simp [w, hprod]
  · intro B hsymm hzero
    have hb0 : B 0 0 + B 0 1 + B 0 2 + B 0 3 = 0 := by
      have h := congr_fun hzero 0
      simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        Pi.one_apply, mul_one, Pi.zero_apply] using h
    have hb1 : B 1 0 + B 1 1 + B 1 2 + B 1 3 = 0 := by
      have h := congr_fun hzero 1
      simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        Pi.one_apply, mul_one, Pi.zero_apply] using h
    have hb2 : B 2 0 + B 2 1 + B 2 2 + B 2 3 = 0 := by
      have h := congr_fun hzero 2
      simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        Pi.one_apply, mul_one, Pi.zero_apply] using h
    have hb3 : B 3 0 + B 3 1 + B 3 2 + B 3 3 = 0 := by
      have h := congr_fun hzero 3
      simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        Pi.one_apply, mul_one, Pi.zero_apply] using h
    have h10 : B 1 0 = B 0 1 := congr_fun (congr_fun hsymm 0) 1
    have h20 : B 2 0 = B 0 2 := congr_fun (congr_fun hsymm 0) 2
    have h30 : B 3 0 = B 0 3 := congr_fun (congr_fun hsymm 0) 3
    have h21 : B 2 1 = B 1 2 := congr_fun (congr_fun hsymm 1) 2
    have h31 : B 3 1 = B 1 3 := congr_fun (congr_fun hsymm 1) 3
    have h32 : B 3 2 = B 2 3 := congr_fun (congr_fun hsymm 2) 3
    simp_rw [w, mul_assoc]
    rw [← Finset.mul_sum]
    rw [productProbability_choiceFunctional p hrow q B]
    simp only [Fin.sum_univ_four]
    simp only [hpdiag, zero_mul, add_zero]
    simp_rw [h10, h20, h30, h21, h31, h32] at hb1 hb2 hb3 ⊢
    linear_combination
      W * q 0 * hb0 + W * q 1 * hb1 + W * q 2 * hb2 + W * q 3 * hb3 -
      B 0 1 * h₀₁ - B 0 2 * h₀₂ - B 0 3 * h₀₃ -
      B 1 2 * h₁₂ - B 1 3 * h₁₃ - B 2 3 * h₂₃

private theorem weighted_two_distance_le
    (v₁ v₂ y₁ y₂ : ℝ) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (henergy : v₁ * y₁ ^ 2 + v₂ * y₂ ^ 2 ≤ 1) :
    v₁ * v₂ * (y₁ - y₂) ^ 2 ≤ v₁ + v₂ := by
  have hscale := mul_le_mul_of_nonneg_left henergy (add_nonneg hv₁ hv₂)
  nlinarith [sq_nonneg (v₁ * y₁ + v₂ * y₂)]


private theorem canonical_capacity_nonneg
    (vi vj d : ℝ) (h : vi * vj * d ≤ vi + vj) :
    0 ≤ (vi + vj - vi * vj * d) / 2 := by
  exact div_nonneg (sub_nonneg.mpr h) (by norm_num)

private theorem canonical_capacity_le
    (vi vj d : ℝ)
    (hvi : 0 ≤ vi) (hvj : 0 ≤ vj) (hd : 0 ≤ d) :
    (vi + vj - vi * vj * d) / 2 ≤ vi + vj := by
  have hterm : 0 ≤ vi * vj * d :=
    mul_nonneg (mul_nonneg hvi hvj) hd
  linarith only [hvi, hvj, hterm]

private theorem weighted_three_cauchy
    (a b c x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a * x + b * y + c * z) ^ 2 ≤
      (a + b + c) * (a * x ^ 2 + b * y ^ 2 + c * z ^ 2) := by
  have hab : 0 ≤ a * b * (x - y) ^ 2 :=
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  have hac : 0 ≤ a * c * (x - z) ^ 2 :=
    mul_nonneg (mul_nonneg ha hc) (sq_nonneg _)
  have hbc : 0 ≤ b * c * (y - z) ^ 2 :=
    mul_nonneg (mul_nonneg hb hc) (sq_nonneg _)
  calc
    (a * x + b * y + c * z) ^ 2 ≤
        (a * x + b * y + c * z) ^ 2 +
          (a * b * (x - y) ^ 2 + a * c * (x - z) ^ 2 +
            b * c * (y - z) ^ 2) := by
      exact le_add_of_nonneg_right (add_nonneg (add_nonneg hab hac) hbc)
    _ = (a + b + c) * (a * x ^ 2 + b * y ^ 2 + c * z ^ 2) := by ring

private theorem normalized_vertex_bound
    (a b c d x y z t : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hm : a * x + b * y + c * z + d * t = 0)
    (he : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + d * t ^ 2 = 1) :
    a ≤ ((a + b) - a * b * (x - y) ^ 2) / 2 +
      ((a + c) - a * c * (x - z) ^ 2) / 2 +
      ((a + d) - a * d * (x - t) ^ 2) / 2 := by
  have hcs_le := weighted_three_cauchy b c d y z t hb hc hd
  have hcs :
      0 ≤ (b + c + d) * (b * y ^ 2 + c * z ^ 2 + d * t ^ 2) -
        (b * y + c * z + d * t) ^ 2 :=
    sub_nonneg.mpr hcs_le
  have hid :
      (((a + b) - a * b * (x - y) ^ 2) / 2 +
        ((a + c) - a * c * (x - z) ^ 2) / 2 +
        ((a + d) - a * d * (x - t) ^ 2) / 2) - a =
        ((b + c + d) * (b * y ^ 2 + c * z ^ 2 + d * t ^ 2) -
          (b * y + c * z + d * t) ^ 2) / 2 := by
    linear_combination
      -((a + b + c + d) / 2) * he +
      ((a * x + b * y + c * z + d * t) / 2) * hm
  have hdiff :
      0 ≤ (((a + b) - a * b * (x - y) ^ 2) / 2 +
        ((a + c) - a * c * (x - z) ^ 2) / 2 +
        ((a + d) - a * d * (x - t) ^ 2) / 2) - a := by
    rw [hid]
    exact div_nonneg hcs (by norm_num)
  linarith only [hdiff]

private theorem canonical_k4_capacity_total
    (v₀ v₁ v₂ v₃ : ℝ) (y : Fin 4 → ℝ)
    (hvariance :
      v₀ * v₁ * (y 0 - y 1) ^ 2 + v₀ * v₂ * (y 0 - y 2) ^ 2 +
        v₀ * v₃ * (y 0 - y 3) ^ 2 + v₁ * v₂ * (y 1 - y 2) ^ 2 +
        v₁ * v₃ * (y 1 - y 3) ^ 2 + v₂ * v₃ * (y 2 - y 3) ^ 2 =
          v₀ + v₁ + v₂ + v₃) :
    v₀ + v₁ + v₂ + v₃ =
      (v₀ + v₁ - v₀ * v₁ * (y 0 - y 1) ^ 2) / 2 +
      (v₀ + v₂ - v₀ * v₂ * (y 0 - y 2) ^ 2) / 2 +
      (v₀ + v₃ - v₀ * v₃ * (y 0 - y 3) ^ 2) / 2 +
      (v₁ + v₂ - v₁ * v₂ * (y 1 - y 2) ^ 2) / 2 +
      (v₁ + v₃ - v₁ * v₃ * (y 1 - y 3) ^ 2) / 2 +
      (v₂ + v₃ - v₂ * v₃ * (y 2 - y 3) ^ 2) / 2 := by
  linear_combination (1 / 2) * hvariance

private theorem probability_pair_of_edge
    (qi qj vi vj aij aji d : ℝ)
    (hqi : qi * vi = 1) (hqj : qj * vj = 1)
    (hedge : aij + aji = (vi + vj - vi * vj * d) / 2) :
    qi + qj - 2 * (qi * (qj * aji) + qj * (qi * aij)) = d := by
  have hprod : qi * qj * vi * vj = 1 := by
    calc
      qi * qj * vi * vj = (qi * vi) * (qj * vj) := by ring
      _ = 1 := by rw [hqi, hqj]; ring
  have hsum : qi * qj * (vi + vj) = qi + qj := by
    calc
      qi * qj * (vi + vj) = (qi * vi) * qj + (qj * vj) * qi := by ring
      _ = qi + qj := by rw [hqi, hqj]; ring
  have hscaled :
      2 * (qi * qj) * (aij + aji) = qi + qj - d := by
    calc
      2 * (qi * qj) * (aij + aji) =
          qi * qj * (vi + vj - vi * vj * d) := by rw [hedge]; ring
      _ = qi * qj * (vi + vj) - (qi * qj * vi * vj) * d := by ring
      _ = qi + qj - d := by rw [hsum, hprod]; ring
  calc
    qi + qj - 2 * (qi * (qj * aji) + qj * (qi * aij)) =
        qi + qj - 2 * (qi * qj) * (aij + aji) := by ring
    _ = d := by rw [hscaled]; ring

private theorem centered_four_mean_of_scale
    (v₀ v₁ v₂ v₃ z₀ z₁ z₂ z₃ m : ℝ)
    (hm :
      (v₀ + v₁ + v₂ + v₃) * m =
        v₀ * z₀ + v₁ * z₁ + v₂ * z₂ + v₃ * z₃) :
    v₀ * (z₀ - m) + v₁ * (z₁ - m) +
      v₂ * (z₂ - m) + v₃ * (z₃ - m) = 0 := by
  linear_combination -hm

private theorem four_weighted_sq_zero
    (v₀ v₁ v₂ v₃ x₀ x₁ x₂ x₃ : ℝ)
    (hv₀ : 0 < v₀) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hv₃ : 0 < v₃)
    (hzero :
      v₀ * x₀ ^ 2 + v₁ * x₁ ^ 2 + v₂ * x₂ ^ 2 + v₃ * x₃ ^ 2 = 0) :
    x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  have ht₀ : 0 ≤ v₀ * x₀ ^ 2 := mul_nonneg hv₀.le (sq_nonneg _)
  have ht₁ : 0 ≤ v₁ * x₁ ^ 2 := mul_nonneg hv₁.le (sq_nonneg _)
  have ht₂ : 0 ≤ v₂ * x₂ ^ 2 := mul_nonneg hv₂.le (sq_nonneg _)
  have ht₃ : 0 ≤ v₃ * x₃ ^ 2 := mul_nonneg hv₃.le (sq_nonneg _)
  have hz₀ : v₀ * x₀ ^ 2 = 0 := by
    linarith only [hzero, ht₀, ht₁, ht₂, ht₃]
  have hz₁ : v₁ * x₁ ^ 2 = 0 := by
    linarith only [hzero, ht₀, ht₁, ht₂, ht₃]
  have hz₂ : v₂ * x₂ ^ 2 = 0 := by
    linarith only [hzero, ht₀, ht₁, ht₂, ht₃]
  have hz₃ : v₃ * x₃ ^ 2 = 0 := by
    linarith only [hzero, ht₀, ht₁, ht₂, ht₃]
  have hx₀sq : x₀ ^ 2 = 0 := (mul_eq_zero.mp hz₀).resolve_left hv₀.ne'
  have hx₁sq : x₁ ^ 2 = 0 := (mul_eq_zero.mp hz₁).resolve_left hv₁.ne'
  have hx₂sq : x₂ ^ 2 = 0 := (mul_eq_zero.mp hz₂).resolve_left hv₂.ne'
  have hx₃sq : x₃ ^ 2 = 0 := (mul_eq_zero.mp hz₃).resolve_left hv₃.ne'
  exact ⟨sq_eq_zero_iff.mp hx₀sq, sq_eq_zero_iff.mp hx₁sq,
    sq_eq_zero_iff.mp hx₂sq, sq_eq_zero_iff.mp hx₃sq⟩

private theorem div_mean_four
    (a b c d x y z t r : ℝ) (_hr : r ≠ 0)
    (hmean : a * x + b * y + c * z + d * t = 0) :
    a * (x / r) + b * (y / r) + c * (z / r) + d * (t / r) = 0 := by
  calc
    a * (x / r) + b * (y / r) + c * (z / r) + d * (t / r) =
        (a * x + b * y + c * z + d * t) / r := by ring
    _ = 0 := by rw [hmean, zero_div]

private theorem div_sq_sum_four
    (a b c d x y z t r : ℝ) (hr : r ≠ 0) :
    a * (x / r) ^ 2 + b * (y / r) ^ 2 +
      c * (z / r) ^ 2 + d * (t / r) ^ 2 =
        (a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + d * t ^ 2) / r ^ 2 := by
  field_simp [hr]

private theorem sqrt_scaled_sub
    (V r m zi zj : ℝ) (hr2 : r ^ 2 = V) (hr : r ≠ 0) :
    V * (((zi - m) / r) - ((zj - m) / r)) ^ 2 = (zi - zj) ^ 2 := by
  rw [← hr2]
  field_simp [hr]
  ring


private theorem normalized_k4_edge_matrix
    (v y : Fin 4 → ℝ) (hv : ∀ i, 0 < v i)
    (hmean : ∑ i, v i * y i = 0)
    (henergy : ∑ i, v i * (y i) ^ 2 = 1) :
    ∃ A : Matrix (Fin 4) (Fin 4) ℝ,
      (∀ i j, 0 ≤ A i j) ∧
      (∀ i, A i i = 0) ∧
      (∀ i, ∑ j, A i j = v i) ∧
      A 0 1 + A 1 0 =
        (v 0 + v 1 - v 0 * v 1 * (y 0 - y 1) ^ 2) / 2 ∧
      A 0 2 + A 2 0 =
        (v 0 + v 2 - v 0 * v 2 * (y 0 - y 2) ^ 2) / 2 ∧
      A 0 3 + A 3 0 =
        (v 0 + v 3 - v 0 * v 3 * (y 0 - y 3) ^ 2) / 2 ∧
      A 1 2 + A 2 1 =
        (v 1 + v 2 - v 1 * v 2 * (y 1 - y 2) ^ 2) / 2 ∧
      A 1 3 + A 3 1 =
        (v 1 + v 3 - v 1 * v 3 * (y 1 - y 3) ^ 2) / 2 ∧
      A 2 3 + A 3 2 =
        (v 2 + v 3 - v 2 * v 3 * (y 2 - y 3) ^ 2) / 2 := by
  have hv0 := (hv 0).le
  have hv1 := (hv 1).le
  have hv2 := (hv 2).le
  have hv3 := (hv 3).le
  have hmean4 :
      v 0 * y 0 + v 1 * y 1 + v 2 * y 2 + v 3 * y 3 = 0 := by
    simpa only [Fin.sum_univ_four] using hmean
  have henergy4 :
      v 0 * (y 0) ^ 2 + v 1 * (y 1) ^ 2 +
        v 2 * (y 2) ^ 2 + v 3 * (y 3) ^ 2 = 1 := by
    simpa only [Fin.sum_univ_four] using henergy
  have ht0 : 0 ≤ v 0 * (y 0) ^ 2 := mul_nonneg hv0 (sq_nonneg _)
  have ht1 : 0 ≤ v 1 * (y 1) ^ 2 := mul_nonneg hv1 (sq_nonneg _)
  have ht2 : 0 ≤ v 2 * (y 2) ^ 2 := mul_nonneg hv2 (sq_nonneg _)
  have ht3 : 0 ≤ v 3 * (y 3) ^ 2 := mul_nonneg hv3 (sq_nonneg _)
  have he01 : v 0 * (y 0) ^ 2 + v 1 * (y 1) ^ 2 ≤ 1 := by
    linarith only [henergy4, ht2, ht3]
  have he02 : v 0 * (y 0) ^ 2 + v 2 * (y 2) ^ 2 ≤ 1 := by
    linarith only [henergy4, ht1, ht3]
  have he03 : v 0 * (y 0) ^ 2 + v 3 * (y 3) ^ 2 ≤ 1 := by
    linarith only [henergy4, ht1, ht2]
  have he12 : v 1 * (y 1) ^ 2 + v 2 * (y 2) ^ 2 ≤ 1 := by
    linarith only [henergy4, ht0, ht3]
  have he13 : v 1 * (y 1) ^ 2 + v 3 * (y 3) ^ 2 ≤ 1 := by
    linarith only [henergy4, ht0, ht2]
  have he23 : v 2 * (y 2) ^ 2 + v 3 * (y 3) ^ 2 ≤ 1 := by
    linarith only [henergy4, ht0, ht1]
  have hd01 := weighted_two_distance_le (v 0) (v 1) (y 0) (y 1) hv0 hv1 he01
  have hd02 := weighted_two_distance_le (v 0) (v 2) (y 0) (y 2) hv0 hv2 he02
  have hd03 := weighted_two_distance_le (v 0) (v 3) (y 0) (y 3) hv0 hv3 he03
  have hd12 := weighted_two_distance_le (v 1) (v 2) (y 1) (y 2) hv1 hv2 he12
  have hd13 := weighted_two_distance_le (v 1) (v 3) (y 1) (y 3) hv1 hv3 he13
  have hd23 := weighted_two_distance_le (v 2) (v 3) (y 2) (y 3) hv2 hv3 he23
  let c01 : ℝ := (v 0 + v 1 - v 0 * v 1 * (y 0 - y 1) ^ 2) / 2
  let c02 : ℝ := (v 0 + v 2 - v 0 * v 2 * (y 0 - y 2) ^ 2) / 2
  let c03 : ℝ := (v 0 + v 3 - v 0 * v 3 * (y 0 - y 3) ^ 2) / 2
  let c12 : ℝ := (v 1 + v 2 - v 1 * v 2 * (y 1 - y 2) ^ 2) / 2
  let c13 : ℝ := (v 1 + v 3 - v 1 * v 3 * (y 1 - y 3) ^ 2) / 2
  let c23 : ℝ := (v 2 + v 3 - v 2 * v 3 * (y 2 - y 3) ^ 2) / 2
  have hc01 : 0 ≤ c01 := by
    exact canonical_capacity_nonneg _ _ _ hd01
  have hc02 : 0 ≤ c02 := by
    exact canonical_capacity_nonneg _ _ _ hd02
  have hc03 : 0 ≤ c03 := by
    exact canonical_capacity_nonneg _ _ _ hd03
  have hc12 : 0 ≤ c12 := by
    exact canonical_capacity_nonneg _ _ _ hd12
  have hc13 : 0 ≤ c13 := by
    exact canonical_capacity_nonneg _ _ _ hd13
  have hc23 : 0 ≤ c23 := by
    exact canonical_capacity_nonneg _ _ _ hd23
  have hvariance :
      v 0 * v 1 * (y 0 - y 1) ^ 2 + v 0 * v 2 * (y 0 - y 2) ^ 2 +
        v 0 * v 3 * (y 0 - y 3) ^ 2 + v 1 * v 2 * (y 1 - y 2) ^ 2 +
        v 1 * v 3 * (y 1 - y 3) ^ 2 + v 2 * v 3 * (y 2 - y 3) ^ 2 =
          v 0 + v 1 + v 2 + v 3 := by
    calc
      _ = (v 0 + v 1 + v 2 + v 3) *
            (v 0 * (y 0) ^ 2 + v 1 * (y 1) ^ 2 +
              v 2 * (y 2) ^ 2 + v 3 * (y 3) ^ 2) -
            (v 0 * y 0 + v 1 * y 1 + v 2 * y 2 + v 3 * y 3) ^ 2 := by ring
      _ = v 0 + v 1 + v 2 + v 3 := by rw [henergy4, hmean4]; ring
  have htotal :
      v 0 + v 1 + v 2 + v 3 = c01 + c02 + c03 + c12 + c13 + c23 := by
    simpa [c01, c02, c03, c12, c13, c23] using
      (canonical_k4_capacity_total (v 0) (v 1) (v 2) (v 3) y hvariance)
  have hp01 : c01 ≤ v 0 + v 1 := by
    exact canonical_capacity_le _ _ _ hv0 hv1 (sq_nonneg _)
  have hp02 : c02 ≤ v 0 + v 2 := by
    exact canonical_capacity_le _ _ _ hv0 hv2 (sq_nonneg _)
  have hp03 : c03 ≤ v 0 + v 3 := by
    exact canonical_capacity_le _ _ _ hv0 hv3 (sq_nonneg _)
  have hp12 : c12 ≤ v 1 + v 2 := by
    exact canonical_capacity_le _ _ _ hv1 hv2 (sq_nonneg _)
  have hp13 : c13 ≤ v 1 + v 3 := by
    exact canonical_capacity_le _ _ _ hv1 hv3 (sq_nonneg _)
  have hp23 : c23 ≤ v 2 + v 3 := by
    exact canonical_capacity_le _ _ _ hv2 hv3 (sq_nonneg _)
  have hinc0 : v 0 ≤ c01 + c02 + c03 := by
    simpa [c01, c02, c03] using
      (normalized_vertex_bound (v 0) (v 1) (v 2) (v 3)
        (y 0) (y 1) (y 2) (y 3) hv1 hv2 hv3 hmean4 henergy4)
  have hm1 : v 1 * y 1 + v 0 * y 0 + v 2 * y 2 + v 3 * y 3 = 0 := by
    linarith only [hmean4]
  have he1 :
      v 1 * (y 1) ^ 2 + v 0 * (y 0) ^ 2 +
        v 2 * (y 2) ^ 2 + v 3 * (y 3) ^ 2 = 1 := by
    linarith only [henergy4]
  have hinc1raw := normalized_vertex_bound (v 1) (v 0) (v 2) (v 3)
    (y 1) (y 0) (y 2) (y 3) hv0 hv2 hv3 hm1 he1
  have hinc1 : v 1 ≤ c01 + c12 + c13 := by
    dsimp [c01, c12, c13]
    (convert hinc1raw using 1; ring)
  have hm2 : v 2 * y 2 + v 0 * y 0 + v 1 * y 1 + v 3 * y 3 = 0 := by
    linarith only [hmean4]
  have he2 :
      v 2 * (y 2) ^ 2 + v 0 * (y 0) ^ 2 +
        v 1 * (y 1) ^ 2 + v 3 * (y 3) ^ 2 = 1 := by
    linarith only [henergy4]
  have hinc2raw := normalized_vertex_bound (v 2) (v 0) (v 1) (v 3)
    (y 2) (y 0) (y 1) (y 3) hv0 hv1 hv3 hm2 he2
  have hinc2 : v 2 ≤ c02 + c12 + c23 := by
    dsimp [c02, c12, c23]
    (convert hinc2raw using 1; ring)
  have hm3 : v 3 * y 3 + v 0 * y 0 + v 1 * y 1 + v 2 * y 2 = 0 := by
    linarith only [hmean4]
  have he3 :
      v 3 * (y 3) ^ 2 + v 0 * (y 0) ^ 2 +
        v 1 * (y 1) ^ 2 + v 2 * (y 2) ^ 2 = 1 := by
    linarith only [henergy4]
  have hinc3raw := normalized_vertex_bound (v 3) (v 0) (v 1) (v 2)
    (y 3) (y 0) (y 1) (y 2) hv0 hv1 hv2 hm3 he3
  have hinc3 : v 3 ≤ c03 + c13 + c23 := by
    dsimp [c03, c13, c23]
    (convert hinc3raw using 1; ring)
  have ht012 : c01 + c02 + c12 ≤ v 0 + v 1 + v 2 := by
    linarith only [htotal, hinc3]
  have ht013 : c01 + c03 + c13 ≤ v 0 + v 1 + v 3 := by
    linarith only [htotal, hinc2]
  have ht023 : c02 + c03 + c23 ≤ v 0 + v 2 + v 3 := by
    linarith only [htotal, hinc1]
  have ht123 : c12 + c13 + c23 ≤ v 1 + v 2 + v 3 := by
    linarith only [htotal, hinc0]
  obtain ⟨A, hA0, hAdiag, hArow, hA01, hA02, hA03, hA12, hA13, hA23⟩ :=
    k4_edge_allocation c01 c02 c03 c12 c13 c23
      (v 0) (v 1) (v 2) (v 3)
      hc01 hc02 hc03 hc12 hc13 hc23 hv0 hv1 hv2 hv3 htotal
      hp01 hp02 hp03 hp12 hp13 hp23 ht012 ht013 ht023 ht123
  refine ⟨A, hA0, hAdiag, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi := hArow i
    fin_cases i <;> simpa using hi
  · simpa [c01] using hA01
  · simpa [c02] using hA02
  · simpa [c03] using hA03
  · simpa [c12] using hA12
  · simpa [c13] using hA13
  · simpa [c23] using hA23

private theorem probabilities_of_canonical_edge_matrix
    (q v y : Fin 4 → ℝ) (hq : ∀ i, 0 < q i)
    (hqv : ∀ i, q i * v i = 1)
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA0 : ∀ i j, 0 ≤ A i j)
    (hAdiag : ∀ i, A i i = 0)
    (hArow : ∀ i, ∑ j, A i j = v i)
    (hA01 : A 0 1 + A 1 0 =
      (v 0 + v 1 - v 0 * v 1 * (y 0 - y 1) ^ 2) / 2)
    (hA02 : A 0 2 + A 2 0 =
      (v 0 + v 2 - v 0 * v 2 * (y 0 - y 2) ^ 2) / 2)
    (hA03 : A 0 3 + A 3 0 =
      (v 0 + v 3 - v 0 * v 3 * (y 0 - y 3) ^ 2) / 2)
    (hA12 : A 1 2 + A 2 1 =
      (v 1 + v 2 - v 1 * v 2 * (y 1 - y 2) ^ 2) / 2)
    (hA13 : A 1 3 + A 3 1 =
      (v 1 + v 3 - v 1 * v 3 * (y 1 - y 3) ^ 2) / 2)
    (hA23 : A 2 3 + A 3 2 =
      (v 2 + v 3 - v 2 * v 3 * (y 2 - y 3) ^ 2) / 2) :
    ∃ p : Fin 4 → Fin 4 → ℝ,
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, p i i = 0) ∧
      (∀ i, ∑ j, p i j = 1) ∧
      (q 0 + q 1) - 2 * (q 0 * p 1 0 + q 1 * p 0 1) = (y 0 - y 1) ^ 2 ∧
      (q 0 + q 2) - 2 * (q 0 * p 2 0 + q 2 * p 0 2) = (y 0 - y 2) ^ 2 ∧
      (q 0 + q 3) - 2 * (q 0 * p 3 0 + q 3 * p 0 3) = (y 0 - y 3) ^ 2 ∧
      (q 1 + q 2) - 2 * (q 1 * p 2 1 + q 2 * p 1 2) = (y 1 - y 2) ^ 2 ∧
      (q 1 + q 3) - 2 * (q 1 * p 3 1 + q 3 * p 1 3) = (y 1 - y 3) ^ 2 ∧
      (q 2 + q 3) - 2 * (q 2 * p 3 2 + q 3 * p 2 3) = (y 2 - y 3) ^ 2 := by
  let p : Fin 4 → Fin 4 → ℝ := fun i j => q i * A i j
  refine ⟨p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact mul_nonneg (hq i).le (hA0 i j)
  · intro i
    simp only [p, hAdiag i, mul_zero]
  · intro i
    simp only [p]
    rw [← Finset.mul_sum, hArow i, hqv i]
  · simpa only [p] using
      probability_pair_of_edge
        (q 0) (q 1) (v 0) (v 1) (A 0 1) (A 1 0) ((y 0 - y 1) ^ 2)
        (hqv 0) (hqv 1) hA01
  · simpa only [p] using
      probability_pair_of_edge
        (q 0) (q 2) (v 0) (v 2) (A 0 2) (A 2 0) ((y 0 - y 2) ^ 2)
        (hqv 0) (hqv 2) hA02
  · simpa only [p] using
      probability_pair_of_edge
        (q 0) (q 3) (v 0) (v 3) (A 0 3) (A 3 0) ((y 0 - y 3) ^ 2)
        (hqv 0) (hqv 3) hA03
  · simpa only [p] using
      probability_pair_of_edge
        (q 1) (q 2) (v 1) (v 2) (A 1 2) (A 2 1) ((y 1 - y 2) ^ 2)
        (hqv 1) (hqv 2) hA12
  · simpa only [p] using
      probability_pair_of_edge
        (q 1) (q 3) (v 1) (v 3) (A 1 3) (A 3 1) ((y 1 - y 3) ^ 2)
        (hqv 1) (hqv 3) hA13
  · simpa only [p] using
      probability_pair_of_edge
        (q 2) (q 3) (v 2) (v 3) (A 2 3) (A 3 2) ((y 2 - y 3) ^ 2)
        (hqv 2) (hqv 3) hA23

private theorem normalized_k4_probabilities
    (q : Fin 4 → ℝ) (hq : ∀ i, 0 < q i) (y : Fin 4 → ℝ)
    (hmean : ∑ i, (1 / q i) * y i = 0)
    (henergy : ∑ i, (1 / q i) * (y i) ^ 2 = 1) :
    ∃ p : Fin 4 → Fin 4 → ℝ,
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, p i i = 0) ∧
      (∀ i, ∑ j, p i j = 1) ∧
      (q 0 + q 1) - 2 * (q 0 * p 1 0 + q 1 * p 0 1) = (y 0 - y 1) ^ 2 ∧
      (q 0 + q 2) - 2 * (q 0 * p 2 0 + q 2 * p 0 2) = (y 0 - y 2) ^ 2 ∧
      (q 0 + q 3) - 2 * (q 0 * p 3 0 + q 3 * p 0 3) = (y 0 - y 3) ^ 2 ∧
      (q 1 + q 2) - 2 * (q 1 * p 2 1 + q 2 * p 1 2) = (y 1 - y 2) ^ 2 ∧
      (q 1 + q 3) - 2 * (q 1 * p 3 1 + q 3 * p 1 3) = (y 1 - y 3) ^ 2 ∧
      (q 2 + q 3) - 2 * (q 2 * p 3 2 + q 3 * p 2 3) = (y 2 - y 3) ^ 2 := by
  let v : Fin 4 → ℝ := fun i => 1 / q i
  have hv : ∀ i, 0 < v i := by
    intro i
    exact one_div_pos.mpr (hq i)
  have hqv : ∀ i, q i * v i = 1 := by
    intro i
    dsimp [v]
    field_simp [ne_of_gt (hq i)]
  have hmeanv : ∑ i, v i * y i = 0 := by
    simpa [v] using hmean
  have henergyv : ∑ i, v i * (y i) ^ 2 = 1 := by
    simpa [v] using henergy
  obtain ⟨A, hA0, hAdiag, hArow, hA01, hA02, hA03, hA12, hA13, hA23⟩ :=
    normalized_k4_edge_matrix v y hv hmeanv henergyv
  exact probabilities_of_canonical_edge_matrix
    q v y hq hqv A hA0 hAdiag hArow hA01 hA02 hA03 hA12 hA13 hA23


private theorem four_point_center_or_normalize
    (q : Fin 4 → ℝ) (hq : ∀ i, 0 < q i) (z : Fin 4 → ℝ) :
    (∀ i j, z i = z j) ∨
      ∃ V : ℝ, ∃ y : Fin 4 → ℝ,
        0 < V ∧
        (∑ i, (1 / q i) * y i = 0) ∧
        (∑ i, (1 / q i) * (y i) ^ 2 = 1) ∧
        ∀ i j, V * (y i - y j) ^ 2 = (z i - z j) ^ 2 := by
  let v₀ : ℝ := 1 / q 0
  let v₁ : ℝ := 1 / q 1
  let v₂ : ℝ := 1 / q 2
  let v₃ : ℝ := 1 / q 3
  have hv₀ : 0 < v₀ := one_div_pos.mpr (hq 0)
  have hv₁ : 0 < v₁ := one_div_pos.mpr (hq 1)
  have hv₂ : 0 < v₂ := one_div_pos.mpr (hq 2)
  have hv₃ : 0 < v₃ := one_div_pos.mpr (hq 3)
  let S : ℝ := v₀ + v₁ + v₂ + v₃
  have hS : 0 < S := by
    dsimp [S]
    positivity
  have hSne : S ≠ 0 := ne_of_gt hS
  let m : ℝ :=
    (v₀ * z 0 + v₁ * z 1 + v₂ * z 2 + v₃ * z 3) / S
  have hm : S * m = v₀ * z 0 + v₁ * z 1 + v₂ * z 2 + v₃ * z 3 := by
    dsimp [m]
    field_simp [hSne]
  have hcenter :
      v₀ * (z 0 - m) + v₁ * (z 1 - m) +
        v₂ * (z 2 - m) + v₃ * (z 3 - m) = 0 := by
    apply centered_four_mean_of_scale
    simpa [S] using hm
  let V : ℝ :=
    v₀ * (z 0 - m) ^ 2 + v₁ * (z 1 - m) ^ 2 +
      v₂ * (z 2 - m) ^ 2 + v₃ * (z 3 - m) ^ 2
  have ht₀ : 0 ≤ v₀ * (z 0 - m) ^ 2 := mul_nonneg hv₀.le (sq_nonneg _)
  have ht₁ : 0 ≤ v₁ * (z 1 - m) ^ 2 := mul_nonneg hv₁.le (sq_nonneg _)
  have ht₂ : 0 ≤ v₂ * (z 2 - m) ^ 2 := mul_nonneg hv₂.le (sq_nonneg _)
  have ht₃ : 0 ≤ v₃ * (z 3 - m) ^ 2 := mul_nonneg hv₃.le (sq_nonneg _)
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  by_cases hVzero : V = 0
  · left
    have hsumzero :
        v₀ * (z 0 - m) ^ 2 + v₁ * (z 1 - m) ^ 2 +
          v₂ * (z 2 - m) ^ 2 + v₃ * (z 3 - m) ^ 2 = 0 := by
      simpa [V] using hVzero
    obtain ⟨hx₀, hx₁, hx₂, hx₃⟩ :=
      four_weighted_sq_zero v₀ v₁ v₂ v₃
        (z 0 - m) (z 1 - m) (z 2 - m) (z 3 - m)
        hv₀ hv₁ hv₂ hv₃ hsumzero
    have hz : ∀ i, z i = m := by
      intro i
      fin_cases i
      · simpa using (sub_eq_zero.mp hx₀)
      · simpa using (sub_eq_zero.mp hx₁)
      · simpa using (sub_eq_zero.mp hx₂)
      · simpa using (sub_eq_zero.mp hx₃)
    intro i j
    exact (hz i).trans (hz j).symm
  · right
    have hVpos : 0 < V := lt_of_le_of_ne hVnonneg (Ne.symm hVzero)
    let r : ℝ := Real.sqrt V
    have hrpos : 0 < r := Real.sqrt_pos.2 hVpos
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hr2 : r ^ 2 = V := by
      dsimp [r]
      exact Real.sq_sqrt hVnonneg
    let y : Fin 4 → ℝ := fun i => (z i - m) / r
    have hymean4 :
        v₀ * y 0 + v₁ * y 1 + v₂ * y 2 + v₃ * y 3 = 0 := by
      dsimp [y]
      exact div_mean_four v₀ v₁ v₂ v₃
        (z 0 - m) (z 1 - m) (z 2 - m) (z 3 - m) r hrne hcenter
    have hymean : ∑ i, (1 / q i) * y i = 0 := by
      simp only [Fin.sum_univ_four]
      simpa [v₀, v₁, v₂, v₃] using hymean4
    have hyenergy4 :
        v₀ * y 0 ^ 2 + v₁ * y 1 ^ 2 +
          v₂ * y 2 ^ 2 + v₃ * y 3 ^ 2 = 1 := by
      calc
        _ = (v₀ * (z 0 - m) ^ 2 + v₁ * (z 1 - m) ^ 2 +
              v₂ * (z 2 - m) ^ 2 + v₃ * (z 3 - m) ^ 2) / r ^ 2 := by
          dsimp [y]
          exact div_sq_sum_four v₀ v₁ v₂ v₃
            (z 0 - m) (z 1 - m) (z 2 - m) (z 3 - m) r hrne
        _ = V / r ^ 2 := by rfl
        _ = 1 := by rw [hr2, div_self hVzero]
    have hyenergy : ∑ i, (1 / q i) * (y i) ^ 2 = 1 := by
      simp only [Fin.sum_univ_four]
      simpa [v₀, v₁, v₂, v₃] using hyenergy4
    have hscale : ∀ i j, V * (y i - y j) ^ 2 = (z i - z j) ^ 2 := by
      intro i j
      dsimp [y]
      exact sqrt_scaled_sub V r m (z i) (z j) hr2 hrne
    exact ⟨V, y, hVpos, hymean, hyenergy, hscale⟩

/-- The K4 allocation / choice-cone representation lemma: for any positive vertex weights `q`
and point `z`, the squared-distance edge sum is represented by a nonnegative linear combination
of choice functionals over valid column-pick maps. -/
private theorem k4_choiceCone_allocation
    (q : Fin 4 → ℝ) (hq : ∀ i, 0 < q i) (z : Fin 4 → ℝ) :
    ∃ w : (Fin 4 → Fin 4) → ℝ,
      (∀ pick, 0 ≤ w pick) ∧
      (∀ pick, w pick ≠ 0 → ∀ j, pick j ≠ j) ∧
      ∀ (B : Matrix (Fin 4) (Fin 4) ℝ) (_hsymm : B.IsSymm) (_hzero : B.mulVec (fun _ => 1) = 0),
        (∑ pick, w pick * choiceFunctional q B pick) =
          - B 0 1 * (z 0 - z 1) ^ 2 -
          B 0 2 * (z 0 - z 2) ^ 2 -
          B 0 3 * (z 0 - z 3) ^ 2 -
          B 1 2 * (z 1 - z 2) ^ 2 -
          B 1 3 * (z 1 - z 3) ^ 2 -
          B 2 3 * (z 2 - z 3) ^ 2 := by
  rcases four_point_center_or_normalize q hq z with hconst |
      ⟨V, y, hV, hmean, henergy, hscale⟩
  · refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro pick
      exact le_rfl
    · intro pick hpick
      simp at hpick
    · intro B hsymm hzero
      have hdist : ∀ i j, (z i - z j) ^ 2 = 0 := by
        intro i j
        rw [hconst i j, sub_self]
        norm_num
      simp [hdist]
  · obtain ⟨p, hp, hpdiag, hrow, h01, h02, h03, h12, h13, h23⟩ :=
      normalized_k4_probabilities q hq y hmean henergy
    have hscaled (i j : Fin 4)
        (hij : (q i + q j) -
          2 * (q i * p j i + q j * p i j) = (y i - y j) ^ 2) :
        V * (q i + q j) -
          2 * V * (q i * p j i + q j * p i j) = (z i - z j) ^ 2 := by
      calc
        V * (q i + q j) - 2 * V * (q i * p j i + q j * p i j) =
            V * ((q i + q j) - 2 * (q i * p j i + q j * p i j)) := by ring
        _ = V * (y i - y j) ^ 2 := by rw [hij]
        _ = (z i - z j) ^ 2 := hscale i j
    exact choiceCone_of_probabilities q V
      ((z 0 - z 1) ^ 2) ((z 0 - z 2) ^ 2) ((z 0 - z 3) ^ 2)
      ((z 1 - z 2) ^ 2) ((z 1 - z 3) ^ 2) ((z 2 - z 3) ^ 2)
      p hV.le hp hpdiag hrow
      (hscaled 0 1 h01) (hscaled 0 2 h02) (hscaled 0 3 h03)
      (hscaled 1 2 h12) (hscaled 1 3 h13) (hscaled 2 3 h23)

/-- The four-vertex squared-distance cone used in paper Lemma 5. For a
symmetric zero-row-sum matrix, nonpositivity of all 81 column-choice
functionals forces negative semidefiniteness. -/
private theorem zeroRow_choiceCone_nonpositive
    (q : Fin 4 → ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hq : ∀ i, 0 < q i) (hsymm : B.IsSymm)
    (hzero : B.mulVec (fun _ => 1) = 0)
    (hchoice : ∀ pick : Fin 4 → Fin 4, (∀ j, pick j ≠ j) →
      (∑ i, q i * B i i) +
        2 * ∑ j, q (pick j) * B (pick j) j ≤ 0) :
    ∀ z, quadraticForm4 B z ≤ 0 := by
  intro z
  rw [quadraticForm4_zeroRow_eq_edge_sum B hsymm hzero z]
  obtain ⟨w, hw_nonneg, hw_valid, hw_eq⟩ := k4_choiceCone_allocation q hq z
  rw [← hw_eq B hsymm hzero]
  refine Finset.sum_nonpos (fun pick _ => ?_)
  by_cases hw0 : w pick = 0
  · rw [hw0, zero_mul]
  · have hvalid := hw_valid pick hw0
    have hch := hchoice pick hvalid
    change choiceFunctional q B pick ≤ 0 at hch
    exact mul_nonpos_of_nonneg_of_nonpos (hw_nonneg pick) hch

private lemma quadraticForm4_sub_rankOne (C : Matrix (Fin 4) (Fin 4) ℝ) (g z : Fin 4 → ℝ) (sigma
    : ℝ) :
    quadraticForm4 (fun i j => C i j - g i * g j / sigma) z =
      quadraticForm4 C z - (dotProduct g z) ^ 2 / sigma := by
  dsimp [quadraticForm4, Matrix.mulVec, dotProduct]
  simp_rw [sum_fin4]
  ring

/-- Correct rank-one reduction for paper Lemma 5. Positive row sums permit
subtracting `g gᵀ / sum g` to reach the preceding zero-row-sum cone; adding
one positive rank-one form back cannot create positive index two. -/
private theorem columnFunctional_nonpos_forbids_positiveIndexTwo
    (M : Matrix (Fin 4) (Fin 4) ℝ) (d : Fin 4 → ℝ)
    (hd : ∀ i, 0 < d i)
    (hsymm : ((Matrix.diagonal d) * M).IsSymm)
    (hrow : ∀ i, 0 < (M.mulVec (fun _ => 1)) i)
    (h_le : Matrix.trace M +
      2 * ∑ j, M (columnMaxPicker M j) j ≤ 0) :
    ¬ PositiveIndexAtLeastTwo4 ((Matrix.diagonal d) * M) := by
  intro hpos2
  set C := Matrix.diagonal d * M with hC_def
  set g := C.mulVec (fun _ => 1) with hg_def
  set sigma := ∑ i, g i with hsigma_def
  have hg_pos (i : Fin 4) : 0 < g i := by
    have hgi : g i = d i * (M.mulVec (fun _ => 1) i) := by
      change (C.mulVec (fun _ => 1)) i = d i * (M.mulVec (fun _ => 1) i)
      dsimp [C, Matrix.mulVec, dotProduct]
      simp_rw [sum_fin4]
      simp only [diag_mul_apply]
      ring
    rw [hgi]
    exact mul_pos (hd i) (hrow i)
  have hsigma_pos : 0 < sigma := by
    change 0 < ∑ i, g i
    simp_rw [sum_fin4]
    have h0 := hg_pos 0; have h1 := hg_pos 1; have h2 := hg_pos 2; have h3 := hg_pos 3
    linarith
  set B : Matrix (Fin 4) (Fin 4) ℝ := fun i j => C i j - g i * g j / sigma with hB_def
  set q : Fin 4 → ℝ := fun i => 1 / d i with hq_def
  have hq_pos (i : Fin 4) : 0 < q i := div_pos (by norm_num) (hd i)
  have hB_symm : B.IsSymm := by
    ext i j
    change B j i = B i j
    dsimp [B]
    have hC_ij : C j i = C i j := congr_fun (congr_fun hsymm i) j
    rw [hC_ij]
    ring
  have hB_zero : B.mulVec (fun _ => 1) = 0 := by
    ext i
    dsimp [Matrix.mulVec, dotProduct, B]
    simp_rw [sum_fin4]
    have hg_i : C i 0 + C i 1 + C i 2 + C i 3 = g i := by
      have h : (C.mulVec (fun _ => 1)) i = g i := rfl
      unfold Matrix.mulVec dotProduct at h
      rw [sum_fin4] at h
      linarith
    have hsigma : g 0 + g 1 + g 2 + g 3 = sigma := by
      have h : (∑ k, g k) = sigma := rfl
      simp_rw [sum_fin4] at h
      exact h
    have hsig_ne : sigma ≠ 0 := hsigma_pos.ne'
    have h_sum : (C i 0 - g i * g 0 / sigma) * 1 + (C i 1 - g i * g 1 / sigma) * 1 +
        (C i 2 - g i * g 2 / sigma) * 1 + (C i 3 - g i * g 3 / sigma) * 1 =
        (C i 0 + C i 1 + C i 2 + C i 3) - g i / sigma * (g 0 + g 1 + g 2 + g 3) := by ring
    rw [h_sum, hg_i, hsigma]
    field_simp; ring
  have hchoice (pick : Fin 4 → Fin 4) (hpick : ∀ j, pick j ≠ j) :
      (∑ i, q i * B i i) + 2 * ∑ j, q (pick j) * B (pick j) j ≤ 0 := by
    have hqC_diag (i : Fin 4) : q i * C i i = M i i := by
      change (1 / d i) * ((Matrix.diagonal d * M) i i) = M i i
      rw [diag_mul_apply]
      have hdi := (hd i).ne'
      field_simp
    have hqC_pick (j : Fin 4) : q (pick j) * C (pick j) j = M (pick j) j := by
      change (1 / d (pick j)) * ((Matrix.diagonal d * M) (pick j) j) = M (pick j) j
      rw [diag_mul_apply]
      have hd_pj := (hd (pick j)).ne'
      field_simp
    have hB_expand : (∑ i, q i * B i i) + 2 * ∑ j, q (pick j) * B (pick j) j =
        (Matrix.trace M + 2 * ∑ j, M (pick j) j) -
        (1 / sigma) * ((∑ i, q i * g i ^ 2) + 2 * ∑ j, q (pick j) * g (pick j) * g j) := by
      unfold Matrix.trace Matrix.diag
      simp_rw [sum_fin4]
      dsimp [B]
      have h0 := hqC_diag 0; have h1 := hqC_diag 1; have h2 := hqC_diag 2; have h3 := hqC_diag 3
      have hp0 := hqC_pick 0; have hp1 := hqC_pick 1; have hp2 := hqC_pick 2; have hp3 := hqC_pick 3
      linear_combination h0 + h1 + h2 + h3 + 2 * hp0 + 2 * hp1 + 2 * hp2 + 2 * hp3
    have hpick_sum_le : ∑ j, M (pick j) j ≤ ∑ j, M (columnMaxPicker M j) j := by
      simp_rw [sum_fin4]
      have h0 := columnMaxPicker_le M 0 (pick 0) (hpick 0)
      have h1 := columnMaxPicker_le M 1 (pick 1) (hpick 1)
      have h2 := columnMaxPicker_le M 2 (pick 2) (hpick 2)
      have h3 := columnMaxPicker_le M 3 (pick 3) (hpick 3)
      linarith
    have hpick_le : Matrix.trace M + 2 * ∑ j, M (pick j) j ≤ 0 := by
      linarith [h_le, hpick_sum_le]
    have hpos_term : 0 < (1 / sigma) * ((∑ i, q i * g i ^ 2) + 2 * ∑ j, q (pick j) * g (pick j)
        * g j) := by
      have hsigma_inv : 0 < 1 / sigma := one_div_pos.mpr hsigma_pos
      have hsum_pos : 0 < (∑ i, q i * g i ^ 2) + 2 * ∑ j, q (pick j) * g (pick j) * g j := by
        simp_rw [sum_fin4]
        have hq0 := hq_pos 0; have hq1 := hq_pos 1; have hq2 := hq_pos 2; have hq3 := hq_pos 3
        have hqp0 := hq_pos (pick 0); have hqp1 := hq_pos (pick 1)
        have hqp2 := hq_pos (pick 2); have hqp3 := hq_pos (pick 3)
        have hg0 := hg_pos 0; have hg1 := hg_pos 1; have hg2 := hg_pos 2; have hg3 := hg_pos 3
        have hgp0 := hg_pos (pick 0); have hgp1 := hg_pos (pick 1)
        have hgp2 := hg_pos (pick 2); have hgp3 := hg_pos (pick 3)
        have h_sq0 : 0 < q 0 * g 0 ^ 2 := mul_pos hq0 (sq_pos_of_ne_zero (hg0.ne'))
        have h_sq1 : 0 < q 1 * g 1 ^ 2 := mul_pos hq1 (sq_pos_of_ne_zero (hg1.ne'))
        have h_sq2 : 0 < q 2 * g 2 ^ 2 := mul_pos hq2 (sq_pos_of_ne_zero (hg2.ne'))
        have h_sq3 : 0 < q 3 * g 3 ^ 2 := mul_pos hq3 (sq_pos_of_ne_zero (hg3.ne'))
        have hp0 : 0 < q (pick 0) * g (pick 0) * g 0 := mul_pos (mul_pos hqp0 hgp0) hg0
        have hp1 : 0 < q (pick 1) * g (pick 1) * g 1 := mul_pos (mul_pos hqp1 hgp1) hg1
        have hp2 : 0 < q (pick 2) * g (pick 2) * g 2 := mul_pos (mul_pos hqp2 hgp2) hg2
        have hp3 : 0 < q (pick 3) * g (pick 3) * g 3 := mul_pos (mul_pos hqp3 hgp3) hg3
        linarith
      exact mul_pos hsigma_inv hsum_pos
    rw [hB_expand]
    linarith
  have hB_nonpos := zeroRow_choiceCone_nonpositive q B hq_pos hB_symm hB_zero hchoice
  obtain ⟨u, v, huv⟩ := hpos2
  set gu := dotProduct g u with hgu_def
  set gv := dotProduct g v with hgv_def
  by_cases hg_zero : gu = 0 ∧ gv = 0
  · set z := u
    have hnz : (1 : ℝ) ≠ 0 ∨ (0 : ℝ) ≠ 0 := Or.inl one_ne_zero
    have hCz : 0 < quadraticForm4 C z := by
      have h := huv 1 0 hnz
      have h_eq : (fun i => (1 : ℝ) * u i + (0 : ℝ) * v i) = z := by ext i; ring
      rwa [h_eq] at h
    have hBz : quadraticForm4 B z = quadraticForm4 C z := by
      change quadraticForm4 (fun i j => C i j - g i * g j / sigma) z = quadraticForm4 C z
      rw [quadraticForm4_sub_rankOne]
      have hgu_zero : dotProduct g z = 0 := hg_zero.1
      rw [hgu_zero]
      ring
    have hB_le := hB_nonpos z
    linarith
  · have hg_not : ¬(gu = 0 ∧ gv = 0) := hg_zero
    set a := -gv
    set b := gu
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hab_zero
      push Not at hab_zero
      have ha : a = 0 := hab_zero.1
      have hb : b = 0 := hab_zero.2
      have hgv_zero : gv = 0 := by linarith [ha]
      have hgu_zero : gu = 0 := hb
      exact hg_not ⟨hgu_zero, hgv_zero⟩
    set z : Fin 4 → ℝ := fun i => a * u i + b * v i
    have hCz : 0 < quadraticForm4 C z := huv a b hab
    have hgz : dotProduct g z = 0 := by
      dsimp [dotProduct, z, a, b, gu, gv]
      simp_rw [sum_fin4]
      ring
    have hBz : quadraticForm4 B z = quadraticForm4 C z := by
      change quadraticForm4 (fun i j => C i j - g i * g j / sigma) z = quadraticForm4 C z
      rw [quadraticForm4_sub_rankOne, hgz]
      ring
    have hB_le := hB_nonpos z
    linarith

private lemma quad_expand (M : Matrix (Fin 4) (Fin 4) ℝ) (d : Fin 4 → ℝ)
    (z : Fin 4 → ℝ)
    (hsymm : ((Matrix.diagonal d) * M).IsSymm) :
    dotProduct z (((Matrix.diagonal d) * M).mulVec z) =
      d 0 * (M 0 0 + M 0 1 + M 0 2 + M 0 3) * z 0 ^ 2 +
      d 1 * (M 1 0 + M 1 1 + M 1 2 + M 1 3) * z 1 ^ 2 +
      d 2 * (M 2 0 + M 2 1 + M 2 2 + M 2 3) * z 2 ^ 2 +
      d 3 * (M 3 0 + M 3 1 + M 3 2 + M 3 3) * z 3 ^ 2 -
      d 0 * M 0 1 * (z 0 - z 1) ^ 2 -
      d 0 * M 0 2 * (z 0 - z 2) ^ 2 -
      d 0 * M 0 3 * (z 0 - z 3) ^ 2 -
      d 1 * M 1 2 * (z 1 - z 2) ^ 2 -
      d 1 * M 1 3 * (z 1 - z 3) ^ 2 -
      d 2 * M 2 3 * (z 2 - z 3) ^ 2 := by
  have hsymm_apply (i j : Fin 4) : d j * M j i = d i * M i j := by
    have h := congr_fun (congr_fun hsymm j) i
    dsimp [Matrix.transpose] at h
    rw [diag_mul_apply, diag_mul_apply] at h
    exact h.symm
  have h10 := hsymm_apply 0 1
  have h20 := hsymm_apply 0 2
  have h30 := hsymm_apply 0 3
  have h21 := hsymm_apply 1 2
  have h31 := hsymm_apply 1 3
  have h32 := hsymm_apply 2 3
  have h1 : dotProduct z (((Matrix.diagonal d) * M).mulVec z) =
      ∑ i, z i * (((Matrix.diagonal d) * M).mulVec z i) := rfl
  have h2 (i : Fin 4) : ((Matrix.diagonal d) * M).mulVec z i =
      ∑ j, ((Matrix.diagonal d) * M) i j * z j := rfl
  rw [h1, sum_fin4]
  rw [h2 0, h2 1, h2 2, h2 3]
  rw [sum_fin4, sum_fin4, sum_fin4, sum_fin4]
  simp only [diag_mul_apply]
  linear_combination h10 * (z 0 * z 1 - z 1 ^ 2) + h20 * (z 0 * z 2 - z 2 ^ 2) +
    h30 * (z 0 * z 3 - z 3 ^ 2) + h21 * (z 1 * z 2 - z 2 ^ 2) +
    h31 * (z 1 * z 3 - z 3 ^ 2) + h32 * (z 2 * z 3 - z 3 ^ 2)

/-- Paper Lemma 5, in a max-free but equivalent form: one can choose an
off-diagonal maximizer in each column so that the trace-plus-column-max
expression is positive. -/
theorem columnMax_spectral_inequality
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hspectral : DiagonallySymmetrizableWithPositiveIndexTwo4 M)
    (hrow : ∀ i, 0 < (M.mulVec (fun _ => 1)) i) :
    ∃ pick : Fin 4 → Fin 4,
      (∀ j, pick j ≠ j) ∧
      0 < Matrix.trace M + 2 * ∑ j, M (pick j) j := by
  refine ⟨columnMaxPicker M, columnMaxPicker_ne M, ?_⟩
  by_contra h_le
  push Not at h_le
  obtain ⟨d, hd, hsymm, hpos2⟩ := hspectral
  exact (columnFunctional_nonpos_forbids_positiveIndexTwo
    M d hd hsymm hrow h_le) hpos2

end HeadComplexity
