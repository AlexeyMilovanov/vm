import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Calculus.Deriv.Basic
import HeadComplexity.Separations.SignRank

set_option linter.style.header false

/-!
# Forster's sign-rank lower bound

`specNorm M` is the spectral (`ℓ² → ℓ²` operator) norm of a square real matrix,
and Forster's theorem bounds the sign-rank of a `±1` matrix from below by
`N / specNorm`.  The Kronecker multiplicativity of the spectral norm is what
makes the bound tensor (Theorem B of `audit/sources/EXPLICIT_GAP.md`).
-/

namespace HeadComplexity

open Matrix
open scoped Kronecker
open scoped Matrix.Norms.L2Operator
open Metric

/-- Spectral norm of a square real matrix: the operator norm of the induced map
on Euclidean space. -/
noncomputable def specNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

private theorem norm_sq_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    ‖(WithLp.equiv 2 _).symm v‖^2 = ∑ i, v i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

/-- **±1 spectral lower bound** (PROOFS.md P5.1, the `signRank ≥ N` regime of
Forster): every column of a `±1` matrix has Euclidean norm `√N`
(`‖M *ᵥ eⱼ‖² = ∑ᵢ (M i j)² = N`), so `specNorm M ≥ √N`, i.e.
`card ι ≤ (specNorm M) ^ 2`.  Start from `specNorm M = ‖toEuclideanCLM M‖ ≥
‖toEuclideanCLM M (EuclideanSpace.single j 1)‖`; for an empty index type the
claim is simply `0 ≤ (specNorm M)²`. -/
theorem card_le_specNorm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1) :
    (Fintype.card ι : ℝ) ≤ (specNorm M) ^ 2 := by
  by_cases hι : IsEmpty ι
  · have h_card : Fintype.card ι = 0 := Fintype.card_eq_zero
    rw [h_card, Nat.cast_zero]
    exact sq_nonneg _
  · rw [not_isEmpty_iff] at hι
    have j : ι := Classical.choice hι
    set e_j : ι → ℝ := Pi.single j 1
    have he_j_norm : ‖(WithLp.equiv 2 _).symm e_j‖ = 1 := by
      have hsq : ‖(WithLp.equiv 2 _).symm e_j‖^2 = 1 := by
        rw [norm_sq_eq]
        have h_sum : ∑ i, e_j i ^ 2 = 1 := by
          rw [Finset.sum_eq_single j]
          · simp [e_j]
          · intro b _ hb
            simp [e_j, Pi.single_eq_of_ne hb]
          · intro hb
            exact False.elim (hb (Finset.mem_univ j))
        exact h_sum
      have hpos : 0 ≤ ‖(WithLp.equiv 2 _).symm e_j‖ := norm_nonneg _
      nlinarith
    have h_mulVec : M *ᵥ e_j = fun i => M i j := by
      ext i
      simp [Matrix.mulVec, dotProduct, e_j, Pi.single_apply]
    have h_action_norm : ‖(WithLp.equiv 2 (ι → ℝ)).symm (M *ᵥ e_j)‖^2 =
        (Fintype.card ι : ℝ) := by
      rw [h_mulVec, norm_sq_eq]
      have h_sum : ∑ i, (M i j) ^ 2 = (Fintype.card ι : ℝ) := by
        have h_entry : ∀ i, (M i j) ^ 2 = 1 := by
          intro i
          rcases hM i j with h1 | h2
          · rw [h1]; ring
          · rw [h2]; ring
        simp_rw [h_entry]
        simp
      exact h_sum
    have h_op : ‖(WithLp.equiv 2 _).symm (M *ᵥ e_j)‖ ≤
        specNorm M * ‖(WithLp.equiv 2 _).symm e_j‖ := by
      have : (WithLp.equiv 2 _).symm (M *ᵥ e_j) =
          Matrix.toEuclideanCLM (𝕜 := ℝ) M ((WithLp.equiv 2 _).symm e_j) := rfl
      rw [this]
      exact ContinuousLinearMap.le_opNorm _ _
    rw [he_j_norm, mul_one] at h_op
    have h_op_sq : ‖(WithLp.equiv 2 _).symm (M *ᵥ e_j)‖^2 ≤ (specNorm M)^2 := by
      nlinarith [h_op, norm_nonneg ((WithLp.equiv 2 (ι → ℝ)).symm (M *ᵥ e_j)),
        norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) M)]
    rwa [h_action_norm] at h_op_sq

/-- **Forster's theorem** (Forster 2002): a `±1` matrix of size `N × N` has
sign-rank at least `N / ‖M‖₂` (small rank regime). -/
theorem forster_small_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (h_r : Fintype.card ι ≤ signRank M) :
    (Fintype.card ι : ℝ) ≤ (signRank M : ℝ) * specNorm M := by
  by_cases hcard : Fintype.card ι = 0
  · rw [hcard, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (by unfold specNorm; exact norm_nonneg _)
  · have hcard_one : (1 : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hcard)
    have hspec_sq := card_le_specNorm_sq M hM
    have hspec_nonneg : 0 ≤ specNorm M := norm_nonneg _
    have hspec_one : 1 ≤ specNorm M := by nlinarith
    have hr_cast : (Fintype.card ι : ℝ) ≤ (signRank M : ℝ) := by
      exact_mod_cast h_r
    calc
      (Fintype.card ι : ℝ) ≤ (signRank M : ℝ) := hr_cast
      _ ≤ (signRank M : ℝ) * specNorm M := by
        nlinarith [show 0 ≤ (signRank M : ℝ) by positivity]

-- `forster_large_rank` (the large-rank regime) and the top-level `forster` are
-- assembled at the end of the `ForsterDecomposition` section below, since they
-- depend on its sub-lemmas (`one_le_signRank`, `exists_unit_sign_factorization`,
-- `exists_isotropic_reposition`, `forster_main_chain`).

private theorem norm_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (v : ι → ℝ) : ‖(WithLp.equiv 2 _).symm (A *ᵥ v)‖ ≤ ‖A‖ * ‖(WithLp.equiv 2 _).symm v‖ := by
  have : (WithLp.equiv 2 _).symm (A *ᵥ v) = Matrix.toEuclideanCLM (𝕜 := ℝ) A ((WithLp.equiv 2 _).symm v) := rfl
  rw [this]
  exact ContinuousLinearMap.le_opNorm _ _

private theorem kronecker_one_mulVec_norm_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (u : ι × κ → ℝ) :
    ‖(WithLp.equiv 2 _).symm ((A ⊗ₖ (1 : Matrix κ κ ℝ)) *ᵥ u)‖^2 ≤
      (‖A‖ * ‖(WithLp.equiv 2 _).symm u‖)^2 := by
  have h_eq : ‖(WithLp.equiv 2 _).symm ((A ⊗ₖ (1 : Matrix κ κ ℝ)) *ᵥ u)‖^2 =
      ∑ c, ‖(WithLp.equiv 2 _).symm (A *ᵥ (fun j => u (j, c)))‖^2 := by
    simp_rw [norm_sq_eq, Fintype.sum_prod_type_right]
    congr 1
    ext c
    congr 1
    ext i
    have : ((A ⊗ₖ (1 : Matrix κ κ ℝ)) *ᵥ u) (i, c) = (A *ᵥ (fun j => u (j, c))) i := by
      simp_rw [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply]
      rw [Fintype.sum_prod_type]
      simp
    rw [this]
  rw [h_eq]
  have h_le : ∑ c, ‖(WithLp.equiv 2 _).symm (A *ᵥ (fun j => u (j, c)))‖^2 ≤
      ∑ c, (‖A‖ * ‖(WithLp.equiv 2 _).symm (fun j => u (j, c))‖)^2 := by
    apply Finset.sum_le_sum
    intro c _
    apply sq_le_sq.mpr
    rw [abs_norm, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact norm_mulVec_le A _
  apply le_trans h_le
  apply le_of_eq
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [norm_sq_eq, Fintype.sum_prod_type_right]

private theorem kronecker_one_norm_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) :
    ‖A ⊗ₖ (1 : Matrix κ κ ℝ)‖ ≤ ‖A‖ := by
  have H : ‖A ⊗ₖ (1 : Matrix κ κ ℝ)‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι × κ) (A ⊗ₖ 1)‖ := rfl
  rw [H]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro v
  have h_vec : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι × κ) (A ⊗ₖ 1) v =
      (WithLp.equiv 2 _).symm ((A ⊗ₖ (1 : Matrix κ κ ℝ)) *ᵥ (WithLp.equiv 2 _ v)) := rfl
  rw [h_vec]
  have h_bound := kronecker_one_mulVec_norm_le A (WithLp.equiv 2 _ v)
  have h_v : (WithLp.equiv 2 _).symm (WithLp.equiv 2 _ v) = v := by
    exact Equiv.symm_apply_apply _ _
  rw [h_v] at h_bound
  have h_abs := sq_le_sq.mp h_bound
  rw [abs_norm, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at h_abs
  exact h_abs

private theorem one_kronecker_mulVec_norm_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix κ κ ℝ) (u : ι × κ → ℝ) :
    ‖(WithLp.equiv 2 _).symm (((1 : Matrix ι ι ℝ) ⊗ₖ B) *ᵥ u)‖^2 ≤
      (‖B‖ * ‖(WithLp.equiv 2 _).symm u‖)^2 := by
  have h_eq : ‖(WithLp.equiv 2 _).symm (((1 : Matrix ι ι ℝ) ⊗ₖ B) *ᵥ u)‖^2 =
      ∑ c, ‖(WithLp.equiv 2 _).symm (B *ᵥ (fun j => u (c, j)))‖^2 := by
    simp_rw [norm_sq_eq, Fintype.sum_prod_type]
    congr 1
    ext c
    congr 1
    ext i
    have : (((1 : Matrix ι ι ℝ) ⊗ₖ B) *ᵥ u) (c, i) = (B *ᵥ (fun j => u (c, j))) i := by
      simp_rw [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply]
      rw [Fintype.sum_prod_type]
      simp [mul_comm]
    rw [this]
  rw [h_eq]
  have h_le : ∑ c, ‖(WithLp.equiv 2 _).symm (B *ᵥ (fun j => u (c, j)))‖^2 ≤
      ∑ c, (‖B‖ * ‖(WithLp.equiv 2 _).symm (fun j => u (c, j))‖)^2 := by
    apply Finset.sum_le_sum
    intro c _
    apply sq_le_sq.mpr
    rw [abs_norm, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact norm_mulVec_le B _
  apply le_trans h_le
  apply le_of_eq
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [norm_sq_eq, Fintype.sum_prod_type]

private theorem one_kronecker_norm_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix κ κ ℝ) :
    ‖(1 : Matrix ι ι ℝ) ⊗ₖ B‖ ≤ ‖B‖ := by
  have H : ‖(1 : Matrix ι ι ℝ) ⊗ₖ B‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι × κ) (1 ⊗ₖ B)‖ := rfl
  rw [H]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro v
  have h_vec : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι × κ) (1 ⊗ₖ B) v =
      (WithLp.equiv 2 _).symm (((1 : Matrix ι ι ℝ) ⊗ₖ B) *ᵥ (WithLp.equiv 2 _ v)) := rfl
  rw [h_vec]
  have h_bound := one_kronecker_mulVec_norm_le B (WithLp.equiv 2 _ v)
  have h_v : (WithLp.equiv 2 _).symm (WithLp.equiv 2 _ v) = v := by
    exact Equiv.symm_apply_apply _ _
  rw [h_v] at h_bound
  have h_abs := sq_le_sq.mp h_bound
  rw [abs_norm, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at h_abs
  exact h_abs

private theorem kronecker_vec_mulVec {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (u : ι → ℝ) (v : κ → ℝ) :
    ((A ⊗ₖ B) *ᵥ (fun (i, c) => u i * v c)) = fun (i, c) => (A *ᵥ u) i * (B *ᵥ v) c := by
  ext ⟨i, c⟩
  change ∑ j : ι × κ, (A i j.1 * B c j.2) * (u j.1 * v j.2) = (∑ x, A i x * u x) * (∑ y, B c y * v y)
  rw [Fintype.sum_prod_type]
  have : ∑ x : ι, ∑ x_1 : κ, (A i x * B c x_1) * (u x * v x_1) = ∑ x : ι, (A i x * u x) * ∑ x_1 : κ, B c x_1 * v x_1 := by
    apply Finset.sum_congr rfl
    intro x _
    have h1 : ∑ x_1 : κ, (A i x * B c x_1) * (u x * v x_1) = ∑ x_1 : κ, (A i x * u x) * (B c x_1 * v x_1) := by
      congr 1
      ext x_1
      ring
    rw [h1, ← Finset.mul_sum]
  rw [this, ← Finset.sum_mul]

private theorem attains_opNorm_aux {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ) :
    ∃ u : EuclideanSpace ℝ ι, ‖u‖ = 1 ∧ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A u‖ = ‖A‖ := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  have h_comp : IsCompact (sphere (0 : EuclideanSpace ℝ ι) 1) := isCompact_sphere _ _
  have h_nonemp : (sphere (0 : EuclideanSpace ℝ ι) 1).Nonempty := by
    simp
  have h_cont : Continuous fun x : EuclideanSpace ℝ ι => ‖T x‖ := by
    exact Continuous.norm T.continuous
  obtain ⟨u, hu_sphere, hu_max⟩ := h_comp.exists_isMaxOn h_nonemp h_cont.continuousOn
  use u
  have hu_norm : ‖u‖ = 1 := by simpa using hu_sphere
  refine ⟨hu_norm, ?_⟩
  have H_le : ‖T u‖ ≤ ‖A‖ := by
    have : ‖A‖ = ‖T‖ := rfl
    rw [this]
    have := T.le_opNorm u
    rw [hu_norm, mul_one] at this
    exact this
  have H_ge : ‖A‖ ≤ ‖T u‖ := by
    have : ‖A‖ = ‖T‖ := rfl
    rw [this]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    by_cases hx : x = 0
    · rw [hx]
      simp
    · have h_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have h_unit : (‖x‖⁻¹ • x) ∈ sphere (0 : EuclideanSpace ℝ ι) 1 := by
        simp [norm_smul, h_norm_pos.ne']
      have h_max := hu_max h_unit
      dsimp [IsMaxOn] at h_max
      have h_T : ‖T (‖x‖⁻¹ • x)‖ = ‖x‖⁻¹ * ‖T x‖ := by
        rw [T.map_smul, norm_smul, norm_inv, norm_norm]
      rw [h_T] at h_max
      rw [← div_eq_inv_mul] at h_max
      exact (div_le_iff₀ h_norm_pos).mp h_max
  exact le_antisymm H_le H_ge

private theorem norm_eq_zero_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (A : Matrix ι ι ℝ) :
    ‖A‖ = 0 := by
  have : ‖A‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := rfl
  rw [this]
  have h_sub : Subsingleton (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) := inferInstance
  have h_eq : Matrix.toEuclideanCLM (𝕜 := ℝ) A = 0 := Subsingleton.elim _ _
  rw [h_eq]
  exact norm_zero

private theorem le_specNorm_kronecker_aux {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Nonempty ι] [Nonempty κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    ‖A‖ * ‖B‖ ≤ ‖A ⊗ₖ B‖ := by
  obtain ⟨u, hu, hAu⟩ := attains_opNorm_aux A
  obtain ⟨v, hv, hBv⟩ := attains_opNorm_aux B
  let w : ι × κ → ℝ := fun ⟨i, c⟩ => (WithLp.equiv 2 (ι → ℝ) u) i * (WithLp.equiv 2 (κ → ℝ) v) c
  have hw_norm : ‖(WithLp.equiv 2 (ι × κ → ℝ)).symm w‖ = 1 := by
    have h_sq : ‖(WithLp.equiv 2 (ι × κ → ℝ)).symm w‖^2 = 1 := by
      rw [norm_sq_eq, Fintype.sum_prod_type]
      have : ∑ x, ∑ x_1, w (x, x_1) ^ 2 = ∑ x, (WithLp.equiv 2 (ι → ℝ) u) x ^ 2 * ∑ x_1, (WithLp.equiv 2 (κ → ℝ) v) x_1 ^ 2 := by
        apply Finset.sum_congr rfl
        intro x _
        have h1 : ∑ x_1, w (x, x_1) ^ 2 = ∑ x_1, ((WithLp.equiv 2 (κ → ℝ) v) x_1 ^ 2) * ((WithLp.equiv 2 (ι → ℝ) u) x ^ 2) := by
          apply Finset.sum_congr rfl
          intro y _
          dsimp [w]
          ring
        rw [h1, ← Finset.sum_mul, mul_comm]
      rw [this]
      have hu_sq : ∑ x, (WithLp.equiv 2 (ι → ℝ) u) x ^ 2 = 1 := by
        have := norm_sq_eq (WithLp.equiv 2 (ι → ℝ) u)
        rw [Equiv.symm_apply_apply] at this
        rw [← this, hu, one_pow]
      have hv_sq : ∑ x, (WithLp.equiv 2 (κ → ℝ) v) x ^ 2 = 1 := by
        have := norm_sq_eq (WithLp.equiv 2 (κ → ℝ) v)
        rw [Equiv.symm_apply_apply] at this
        rw [← this, hv, one_pow]
      rw [← Finset.sum_mul]
      simp_rw [hv_sq, mul_one, hu_sq]
    have h_pos : 0 ≤ ‖(WithLp.equiv 2 (ι × κ → ℝ)).symm w‖ := norm_nonneg _
    nlinarith
  have hw_action : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι × κ) (A ⊗ₖ B) ((WithLp.equiv 2 (ι × κ → ℝ)).symm w)‖ = ‖A‖ * ‖B‖ := by
    have h_vec : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι × κ) (A ⊗ₖ B) ((WithLp.equiv 2 (ι × κ → ℝ)).symm w) =
        (WithLp.equiv 2 (ι × κ → ℝ)).symm ((A ⊗ₖ B) *ᵥ w) := rfl
    rw [h_vec]
    have h_mul := kronecker_vec_mulVec A B (WithLp.equiv 2 (ι → ℝ) u) (WithLp.equiv 2 (κ → ℝ) v)
    rw [h_mul]
    have h_sq : ‖(WithLp.equiv 2 (ι × κ → ℝ)).symm (fun x : ι × κ => (A *ᵥ (WithLp.equiv 2 (ι → ℝ) u)) x.1 * (B *ᵥ (WithLp.equiv 2 (κ → ℝ) v)) x.2)‖^2 =
        (‖A‖ * ‖B‖)^2 := by
      rw [norm_sq_eq, Fintype.sum_prod_type]
      have : ∑ x, ∑ x_1, ((A *ᵥ (WithLp.equiv 2 (ι → ℝ) u)) x * (B *ᵥ (WithLp.equiv 2 (κ → ℝ) v)) x_1) ^ 2 =
          ∑ x, (A *ᵥ (WithLp.equiv 2 (ι → ℝ) u)) x ^ 2 * ∑ x_1, (B *ᵥ (WithLp.equiv 2 (κ → ℝ) v)) x_1 ^ 2 := by
        apply Finset.sum_congr rfl
        intro x _
        have h1 : ∑ x_1, ((A *ᵥ (WithLp.equiv 2 (ι → ℝ) u)) x * (B *ᵥ (WithLp.equiv 2 (κ → ℝ) v)) x_1) ^ 2 =
            ∑ x_1, ((B *ᵥ (WithLp.equiv 2 (κ → ℝ) v)) x_1 ^ 2) * ((A *ᵥ (WithLp.equiv 2 (ι → ℝ) u)) x ^ 2) := by
          apply Finset.sum_congr rfl
          intro y _
          ring
        rw [h1, ← Finset.sum_mul, mul_comm]
      rw [this]
      have hAu_sq : ∑ x, (A *ᵥ (WithLp.equiv 2 (ι → ℝ) u)) x ^ 2 = ‖A‖^2 := by
        have := norm_sq_eq (A *ᵥ (WithLp.equiv 2 (ι → ℝ) u))
        have hA_vec : Matrix.toEuclideanCLM (𝕜 := ℝ) A u = (WithLp.equiv 2 (ι → ℝ)).symm (A *ᵥ (WithLp.equiv 2 (ι → ℝ) u)) := by
          have h : u = (WithLp.equiv 2 (ι → ℝ)).symm (WithLp.equiv 2 (ι → ℝ) u) := (Equiv.symm_apply_apply _ _).symm
          nth_rw 1 [h]
          rfl
        rw [← hA_vec, hAu] at this
        exact this.symm
      have hBv_sq : ∑ x, (B *ᵥ (WithLp.equiv 2 (κ → ℝ) v)) x ^ 2 = ‖B‖^2 := by
        have := norm_sq_eq (B *ᵥ (WithLp.equiv 2 (κ → ℝ) v))
        have hB_vec : Matrix.toEuclideanCLM (𝕜 := ℝ) B v = (WithLp.equiv 2 (κ → ℝ)).symm (B *ᵥ (WithLp.equiv 2 (κ → ℝ) v)) := by
          have h : v = (WithLp.equiv 2 (κ → ℝ)).symm (WithLp.equiv 2 (κ → ℝ) v) := (Equiv.symm_apply_apply _ _).symm
          nth_rw 1 [h]
          rfl
        rw [← hB_vec, hBv] at this
        exact this.symm
      rw [← Finset.sum_mul]
      rw [hAu_sq, hBv_sq, mul_pow]
    have h_pos : 0 ≤ ‖(WithLp.equiv 2 (ι × κ → ℝ)).symm (fun x : ι × κ => (A *ᵥ (WithLp.equiv 2 (ι → ℝ) u)) x.1 * (B *ᵥ (WithLp.equiv 2 (κ → ℝ) v)) x.2)‖ := norm_nonneg _
    have h_pos_AB : 0 ≤ ‖A‖ * ‖B‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith
  have h_op := ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι × κ) (A ⊗ₖ B)) ((WithLp.equiv 2 (ι × κ → ℝ)).symm w)
  rw [hw_norm, mul_one, hw_action] at h_op
  have : ‖A ⊗ₖ B‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι × κ) (A ⊗ₖ B)‖ := rfl
  rw [this]
  exact h_op

/-- **Kronecker lower bound** (PROOFS.md P6.2, witness half): the norm-attaining
unit vectors `u, v` for `A, B` give the product witness `w(i,c) = u i · v c`
with `(A ⊗ₖ B) w = (A u) ⊗ (B v)`, so `‖(A ⊗ₖ B) w‖ = ‖A u‖ · ‖B v‖`. -/
theorem le_specNorm_kronecker {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    specNorm A * specNorm B ≤ specNorm (A ⊗ₖ B) := by
  have hA : specNorm A = ‖A‖ := rfl
  have hB : specNorm B = ‖B‖ := rfl
  have hAB : specNorm (A ⊗ₖ B) = ‖A ⊗ₖ B‖ := rfl
  rw [hA, hB, hAB]
  by_cases hι : Nonempty ι
  · by_cases hκ : Nonempty κ
    · exact le_specNorm_kronecker_aux A B
    · rw [not_nonempty_iff] at hκ
      have : ‖B‖ = 0 := norm_eq_zero_of_isEmpty B
      rw [this, mul_zero]
      exact norm_nonneg _
  · rw [not_nonempty_iff] at hι
    have : ‖A‖ = 0 := norm_eq_zero_of_isEmpty A
    rw [this, zero_mul]
    exact norm_nonneg _

/-- **Kronecker upper bound** (PROOFS.md P6.2, submultiplicative half):
`A ⊗ₖ B = (A ⊗ₖ I)(I ⊗ₖ B)`, and each factor has operator norm at most that of
`A` (resp. `B`); operator-norm submultiplicativity finishes. -/
theorem specNorm_kronecker_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    specNorm (A ⊗ₖ B) ≤ specNorm A * specNorm B := by
  have H : A ⊗ₖ B = (A ⊗ₖ 1) * (1 ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hA : specNorm A = ‖A‖ := rfl
  have hB : specNorm B = ‖B‖ := rfl
  have hAB : specNorm (A ⊗ₖ B) = ‖A ⊗ₖ B‖ := rfl
  rw [hA, hB, hAB, H]
  have h_op_mul : ‖(A ⊗ₖ (1 : Matrix κ κ ℝ)) * (1 ⊗ₖ B)‖ ≤ ‖A ⊗ₖ (1 : Matrix κ κ ℝ)‖ * ‖(1 : Matrix ι ι ℝ) ⊗ₖ B‖ :=
    norm_mul_le _ _
  apply le_trans h_op_mul
  apply mul_le_mul (kronecker_one_norm_le A) (one_kronecker_norm_le B) (norm_nonneg _) (norm_nonneg _)

/-- The spectral norm is multiplicative under Kronecker products.  Together
with `Fintype.card (ι × κ) = card ι * card κ` this makes the Forster ratio
`N / ‖M‖₂` multiplicative, which is the engine of the tensored separation.
Assembled from the two one-sided bounds `specNorm_kronecker_le` and
`le_specNorm_kronecker`. -/
theorem specNorm_kronecker {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    specNorm (A ⊗ₖ B) = specNorm A * specNorm B :=
  le_antisymm (specNorm_kronecker_le A B) (le_specNorm_kronecker A B)

/-- The spectral norm is invariant under simultaneous reindexing (PROOFS.md
P6.1): `reindex e e M` is `toEuclideanCLM M` conjugated by the coordinate
permutation isometry `π := piLpCongrLeft`, and operator norms are invariant
under pre/post-composition with linear isometry equivalences. -/
theorem specNorm_reindex {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (M : Matrix ι ι ℝ) :
    specNorm (Matrix.reindex e e M) = specNorm M := by
  unfold specNorm
  set π : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι' :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e with hπ
  have key : Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.reindex e e M)
      = (π : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι').comp
          ((Matrix.toEuclideanCLM (𝕜 := ℝ) M).comp
            (π.symm : EuclideanSpace ℝ ι' →L[ℝ] EuclideanSpace ℝ ι)) := by
    apply ContinuousLinearMap.ext
    intro v
    apply WithLp.ofLp_injective (p := 2) (V := ι' → ℝ)
    funext i'
    rw [Matrix.reindex_apply]
    simp only [ContinuousLinearMap.comp_apply,
      LinearIsometryEquiv.coe_coe'', hπ, LinearIsometryEquiv.piLpCongrLeft_symm,
      LinearIsometryEquiv.piLpCongrLeft_apply, Matrix.ofLp_toEuclideanCLM,
      Matrix.submatrix_mulVec_equiv, Function.comp_apply, Equiv.symm_symm]
    have hv : (Equiv.piCongrLeft' (fun _ : ι' => ℝ) e.symm) (WithLp.ofLp v)
        = (WithLp.ofLp v) ∘ ⇑e := by
      funext k
      simp only [Equiv.piCongrLeft', Equiv.symm_symm, Function.comp_apply,
        Equiv.coe_fn_mk]
    rw [hv]
    rfl
  rw [key, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- `k`-fold Kronecker power of a square matrix, indexed by `Fin k → ι`
(PROOFS.md P8.2): the entry at `(x, y)` is `∏ⱼ M (x j) (y j)`.  This is the
Kronecker object whose reindex is the tensored sign matrix `S_k`. -/
def kroneckerPow (k : ℕ) {ι : Type*} (M : Matrix ι ι ℝ) :
    Matrix (Fin k → ι) (Fin k → ι) ℝ :=
  fun x y => ∏ j, M (x j) (y j)

private def kroneckerPow_e0 (ι : Type*) : (Fin 0 → ι) ≃ Unit where
  toFun _ := ()
  invFun _ := fun i => i.elim0
  left_inv f := by ext i; exact i.elim0
  right_inv _ := rfl

private def kroneckerPow_e_succ (k : ℕ) (ι : Type*) : (Fin (k + 1) → ι) ≃ ι × (Fin k → ι) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    ext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      simp
  right_inv p := by
    ext <;> simp

/-- **Spectral norm of the Kronecker power** (PROOFS.md P8.3):
`specNorm (kroneckerPow k M) = (specNorm M) ^ k`.  Induction on `k`: the base
case is the `1 × 1` matrix with entry `1` (empty product), and the step writes
`kroneckerPow (k+1) M = reindex e e (M ⊗ₖ kroneckerPow k M)` for the equivalence
`e : (Fin (k+1) → ι) ≃ ι × (Fin k → ι)` (`Fin.prod_univ_succ` gives the entrywise
identity), so `specNorm_reindex` and `specNorm_kronecker` reduce it to
`specNorm M * (specNorm M) ^ k`.  This is the multiplicative engine turning the
Forster ratio into `γ_m ^ k` for Theorem B. -/
theorem specNorm_kroneckerPow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (M : Matrix ι ι ℝ) :
    specNorm (kroneckerPow k M) = (specNorm M) ^ k := by
  induction k with
  | zero =>
    have h_eq : kroneckerPow 0 M =
        reindex (kroneckerPow_e0 ι).symm (kroneckerPow_e0 ι).symm (1 : Matrix Unit Unit ℝ) := by
      ext x y
      simp [kroneckerPow, reindex_apply, kroneckerPow_e0]
    rw [h_eq, specNorm_reindex]
    unfold specNorm
    rw [map_one, norm_one, pow_zero]
  | succ k ih =>
    have h_eq : kroneckerPow (k + 1) M =
        reindex (kroneckerPow_e_succ k ι).symm (kroneckerPow_e_succ k ι).symm
          (M ⊗ₖ kroneckerPow k M) := by
      ext x y
      simp [kroneckerPow, reindex_apply, kroneckerPow_e_succ, Fin.prod_univ_succ]
    rw [h_eq, specNorm_reindex, specNorm_kronecker, ih, pow_succ, mul_comm]

/-- The Kronecker power of a `±1` matrix is `±1` (PROOFS.md P8.3): each entry
`∏ⱼ M (x j) (y j)` is a finite product of `±1` values, hence `±1` itself.  This is
what lets Forster's theorem apply to `kroneckerPow k S₁` (the tensored sign
matrix), whose card is `2^{k·m}`. -/
theorem kroneckerPow_mem_pm_one {ι : Type*} (k : ℕ) (M : Matrix ι ι ℝ)
    (hM : ∀ i j, M i j = 1 ∨ M i j = -1) (x y : Fin k → ι) :
    kroneckerPow k M x y = 1 ∨ kroneckerPow k M x y = -1 := by
  have prod_mem_pm_one : ∀ (s : Finset (Fin k)),
      (∏ j ∈ s, M (x j) (y j)) = 1 ∨ (∏ j ∈ s, M (x j) (y j)) = -1 := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty]; exact Or.inl rfl
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases hM (x a) (y a) with h1 | h1 <;> rcases ih with h2 | h2 <;> rw [h1, h2]
      · left; ring
      · right; ring
      · right; ring
      · left; ring
  simpa [kroneckerPow] using prod_mem_pm_one Finset.univ


/-! ### Manual decomposition of `forster_large_rank` (PROOFS.md P5),
2026-08-24.  Assembly: `one_le_signRank` gives `1 ≤ r`; factorize
(`exists_unit_sign_factorization`), repositon (`exists_isotropic_reposition`,
using `r < N`), and finish with `forster_main_chain`. -/

section ForsterDecomposition

open scoped InnerProductSpace

private theorem matrix_rank_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) :
    A.rank = 0 ↔ A = 0 := by
  constructor
  · intro h
    unfold Matrix.rank at h
    rw [Submodule.finrank_eq_zero] at h
    rw [LinearMap.range_eq_bot] at h
    ext i j
    have h1 : A.mulVecLin (Pi.single j 1) = 0 := by rw [h]; rfl
    have h2 := congr_fun h1 i
    rw [Matrix.mulVecLin_apply] at h2
    dsimp [Matrix.mulVec, dotProduct] at h2
    rw [Finset.sum_eq_single j] at h2
    · simpa using h2
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  · rintro rfl
    exact Matrix.rank_zero

/-- P5.1: a nonempty `±1` matrix has sign-rank at least one (any sign-match
of a matrix with a nonzero entry is nonzero, so its rank is positive). -/
theorem one_le_signRank {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1) :
    1 ≤ signRank M := by
  have h_nonempty : {r | ∃ A : Matrix ι ι ℝ, SignMatches M A ∧ A.rank = r}.Nonempty := by
    use M.rank, M
    refine ⟨?_, rfl⟩
    intro i j
    rcases hM i j with h1 | h2
    · rw [h1]; norm_num
    · rw [h2]; norm_num
  have h_mem := Nat.sInf_mem h_nonempty
  rcases h_mem with ⟨A, hA, hA_rank⟩
  unfold signRank
  rw [← hA_rank]
  by_contra hc
  have hA_zero : A.rank = 0 := Nat.lt_one_iff.mp (not_le.mp hc)
  rw [matrix_rank_eq_zero_iff] at hA_zero
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  have h_match := hA i0 i0
  rw [hA_zero] at h_match
  dsimp at h_match
  rw [mul_zero] at h_match
  exact lt_irrefl 0 h_match

/-- P5.1: a rank-`signRank` factorization normalizes to unit vectors with
strict entrywise sign agreement. -/
theorem exists_unit_sign_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (hr : 1 ≤ signRank M) :
    ∃ u v : ι → EuclideanSpace ℝ (Fin (signRank M)),
      (∀ x, ‖u x‖ = 1) ∧ (∀ y, ‖v y‖ = 1) ∧
      ∀ x y, 0 < M x y * ⟪u x, v y⟫_ℝ := by
  classical
  have h_nonempty :
      {q | ∃ A : Matrix ι ι ℝ, SignMatches M A ∧ A.rank = q}.Nonempty := by
    refine ⟨M.rank, M, ?_, rfl⟩
    intro i j
    rcases hM i j with h | h <;> rw [h] <;> norm_num
  have h_min : signRank M ∈
      {q | ∃ A : Matrix ι ι ℝ, SignMatches M A ∧ A.rank = q} := by
    unfold signRank
    exact Nat.sInf_mem h_nonempty
  obtain ⟨A, hA, hArank⟩ := h_min
  have hcard : 1 ≤ Fintype.card ι := by
    calc
      1 ≤ signRank M := hr
      _ = A.rank := hArank.symm
      _ ≤ Fintype.card ι := A.rank_le_card_width
  let b₀ := Module.finBasis ℝ (LinearMap.range A.mulVecLin)
  have hbcard : Module.finrank ℝ (LinearMap.range A.mulVecLin) = signRank M := by
    simpa [Matrix.rank] using hArank
  let b : Module.Basis (Fin (signRank M)) ℝ (LinearMap.range A.mulVecLin) :=
    b₀.reindex (finCongr hbcard)
  let c : ι → LinearMap.range A.mulVecLin := fun y =>
    ⟨A *ᵥ Pi.single y 1, ⟨Pi.single y 1, by rw [Matrix.mulVecLin_apply]⟩⟩
  let u₀ : ι → EuclideanSpace ℝ (Fin (signRank M)) := fun x =>
    (WithLp.equiv 2 _).symm
      (fun i => ((b i : LinearMap.range A.mulVecLin) : ι → ℝ) x)
  let v₀ : ι → EuclideanSpace ℝ (Fin (signRank M)) := fun y =>
    (WithLp.equiv 2 _).symm (fun i => b.repr (c y) i)
  have huv : ∀ x y, ⟪u₀ x, v₀ y⟫_ℝ = A x y := by
    intro x y
    have hsum := congrArg Subtype.val (b.sum_repr (c y))
    have hsumxy := congrFun hsum x
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
    change ∑ i, ((b i : LinearMap.range A.mulVecLin) : ι → ℝ) x *
      b.repr (c y) i = A x y
    calc
      ∑ i, ((b i : LinearMap.range A.mulVecLin) : ι → ℝ) x * b.repr (c y) i =
          ∑ i, b.repr (c y) i *
            ((b i : LinearMap.range A.mulVecLin) : ι → ℝ) x := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = ((c y : LinearMap.range A.mulVecLin) : ι → ℝ) x := by
        simpa only [Finset.sum_apply, Submodule.coe_sum,
          Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul] using hsumxy
      _ = A x y := by simp [c, Matrix.mulVec_single]
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hu₀ : ∀ x, u₀ x ≠ 0 := by
    intro x hx
    obtain ⟨y⟩ := (inferInstance : Nonempty ι)
    have hpos := hA x y
    rw [← huv x y, hx] at hpos
    simp at hpos
  have hv₀ : ∀ y, v₀ y ≠ 0 := by
    intro y hy
    obtain ⟨x⟩ := (inferInstance : Nonempty ι)
    have hpos := hA x y
    rw [← huv x y, hy] at hpos
    simp at hpos
  let u : ι → EuclideanSpace ℝ (Fin (signRank M)) :=
    fun x => ‖u₀ x‖⁻¹ • u₀ x
  let v : ι → EuclideanSpace ℝ (Fin (signRank M)) :=
    fun y => ‖v₀ y‖⁻¹ • v₀ y
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro x
    change ‖‖u₀ x‖⁻¹ • u₀ x‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (hu₀ x)
  · intro y
    change ‖‖v₀ y‖⁻¹ • v₀ y‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (hv₀ y)
  · intro x y
    have hux : 0 < ‖u₀ x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (hu₀ x))
    have hvy : 0 < ‖v₀ y‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (hv₀ y))
    calc
      0 < (‖u₀ x‖⁻¹ * ‖v₀ y‖⁻¹) * (M x y * A x y) :=
        mul_pos (mul_pos hux hvy) (hA x y)
      _ = M x y * ⟪u x, v y⟫_ℝ := by
        change (‖u₀ x‖⁻¹ * ‖v₀ y‖⁻¹) * (M x y * A x y) =
          M x y * ⟪‖u₀ x‖⁻¹ • u₀ x, ‖v₀ y‖⁻¹ • v₀ y⟫_ℝ
        rw [inner_smul_left, inner_smul_right, huv]
        simp only [conj_trivial]
        ring

/-- A finite family of vectors in `ℝ^r` is in **general position** when every
`r` of them (selected by an injective index map) are linearly independent.  This
is the genericity output of Forster's perturbation step (PROOFS.md P5.2) and the
hypothesis consumed by the isotropic-position argument (P5.3): it forces every
proper subspace `W` to contain at most `dim W` of the vectors, which is what
makes the log-det potential `Φ` coercive. -/
def InGeneralPosition {r : ℕ} {ι : Type*}
    (u : ι → EuclideanSpace ℝ (Fin r)) : Prop :=
  ∀ g : Fin r → ι, Function.Injective g → LinearIndependent ℝ (fun i => u (g i))

/-- Real symmetric positive definiteness, stated locally to keep the P5.3
decomposition independent of the heavier matrix spectral-theory imports. -/
def ForsterPosDef {r : ℕ} (P : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  (∀ i j, P i j = P j i) ∧
    ∀ z : Fin r → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (P *ᵥ z)

/-- The log--quadratic potential used in Forster's isotropic-position argument
(PROOFS.md P5.3).  On a positive-definite matrix `P`, every summand is the
logarithm of the positive quadratic value `uₓᵀ P uₓ`. -/
noncomputable def forsterPotential {r : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → EuclideanSpace ℝ (Fin r)) (P : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  ∑ x, Real.log
    ((WithLp.equiv 2 _ (u x)) ⬝ᵥ (P *ᵥ (WithLp.equiv 2 _ (u x))))

/-! ### P5.2 leaf decomposition: perturbation into general position -/

/-- Partial general position along `T`: every subset of `T` of size at most
`r` indexes a linearly independent subfamily.  Established by induction in
`exists_partialGP_mem` and upgraded to `InGeneralPosition` at `T = univ` by
`inGeneralPosition_of_partialGP_univ`. -/
def PartialGP {r : ℕ} {ι : Type*} (u : ι → EuclideanSpace ℝ (Fin r))
    (T : Finset ι) : Prop :=
  ∀ S : Finset ι, S ⊆ T → S.card ≤ r → LinearIndepOn ℝ u (S : Set ι)

/-- A proper subspace of Euclidean space has empty interior: a nonempty
interior would force the subspace to be everything
(`Submodule.eq_top_of_nonempty_interior'`). -/
lemma interior_empty_of_ne_top {r : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin r))) (hW : W ≠ ⊤) :
    interior (W : Set (EuclideanSpace ℝ (Fin r))) = ∅ := by
  sorry

/-- A nonempty open set is not covered by finitely many proper subspaces:
each is closed (`Submodule.closed_of_finiteDimensional`) with empty interior
(`interior_empty_of_ne_top`), so peel them off one at a time
(`Finset.induction_on` on `𝒲`, applying the inductive hypothesis to the
open set `U \ W`, which is nonempty because `U ⊆ W` would put `U` inside
the empty `interior W`). -/
lemma exists_mem_avoiding_subspaces {r : ℕ}
    (𝒲 : Finset (Submodule ℝ (EuclideanSpace ℝ (Fin r))))
    (h𝒲 : ∀ W ∈ 𝒲, W ≠ ⊤) :
    ∀ U : Set (EuclideanSpace ℝ (Fin r)), IsOpen U → U.Nonempty →
      ∃ z ∈ U, ∀ W ∈ 𝒲, z ∉ W := by
  sorry

/-- The one-coordinate slice of an open set of families is open:
`z ↦ Function.update w x₀ z` is continuous (coordinatewise it is either the
identity or a constant). -/
lemma isOpen_update_slice {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → EuclideanSpace ℝ (Fin r))} (hU : IsOpen U)
    (w : ι → EuclideanSpace ℝ (Fin r)) (x₀ : ι) :
    IsOpen {z : EuclideanSpace ℝ (Fin r) | Function.update w x₀ z ∈ U} := by
  sorry

/-- The span of fewer than `r` vectors is a proper subspace of `ℝ^r`:
its finrank is at most the cardinality of the spanning image
(`finrank_span_le_card`), which is less than
`finrank (EuclideanSpace ℝ (Fin r)) = r` (`finrank_euclideanSpace_fin`). -/
lemma span_ne_top_of_card_lt {r : ℕ} {ι : Type*}
    (w : ι → EuclideanSpace ℝ (Fin r)) (S : Finset ι) (hS : S.card < r) :
    Submodule.span ℝ (w '' (S : Set ι)) ≠ ⊤ := by
  sorry

/-- Extending partial general position by one index: a subset of
`insert x₀ T` of size at most `r` either avoids `x₀` (use `hT`) or is
`insert x₀ S'` with `S' = S.erase x₀ ⊆ T` of size `< r`, where `hT` on `S'`
together with `havoid` and the `LinearIndepOn` insert API
(`LinearIndepOn.insert` / `linearIndepOn_insert`) applies. -/
lemma partialGP_insert {r : ℕ} {ι : Type*} [DecidableEq ι]
    {u : ι → EuclideanSpace ℝ (Fin r)} {T : Finset ι} {x₀ : ι} (hx₀ : x₀ ∉ T)
    (hT : PartialGP u T)
    (havoid : ∀ S : Finset ι, S ⊆ T → S.card < r →
      u x₀ ∉ Submodule.span ℝ (u '' (S : Set ι))) :
    PartialGP u (insert x₀ T) := by
  sorry

/-- Partial general position only reads the family on `T`
(`LinearIndepOn` congruence on the base set). -/
lemma partialGP_congr {r : ℕ} {ι : Type*}
    {u w : ι → EuclideanSpace ℝ (Fin r)} {T : Finset ι}
    (h : ∀ i ∈ T, u i = w i) (hw : PartialGP w T) : PartialGP u T := by
  sorry

/-- Induction core of P5.2: inside any nonempty open set of families one can
reach partial general position on any finite `T`, replacing one coordinate
at a time (`Finset.induction_on` on `T`).  Step at `x₀ ∉ T`, given
`w ∈ U` with `PartialGP w T`: the slice `{z | Function.update w x₀ z ∈ U}`
is open (`isOpen_update_slice`) and contains `w x₀`
(`Function.update_eq_self`); the spans of images of subsets `S ⊆ T` with
`S.card < r` form the finite family
`(T.powerset.filter (fun S => S.card < r)).image
  (fun S => Submodule.span ℝ (w '' (S : Set ι)))`
of proper subspaces (`span_ne_top_of_card_lt`); pick an avoiding `z`
(`exists_mem_avoiding_subspaces`) and set `w' := Function.update w x₀ z`.
Then `w' ∈ U`, `w'` agrees with `w` on `T` (`Function.update_of_ne`,
`x₀ ∉ T`), so `PartialGP w' T` (`partialGP_congr`) and the avoided spans are
also the `w'`-spans; conclude with `partialGP_insert`. -/
lemma exists_partialGP_mem {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → EuclideanSpace ℝ (Fin r))} (hU : IsOpen U)
    {u : ι → EuclideanSpace ℝ (Fin r)} (hu : u ∈ U) (T : Finset ι) :
    ∃ w ∈ U, PartialGP w T := by
  sorry

/-- At `T = univ`, partial general position upgrades to general position: an
injective selection `g : Fin r → ι` has image of size `r`, `LinearIndepOn`
on the image is linear independence of the subtype family, and composing
with the injection `Fin r → ↑(Finset.univ.image g)`, `i ↦ ⟨g i, _⟩`
(`LinearIndependent.comp`) yields independence of `fun i => u (g i)`. -/
lemma inGeneralPosition_of_partialGP_univ {r : ℕ} {ι : Type*} [Fintype ι]
    {u : ι → EuclideanSpace ℝ (Fin r)} (h : PartialGP u Finset.univ) :
    InGeneralPosition u := by
  sorry

lemma exists_inGeneralPosition_of_isOpen_nonempty {r : ℕ} {ι : Type*} [Fintype ι]
    (_hr : 0 < r) (U : Set (ι → EuclideanSpace ℝ (Fin r))) (hU_open : IsOpen U)
    (u : ι → EuclideanSpace ℝ (Fin r)) (hu : u ∈ U) :
    ∃ w ∈ U, InGeneralPosition w := by
  classical
  obtain ⟨w, hwU, hgp⟩ := exists_partialGP_mem hU_open hu Finset.univ
  exact ⟨w, hwU, inGeneralPosition_of_partialGP_univ hgp⟩

lemma isOpen_strict_sign_margin_pullback {r : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin r)) (s : ι → ι → ℝ) :
    IsOpen {w : ι → EuclideanSpace ℝ (Fin r) | (∀ x, w x ≠ 0) ∧ ∀ x y, 0 < s x y * ⟪(‖w x‖⁻¹ : ℝ) • w x, v y⟫_ℝ} := by
  sorry

lemma inGeneralPosition_smul {r : ℕ} {ι : Type*} [Fintype ι]
    {u : ι → EuclideanSpace ℝ (Fin r)} (hu : InGeneralPosition u)
    {c : ι → ℝ} (hc : ∀ x, c x ≠ 0) :
    InGeneralPosition (fun x ↦ c x • u x) := by
  sorry

lemma norm_normalize_eq_one {r : ℕ}
    {x : EuclideanSpace ℝ (Fin r)} (hx : x ≠ 0) :
    ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
  sorry

lemma inv_norm_ne_zero {r : ℕ} {x : EuclideanSpace ℝ (Fin r)} (hx : x ≠ 0) :
    (‖x‖⁻¹ : ℝ) ≠ 0 := by
  sorry

/-- **P5.2 (general position).**  Unit vectors `u` with a strict sign margin
against `v` can be perturbed by an arbitrarily small amount into unit vectors
`u₁` that are in general position, without changing any of the (finitely many,
strict) inner-product signs.  The excluded configurations — some `r` of the
perturbed vectors linearly dependent — form a finite union of measure-zero sets,
so a suitable perturbation exists strictly inside the sign-margin ball. -/
theorem exists_generalPosition_reposition {r : ℕ} {ι : Type*} [Fintype ι]
    (hr : 0 < r) (u v : ι → EuclideanSpace ℝ (Fin r))
    (hu : ∀ x, ‖u x‖ = 1) (s : ι → ι → ℝ)
    (hs : ∀ x y, 0 < s x y * ⟪u x, v y⟫_ℝ) :
    ∃ u₁ : ι → EuclideanSpace ℝ (Fin r),
      (∀ x, ‖u₁ x‖ = 1) ∧ (∀ x y, 0 < s x y * ⟪u₁ x, v y⟫_ℝ) ∧
      InGeneralPosition u₁ := by
  let U := {w : ι → EuclideanSpace ℝ (Fin r) | (∀ x, w x ≠ 0) ∧ ∀ x y, 0 < s x y * ⟪(‖w x‖⁻¹ : ℝ) • w x, v y⟫_ℝ}
  have hU_open : IsOpen U := isOpen_strict_sign_margin_pullback v s
  have hu_ne : ∀ x, u x ≠ 0 := by
    intro x h
    have := hu x
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hu_in_U : u ∈ U := by
    refine ⟨hu_ne, ?_⟩
    intro x y
    have h_norm : ‖u x‖⁻¹ = 1 := by rw [hu x, inv_one]
    have h_smul : (‖u x‖⁻¹ : ℝ) • u x = u x := by rw [h_norm, one_smul]
    rw [h_smul]
    exact hs x y
  obtain ⟨w, hwU, hwGen⟩ := exists_inGeneralPosition_of_isOpen_nonempty hr U hU_open u hu_in_U
  use fun x ↦ (‖w x‖⁻¹ : ℝ) • w x
  refine ⟨?_, hwU.2, ?_⟩
  · intro x
    exact norm_normalize_eq_one (hwU.1 x)
  · apply inGeneralPosition_smul hwGen
    intro x
    exact inv_norm_ne_zero (hwU.1 x)

/-! ### P5.3a leaf decomposition: coercivity of the Forster potential -/

/-- The quadratic form `z ↦ zᵀ P z` on Euclidean space; `forsterPotential`
is the sum of its logarithms over the family
(`forsterPotential_eq_sum_log`). -/
noncomputable def forsterQuad {r : ℕ} (P : Matrix (Fin r) (Fin r) ℝ)
    (z : EuclideanSpace ℝ (Fin r)) : ℝ :=
  (WithLp.equiv 2 _ z) ⬝ᵥ (P *ᵥ (WithLp.equiv 2 _ z))

lemma forsterPotential_eq_sum_log {r : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → EuclideanSpace ℝ (Fin r)) (P : Matrix (Fin r) (Fin r) ℝ) :
    forsterPotential u P = ∑ x, Real.log (forsterQuad P (u x)) := rfl

/-- An `ℓ¹`-normalized combination of linearly independent vectors is
bounded away from zero.  Recipe: for `k = 0` there is no admissible `c`
(the empty sum is `0 ≠ 1`), so take `η = 1`; otherwise the coefficient
sphere `{c | ∑ i, |c i| = 1}` is compact (closed by continuity of
`c ↦ ∑ i, |c i|`, bounded since each `|c i| ≤ 1`), the map
`c ↦ ‖∑ i, c i • v i‖` is continuous and attains a minimum
(`IsCompact.exists_isMinOn`), and the minimum is positive because a
vanishing combination with `∑ |c i| = 1 ≠ 0` contradicts
`linearIndependent_iff'` applied to `hv`. -/
lemma exists_l1_min_of_linearIndependent {k r : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin r)} (hv : LinearIndependent ℝ v) :
    ∃ η : ℝ, 0 < η ∧
      ∀ c : Fin k → ℝ, ∑ i, |c i| = 1 → η ≤ ‖∑ i, c i • v i‖ := by
  sorry

/-- More vectors than the dimension of their ambient subspace admit an
`ℓ¹`-normalized linear relation: `w + 1 > finrank W` vectors in `W` are
linearly dependent (transport a dependency of the subtype family, e.g. via
`Module.finrank`-based `not_linearIndependent_iff` on `W`), and any
nontrivial relation can be divided by its positive `ℓ¹`-norm
`∑ i, |c i| ≠ 0`. -/
lemma exists_l1_relation_of_finrank_lt {w r : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin r))) (hW : Module.finrank ℝ W ≤ w)
    (p : Fin (w + 1) → EuclideanSpace ℝ (Fin r)) (hp : ∀ i, p i ∈ W) :
    ∃ c : Fin (w + 1) → ℝ, ∑ i, |c i| = 1 ∧ ∑ i, c i • p i = 0 := by
  sorry

/-- Sub-selections of a general-position family are linearly independent:
extend the injection `e : Fin k → ι` to an injective `g : Fin r → ι` —
possible since the complement of the image of `e` has at least `r - k`
elements when `r ≤ card ι` — apply `hgen g`, and restrict along the first
`k` coordinates (`Fin.castLE hk`, `LinearIndependent.comp`). -/
lemma linearIndependent_selection_of_inGeneralPosition {r : ℕ} {ι : Type*}
    [Fintype ι] {u : ι → EuclideanSpace ℝ (Fin r)}
    (hgen : InGeneralPosition u) (hcard : r ≤ Fintype.card ι)
    {k : ℕ} (hk : k ≤ r) (e : Fin k → ι) (he : Function.Injective e) :
    LinearIndependent ℝ (u ∘ e) := by
  sorry

/-- **Quantitative general position.**  There is a margin `δ > 0` such that
every proper subspace `W` has at most `finrank W` of the unit vectors
`δ`-close to it.  Recipe: for each subset of indices of size `≤ r` the
selected subfamily is independent
(`linearIndependent_selection_of_inGeneralPosition`), so
`exists_l1_min_of_linearIndependent` gives a positive margin; let `δ` be the
minimum of `1` and half the minimum of these finitely many margins.  If some
`w + 1` distinct indices (with `w := Module.finrank ℝ W < r`) were `δ`-close
to `W`, pick approximants `q i ∈ W` with `‖u (x i) - q i‖ < δ`, take an
`ℓ¹`-normalized relation `c` of the `q`s
(`exists_l1_relation_of_finrank_lt`), and estimate
`‖∑ i, c i • u (x i)‖ = ‖∑ i, c i • (u (x i) - q i)‖ ≤ ∑ i, |c i| * δ = δ`,
contradicting the margin.  Only the finitely many index subsets matter; get
the `w + 1` distinct near indices from `Set.ncard` exceeding `w`
(`Set.exists_subset_card_eq` style extraction on a finite type). -/
lemma card_near_subspace_le_finrank {r : ℕ} {ι : Type*} [Fintype ι]
    (hcard : r ≤ Fintype.card ι)
    {u : ι → EuclideanSpace ℝ (Fin r)} (hu : ∀ x, ‖u x‖ = 1)
    (hgen : InGeneralPosition u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin r)), Module.finrank ℝ W < r →
        ({x : ι | ∃ p ∈ W, ‖u x - p‖ < δ} : Set ι).ncard ≤
          Module.finrank ℝ W := by
  sorry

/-- Sorted spectral data for a `ForsterPosDef` matrix: an orthonormal
spanning eigen-family with nondecreasing positive eigenvalues whose product
is the determinant, diagonalizing the quadratic form.  Recipe: `hP.1` makes
`P` Hermitian over `ℝ` (`Matrix.IsHermitian`, real conjugation is trivial);
use `Matrix.IsHermitian.eigenvectorBasis` and
`Matrix.IsHermitian.eigenvalues` with `mulVec_eigenvectorBasis` for the
diagonalization, `Matrix.IsHermitian.det_eq_prod_eigenvalues` for the
determinant, and positivity of each eigenvalue by evaluating `hP.2` at the
eigenvector.  Sort by composing with the permutation produced by
`Tuple.sort` (all conjuncts are invariant under a simultaneous permutation:
`Equiv.sum_comp`, `Equiv.prod_comp`); spanning comes from `Basis.span_eq` of
the orthonormal basis. -/
lemma exists_sorted_eigen_data {r : ℕ} (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : ForsterPosDef P) :
    ∃ (e : Fin r → EuclideanSpace ℝ (Fin r)) (lam : Fin r → ℝ),
      Orthonormal ℝ e ∧ Submodule.span ℝ (Set.range e) = ⊤ ∧
      Monotone lam ∧ (∀ i, 0 < lam i) ∧ ∏ i, lam i = P.det ∧
      ∀ z : EuclideanSpace ℝ (Fin r),
        forsterQuad P z = ∑ i, lam i * ⟪e i, z⟫_ℝ ^ 2 := by
  sorry

/-- If `z` is `δ`-far from the span of the low eigenvectors `{i | i < k}`,
the quadratic form at `z` is at least `lam k * δ²`.  Recipe: the orthogonal
projection `p := ∑ i ∈ Finset.univ.filter (· < k), ⟪e i, z⟫_ℝ • e i` lies in
the span, and `‖z - p‖² = ∑ i ∈ Finset.univ.filter (¬ · < k), ⟪e i, z⟫_ℝ ^ 2`
by the orthonormal expansion of `z` (spanning hypothesis; Parseval); each
high term of `hquad` carries `lam i ≥ lam k` (`hmono`), so
`forsterQuad P z ≥ lam k * ∑_{i ≥ k} ⟪e i, z⟫² = lam k * ‖z - p‖² ≥
lam k * δ²` using `hfar p`. -/
lemma forsterQuad_ge_of_far {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ}
    {e : Fin r → EuclideanSpace ℝ (Fin r)} {lam : Fin r → ℝ}
    (he : Orthonormal ℝ e) (hspan : Submodule.span ℝ (Set.range e) = ⊤)
    (hmono : Monotone lam) (hpos : ∀ i, 0 < lam i)
    (hquad : ∀ z, forsterQuad P z = ∑ i, lam i * ⟪e i, z⟫_ℝ ^ 2)
    (k : Fin r) {z : EuclideanSpace ℝ (Fin r)} {δ : ℝ} (hδ : 0 ≤ δ)
    (hfar : ∀ p ∈ Submodule.span ℝ (e '' {i | i < k}), δ ≤ ‖z - p‖) :
    lam k * δ ^ 2 ≤ forsterQuad P z := by
  sorry

/-- **Abel counting bound.**  If at most `k` items sit strictly below each
level `k`, the level-sum of a monotone `f` is at least the extremal
configuration: one item at each level below the top, everything else at the
top.  Recipe: write
`f (level x) = f (Fin.last m) - ∑ k ∈ Finset.univ.filter (level x < ·), d k`
where `d k := f k - f (k.pred-style predecessor)` telescopes over
successors; swap the two sums, bound each inner count via `hcount` and
`d k ≥ 0` (`hf`); the resulting identity
`∑_{k=1}^{m} (f k - f (k-1)) * k = m * f (Fin.last m) - ∑_{k<m} f k`
finishes.  Alternatively induct on `m`. -/
lemma sum_level_lower_bound {m : ℕ} {f : Fin (m + 1) → ℝ} (hf : Monotone f)
    {ι : Type*} [Fintype ι] (level : ι → Fin (m + 1))
    (hcount : ∀ k : Fin (m + 1),
      ({x : ι | level x < k} : Set ι).ncard ≤ (k : ℕ)) :
    ((Fintype.card ι : ℝ) - (m + 1)) * f (Fin.last m) + ∑ k, f k ≤
      ∑ x, f (level x) := by
  sorry

/-- **Coercivity of the Forster potential** (PROOFS.md P5.3, quantitative
form).  Recipe: take `δ` from `card_near_subspace_le_finrank` and, for a
given `P`, sorted eigen-data from `exists_sorted_eigen_data`; for each `x`
let `level x : Fin r` be the largest `k` such that `u x` is `δ`-far from
`Submodule.span ℝ (e '' {i | i < k})` (the far set contains `k = 0`, where
the span is `⊥` and `δ ≤ 1 = ‖u x‖`; farness is antitone in `k`, so
`level x < k` implies `δ`-nearness at `k`).  Then
`forsterQuad P (u x) ≥ lam (level x) * δ²` (`forsterQuad_ge_of_far`), so
`forsterPotential u P ≥ ∑ x, Real.log (lam (level x)) + N * Real.log (δ²)`;
the level count matches `card_near_subspace_le_finrank` because the span at
`k` has finrank `≤ k < r` (`finrank_span_le_card`), so
`sum_level_lower_bound` with the monotone `f := Real.log ∘ lam` and
`∑ i, Real.log (lam i) = Real.log (∏ i, lam i) = Real.log P.det = 0` gives
`forsterPotential u P ≥ (N - r) * Real.log (lam (Fin.last _)) +
2 * N * Real.log δ`.  Finally `forsterQuad P z ≤ lam (Fin.last _)` for unit
`z` (Parseval with `hquad` and monotonicity), and `N - r > 0` lets one pass
to the exponential bound (`Real.exp_log`, `Real.exp_le_exp`,
`div_le_iff`). Obtain `Fin.last` from `0 < r` by `cases r`. -/
lemma forsterPotential_coercive {r : ℕ} {ι : Type*} [Fintype ι]
    (hr : 0 < r) (hcard : r < Fintype.card ι)
    {u : ι → EuclideanSpace ℝ (Fin r)} (hu : ∀ x, ‖u x‖ = 1)
    (hgen : InGeneralPosition u) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ P : Matrix (Fin r) (Fin r) ℝ, ForsterPosDef P → P.det = 1 →
        ∀ z : EuclideanSpace ℝ (Fin r), ‖z‖ = 1 →
          forsterQuad P z ≤ Real.exp
            ((forsterPotential u P - 2 * Fintype.card ι * Real.log δ) /
              (Fintype.card ι - r)) := by
  sorry

/-- Symmetric positive-semidefinite matrices with determinant one are
positive definite.  Recipe: if `z ⬝ᵥ (P *ᵥ z) = 0` for some `z ≠ 0`,
polarize — `0 ≤ (z + t • w) ⬝ᵥ (P *ᵥ (z + t • w)) = 2 * t * (w ⬝ᵥ (P *ᵥ z))
+ t ^ 2 * (w ⬝ᵥ (P *ᵥ w))` for every `t` (symmetry of `P`) forces
`w ⬝ᵥ (P *ᵥ z) = 0` for every `w`, i.e. `P *ᵥ z = 0` — so `P` is singular
(`Matrix.exists_mulVec_eq_zero_iff`), contradicting `P.det = 1 ≠ 0`. -/
lemma forsterPosDef_of_psd_det_one {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ}
    (hsym : ∀ i j, P i j = P j i)
    (hpsd : ∀ z : Fin r → ℝ, 0 ≤ z ⬝ᵥ (P *ᵥ z))
    (hdet : P.det = 1) : ForsterPosDef P := by
  sorry

/-- A `ForsterPosDef` matrix has nonzero determinant: a vanishing
determinant gives a nonzero kernel vector
(`Matrix.exists_mulVec_eq_zero_iff`), whose quadratic value `0` contradicts
positive definiteness. -/
lemma forsterPosDef_det_ne_zero {r : ℕ} {B : Matrix (Fin r) (Fin r) ℝ}
    (hB : ForsterPosDef B) : B.det ≠ 0 := by
  sorry

/-- Entry bound from the quadratic form: `P i i = forsterQuad P
(EuclideanSpace.single i 1)` (a unit vector, `EuclideanSpace.norm_single`),
and evaluating the form at the unit vectors
`(Real.sqrt 2)⁻¹ • (EuclideanSpace.single i 1 ± EuclideanSpace.single j 1)`
(for `i ≠ j`) gives `(P i i + P j j ± 2 * P i j) / 2 ∈ [0, C]`, whence
`|P i j| ≤ C`. -/
lemma forster_entry_bound {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ} {C : ℝ}
    (hsym : ∀ i j, P i j = P j i)
    (hpsd : ∀ z : Fin r → ℝ, 0 ≤ z ⬝ᵥ (P *ᵥ z))
    (hdiag : ∀ z : EuclideanSpace ℝ (Fin r), ‖z‖ = 1 → forsterQuad P z ≤ C) :
    ∀ i j, |P i j| ≤ C := by
  sorry

/-- Continuity of the Forster potential where all quadratic values are
positive: each `P ↦ forsterQuad P (u x)` is a polynomial in the entries of
`P` (finite sums of products), hence continuous; `Real.log` is continuous
at nonzero points; combine `ContinuousOn.sum`, `ContinuousAt.continuousOn`,
`Real.continuousAt_log`. -/
lemma continuousOn_forsterPotential {r : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → EuclideanSpace ℝ (Fin r)) :
    ContinuousOn (forsterPotential u)
      {P : Matrix (Fin r) (Fin r) ℝ | ∀ x, 0 < forsterQuad P (u x)} := by
  sorry

/-- **P5.3a (coercivity and attainment).**  For a general-position unit family
with more vectors than the ambient dimension, the Forster potential is
coercive on the positive-definite determinant-one matrices and therefore
attains a global minimum there.  This is the compactness/coercivity half of
PROOFS.md P5.3; the first-order and normalization half is isolated in
`exists_isotropic_of_forsterPotential_minimizer`. -/
theorem exists_forsterPotential_minimizer {r : ℕ} {ι : Type*} [Fintype ι]
    (hr : 0 < r) (hcard : r < Fintype.card ι)
    (u : ι → EuclideanSpace ℝ (Fin r)) (hu : ∀ x, ‖u x‖ = 1)
    (hgen : InGeneralPosition u) :
    ∃ P : Matrix (Fin r) (Fin r) ℝ,
      ForsterPosDef P ∧ P.det = 1 ∧
        ∀ Q : Matrix (Fin r) (Fin r) ℝ,
          ForsterPosDef Q → Q.det = 1 →
            forsterPotential u P ≤ forsterPotential u Q := by
  sorry

/-! ### P5.3b leaf decomposition: first-order condition and the isotropic
transform -/

/-- Scaling the matrix shifts the potential by `N * log c`:
`forsterQuad (c • P) z = c * forsterQuad P z` (`Matrix.smul_mulVec_assoc`,
`dotProduct_smul`), and `Real.log_mul` term by term (all quadratic values
are nonzero). -/
lemma forsterPotential_smul {r : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → EuclideanSpace ℝ (Fin r)) (P : Matrix (Fin r) (Fin r) ℝ)
    {c : ℝ} (hc : 0 < c) (hq : ∀ x, forsterQuad P (u x) ≠ 0) :
    forsterPotential u (c • P) =
      Fintype.card ι * Real.log c + forsterPotential u P := by
  sorry

/-- Positive definiteness survives small symmetric perturbations: on the
compact unit sphere (`isCompact_sphere`, nonempty since `z / ‖z‖` reduces
the general case to it by homogeneity of degree `2`) the form of `P` has a
positive minimum `m` and the form of `X` a finite maximum absolute value
`M` (`IsCompact.exists_isMinOn` / `exists_isMaxOn` with continuity of the
quadratic forms); take `ε := m / (M + 1)`. -/
lemma forsterPosDef_perturb {r : ℕ} {P X : Matrix (Fin r) (Fin r) ℝ}
    (hP : ForsterPosDef P) (hX : ∀ i j, X i j = X j i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ForsterPosDef (P + t • X) := by
  sorry

/-- Derivative of the potential along a matrix line: each
`t ↦ forsterQuad (P + t • X) (u x)` is affine in `t` (`forsterQuad` is
linear in the matrix argument: `Matrix.add_mulVec`, `Matrix.smul_mulVec_assoc`,
`dotProduct_add`), so its `log` has derivative
`forsterQuad X (u x) / forsterQuad P (u x)` at `0` (`HasDerivAt.log` on the
affine `HasDerivAt` with positive value at `0`); sum with
`HasDerivAt.sum`. -/
lemma hasDerivAt_forsterPotential {r : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → EuclideanSpace ℝ (Fin r)) (P X : Matrix (Fin r) (Fin r) ℝ)
    (hq : ∀ x, 0 < forsterQuad P (u x)) :
    HasDerivAt (fun t : ℝ => forsterPotential u (P + t • X))
      (∑ x, forsterQuad X (u x) / forsterQuad P (u x)) 0 := by
  sorry

/-- Derivative of the determinant along a matrix line through a
determinant-one point: `det (P + t • X) = det P * det (1 + t • (P⁻¹ * X))`
(factor `P` on the left; `P` is invertible since `P.det = 1`,
`Matrix.invOf`/`Matrix.nonsing_inv` API), and `Matrix.det_one_add_smul`
expands the latter as `1 + t * (P⁻¹ * X).trace + t ^ 2 * (…)`, a polynomial
in `t`; differentiate with `Polynomial`-free calculus
(`HasDerivAt.const_add`, `HasDerivAt.mul` on monomials). -/
lemma hasDerivAt_det_line {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ}
    (X : Matrix (Fin r) (Fin r) ℝ) (hdet : P.det = 1) :
    HasDerivAt (fun t : ℝ => (P + t • X).det) ((P⁻¹ * X).trace) 0 := by
  sorry

/-- **First-order condition at the minimizer** (PROOFS.md P5.3).  Recipe:
for symmetric `X` consider the normalized line
`Q t := ((P + t • X).det) ^ (-(1 : ℝ) / r) • (P + t • X)` (real `rpow`).
For small `t`: `P + t • X` is `ForsterPosDef` (`forsterPosDef_perturb`) and
its determinant is positive and continuous in `t` (near `1`,
`hasDerivAt_det_line`.continuousAt), so `Q t` is `ForsterPosDef` with
`(Q t).det = 1` (`Matrix.det_smul`, `Real.rpow_natCast` bookkeeping:
`(d ^ (-(1:ℝ)/r)) ^ r * d = 1` for `d > 0`).  Minimality of `P` gives a
local minimum at `t = 0` of `g t := forsterPotential u (Q t) =
forsterPotential u (P + t • X) - (N / r) * Real.log ((P + t • X).det)`
(`forsterPotential_smul`, `Real.log_rpow`).  `g` is differentiable at `0`
(`hasDerivAt_forsterPotential`, `hasDerivAt_det_line`, `Real.log`,
chain rule) with derivative
`∑ x, forsterQuad X (u x) / forsterQuad P (u x) - (N / r) * (P⁻¹ * X).trace`,
which must vanish (`IsLocalMin.hasDerivAt_eq_zero`). -/
lemma forster_first_order {r : ℕ} {ι : Type*} [Fintype ι]
    (hr : 0 < r) (u : ι → EuclideanSpace ℝ (Fin r)) (hu : ∀ x, ‖u x‖ = 1)
    (P : Matrix (Fin r) (Fin r) ℝ) (hP : ForsterPosDef P) (hdet : P.det = 1)
    (hmin : ∀ Q : Matrix (Fin r) (Fin r) ℝ,
      ForsterPosDef Q → Q.det = 1 →
        forsterPotential u P ≤ forsterPotential u Q)
    (X : Matrix (Fin r) (Fin r) ℝ) (hX : ∀ i j, X i j = X j i) :
    ∑ x, forsterQuad X (u x) / forsterQuad P (u x)
      = (Fintype.card ι : ℝ) / r * (P⁻¹ * X).trace := by
  sorry

/-- The first-order condition for all symmetric `X` packages into the
moment identity `∑ₓ (uₓ uₓᵀ) / (uₓᵀ P uₓ) = (N/r) • P⁻¹`.  Recipe: test
`X := Matrix.single i i 1` and, for `i ≠ j`,
`X := Matrix.single i j 1 + Matrix.single j i 1` (symmetric);
`forsterQuad X z` picks out `z i ^ 2` resp. `2 * z i * z j`, and
`(P⁻¹ * X).trace` picks out `P⁻¹ i i` resp. `P⁻¹ j i + P⁻¹ i j`; conclude
entrywise (`Matrix.ext`), using that `P⁻¹` is symmetric
(`Matrix.transpose_nonsing_inv` with `hP.1`) and that both sides are
symmetric.  (If `Matrix.single` is named differently in this mathlib, use
`Matrix.stdBasisMatrix i j 1`.) -/
lemma forster_moment_matrix {r : ℕ} {ι : Type*} [Fintype ι]
    (hr : 0 < r) (u : ι → EuclideanSpace ℝ (Fin r)) (hu : ∀ x, ‖u x‖ = 1)
    (P : Matrix (Fin r) (Fin r) ℝ) (hP : ForsterPosDef P)
    (hfo : ∀ X : Matrix (Fin r) (Fin r) ℝ, (∀ i j, X i j = X j i) →
      ∑ x, forsterQuad X (u x) / forsterQuad P (u x)
        = (Fintype.card ι : ℝ) / r * (P⁻¹ * X).trace) :
    ∑ x, (forsterQuad P (u x))⁻¹ •
        Matrix.vecMulVec (WithLp.equiv 2 _ (u x)) (WithLp.equiv 2 _ (u x))
      = ((Fintype.card ι : ℝ) / r) • P⁻¹ := by
  sorry

/-- Positive-definite square root via the spectral theorem: write
`P = U * diagonal lam * Uᴴ` (`Matrix.IsHermitian.spectral_theorem` for the
Hermitian matrix given by `hP.1`; real entries), with positive eigenvalues
(evaluate `hP.2` at the eigenvectors), and set
`B := U * diagonal (fun i => Real.sqrt (lam i)) * Uᴴ`; then `B * B = P`
(`diagonal_mul_diagonal`, `Real.mul_self_sqrt`, unitarity of `U`), `B` is
symmetric, and `B`'s quadratic form is positive (its eigenvalues are the
positive `Real.sqrt (lam i)`). -/
lemma exists_forster_sqrt {r : ℕ} (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : ForsterPosDef P) :
    ∃ B : Matrix (Fin r) (Fin r) ℝ, ForsterPosDef B ∧ B * B = P := by
  sorry

/-- **P5.3b (first-order condition and normalization).**  A global minimizer
of the Forster potential yields the isotropic repositioning: take its
positive-definite square root `B`, normalize `B uₓ`, transform the dual vectors
by `B⁻ᵀ`, and use the determinant-one first-order condition to obtain
`∑ₓ ⟪u'ₓ,w⟫² = (N/r)‖w‖²`.  The paired transformations preserve every strict
inner-product sign. -/
theorem exists_isotropic_of_forsterPotential_minimizer
    {r : ℕ} {ι : Type*} [Fintype ι]
    (hr : 0 < r) (hcard : r < Fintype.card ι)
    (u v : ι → EuclideanSpace ℝ (Fin r))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ y, ‖v y‖ = 1)
    (s : ι → ι → ℝ) (hs : ∀ x y, 0 < s x y * ⟪u x, v y⟫_ℝ)
    (P : Matrix (Fin r) (Fin r) ℝ) (hP : ForsterPosDef P) (hdet : P.det = 1)
    (hmin : ∀ Q : Matrix (Fin r) (Fin r) ℝ,
      ForsterPosDef Q → Q.det = 1 → forsterPotential u P ≤ forsterPotential u Q) :
    ∃ u' v' : ι → EuclideanSpace ℝ (Fin r),
      (∀ x, ‖u' x‖ = 1) ∧ (∀ y, ‖v' y‖ = 1) ∧
      (∀ x y, 0 < s x y * ⟪u' x, v' y⟫_ℝ) ∧
      ∀ w : EuclideanSpace ℝ (Fin r),
        ∑ x, ⟪u' x, w⟫_ℝ ^ 2 = (Fintype.card ι : ℝ) / r * ‖w‖ ^ 2 := by
  sorry

/-- **P5.3 (isotropic position — the analytic kernel).**  Unit vectors `u` in
general position, with a strict sign margin against unit vectors `v`, can be
brought to isotropic position: there are unit vectors `u'`, `v'` preserving every
sign with `∑_x u'_x u'_xᵀ = (N/r)·I` (stated as the quadratic-form identity
`∑_x ⟪u'_x, w⟫² = (N/r)‖w‖²`).  **Assembly** (PROOFS.md P5.3):
`exists_forsterPotential_minimizer` supplies the positive-definite,
determinant-one minimizer using general position and coercivity;
`exists_isotropic_of_forsterPotential_minimizer` applies the first-order
condition and the paired square-root/dual transformations. -/
theorem exists_isotropic_of_generalPosition {r : ℕ} {ι : Type*} [Fintype ι]
    (hr : 0 < r) (hcard : r < Fintype.card ι)
    (u v : ι → EuclideanSpace ℝ (Fin r))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ y, ‖v y‖ = 1)
    (s : ι → ι → ℝ) (hs : ∀ x y, 0 < s x y * ⟪u x, v y⟫_ℝ)
    (hgen : InGeneralPosition u) :
    ∃ u' v' : ι → EuclideanSpace ℝ (Fin r),
      (∀ x, ‖u' x‖ = 1) ∧ (∀ y, ‖v' y‖ = 1) ∧
      (∀ x y, 0 < s x y * ⟪u' x, v' y⟫_ℝ) ∧
      ∀ w : EuclideanSpace ℝ (Fin r),
        ∑ x, ⟪u' x, w⟫_ℝ ^ 2 = (Fintype.card ι : ℝ) / r * ‖w‖ ^ 2 := by
  obtain ⟨P, hP, hdet, hmin⟩ :=
    exists_forsterPotential_minimizer hr hcard u hu hgen
  exact exists_isotropic_of_forsterPotential_minimizer
    hr hcard u v hu hv s hs P hP hdet hmin

/-- P5.2 + P5.3 (the analytic kernel): unit vectors with a strict sign margin
can be perturbed into general position and then brought to isotropic position
by an invertible transformation, without changing any sign.  Isotropy is
stated as the quadratic-form identity `∑_x ⟪u'_x, w⟫² = (N/r)·‖w‖²`.  **Assembly**
(PROOFS.md P5.2–P5.3): `exists_generalPosition_reposition` perturbs `u` into
general position preserving signs, then `exists_isotropic_of_generalPosition`
runs the log-det minimization to isotropy. -/
theorem exists_isotropic_reposition {r : ℕ} {ι : Type*} [Fintype ι]
    (hr : 0 < r) (hcard : r < Fintype.card ι)
    (u v : ι → EuclideanSpace ℝ (Fin r))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ y, ‖v y‖ = 1)
    (s : ι → ι → ℝ) (hs : ∀ x y, 0 < s x y * ⟪u x, v y⟫_ℝ) :
    ∃ u' v' : ι → EuclideanSpace ℝ (Fin r),
      (∀ x, ‖u' x‖ = 1) ∧ (∀ y, ‖v' y‖ = 1) ∧
      (∀ x y, 0 < s x y * ⟪u' x, v' y⟫_ℝ) ∧
      ∀ w : EuclideanSpace ℝ (Fin r),
        ∑ x, ⟪u' x, w⟫_ℝ ^ 2 = (Fintype.card ι : ℝ) / r * ‖w‖ ^ 2 := by
  obtain ⟨u₁, hu₁, hs₁, hgen⟩ := exists_generalPosition_reposition hr u v hu s hs
  exact exists_isotropic_of_generalPosition hr hcard u₁ v hu₁ hv s hs₁ hgen

/-- **P5.4a (isotropy lower bound).**  With unit vectors, sign match, and
isotropy, the correlation `∑_{x,y} M_{xy}⟪u_x,v_y⟫` is at least `N²/r`: each
term equals `|⟪u_x,v_y⟫|` (sign match, `|M_{xy}| = 1`), which dominates its
square (`|t| ≤ ‖u_x‖‖v_y‖ = 1`), and `∑_{x,y} ⟪u_x,v_y⟫² = ∑_y (N/r)‖v_y‖² =
N²/r` by isotropy applied to each `v_y`. -/
theorem forster_isotropy_lower {r : ℕ} {ι : Type*} [Fintype ι]
    (_hr : 0 < r) (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (u v : ι → EuclideanSpace ℝ (Fin r))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ y, ‖v y‖ = 1)
    (hsign : ∀ x y, 0 < M x y * ⟪u x, v y⟫_ℝ)
    (hiso : ∀ w : EuclideanSpace ℝ (Fin r),
      ∑ x, ⟪u x, w⟫_ℝ ^ 2 = (Fintype.card ι : ℝ) / r * ‖w‖ ^ 2) :
    (Fintype.card ι : ℝ) ^ 2 / (r : ℝ) ≤ ∑ x, ∑ y, M x y * ⟪u x, v y⟫_ℝ := by
  -- each summand dominates the square of the inner product
  have hterm : ∀ x y, ⟪u x, v y⟫_ℝ ^ 2 ≤ M x y * ⟪u x, v y⟫_ℝ := by
    intro x y
    have habs : M x y * ⟪u x, v y⟫_ℝ = |⟪u x, v y⟫_ℝ| := by
      rw [(abs_of_pos (hsign x y)).symm, abs_mul]
      rcases hM x y with h | h <;> rw [h] <;> simp
    rw [habs, ← sq_abs (⟪u x, v y⟫_ℝ)]
    have hle1 : |⟪u x, v y⟫_ℝ| ≤ 1 := by
      have hcs := abs_real_inner_le_norm (u x) (v y)
      rw [hu x, hv y, mul_one] at hcs
      exact hcs
    nlinarith [abs_nonneg (⟪u x, v y⟫_ℝ), hle1]
  -- the square-sum equals `N²/r`
  have hsumsq : ∑ x, ∑ y, ⟪u x, v y⟫_ℝ ^ 2 = (Fintype.card ι : ℝ) ^ 2 / (r : ℝ) := by
    rw [Finset.sum_comm]
    have hcol : ∀ y, ∑ x, ⟪u x, v y⟫_ℝ ^ 2 = (Fintype.card ι : ℝ) / r := by
      intro y; rw [hiso (v y), hv y]; ring
    rw [Finset.sum_congr rfl (fun y _ => hcol y), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  calc (Fintype.card ι : ℝ) ^ 2 / (r : ℝ)
      = ∑ x, ∑ y, ⟪u x, v y⟫_ℝ ^ 2 := hsumsq.symm
    _ ≤ ∑ x, ∑ y, M x y * ⟪u x, v y⟫_ℝ := by
        refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hterm x y))

/-- **P5.4b (spectral upper bound — Cauchy–Schwarz over columns).**  Writing the
correlation as `∑_{j<r} (U^{(j)})ᵀ M V^{(j)}` for the coordinate columns
`U^{(j)}(x) = u_x(j)`, `V^{(j)}(y) = v_y(j)`, each term is at most
`‖U^{(j)}‖·specNorm·‖V^{(j)}‖`, and column Cauchy–Schwarz with
`∑_j ‖U^{(j)}‖² = ∑_x ‖u_x‖² = N` (and likewise for `V`) bounds the whole sum by
`specNorm·N`. -/
theorem forster_specNorm_upper {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ)
    (u v : ι → EuclideanSpace ℝ (Fin r))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ y, ‖v y‖ = 1) :
    ∑ x, ∑ y, M x y * ⟪u x, v y⟫_ℝ ≤ specNorm M * (Fintype.card ι : ℝ) := by
  let U : Fin r → EuclideanSpace ℝ ι := fun j => (WithLp.equiv 2 _).symm (fun x => (u x).ofLp j)
  let V : Fin r → EuclideanSpace ℝ ι := fun j => (WithLp.equiv 2 _).symm (fun y => (v y).ofLp j)
  have H1 : ∀ x y, ⟪u x, v y⟫_ℝ = ∑ j : Fin r, (U j).ofLp x * (V j).ofLp y := by
    intro x y
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact Real.inner_apply _ _
  have H2 : ∀ j, ∑ x, (U j).ofLp x * (M *ᵥ (V j).ofLp) x = ⟪U j, (WithLp.equiv 2 _).symm (M *ᵥ (V j).ofLp)⟫_ℝ := by
    intro j
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro x _
    exact (Real.inner_apply _ _).symm
  have H3 : ∀ j : Fin r, ‖(WithLp.equiv 2 _).symm (M *ᵥ (V j).ofLp)‖ ≤ specNorm M * ‖V j‖ := by
    intro j
    have : (WithLp.equiv 2 _).symm (M *ᵥ (V j).ofLp) = Matrix.toEuclideanCLM (𝕜 := ℝ) M ((WithLp.equiv 2 _).symm (V j).ofLp) := rfl
    rw [this]
    have H_norm : specNorm M = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ := rfl
    rw [H_norm]
    have := ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) M) ((WithLp.equiv 2 (ι → ℝ)).symm (V j).ofLp)
    have h_symm : (WithLp.equiv 2 (ι → ℝ)).symm (V j).ofLp = V j := (Equiv.symm_apply_apply _ _).symm
    rw [h_symm] at this
    exact this
  calc
    ∑ x, ∑ y, M x y * ⟪u x, v y⟫_ℝ
      = ∑ x, ∑ y, M x y * ∑ j : Fin r, (U j).ofLp x * (V j).ofLp y := by simp_rw [H1]
    _ = ∑ x, ∑ y, ∑ j : Fin r, M x y * (U j).ofLp x * (V j).ofLp y := by
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro y _
        have : M x y * ∑ j : Fin r, (U j).ofLp x * (V j).ofLp y = ∑ j : Fin r, M x y * ((U j).ofLp x * (V j).ofLp y) := by rw [Finset.mul_sum]
        rw [this]
        apply Finset.sum_congr rfl; intro j _
        ring
    _ = ∑ j : Fin r, ∑ x, ∑ y, M x y * (U j).ofLp x * (V j).ofLp y := by
        have h1 : ∑ x, ∑ y, ∑ j : Fin r, M x y * (U j).ofLp x * (V j).ofLp y = ∑ x, ∑ j : Fin r, ∑ y, M x y * (U j).ofLp x * (V j).ofLp y := by
          apply Finset.sum_congr rfl; intro x _
          exact Finset.sum_comm
        rw [h1, Finset.sum_comm]
    _ = ∑ j : Fin r, ∑ x, (U j).ofLp x * ∑ y, M x y * (V j).ofLp y := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro x _
        have : ∑ y, M x y * (U j).ofLp x * (V j).ofLp y = ∑ y, (U j).ofLp x * (M x y * (V j).ofLp y) := by
          apply Finset.sum_congr rfl; intro y _
          ring
        rw [this, ← Finset.mul_sum]
    _ = ∑ j : Fin r, ⟪U j, (WithLp.equiv 2 _).symm (M *ᵥ (V j).ofLp)⟫_ℝ := by
        apply Finset.sum_congr rfl; intro j _
        have h_mulvec : ∀ x, ∑ y, M x y * (V j).ofLp y = (M *ᵥ (V j).ofLp) x := fun x => rfl
        simp_rw [h_mulvec]
        exact H2 j
    _ ≤ ∑ j : Fin r, ‖U j‖ * ‖(WithLp.equiv 2 _).symm (M *ᵥ (V j).ofLp)‖ := by
        apply Finset.sum_le_sum; intro j _
        exact real_inner_le_norm _ _
    _ ≤ ∑ j : Fin r, ‖U j‖ * (specNorm M * ‖V j‖) := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left (H3 j) (norm_nonneg _)
    _ = specNorm M * ∑ j : Fin r, ‖U j‖ * ‖V j‖ := by
        have : ∑ j : Fin r, ‖U j‖ * (specNorm M * ‖V j‖) = ∑ j : Fin r, specNorm M * (‖U j‖ * ‖V j‖) := by
          apply Finset.sum_congr rfl; intro j _
          ring
        rw [this, ← Finset.mul_sum]
    _ ≤ specNorm M * (Real.sqrt (∑ j : Fin r, ‖U j‖^2) * Real.sqrt (∑ j : Fin r, ‖V j‖^2)) := by
        have h_cs : ∑ j, ‖U j‖ * ‖V j‖ ≤ Real.sqrt (∑ j, ‖U j‖^2) * Real.sqrt (∑ j, ‖V j‖^2) := by
          let U' : EuclideanSpace ℝ (Fin r) := (WithLp.equiv 2 _).symm (fun j => ‖U j‖)
          let V' : EuclideanSpace ℝ (Fin r) := (WithLp.equiv 2 _).symm (fun j => ‖V j‖)
          have h1 : ⟪U', V'⟫_ℝ = ∑ j, ‖U j‖ * ‖V j‖ := by
            rw [PiLp.inner_apply]
            apply Finset.sum_congr rfl
            intro j _
            exact Real.inner_apply _ _
          have h2 : ‖U'‖ = Real.sqrt (∑ j, ‖U j‖^2) := by
            have h_sq : ‖U'‖^2 = ∑ j, ‖U j‖^2 := norm_sq_eq (fun j => ‖U j‖)
            rw [← h_sq]
            exact (Real.sqrt_sq (norm_nonneg _)).symm
          have h3 : ‖V'‖ = Real.sqrt (∑ j, ‖V j‖^2) := by
            have h_sq : ‖V'‖^2 = ∑ j, ‖V j‖^2 := norm_sq_eq (fun j => ‖V j‖)
            rw [← h_sq]
            exact (Real.sqrt_sq (norm_nonneg _)).symm
          have := real_inner_le_norm U' V'
          rw [h1, h2, h3] at this
          exact this
        apply mul_le_mul_of_nonneg_left h_cs (norm_nonneg _)
    _ = specNorm M * (Real.sqrt (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) := by
        have h_sumU : ∑ j : Fin r, ‖U j‖^2 = (Fintype.card ι : ℝ) := by
          have h_sq : ∑ j : Fin r, ‖U j‖^2 = ∑ j : Fin r, ∑ x : ι, ((u x).ofLp j)^2 := by
            apply Finset.sum_congr rfl; intro j _
            exact norm_sq_eq _
          rw [h_sq]
          rw [Finset.sum_comm]
          have h_ux : ∀ x, ∑ j : Fin r, ((u x).ofLp j)^2 = 1 := by
            intro x
            have hx := hu x
            have h_sq2 : ‖u x‖^2 = ∑ j : Fin r, ((u x).ofLp j)^2 := norm_sq_eq (u x).ofLp
            rw [← h_sq2, hx, one_pow]
          simp_rw [h_ux, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        have h_sumV : ∑ j : Fin r, ‖V j‖^2 = (Fintype.card ι : ℝ) := by
          have h_sq : ∑ j : Fin r, ‖V j‖^2 = ∑ j : Fin r, ∑ y : ι, ((v y).ofLp j)^2 := by
            apply Finset.sum_congr rfl; intro j _
            exact norm_sq_eq _
          rw [h_sq]
          rw [Finset.sum_comm]
          have h_vy : ∀ y, ∑ j : Fin r, ((v y).ofLp j)^2 = 1 := by
            intro y
            have hy := hv y
            have h_sq2 : ‖v y‖^2 = ∑ j : Fin r, ((v y).ofLp j)^2 := norm_sq_eq (v y).ofLp
            rw [← h_sq2, hy, one_pow]
          simp_rw [h_vy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        rw [h_sumU, h_sumV]
    _ = specNorm M * (Fintype.card ι : ℝ) := by
        congr 1
        exact Real.mul_self_sqrt (Nat.cast_nonneg _)

/-- P5.4: the main chain.  `∑_{x,y} M_{xy}⟪u_x,v_y⟫ = ∑ |⟪u_x,v_y⟫| ≥
∑ ⟪u_x,v_y⟫² = N²/r` by isotropy (`forster_isotropy_lower`), while the same sum
is at most `specNorm·N` by the column decomposition and Cauchy–Schwarz
(`forster_specNorm_upper`); dividing `N²/r ≤ specNorm·N` by `N` gives the
result. -/
theorem forster_main_chain {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (u v : ι → EuclideanSpace ℝ (Fin r))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ y, ‖v y‖ = 1)
    (hsign : ∀ x y, 0 < M x y * ⟪u x, v y⟫_ℝ)
    (hiso : ∀ w : EuclideanSpace ℝ (Fin r),
      ∑ x, ⟪u x, w⟫_ℝ ^ 2 = (Fintype.card ι : ℝ) / r * ‖w‖ ^ 2) :
    (Fintype.card ι : ℝ) ≤ (r : ℝ) * specNorm M := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hspec : 0 ≤ specNorm M := norm_nonneg _
  have hNpos : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hchain : (Fintype.card ι : ℝ) ^ 2 / (r : ℝ) ≤ specNorm M * (Fintype.card ι : ℝ) :=
    (forster_isotropy_lower hr M hM u v hu hv hsign hiso).trans
      (forster_specNorm_upper M u v hu hv)
  have hchain2 : (Fintype.card ι : ℝ) ^ 2 ≤ specNorm M * (Fintype.card ι : ℝ) * r :=
    (div_le_iff₀ hrpos).mp hchain
  rcases eq_or_lt_of_le hNpos with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith [hchain2, hpos, hspec, hrpos]

/-- **Forster's theorem, large-rank regime** (Forster 2002; PROOFS.md P5.1–P5.4).
Assembly: `one_le_signRank` gives `1 ≤ r := signRank M`; `exists_unit_sign_factorization`
produces the unit factorization; `exists_isotropic_reposition` (using `r < N`) brings it
to isotropic position preserving signs; `forster_main_chain` is the Cauchy–Schwarz /
isotropy inequality. -/
theorem forster_large_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (h_r : signRank M < Fintype.card ι) :
    (Fintype.card ι : ℝ) ≤ (signRank M : ℝ) * specNorm M := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hr1 : 1 ≤ signRank M := one_le_signRank M hM
  obtain ⟨u, v, hu, hv, hsign⟩ := exists_unit_sign_factorization M hM hr1
  obtain ⟨u', v', hu', hv', hsign', hiso⟩ :=
    exists_isotropic_reposition hr1 h_r u v hu hv (fun x y => M x y) hsign
  have hsign'' : ∀ x y, 0 < M x y * ⟪u' x, v' y⟫_ℝ := hsign'
  exact forster_main_chain hr1 M hM u' v' hu' hv' hsign'' hiso

/-- **Forster's theorem** (Forster 2002): a `±1` matrix of size `N × N` has
sign-rank at least `N / ‖M‖₂`.  Split into the small-rank (`N ≤ r`) and large-rank
regimes. -/
theorem forster {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1) :
    (Fintype.card ι : ℝ) ≤ (signRank M : ℝ) * specNorm M := by
  by_cases h : Fintype.card ι ≤ signRank M
  · exact forster_small_rank M hM h
  · push Not at h
    exact forster_large_rank M hM h

end ForsterDecomposition

end HeadComplexity
