import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
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

open scoped Kronecker

/-- Spectral norm of a square real matrix: the operator norm of the induced map
on Euclidean space. -/
noncomputable def specNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

/-- **Forster's theorem** (Forster 2002): a `±1` matrix of size `N × N` has
sign-rank at least `N / ‖M‖₂`. -/
theorem forster {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1) :
    (Fintype.card ι : ℝ) ≤ (signRank M : ℝ) * specNorm M := by
  sorry

open Matrix
open scoped Kronecker
open scoped Matrix.Norms.L2Operator
open Metric

private theorem norm_sq_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    ‖(WithLp.equiv 2 _).symm v‖^2 = ∑ i, v i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

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

/-- **±1 spectral lower bound** (PROOFS.md P5.1, the `signRank ≥ N` regime of
Forster): every column of a `±1` matrix has Euclidean norm `√N`
(`‖M *ᵥ eⱼ‖² = ∑ᵢ (M i j)² = N`), so `specNorm M ≥ √N`, i.e.
`card ι ≤ (specNorm M) ^ 2`.  Start from `specNorm M = ‖toEuclideanCLM M‖ ≥
‖toEuclideanCLM M (EuclideanSpace.single j 1)‖`; the empty index type gives
`0 ≤ 0` via `norm_eq_zero_of_isEmpty`. -/
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
    have h_op : ‖(WithLp.equiv 2 _).symm (M *ᵥ e_j)‖ ≤ specNorm M * ‖(WithLp.equiv 2 _).symm e_j‖ := by
      have : (WithLp.equiv 2 _).symm (M *ᵥ e_j) = Matrix.toEuclideanCLM (𝕜 := ℝ) M ((WithLp.equiv 2 _).symm e_j) := rfl
      rw [this]
      exact ContinuousLinearMap.le_opNorm _ _
    rw [he_j_norm, mul_one] at h_op
    have h_op_sq : ‖(WithLp.equiv 2 _).symm (M *ᵥ e_j)‖^2 ≤ (specNorm M)^2 := by
      nlinarith [h_op, norm_nonneg ((WithLp.equiv 2 (ι → ℝ)).symm (M *ᵥ e_j)), norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) M)]
    rwa [h_action_norm] at h_op_sq

end HeadComplexity
