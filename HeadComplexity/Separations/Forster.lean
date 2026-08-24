import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import HeadComplexity.Separations.SignRank
import Mathlib.Analysis.Matrix.Spectrum

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
  by_contra h
  have hne : (interior (W : Set (EuclideanSpace ℝ (Fin r)))).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr h
  have htop := Submodule.eq_top_of_nonempty_interior' W hne
  exact hW htop

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
  induction 𝒲 using Finset.induction_on with
  | empty =>
    intro U _ hU_nonempty
    obtain ⟨z, hz⟩ := hU_nonempty
    use z, hz
    intro W hW
    simp at hW
  | insert W 𝒲 _ ih =>
    intro U hU hU_nonempty
    have hW_ne_top : W ≠ ⊤ := h𝒲 W (Finset.mem_insert_self W 𝒲)
    have h𝒲' : ∀ W' ∈ 𝒲, W' ≠ ⊤ := fun W' hW' => h𝒲 W' (Finset.mem_insert_of_mem hW')
    have hW_closed : IsClosed (W : Set (EuclideanSpace ℝ (Fin r))) := Submodule.closed_of_finiteDimensional W
    set U' := U \ W with hU'_def
    have hU'_open : IsOpen U' := hU.sdiff hW_closed
    have hU'_nonempty : U'.Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      have hU_sub_W : U ⊆ W := Set.sdiff_eq_empty.mp hc
      have hU_sub_int : U ⊆ interior (W : Set (EuclideanSpace ℝ (Fin r))) := by
        rw [hU.subset_interior_iff]
        exact hU_sub_W
      rw [interior_empty_of_ne_top W hW_ne_top] at hU_sub_int
      obtain ⟨z, hz⟩ := hU_nonempty
      exact hU_sub_int hz
    obtain ⟨z, hzU', hz𝒲⟩ := ih h𝒲' U' hU'_open hU'_nonempty
    have hzU : z ∈ U := hzU'.1
    have hzW : z ∉ W := hzU'.2
    use z, hzU
    intro W' hW'
    rcases Finset.mem_insert.mp hW' with rfl | hW'_in_𝒲
    · exact hzW
    · exact hz𝒲 W' hW'_in_𝒲

/-- The one-coordinate slice of an open set of families is open:
`z ↦ Function.update w x₀ z` is continuous (coordinatewise it is either the
identity or a constant). -/
lemma isOpen_update_slice {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → EuclideanSpace ℝ (Fin r))} (hU : IsOpen U)
    (w : ι → EuclideanSpace ℝ (Fin r)) (x₀ : ι) :
    IsOpen {z : EuclideanSpace ℝ (Fin r) | Function.update w x₀ z ∈ U} := by
  have h_cont : Continuous (fun (z : EuclideanSpace ℝ (Fin r)) => Function.update w x₀ z) := by
    apply continuous_pi
    intro i
    by_cases hi : i = x₀
    · subst hi
      simp
      exact continuous_id
    · simp [hi]
      exact continuous_const
  exact hU.preimage h_cont

/-- The span of fewer than `r` vectors is a proper subspace of `ℝ^r`:
its finrank is at most the cardinality of the spanning image
(`finrank_span_le_card`), which is less than
`finrank (EuclideanSpace ℝ (Fin r)) = r` (`finrank_euclideanSpace_fin`). -/
lemma span_ne_top_of_card_lt {r : ℕ} {ι : Type*}
    (w : ι → EuclideanSpace ℝ (Fin r)) (S : Finset ι) (hS : S.card < r) :
    Submodule.span ℝ (w '' (S : Set ι)) ≠ ⊤ := by
  intro htop
  have h1 : Module.finrank ℝ (Submodule.span ℝ (w '' (S : Set ι))) = Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) := by
    rw [htop, finrank_top]
  have h2 : Module.finrank ℝ (Submodule.span ℝ (w '' (S : Set ι))) ≤ (S.image w).card := by
    have h_set : w '' (S : Set ι) = ↑(S.image w) := Finset.coe_image.symm
    rw [h_set]
    exact finrank_span_finset_le_card (S.image w)
  have h3 : (S.image w).card ≤ S.card := Finset.card_image_le
  have h4 : Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) = r := finrank_euclideanSpace_fin
  rw [h1, h4] at h2
  omega

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
  intro S hS hScard
  by_cases hxS : x₀ ∈ S
  · have hx0_notin : x₀ ∉ (S.erase x₀ : Set ι) := by
      intro h
      rw [Finset.mem_coe, Finset.mem_erase] at h
      exact h.1 rfl
    have hS'_sub : S.erase x₀ ⊆ T := by
      intro y hy
      rw [Finset.mem_erase] at hy
      have hy_ins := hS hy.2
      rw [Finset.mem_insert] at hy_ins
      exact hy_ins.resolve_left hy.1
    have hS_card_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨x₀, hxS⟩
    have hS'_card : (S.erase x₀).card < r := by
      rw [Finset.card_erase_of_mem hxS]
      omega
    have h_indep : LinearIndepOn ℝ u (S.erase x₀ : Set ι) :=
      hT (S.erase x₀) hS'_sub (by omega)
    have h_not_in : u x₀ ∉ Submodule.span ℝ (u '' (S.erase x₀ : Set ι)) :=
      havoid (S.erase x₀) hS'_sub hS'_card
    have hS_eq : S = insert x₀ (S.erase x₀) := (Finset.insert_erase hxS).symm
    rw [hS_eq, Finset.coe_insert]
    rw [linearIndepOn_insert hx0_notin]
    exact ⟨h_indep, h_not_in⟩
  · have hS_sub : S ⊆ T := by
      intro y hy
      have hy_ins := hS hy
      rw [Finset.mem_insert] at hy_ins
      exact hy_ins.resolve_left (fun h => hxS (h ▸ hy))
    exact hT S hS_sub hScard

/-- Partial general position only reads the family on `T`
(`LinearIndepOn` congruence on the base set). -/
lemma partialGP_congr {r : ℕ} {ι : Type*}
    {u w : ι → EuclideanSpace ℝ (Fin r)} {T : Finset ι}
    (h : ∀ i ∈ T, u i = w i) (hw : PartialGP w T) : PartialGP u T := by
  intro S hS hcard
  refine LinearIndepOn.congr (hw S hS hcard) ?_
  intro i hi
  exact (h i (hS hi)).symm

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
  classical
  induction T using Finset.induction_on with
  | empty =>
    use u, hu
    intro S hS hScard
    have hS_empty : S = ∅ := Finset.subset_empty.mp hS
    rw [hS_empty, Finset.coe_empty]
    exact linearIndepOn_empty ℝ u
  | insert x0 T hx0 ih =>
    obtain ⟨w, hwU, hwGP⟩ := ih
    let V := {z : EuclideanSpace ℝ (Fin r) | Function.update w x0 z ∈ U}
    have hV_open : IsOpen V := isOpen_update_slice hU w x0
    have hV_nonempty : V.Nonempty := ⟨w x0, by
      change Function.update w x0 (w x0) ∈ U
      rw [Function.update_eq_self]
      exact hwU⟩
    let subsets : Finset (Finset ι) := T.powerset.filter (fun S => S.card < r)
    let 𝒲 : Finset (Submodule ℝ (EuclideanSpace ℝ (Fin r))) :=
      Finset.image (fun (S : Finset ι) => Submodule.span ℝ (w '' (S : Set ι))) subsets
    have h𝒲 : ∀ W ∈ 𝒲, W ≠ ⊤ := by
      intro W hW
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hW
      have hS' := Finset.mem_filter.mp hS
      exact span_ne_top_of_card_lt w S hS'.2
    obtain ⟨z, hzV, hz_avoid⟩ := exists_mem_avoiding_subspaces 𝒲 h𝒲 V hV_open hV_nonempty
    let w' := Function.update w x0 z
    have hw'U : w' ∈ U := hzV
    have hw'_eq_w : ∀ i ∈ T, w' i = w i := by
      intro i hi
      have hne : i ≠ x0 := fun h => hx0 (h ▸ hi)
      exact Function.update_of_ne hne z w
    have hw'GP : PartialGP w' T := partialGP_congr hw'_eq_w hwGP
    refine ⟨w', hw'U, partialGP_insert hx0 hw'GP ?_⟩
    intro S hS hScard
    have hw'x0 : w' x0 = z := Function.update_self x0 z w
    rw [hw'x0]
    have h_image : w' '' (S : Set ι) = w '' (S : Set ι) := by
      apply Set.image_congr
      intro i hi
      exact hw'_eq_w i (hS hi)
    rw [h_image]
    have hS_mem_subsets : S ∈ subsets := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hS, hScard⟩
    have hW_mem : Submodule.span ℝ (w '' (S : Set ι)) ∈ 𝒲 := by
      rw [Finset.mem_image]
      exact ⟨S, hS_mem_subsets, rfl⟩
    exact hz_avoid _ hW_mem

/-- At `T = univ`, partial general position upgrades to general position: an
injective selection `g : Fin r → ι` has image of size `r`, `LinearIndepOn`
on the image is linear independence of the subtype family, and composing
with the injection `Fin r → ↑(Finset.univ.image g)`, `i ↦ ⟨g i, _⟩`
(`LinearIndependent.comp`) yields independence of `fun i => u (g i)`. -/
lemma inGeneralPosition_of_partialGP_univ {r : ℕ} {ι : Type*} [Fintype ι]
    {u : ι → EuclideanSpace ℝ (Fin r)} (h : PartialGP u Finset.univ) :
    InGeneralPosition u := by
  classical
  intro g hg
  let S : Finset ι := Finset.univ.image g
  have hS_sub : S ⊆ Finset.univ := Finset.subset_univ S
  have hS_card : S.card = r := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hS_card_le : S.card ≤ r := hS_card.le
  have h_indep : LinearIndepOn ℝ u (S : Set ι) := h S hS_sub hS_card_le
  have hli : LinearIndependent ℝ (fun (x : ↑(S : Set ι)) => u ↑x) := h_indep.linearIndependent
  let f : Fin r → ↑(S : Set ι) := fun i => ⟨g i, Finset.mem_coe.mpr (Finset.mem_image_of_mem g (Finset.mem_univ i))⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    have h_eq : g i = g j := Subtype.ext_iff.mp hij
    exact hg h_eq
  have h_comp := LinearIndependent.comp hli f hf_inj
  exact h_comp

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
  have h_eq : {w : ι → EuclideanSpace ℝ (Fin r) | (∀ x, w x ≠ 0) ∧ ∀ x y, 0 < s x y * ⟪(‖w x‖⁻¹ : ℝ) • w x, v y⟫_ℝ} =
              (⋂ x, {w | w x ≠ (0 : EuclideanSpace ℝ (Fin r))}) ∩
              (⋂ (x : ι) (y : ι), {w | 0 < s x y * ⟪w x, v y⟫_ℝ}) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hne, hgt⟩
      refine ⟨hne, fun x y => ?_⟩
      have hgtxy := hgt x y
      rw [real_inner_smul_left] at hgtxy
      have h1 : s x y * (‖w x‖⁻¹ * ⟪w x, v y⟫_ℝ) = ‖w x‖⁻¹ * (s x y * ⟪w x, v y⟫_ℝ) := by ring
      rw [h1] at hgtxy
      have hpos : 0 < ‖w x‖ := norm_pos_iff.mpr (hne x)
      have hinvpos : 0 < ‖w x‖⁻¹ := inv_pos.mpr hpos
      exact pos_of_mul_pos_right hgtxy (le_of_lt hinvpos)
    · rintro ⟨hne, hgt⟩
      refine ⟨hne, fun x y => ?_⟩
      have hgtxy := hgt x y
      rw [real_inner_smul_left]
      have h1 : s x y * (‖w x‖⁻¹ * ⟪w x, v y⟫_ℝ) = ‖w x‖⁻¹ * (s x y * ⟪w x, v y⟫_ℝ) := by ring
      rw [h1]
      have hpos : 0 < ‖w x‖ := norm_pos_iff.mpr (hne x)
      have hinvpos : 0 < ‖w x‖⁻¹ := inv_pos.mpr hpos
      exact mul_pos hinvpos hgtxy

  rw [h_eq]
  refine IsOpen.inter ?_ ?_
  · apply isOpen_iInter_of_finite
    intro x
    have h_cont : Continuous (fun (w : ι → EuclideanSpace ℝ (Fin r)) ↦ w x) := continuous_apply x
    have h_open : IsOpen ({(0 : EuclideanSpace ℝ (Fin r))}ᶜ) := isOpen_compl_singleton
    exact h_open.preimage h_cont
  · apply isOpen_iInter_of_finite
    intro x
    apply isOpen_iInter_of_finite
    intro y
    have h_mul : Continuous (fun (w : ι → EuclideanSpace ℝ (Fin r)) ↦ s x y * ⟪w x, v y⟫_ℝ) :=
      continuous_const.mul ((continuous_apply x).inner continuous_const)
    exact isOpen_Ioi.preimage h_mul

lemma inGeneralPosition_smul {r : ℕ} {ι : Type*} [Fintype ι]
    {u : ι → EuclideanSpace ℝ (Fin r)} (hu : InGeneralPosition u)
    {c : ι → ℝ} (hc : ∀ x, c x ≠ 0) :
    InGeneralPosition (fun x ↦ c x • u x) := by
  intro g hg
  have h_lin := hu g hg
  let w : Fin r → ℝˣ := fun i => Units.mk0 (c (g i)) (hc (g i))
  have h_units := LinearIndependent.units_smul h_lin w
  have h_eq : (w • (fun i => u (g i))) = (fun i => c (g i) • u (g i)) := by
    ext i
    rfl
  rw [h_eq] at h_units
  exact h_units

lemma norm_normalize_eq_one {r : ℕ}
    {x : EuclideanSpace ℝ (Fin r)} (hx : x ≠ 0) :
    ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr hx

lemma inv_norm_ne_zero {r : ℕ} {x : EuclideanSpace ℝ (Fin r)} (hx : x ≠ 0) :
    (‖x‖⁻¹ : ℝ) ≠ 0 :=
  inv_ne_zero (norm_ne_zero_iff.mpr hx)

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
  classical
  let S : Set (Fin k → ℝ) := {c | ∑ i, |c i| = 1}
  have h_l1_cont : Continuous (fun c : Fin k → ℝ ↦ ∑ i, |c i|) :=
    continuous_finsetSum Finset.univ fun i _ ↦ (continuous_apply i).abs
  have hS_closed : IsClosed S := by
    exact isClosed_eq h_l1_cont continuous_const
  have hS_bounded : Bornology.IsBounded S := by
    refine isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩
    intro c hc
    change (∑ i, |c i|) = 1 at hc
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    calc
      |c i| ≤ ∑ j, |c j| :=
        Finset.single_le_sum (fun j _ ↦ abs_nonneg (c j)) (Finset.mem_univ i)
      _ = 1 := hc
  have hS_compact : IsCompact S :=
    isCompact_iff_isClosed_bounded.mpr ⟨hS_closed, hS_bounded⟩
  have h_norm_cont : Continuous (fun c : Fin k → ℝ ↦ ‖∑ i, c i • v i‖) := by
    apply Continuous.norm
    exact continuous_finsetSum Finset.univ fun i _ ↦
      (continuous_apply i).smul continuous_const
  have h_pos : ∀ c ∈ S, 0 < ‖∑ i, c i • v i‖ := by
    intro c hc
    change (∑ i, |c i|) = 1 at hc
    rw [norm_pos_iff]
    intro hcomb
    have hc_zero : ∀ i, c i = 0 :=
      Fintype.linearIndependent_iff.mp hv c hcomb
    have : (∑ i, |c i|) = 0 := by simp [hc_zero]
    linarith [hc]
  obtain ⟨η, hη_pos, hη⟩ :=
    hS_compact.exists_forall_le' h_norm_cont.continuousOn h_pos
  exact ⟨η, hη_pos, fun c hc ↦ hη c hc⟩

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
  let pW : Fin (w + 1) → W := fun i => ⟨p i, hp i⟩
  have h_not_li : ¬ LinearIndependent ℝ pW := by
    intro hli
    have h_card := LinearIndependent.fintype_card_le_finrank hli
    simp only [Fintype.card_fin] at h_card
    omega
  rw [Fintype.not_linearIndependent_iff] at h_not_li
  rcases h_not_li with ⟨g, hg_sum, i0, hgi0⟩
  have h_sum_abs_pos : 0 < ∑ i, |g i| := by
    apply Finset.sum_pos'
    · intro i _
      exact abs_nonneg (g i)
    · use i0
      refine ⟨Finset.mem_univ i0, ?_⟩
      exact abs_pos.mpr hgi0
  let S := ∑ i, |g i|
  use fun i => g i / S
  constructor
  · have h_abs : ∀ i, |g i / S| = |g i| / S := by
      intro i
      rw [abs_div, abs_of_pos h_sum_abs_pos]
    simp_rw [h_abs]
    rw [← Finset.sum_div, div_self (ne_of_gt h_sum_abs_pos)]
  · have h_sum_val : (∑ i, g i • pW i : W).val = 0 := by rw [hg_sum, Submodule.coe_zero]
    rw [Submodule.coe_sum] at h_sum_val
    simp only [Submodule.coe_smul] at h_sum_val
    have h_smul : ∀ i, (g i / S) • p i = S⁻¹ • (g i • p i) := by
      intro i
      rw [div_eq_inv_mul, mul_smul, smul_smul, mul_comm]
    simp_rw [h_smul]
    rw [← Finset.smul_sum, h_sum_val, smul_zero]

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
  classical
  let s : Finset ι := Finset.image e Finset.univ
  have hs_card : s.card = k := by
    rw [Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fin]
  have hcompl_card : sᶜ.card = Fintype.card ι - k := by
    rw [Finset.card_compl, hs_card]
  have h_rem : r - k ≤ sᶜ.card := by
    rw [hcompl_card]
    exact Nat.sub_le_sub_right hcard k
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq h_rem
  let e' : Fin (r - k) ≃ t := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, ht_card]) |>.symm
  let f2 : Fin (r - k) → ι := fun i => (e' i).val
  have hf2_inj : Function.Injective f2 := by
    intro i j h
    have h'' : e' i = e' j := Subtype.ext h
    exact e'.injective h''
  have h_disj : ∀ i j, e i ≠ f2 j := by
    intro i j h
    have h_in_s : e i ∈ s := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have h_in_t : f2 j ∈ t := (e' j).2
    have h_in_sc : f2 j ∈ sᶜ := ht_sub h_in_t
    rw [Finset.mem_compl] at h_in_sc
    rw [h] at h_in_s
    exact h_in_sc h_in_s
  let g0 : Fin k ⊕ Fin (r - k) → ι := Sum.elim e f2
  have hg0_inj : Function.Injective g0 := by
    rintro (i1|j1) (i2|j2) h
    · dsimp [g0] at h
      rw [he h]
    · dsimp [g0] at h
      exact False.elim (h_disj i1 j2 h)
    · dsimp [g0] at h
      exact False.elim (h_disj i2 j1 h.symm)
    · dsimp [g0] at h
      rw [hf2_inj h]
  have hkr : k + (r - k) = r := Nat.add_sub_of_le hk
  let g : Fin r → ι := fun i => g0 (finSumFinEquiv.symm (Fin.cast hkr.symm i))
  have hg_inj : Function.Injective g := by
    intro i j h
    dsimp [g] at h
    have h1 := hg0_inj h
    have h2 := finSumFinEquiv.symm.injective h1
    have h3 := Fin.cast_injective hkr.symm h2
    exact h3
  have hg_e : ∀ i : Fin k, g (Fin.castLE hk i) = e i := by
    intro i
    dsimp [g, g0]
    have h1 : Fin.cast hkr.symm (Fin.castLE hk i) = Fin.castAdd (r - k) i := by ext; rfl
    rw [h1, ← finSumFinEquiv_apply_left, finSumFinEquiv.symm_apply_apply]
    rfl
  have h_li : LinearIndependent ℝ (u ∘ g) := hgen g hg_inj
  have h_li_sub : LinearIndependent ℝ ((u ∘ g) ∘ Fin.castLE hk) :=
    LinearIndependent.comp h_li (Fin.castLE hk) (Fin.castLE_injective hk)
  have h_eq : (u ∘ g) ∘ Fin.castLE hk = u ∘ e := by
    ext i
    dsimp
    rw [hg_e i]
  rwa [h_eq] at h_li_sub

private lemma exists_injective_of_le_ncard {ι : Type*} [Fintype ι] {S : Set ι} {k : ℕ} (hk : k ≤ S.ncard) :
    ∃ e : Fin k → ι, Function.Injective e ∧ ∀ i, e i ∈ S := by
  classical
  have hfin : S.Finite := Set.toFinite S
  rw [Set.ncard_eq_toFinset_card S hfin] at hk
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hk
  obtain ⟨e⟩ := Fintype.truncEquivFin T
  have hTcard' : Fintype.card T = k := by
    rw [Fintype.card_coe]
    exact hTcard
  let e' : Fin k → T := fun i => (e.symm (Fin.cast hTcard'.symm i))
  use fun i => (e' i).val
  refine ⟨?_, ?_⟩
  · intro i j hij
    have h1 : e' i = e' j := Subtype.ext hij
    dsimp [e'] at h1
    have h2 := e.symm.injective h1
    have h3 := Fin.ext_iff.mp (Fin.cast_injective _ h2)
    exact Fin.ext h3
  · intro i
    have hT := hTS (e' i).2
    rwa [Set.Finite.mem_toFinset] at hT

private lemma l1_norm_sum_sub_le {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u p : Fin k → V) (c : Fin k → ℝ) (hc_sum : ∑ i, c i • p i = 0) (hc1 : ∑ i, |c i| = 1)
    (δ : ℝ) (hδ : ∀ i, ‖u i - p i‖ ≤ δ) :
    ‖∑ i, c i • u i‖ ≤ δ := by
  have h_eq : ∑ i, c i • u i = ∑ i, c i • (u i - p i) := by
    rw [← sub_zero (∑ i, c i • u i), ← hc_sum, ← Finset.sum_sub_distrib]
    congr 1
    ext i
    rw [smul_sub]
  rw [h_eq]
  calc
    ‖∑ i, c i • (u i - p i)‖ ≤ ∑ i, ‖c i • (u i - p i)‖ := norm_sum_le _ _
    _ = ∑ i, |c i| * ‖u i - p i‖ := by
      congr 1; ext i; rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |c i| * δ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hδ i) (abs_nonneg _)
    _ = δ := by
      rw [← Finset.sum_mul, hc1, one_mul]

private noncomputable def marginVal {r : ℕ} {ι : Type*} [Fintype ι]
    (hcard : r ≤ Fintype.card ι)
    (u : ι → EuclideanSpace ℝ (Fin r))
    (hgen : InGeneralPosition u)
    (p : (k : Fin (r + 1)) × (Fin k → ι)) : ℝ :=
  open Classical in
  if he : Function.Injective p.2 then
    (exists_l1_min_of_linearIndependent
      (linearIndependent_selection_of_inGeneralPosition hgen hcard p.1.is_le p.2 he)).choose
  else 1

private lemma marginVal_pos {r : ℕ} {ι : Type*} [Fintype ι]
    (hcard : r ≤ Fintype.card ι)
    (u : ι → EuclideanSpace ℝ (Fin r))
    (hgen : InGeneralPosition u)
    (p : (k : Fin (r + 1)) × (Fin k → ι)) :
    0 < marginVal hcard u hgen p := by
  unfold marginVal
  split_ifs with he
  · exact (exists_l1_min_of_linearIndependent
      (linearIndependent_selection_of_inGeneralPosition hgen hcard p.1.is_le p.2 he)).choose_spec.1
  · exact zero_lt_one

private lemma marginVal_le {r : ℕ} {ι : Type*} [Fintype ι]
    (hcard : r ≤ Fintype.card ι)
    (u : ι → EuclideanSpace ℝ (Fin r))
    (hgen : InGeneralPosition u)
    (k : ℕ) (hk : k ≤ r) (e : Fin k → ι) (he : Function.Injective e)
    (c : Fin k → ℝ) (hc : ∑ i, |c i| = 1) :
    marginVal hcard u hgen ⟨⟨k, Nat.lt_succ_of_le hk⟩, e⟩ ≤ ‖∑ i, c i • u (e i)‖ := by
  unfold marginVal
  rw [dif_pos he]
  exact (exists_l1_min_of_linearIndependent
    (linearIndependent_selection_of_inGeneralPosition hgen hcard hk e he)).choose_spec.2 c hc

private lemma exists_margin_delta {r : ℕ} {ι : Type*} [Fintype ι]
    (hcard : r ≤ Fintype.card ι)
    {u : ι → EuclideanSpace ℝ (Fin r)}
    (hgen : InGeneralPosition u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (k : ℕ) (hk : k ≤ r) (e : Fin k → ι) (he : Function.Injective e)
        (c : Fin k → ℝ) (hc : ∑ i, |c i| = 1),
        δ < ‖∑ i, c i • u (e i)‖ := by
  classical
  haveI : Nonempty ((k : Fin (r + 1)) × (Fin k → ι)) := ⟨⟨0, fun i => i.elim0⟩⟩
  set S : Finset ((k : Fin (r + 1)) × (Fin k → ι)) := Finset.univ
  have hS_nonempty : S.Nonempty := Finset.univ_nonempty
  set f := marginVal hcard u hgen
  set η_min := (S.image f).min' (by simpa using hS_nonempty)
  have hη_pos : 0 < η_min := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨p, _, rfl⟩ := hy
    exact marginVal_pos hcard u hgen p
  set δ := min (1/2) (η_min / 2)
  have hδ_pos : 0 < δ := lt_min (by norm_num) (half_pos hη_pos)
  have hδ_le1 : δ ≤ 1 := by
    calc δ ≤ 1/2 := min_le_left _ _
    _ ≤ 1 := by norm_num
  refine ⟨δ, hδ_pos, hδ_le1, ?_⟩
  intro k hk e he c hc
  have hp : ⟨⟨k, Nat.lt_succ_of_le hk⟩, e⟩ ∈ S := Finset.mem_univ _
  have h_min_le : η_min ≤ f ⟨⟨k, Nat.lt_succ_of_le hk⟩, e⟩ := by
    apply Finset.min'_le
    rw [Finset.mem_image]
    exact ⟨_, hp, rfl⟩
  have h_le := marginVal_le hcard u hgen k hk e he c hc
  calc δ ≤ η_min / 2 := min_le_right _ _
  _ < η_min := half_lt_self hη_pos
  _ ≤ f ⟨⟨k, Nat.lt_succ_of_le hk⟩, e⟩ := h_min_le
  _ ≤ ‖∑ i, c i • u (e i)‖ := h_le

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
  obtain ⟨δ, hδ_pos, hδ_le1, hδ_margin⟩ := exists_margin_delta hcard hgen
  refine ⟨δ, hδ_pos, hδ_le1, ?_⟩
  intro W hW
  by_contra hc
  have hc_gt : Module.finrank ℝ W < ({x : ι | ∃ p ∈ W, ‖u x - p‖ < δ} : Set ι).ncard := not_le.mp hc
  set w := Module.finrank ℝ W
  have hw_le : w + 1 ≤ ({x : ι | ∃ p ∈ W, ‖u x - p‖ < δ} : Set ι).ncard := hc_gt
  obtain ⟨e, he_inj, he_mem⟩ := exists_injective_of_le_ncard hw_le
  have hw1_le_r : w + 1 ≤ r := hW
  have hp_ex : ∀ i : Fin (w + 1), ∃ p ∈ W, ‖u (e i) - p‖ < δ := fun i => he_mem i
  choose p hp_in hp_dist using hp_ex
  obtain ⟨c, hc1, hc_sum⟩ := exists_l1_relation_of_finrank_lt W (le_refl w) p hp_in
  have h_bound : ‖∑ i, c i • u (e i)‖ ≤ δ := by
    apply l1_norm_sum_sub_le (u ∘ e) p c hc_sum hc1 δ
    intro i
    exact le_of_lt (hp_dist i)
  have h_margin := hδ_margin (w + 1) hw1_le_r e he_inj c hc1
  linarith

/-- **Real positive-definite ⇒ Hermitian.**  Over `ℝ` conjugation is trivial,
so the symmetry field `ForsterPosDef.1` already yields `Matrix.IsHermitian`.
Proved helper feeding the eigen-data extraction. -/
lemma forsterPosDef_isHermitian {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ}
    (hP : ForsterPosDef P) : P.IsHermitian := by
  ext i j
  change star (P j i) = P i j
  simp [hP.1 i j]

/-- **P5.3a-M5b (diagonalization leaf).**  An orthonormal spanning eigen-family
`(e, lam)` diagonalizes the quadratic form.  Start: build the orthonormal basis
`B := OrthonormalBasis.mk he (le_of_eq hspan.symm)` and expand
`z = ∑ i, ⟪e i, z⟫_ℝ • e i` (`B.sum_repr`, `OrthonormalBasis.repr_apply_apply`,
`OrthonormalBasis.coe_mk`, as in `forsterQuad_ge_of_far`).  Unfold `forsterQuad`
to `(WithLp.equiv 2 _ z) ⬝ᵥ (P *ᵥ (WithLp.equiv 2 _ z))`, push `P` through the
expansion with `heig` (`mulVec_sum`, `mulVec_smul`), and collapse the double sum
by orthonormality (`WithLp.equiv 2 _ (e i) ⬝ᵥ WithLp.equiv 2 _ (e j) = ⟪e i,e j⟫_ℝ`,
zero off-diagonal; `EuclideanSpace.inner_eq_star_dotProduct`, `star` on `ℝ` is `id`).
Note `⟪e i, z⟫_ℝ = WithLp.equiv 2 _ (e i) ⬝ᵥ WithLp.equiv 2 _ z`. -/
lemma forsterQuad_eq_sum_sq_eigen {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ}
    {e : Fin r → EuclideanSpace ℝ (Fin r)} {lam : Fin r → ℝ}
    (he : Orthonormal ℝ e) (hspan : Submodule.span ℝ (Set.range e) = ⊤)
    (heig : ∀ i, P *ᵥ ⇑(e i) = lam i • ⇑(e i)) :
    ∀ z : EuclideanSpace ℝ (Fin r), forsterQuad P z = ∑ i, lam i * ⟪e i, z⟫_ℝ ^ 2 := by
  intro z
  -- Expand `z` in the orthonormal eigenbasis.
  have hz : z = ∑ i, ⟪e i, z⟫_ℝ • e i := by
    let B := OrthonormalBasis.mk he (le_of_eq hspan.symm)
    have h_repr := B.sum_repr z
    dsimp [B] at h_repr
    simp_rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_mk] at h_repr
    exact h_repr.symm
  -- `P` scales each eigenvector `e i` by `lam i`.
  have hTe : ∀ i, Matrix.toLpLin 2 2 P (e i) = lam i • e i := by
    intro i
    apply WithLp.ofLp_injective 2
    rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, heig i]
    rfl
  -- Rewrite the quadratic form as an inner product `⟪z, P z⟫`.
  have hquad_inner : forsterQuad P z = ⟪z, Matrix.toLpLin 2 2 P z⟫_ℝ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply]
    show (⇑z : Fin r → ℝ) ⬝ᵥ (P *ᵥ ⇑z) = (P *ᵥ ⇑z) ⬝ᵥ ⇑z
    rw [dotProduct_comm]
  rw [hquad_inner]
  conv_lhs => rw [hz]
  rw [map_sum]
  simp_rw [map_smul, hTe, smul_smul]
  rw [he.inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [conj_trivial]
  ring

/-- **P5.3a-M5c (eigenvalue positivity leaf).**  Eigenvalues of a `ForsterPosDef`
matrix are positive.  Start: `e i ≠ 0` since `‖e i‖ = 1` (orthonormality `he`);
`forsterQuad P (e i) = WithLp.equiv 2 _ (e i) ⬝ᵥ (P *ᵥ WithLp.equiv 2 _ (e i))
= WithLp.equiv 2 _ (e i) ⬝ᵥ (lam i • WithLp.equiv 2 _ (e i))` (`heig`)
`= lam i * ‖e i‖ ^ 2 = lam i`, while `0 < forsterQuad P (e i)` by `hP.2` at the
nonzero `e i`.  Mirrors the positivity block of `exists_forster_sqrt`. -/
lemma eigenvalue_pos_of_eigen {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ}
    (hP : ForsterPosDef P) {e : Fin r → EuclideanSpace ℝ (Fin r)} {lam : Fin r → ℝ}
    (he : Orthonormal ℝ e)
    (heig : ∀ i, P *ᵥ ⇑(e i) = lam i • ⇑(e i)) :
    ∀ i, 0 < lam i := by
  intro i
  have hnorm : ‖e i‖ = 1 := he.1 i
  have hne : (⇑(e i) : Fin r → ℝ) ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 (he.ne_zero i)
  have hself : (⇑(e i) : Fin r → ℝ) ⬝ᵥ (⇑(e i)) = 1 := by
    have h := EuclideanSpace.inner_eq_star_dotProduct (e i) (e i)
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow] at h
    rw [star_trivial] at h
    exact h.symm
  have hval : (⇑(e i) : Fin r → ℝ) ⬝ᵥ (P *ᵥ ⇑(e i)) = lam i := by
    rw [heig i, dotProduct_smul, smul_eq_mul, hself, mul_one]
  have hpos := hP.2 (⇑(e i)) hne
  rwa [hval] at hpos

/-- **P5.3a-M5a (eigen-data extraction leaf).**  A `ForsterPosDef` matrix has an
orthonormal spanning eigen-family whose eigenvalue product is the determinant.
Start: `hHerm := forsterPosDef_isHermitian hP`; take `e := ⇑ hHerm.eigenvectorBasis`,
`lam := hHerm.eigenvalues`.  Orthonormality is `hHerm.eigenvectorBasis.orthonormal`;
`span = ⊤` from the basis (`hHerm.eigenvectorBasis.toBasis.span_eq`, with
`Set.range ⇑(·.toBasis) = Set.range ⇑·`); the eigen-equation is
`hHerm.mulVec_eigenvectorBasis`; and `∏ lam = det` is
`hHerm.det_eq_prod_eigenvalues` (over `ℝ`, `RCLike.ofReal` is `id`). -/
lemma exists_eigen_of_forsterPosDef {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ}
    (hP : ForsterPosDef P) :
    ∃ (e : Fin r → EuclideanSpace ℝ (Fin r)) (lam : Fin r → ℝ),
      Orthonormal ℝ e ∧ Submodule.span ℝ (Set.range e) = ⊤ ∧
      (∀ i, P *ᵥ ⇑(e i) = lam i • ⇑(e i)) ∧
      ∏ i, lam i = P.det := by
  have hHerm := forsterPosDef_isHermitian hP
  refine ⟨⇑hHerm.eigenvectorBasis, hHerm.eigenvalues,
    hHerm.eigenvectorBasis.orthonormal, ?_, hHerm.mulVec_eigenvectorBasis, ?_⟩
  · have h := hHerm.eigenvectorBasis.toBasis.span_eq
    rwa [OrthonormalBasis.coe_toBasis] at h
  · rw [hHerm.det_eq_prod_eigenvalues]
    norm_cast

/-- **P5.3a-M5d (sorting leaf).**  Reindex eigen-data by the sorting permutation
so the eigenvalues become nondecreasing, transporting every other invariant.
Start: `σ := Tuple.sort lam`, `e' := fun i => e (σ i)`, `lam' := fun i => lam (σ i)`.
`Monotone lam'` is `Tuple.monotone_sort lam`; `Orthonormal ℝ e'` is
`he.comp σ σ.injective`; `Set.range e' = Set.range e` (σ surjective; `Set.range_comp`
+ `σ.surjective.range_eq`) transports the span; positivity, `∏`, and the quadratic
identity transport by reindexing the finite product/sum over `σ`
(`Equiv.prod_comp`, `Fintype.sum_equiv σ`). -/
lemma exists_sorted_of_eigen_data {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ}
    {e : Fin r → EuclideanSpace ℝ (Fin r)} {lam : Fin r → ℝ}
    (he : Orthonormal ℝ e) (hspan : Submodule.span ℝ (Set.range e) = ⊤)
    (hpos : ∀ i, 0 < lam i) (hprod : ∏ i, lam i = P.det)
    (hquad : ∀ z : EuclideanSpace ℝ (Fin r), forsterQuad P z = ∑ i, lam i * ⟪e i, z⟫_ℝ ^ 2) :
    ∃ (e' : Fin r → EuclideanSpace ℝ (Fin r)) (lam' : Fin r → ℝ),
      Orthonormal ℝ e' ∧ Submodule.span ℝ (Set.range e') = ⊤ ∧
      Monotone lam' ∧ (∀ i, 0 < lam' i) ∧ ∏ i, lam' i = P.det ∧
      ∀ z : EuclideanSpace ℝ (Fin r),
        forsterQuad P z = ∑ i, lam' i * ⟪e' i, z⟫_ℝ ^ 2 := by
  set σ := Tuple.sort lam with hσ
  refine ⟨fun i => e (σ i), fun i => lam (σ i), he.comp _ σ.injective, ?_,
    Tuple.monotone_sort lam, fun i => hpos (σ i), ?_, ?_⟩
  · -- span invariance under the reindexing (σ is a bijection)
    have hrange : Set.range (fun i => e (σ i)) = Set.range e := by
      rw [show (fun i => e (σ i)) = e ∘ ⇑σ from rfl, Set.range_comp,
        σ.surjective.range_eq, Set.image_univ]
    rw [hrange]; exact hspan
  · -- eigenvalue product is permutation-invariant
    rw [Equiv.prod_comp σ lam]; exact hprod
  · -- the diagonalization transports term-by-term along σ
    intro z
    rw [hquad z]
    exact (Equiv.sum_comp σ (fun j => lam j * ⟪e j, z⟫_ℝ ^ 2)).symm

/-- Sorted spectral data for a `ForsterPosDef` matrix: an orthonormal
spanning eigen-family with nondecreasing positive eigenvalues whose product
is the determinant, diagonalizing the quadratic form.

**Assembly (sorry-free).**  Extract the eigen-family and its eigenvalue product
(`exists_eigen_of_forsterPosDef`); diagonalize the quadratic form
(`forsterQuad_eq_sum_sq_eigen`); positivity of the eigenvalues
(`eigenvalue_pos_of_eigen`); then sort to nondecreasing eigenvalues while
transporting every invariant (`exists_sorted_of_eigen_data`). -/
lemma exists_sorted_eigen_data {r : ℕ} (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : ForsterPosDef P) :
    ∃ (e : Fin r → EuclideanSpace ℝ (Fin r)) (lam : Fin r → ℝ),
      Orthonormal ℝ e ∧ Submodule.span ℝ (Set.range e) = ⊤ ∧
      Monotone lam ∧ (∀ i, 0 < lam i) ∧ ∏ i, lam i = P.det ∧
      ∀ z : EuclideanSpace ℝ (Fin r),
        forsterQuad P z = ∑ i, lam i * ⟪e i, z⟫_ℝ ^ 2 := by
  obtain ⟨e, lam, he, hspan, heig, hprod⟩ := exists_eigen_of_forsterPosDef hP
  have hquad := forsterQuad_eq_sum_sq_eigen he hspan heig
  have hpos := eigenvalue_pos_of_eigen hP he heig
  exact exists_sorted_of_eigen_data he hspan hpos hprod hquad

private lemma norm_sq_sum_eq_sum_sq {r : ℕ} (e : Fin r → EuclideanSpace ℝ (Fin r)) (he : Orthonormal ℝ e)
    (f : Fin r → ℝ) (s : Finset (Fin r)) :
    ‖∑ i ∈ s, f i • e i‖^2 = ∑ i ∈ s, (f i)^2 := by
  have h_inner := he.inner_sum f f s
  have h_norm : ‖∑ i ∈ s, f i • e i‖^2 = ⟪∑ i ∈ s, f i • e i, ∑ i ∈ s, f i • e i⟫_ℝ := by
    rw [real_inner_self_eq_norm_mul_norm, sq]
  rw [h_norm, h_inner]
  congr 1
  ext i
  simp [sq]

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
  let B := OrthonormalBasis.mk he (le_of_eq hspan.symm)
  let p := ∑ i ∈ Finset.univ.filter (fun i => i < k), ⟪e i, z⟫_ℝ • e i
  have hp : p ∈ Submodule.span ℝ (e '' {i | i < k}) := by
    dsimp [p]
    apply Submodule.sum_mem
    intro i hi
    rw [Finset.mem_filter] at hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_image_of_mem e hi.2
  have h_zp : z - p = ∑ i ∈ Finset.univ.filter (fun i => ¬ i < k), ⟪e i, z⟫_ℝ • e i := by
    dsimp [p]
    have h_sum : z = ∑ i, ⟪e i, z⟫_ℝ • e i := by
      have h_repr := B.sum_repr z
      dsimp [B] at h_repr
      simp_rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_mk] at h_repr
      exact h_repr.symm
    nth_rw 1 [h_sum]
    have h_sub : Finset.filter (fun i => i < k) Finset.univ ⊆ Finset.univ := Finset.filter_subset _ _
    rw [← Finset.sum_sdiff (f := fun i => ⟪e i, z⟫_ℝ • e i) h_sub]
    have h_sdiff : Finset.univ \ Finset.univ.filter (fun i => i < k) = Finset.univ.filter (fun i => ¬ i < k) := by
      ext i
      simp
    rw [h_sdiff]
    exact add_sub_cancel_right _ _
  have h_norm_zp : ‖z - p‖^2 = ∑ i ∈ Finset.univ.filter (fun i => ¬ i < k), ⟪e i, z⟫_ℝ ^ 2 := by
    rw [h_zp]
    exact norm_sq_sum_eq_sum_sq e he (fun i => ⟪e i, z⟫_ℝ) (Finset.univ.filter (fun i => ¬ i < k))
  have h_δ_le : δ^2 ≤ ‖z - p‖^2 := by
    have h_le := hfar p hp
    nlinarith
  have h_quad_split : forsterQuad P z = (∑ i ∈ Finset.univ.filter (fun i => i < k), lam i * ⟪e i, z⟫_ℝ ^ 2) +
      (∑ i ∈ Finset.univ.filter (fun i => ¬ i < k), lam i * ⟪e i, z⟫_ℝ ^ 2) := by
    rw [hquad]
    have h_sub : Finset.filter (fun i => i < k) Finset.univ ⊆ Finset.univ := Finset.filter_subset _ _
    have h_split := (Finset.sum_sdiff (f := fun i => lam i * ⟪e i, z⟫_ℝ ^ 2) h_sub).symm
    have h_sdiff : Finset.univ \ Finset.univ.filter (fun i => i < k) = Finset.univ.filter (fun i => ¬ i < k) := by
      ext i
      simp
    rw [h_sdiff] at h_split
    rw [h_split, add_comm]
  have h_low_nonneg : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => i < k), lam i * ⟪e i, z⟫_ℝ ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (le_of_lt (hpos i)) (sq_nonneg _)
  have h_high_bound : lam k * (∑ i ∈ Finset.univ.filter (fun i => ¬ i < k), ⟪e i, z⟫_ℝ ^ 2) ≤
      ∑ i ∈ Finset.univ.filter (fun i => ¬ i < k), lam i * ⟪e i, z⟫_ℝ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_filter] at hi
    have hik : k ≤ i := not_lt.mp hi.2
    have h_lam_le : lam k ≤ lam i := hmono hik
    exact mul_le_mul_of_nonneg_right h_lam_le (sq_nonneg _)
  have h_lam_delta : lam k * δ^2 ≤ lam k * (∑ i ∈ Finset.univ.filter (fun i => ¬ i < k), ⟪e i, z⟫_ℝ ^ 2) := by
    rw [← h_norm_zp]
    exact mul_le_mul_of_nonneg_left h_δ_le (le_of_lt (hpos k))
  linarith

open Finset in
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
  let F : ℕ → ℝ := fun n => if h : n < m + 1 then f ⟨n, h⟩ else f (Fin.last m)
  have hF (n : Fin (m + 1)) : F n = f n := dif_pos n.isLt
  have hF_last : F m = f (Fin.last m) := dif_pos (Nat.lt_succ_self m)
  
  have hF_mono : Monotone F := by
    intro a b hab
    dsimp [F]
    split_ifs with ha hb hb
    · exact hf (Fin.mk_le_mk.mpr hab)
    · exact hf (Fin.le_last _)
    · linarith
    · rfl
    
  let d : ℕ → ℝ := fun j => F (j + 1) - F j
  have hd_nonneg (j : ℕ) : 0 ≤ d j := sub_nonneg.mpr (hF_mono (Nat.le_succ j))
  
  have telescope : ∀ l ≤ m, F m - F l = ∑ j ∈ range m, if l ≤ j then d j else 0 := by
    intro l hl
    have h1 : ∑ k ∈ range m, (F (k + 1) - F k) = F m - F 0 := sum_range_sub F m
    have h2 : ∑ k ∈ range l, (F (k + 1) - F k) = F l - F 0 := sum_range_sub F l
    have h3 : ∑ j ∈ Ico l m, d j = F m - F l := by
      dsimp [d]
      rw [sum_Ico_eq_sub _ hl, h1, h2]
      ring
    have h4 : (range m).filter (fun j => l ≤ j) = Ico l m := by
      ext x
      simp
      omega
    rw [← h3, ← sum_filter, ← h4]
    
  have h_sum_x : ∑ x : ι, (F m - F (level x)) = ∑ j ∈ range m, ({x : ι | (level x : ℕ) ≤ j} : Set ι).ncard * d j := by
    calc ∑ x : ι, (F m - F (level x))
      _ = ∑ x : ι, ∑ j ∈ range m, if (level x : ℕ) ≤ j then d j else 0 := by
        apply sum_congr rfl
        intro x _
        exact telescope (level x : ℕ) (Fin.is_le (level x))
      _ = ∑ j ∈ range m, ∑ x : ι, if (level x : ℕ) ≤ j then d j else 0 := sum_comm
      _ = ∑ j ∈ range m, (univ.filter (fun x : ι => (level x : ℕ) ≤ j)).card * d j := by
        apply sum_congr rfl
        intro j _
        rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
      _ = ∑ j ∈ range m, ({x : ι | (level x : ℕ) ≤ j} : Set ι).ncard * d j := by
        apply sum_congr rfl
        intro j _
        have h1 : Fintype.card {x : ι // (level x : ℕ) ≤ j} = Nat.card {x : ι // (level x : ℕ) ≤ j} := by
          exact Nat.card_eq_fintype_card.symm
        have h2 : (univ.filter (fun x : ι => (level x : ℕ) ≤ j)).card = Fintype.card {x : ι // (level x : ℕ) ≤ j} := by
          exact (Fintype.card_subtype _).symm
        have h3 : Nat.card {x : ι // (level x : ℕ) ≤ j} = ({x : ι | (level x : ℕ) ≤ j} : Set ι).ncard := by
          exact Set.ncard_def _
        rw [h2, h1, h3]
        
  have h_bound : ∑ j ∈ range m, (({x : ι | (level x : ℕ) ≤ j} : Set ι).ncard : ℝ) * d j ≤ ∑ j ∈ range m, (j + 1 : ℝ) * d j := by
    apply sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_right _ (hd_nonneg j)
    have hj_lt : j + 1 < m + 1 := by
      rw [mem_range] at hj
      omega
    have H := hcount ⟨j + 1, hj_lt⟩
    have heq : {x : ι | (level x : ℕ) ≤ j} = {x : ι | level x < (⟨j + 1, hj_lt⟩ : Fin (m + 1))} := by
      ext x
      simp [Fin.lt_def]
    rw [heq]
    exact_mod_cast H

  have h_sum_k : ∑ k : Fin (m + 1), (F m - f k) = ∑ j ∈ range m, (j + 1 : ℝ) * d j := by
    calc ∑ k : Fin (m + 1), (F m - f k)
      _ = ∑ k : Fin (m + 1), (F m - F (k : ℕ)) := by
        apply sum_congr rfl
        intro k _
        rw [hF k]
      _ = ∑ k : Fin (m + 1), ∑ j ∈ range m, if (k : ℕ) ≤ j then d j else 0 := by
        apply sum_congr rfl
        intro k _
        exact telescope (k : ℕ) (Fin.is_le k)
      _ = ∑ j ∈ range m, ∑ k : Fin (m + 1), if (k : ℕ) ≤ j then d j else 0 := sum_comm
      _ = ∑ j ∈ range m, (univ.filter (fun k : Fin (m + 1) => (k : ℕ) ≤ j)).card * d j := by
        apply sum_congr rfl
        intro j _
        rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
      _ = ∑ j ∈ range m, (j + 1 : ℝ) * d j := by
        apply sum_congr rfl
        intro j hj
        rw [mem_range] at hj
        have h1 : (univ.filter (fun k : Fin (m + 1) => (k : ℕ) ≤ j)).image Fin.val = range (j + 1) := by
          ext x
          simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
          constructor
          · rintro ⟨a, ha, rfl⟩
            omega
          · intro hx
            have hx' : x < m + 1 := by omega
            refine ⟨⟨x, hx'⟩, by exact Nat.le_of_lt_succ hx, rfl⟩
        have h2 : (univ.filter (fun k : Fin (m + 1) => (k : ℕ) ≤ j)).card = j + 1 := by
          rw [← card_range (j + 1), ← h1, card_image_of_injective]
          exact Fin.val_injective
        rw [h2]
        have heq : ((j + 1 : ℕ) : ℝ) = (j + 1 : ℝ) := by push_cast; rfl
        rw [heq]

  have main : ∑ x : ι, (F m - f (level x)) ≤ ∑ k : Fin (m + 1), (F m - f k) := by
    have hF_level (x : ι) : F m - f (level x) = F m - F (level x) := by rw [hF (level x)]
    simp_rw [hF_level]
    rw [h_sum_x, h_sum_k]
    exact h_bound
    
  have hL_x : ∑ x : ι, (F m - f (level x)) = (Fintype.card ι : ℝ) * f (Fin.last m) - ∑ x, f (level x) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← hF_last]
    rfl
  have hL_k : ∑ k : Fin (m + 1), (F m - f k) = (m + 1 : ℝ) * f (Fin.last m) - ∑ k, f k := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← hF_last]
    have : (univ : Finset (Fin (m + 1))).card = m + 1 := Fintype.card_fin (m + 1)
    rw [this]
    push_cast
    rfl
    
  rw [hL_x, hL_k] at main
  linarith

open scoped Classical

private lemma sum_inner_sq_eq_one {r : ℕ} {e : Fin r → EuclideanSpace ℝ (Fin r)}
    (he : Orthonormal ℝ e) (hspan : Submodule.span ℝ (Set.range e) = ⊤)
    (z : EuclideanSpace ℝ (Fin r)) (hz : ‖z‖ = 1) :
    ∑ i, ⟪e i, z⟫_ℝ ^ 2 = 1 := by
  let b : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)) :=
    OrthonormalBasis.mk he (ge_of_eq hspan)
  have h_repr (i : Fin r) : (b.repr z).ofLp i = ⟪e i, z⟫_ℝ := by
    have h1 := b.repr_apply_apply z i
    have h2 : b i = e i := by
      change ⇑(OrthonormalBasis.mk he (ge_of_eq hspan)) i = e i
      rw [OrthonormalBasis.coe_mk]
    rw [h2] at h1
    exact h1
  have h_norm : ‖b.repr z‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, hz]
  have h_sq : ‖b.repr z‖ ^ 2 = 1 := by rw [h_norm, one_pow]
  have h_norm_sq := EuclideanSpace.real_norm_sq_eq (b.repr z)
  rw [h_sq] at h_norm_sq
  simp_rw [h_repr] at h_norm_sq
  exact h_norm_sq.symm

private lemma forsterQuad_le_top_eigenvalue {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ}
    {e : Fin r → EuclideanSpace ℝ (Fin r)} {lam : Fin r → ℝ}
    (he : Orthonormal ℝ e) (hspan : Submodule.span ℝ (Set.range e) = ⊤)
    (hmono : Monotone lam)
    (hquad : ∀ z, forsterQuad P z = ∑ i, lam i * ⟪e i, z⟫_ℝ ^ 2)
    (m : ℕ) (hr : r = m + 1)
    (z : EuclideanSpace ℝ (Fin r)) (hz : ‖z‖ = 1) :
    forsterQuad P z ≤ lam (Fin.cast hr.symm (Fin.last m)) := by
  rw [hquad z]
  have h_le (i : Fin r) : lam i ≤ lam (Fin.cast hr.symm (Fin.last m)) := by
    apply hmono
    rw [← Fin.val_fin_le]
    subst hr
    exact Fin.le_last i
  have h_sum_le : ∑ i, lam i * ⟪e i, z⟫_ℝ ^ 2 ≤ ∑ i, lam (Fin.cast hr.symm (Fin.last m)) * ⟪e i, z⟫_ℝ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (h_le i) (sq_nonneg _)
  rw [← Finset.mul_sum, sum_inner_sq_eq_one he hspan z hz, mul_one] at h_sum_le
  exact h_sum_le

private lemma sum_log_lam_eq_zero {r : ℕ} {lam : Fin r → ℝ} (hpos : ∀ i, 0 < lam i)
    (hprod : ∏ i, lam i = 1) :
    ∑ i, Real.log (lam i) = 0 := by
  rw [← Real.log_prod (fun i _ => ne_of_gt (hpos i)), hprod, Real.log_one]

private lemma mem_far_zero {m : ℕ} {e : Fin (m + 1) → EuclideanSpace ℝ (Fin (m + 1))}
    {u : EuclideanSpace ℝ (Fin (m + 1))} (hu : ‖u‖ = 1) {δ : ℝ} (hδ : δ ≤ 1) :
    (0 : Fin (m + 1)) ∈ { k : Fin (m + 1) | ∀ p ∈ Submodule.span ℝ (e '' {i | i < k}), δ ≤ ‖u - p‖ } := by
  simp only [Set.mem_setOf_eq]
  intro p hp
  have h_empty : {i : Fin (m + 1) | i < (0 : Fin (m + 1))} = ∅ := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact Fin.zero_le i
  rw [h_empty, Set.image_empty, Submodule.span_empty] at hp
  have hp0 : p = 0 := hp
  rw [hp0, sub_zero, hu]
  exact hδ

private lemma level_lt_imp_near {m : ℕ} {ι : Type*}
    {e : Fin (m + 1) → EuclideanSpace ℝ (Fin (m + 1))}
    {u : ι → EuclideanSpace ℝ (Fin (m + 1))}
    {δ : ℝ} (x : ι) (k level_x : Fin (m + 1))
    (S_x : Set (Fin (m + 1))) (hS : S_x = { k | ∀ p ∈ Submodule.span ℝ (e '' {i | i < k}), δ ≤ ‖u x - p‖ })
    (hnonempty : (Finset.univ.filter (· ∈ S_x)).Nonempty)
    (hlevel : level_x = Finset.max' (Finset.univ.filter (· ∈ S_x)) hnonempty)
    (hlt : level_x < k) :
    ∃ p ∈ Submodule.span ℝ (e '' {i | i < k}), ‖u x - p‖ < δ := by
  have hk_not_mem : k ∉ Finset.univ.filter (· ∈ S_x) := by
    intro hk
    have h_le := Finset.le_max' (Finset.univ.filter (· ∈ S_x)) k hk
    rw [← hlevel] at h_le
    exact not_le.mpr hlt h_le
  rw [Finset.mem_filter] at hk_not_mem
  have hk_S : k ∉ S_x := by
    intro hkS
    exact hk_not_mem ⟨Finset.mem_univ _, hkS⟩
  rw [hS, Set.mem_setOf_eq] at hk_S
  push Not at hk_S
  exact hk_S

private lemma finrank_span_low_lt {m : ℕ}
    {e : Fin (m + 1) → EuclideanSpace ℝ (Fin (m + 1))}
    (k : Fin (m + 1)) :
    Module.finrank ℝ (Submodule.span ℝ (e '' {i | i < k})) < m + 1 := by
  have h_span_eq : Submodule.span ℝ (e '' {i | i < k}) =
      Submodule.span ℝ (Finset.image e (Finset.Iio k) : Set (EuclideanSpace ℝ (Fin (m + 1)))) := by
    congr 1; ext x; simp
  rw [h_span_eq]
  have h_le := finrank_span_le_card (R := ℝ) (s := (Finset.image e (Finset.Iio k) : Set (EuclideanSpace ℝ (Fin (m + 1)))))
  have h_card_le : (Finset.image e (Finset.Iio k)).card ≤ k.val := by
    calc
      (Finset.image e (Finset.Iio k)).card ≤ (Finset.Iio k).card := Finset.card_image_le
      _ = k.val := by simp
  have h_le_k : Module.finrank ℝ (Submodule.span ℝ (Finset.image e (Finset.Iio k) : Set (EuclideanSpace ℝ (Fin (m + 1))))) ≤ k.val := by
    have h_toFinset : (Finset.image e (Finset.Iio k) : Set (EuclideanSpace ℝ (Fin (m + 1)))).toFinset = Finset.image e (Finset.Iio k) := by
      ext; simp
    rw [h_toFinset] at h_le
    exact le_trans h_le h_card_le
  exact lt_of_le_of_lt h_le_k k.is_lt

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
  obtain ⟨m, hr_eq⟩ : ∃ m, r = m + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hr)
  subst hr_eq
  obtain ⟨δ, hδ0, hδ1, hnear⟩ := card_near_subspace_le_finrank (le_of_lt hcard) hu hgen
  use δ, hδ0
  intro P hP hdet z hz
  obtain ⟨e, lam, he, hspan, hmono, hpos, hprod, hquad⟩ := exists_sorted_eigen_data P hP
  have hprod_one : ∏ i, lam i = 1 := hprod.trans hdet
  let S (x : ι) : Set (Fin (m + 1)) :=
    { k | ∀ p ∈ Submodule.span ℝ (e '' {i | i < k}), δ ≤ ‖u x - p‖ }
  have hnonempty (x : ι) : (Finset.univ.filter (· ∈ S x)).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_far_zero (hu x) hδ1⟩⟩
  let level (x : ι) : Fin (m + 1) :=
    Finset.max' (Finset.univ.filter (· ∈ S x)) (hnonempty x)
  have hlevel_mem (x : ι) : level x ∈ S x := by
    have h_mem := Finset.max'_mem (Finset.univ.filter (· ∈ S x)) (hnonempty x)
    exact (Finset.mem_filter.mp h_mem).2
  have hfar (x : ι) : ∀ p ∈ Submodule.span ℝ (e '' {i | i < level x}), δ ≤ ‖u x - p‖ :=
    hlevel_mem x
  have hquad_ge (x : ι) : lam (level x) * δ ^ 2 ≤ forsterQuad P (u x) :=
    forsterQuad_ge_of_far he hspan hmono hpos hquad (level x) (le_of_lt hδ0) (hfar x)
  have hcount (k : Fin (m + 1)) : ({x : ι | level x < k} : Set ι).ncard ≤ (k : ℕ) := by
    have hsub : {x : ι | level x < k} ⊆ {x : ι | ∃ p ∈ Submodule.span ℝ (e '' {i | i < k}), ‖u x - p‖ < δ} := by
      intro x hx
      exact level_lt_imp_near x k (level x) (S x) rfl (hnonempty x) rfl hx
    have h_ncard_le := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h_finrank_lt := finrank_span_low_lt (e := e) k
    have h_near_bound := hnear (Submodule.span ℝ (e '' {i | i < k})) h_finrank_lt
    have h_finrank_le : Module.finrank ℝ (Submodule.span ℝ (e '' {i | i < k})) ≤ (k : ℕ) := by
      have h_span_eq : Submodule.span ℝ (e '' {i | i < k}) =
          Submodule.span ℝ (Finset.image e (Finset.Iio k) : Set (EuclideanSpace ℝ (Fin (m + 1)))) := by
        congr 1; ext y; simp
      rw [h_span_eq]
      have h_le := finrank_span_le_card (R := ℝ) (s := (Finset.image e (Finset.Iio k) : Set (EuclideanSpace ℝ (Fin (m + 1)))))
      have h_card_le : (Finset.image e (Finset.Iio k)).card ≤ k.val := by
        calc
          (Finset.image e (Finset.Iio k)).card ≤ (Finset.Iio k).card := Finset.card_image_le
          _ = k.val := by simp
      have h_toFinset : (Finset.image e (Finset.Iio k) : Set (EuclideanSpace ℝ (Fin (m + 1)))).toFinset = Finset.image e (Finset.Iio k) := by
        ext; simp
      rw [h_toFinset] at h_le
      exact le_trans h_le h_card_le
    exact le_trans (le_trans h_ncard_le h_near_bound) h_finrank_le
  have hf : Monotone (Real.log ∘ lam) := fun a b hab => Real.log_le_log (hpos a) (hmono hab)
  have habel := sum_level_lower_bound hf level hcount
  have hsum_zero : ∑ i, (Real.log ∘ lam) i = 0 := sum_log_lam_eq_zero hpos hprod_one
  rw [hsum_zero, add_zero] at habel
  have hlog_quad (x : ι) : Real.log (lam (level x)) + 2 * Real.log δ ≤ Real.log (forsterQuad P (u x)) := by
    have h1 : Real.log (lam (level x) * δ ^ 2) ≤ Real.log (forsterQuad P (u x)) :=
      Real.log_le_log (mul_pos (hpos (level x)) (sq_pos_of_ne_zero (ne_of_gt hδ0))) (hquad_ge x)
    have h2 : Real.log (lam (level x) * δ ^ 2) = Real.log (lam (level x)) + Real.log (δ ^ 2) :=
      Real.log_mul (ne_of_gt (hpos (level x))) (ne_of_gt (sq_pos_of_ne_zero (ne_of_gt hδ0)))
    have h3 : Real.log (δ ^ 2) = 2 * Real.log δ := by
      rw [sq, Real.log_mul (ne_of_gt hδ0) (ne_of_gt hδ0)]
      ring
    rw [h2, h3] at h1
    exact h1
  have hpot_ge : ((Fintype.card ι : ℝ) - (m + 1)) * Real.log (lam (Fin.last m)) + 2 * Fintype.card ι * Real.log δ ≤ forsterPotential u P := by
    rw [forsterPotential_eq_sum_log]
    calc
      ((Fintype.card ι : ℝ) - (m + 1)) * Real.log (lam (Fin.last m)) + 2 * Fintype.card ι * Real.log δ
        = ((Fintype.card ι : ℝ) - (m + 1)) * Real.log (lam (Fin.last m)) + ∑ x : ι, (2 * Real.log δ) := by
          have h_sum_const : ∑ x : ι, (2 * Real.log δ) = (Fintype.card ι : ℝ) * (2 * Real.log δ) := by simp
          rw [h_sum_const]
          ring
      _ ≤ ∑ x, Real.log (lam (level x)) + ∑ x : ι, (2 * Real.log δ) := by
          have h1 : ((Fintype.card ι : ℝ) - (m + 1)) * Real.log (lam (Fin.last m)) ≤ ∑ x, Real.log (lam (level x)) := habel
          linarith [h1]
      _ = ∑ x, (Real.log (lam (level x)) + 2 * Real.log δ) := by rw [Finset.sum_add_distrib]
      _ ≤ ∑ x, Real.log (forsterQuad P (u x)) := Finset.sum_le_sum (fun x _ => hlog_quad x)
  have hcard_real : (m + 1 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
  have hN_r_pos : 0 < (Fintype.card ι : ℝ) - (m + 1) := sub_pos.mpr hcard_real
  have hlog_top_le : Real.log (lam (Fin.last m)) ≤ (forsterPotential u P - 2 * Fintype.card ι * Real.log δ) / ((Fintype.card ι : ℝ) - (m + 1)) := by
    rw [le_div_iff₀ hN_r_pos]
    linarith [hpot_ge]
  have hquad_z_le := forsterQuad_le_top_eigenvalue he hspan hmono hquad m rfl z hz
  change forsterQuad P z ≤ lam (Fin.last m) at hquad_z_le
  have h_top_pos : 0 < lam (Fin.last m) := hpos (Fin.last m)
  have h_exp_log : Real.exp (Real.log (lam (Fin.last m))) = lam (Fin.last m) := Real.exp_log h_top_pos
  have h_exp_le : Real.exp (Real.log (lam (Fin.last m))) ≤ Real.exp ((forsterPotential u P - 2 * Fintype.card ι * Real.log δ) / ((Fintype.card ι : ℝ) - (m + 1))) :=
    Real.exp_le_exp.mpr hlog_top_le
  rw [h_exp_log] at h_exp_le
  have h_cast : ((Fintype.card ι : ℝ) - (m + 1 : ℕ)) = ((Fintype.card ι : ℝ) - (m + 1 : ℝ)) := by norm_cast
  rw [h_cast]
  exact le_trans hquad_z_le h_exp_le

private lemma dotProduct_mulVec_comm {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ}
    (hsym : ∀ i j, P i j = P j i) (v w : Fin r → ℝ) :
    v ⬝ᵥ (P *ᵥ w) = w ⬝ᵥ (P *ᵥ v) := by
  dsimp [dotProduct, mulVec]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym i j]
  ring

private lemma quad_add_smul_expand {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ}
    (hsym : ∀ i j, P i j = P j i) (z w : Fin r → ℝ) (t : ℝ) (hz : z ⬝ᵥ (P *ᵥ z) = 0) :
    (z + t • w) ⬝ᵥ (P *ᵥ (z + t • w)) = 2 * t * (w ⬝ᵥ (P *ᵥ z)) + t ^ 2 * (w ⬝ᵥ (P *ᵥ w)) := by
  rw [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add]
  rw [dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul]
  rw [dotProduct_mulVec_comm hsym z w]
  rw [hz]
  ring

private lemma linear_quad_nonneg_imp_zero (A B : ℝ)
    (h : ∀ t : ℝ, 0 ≤ 2 * t * A + t ^ 2 * B) : A = 0 := by
  by_contra hA
  have hA_abs : 0 < |A| := abs_pos.mpr hA
  set ε := |A| / (|B| + 1)
  have hdenom : 0 < |B| + 1 := by positivity
  have hε_pos : 0 < ε := div_pos hA_abs hdenom
  let sgn : ℝ := if 0 < A then -1 else 1
  have hsgn_sq : sgn ^ 2 = 1 := by
    dsimp [sgn]
    split_ifs <;> ring
  have hsgn_A : sgn * A = -|A| := by
    dsimp [sgn]
    split_ifs with hpos
    · rw [neg_one_mul, abs_of_pos hpos]
    · have hneg : A < 0 := lt_of_le_of_ne (not_lt.mp hpos) hA
      rw [one_mul, abs_of_neg hneg, neg_neg]
  have h_spec := h (ε * sgn)
  have h_exp : 2 * (ε * sgn) * A + (ε * sgn) ^ 2 * B = ε * (2 * (sgn * A) + ε * B) := by
    calc 2 * (ε * sgn) * A + (ε * sgn) ^ 2 * B
      _ = 2 * ε * (sgn * A) + ε ^ 2 * (sgn ^ 2) * B := by ring
      _ = 2 * ε * (sgn * A) + ε ^ 2 * 1 * B := by rw [hsgn_sq]
      _ = ε * (2 * (sgn * A) + ε * B) := by ring
  rw [h_exp] at h_spec
  rw [hsgn_A] at h_spec
  have h_eps_B : ε * B ≤ |A| := by
    calc ε * B ≤ ε * |B| := mul_le_mul_of_nonneg_left (le_abs_self B) hε_pos.le
    _ = (|A| * |B|) / (|B| + 1) := by dsimp [ε]; ring
    _ ≤ (|A| * (|B| + 1)) / (|B| + 1) := by
      apply div_le_div_of_nonneg_right _ hdenom.le
      nlinarith [abs_nonneg A]
    _ = |A| := mul_div_cancel_right₀ |A| hdenom.ne'
  have h_inner : 2 * -|A| + ε * B < 0 := by linarith
  have h_prod : ε * (2 * -|A| + ε * B) < 0 := mul_neg_of_pos_of_neg hε_pos h_inner
  linarith

private lemma mulVec_eq_zero_of_forall_dotProduct_eq_zero {r : ℕ} {v : Fin r → ℝ}
    (h : ∀ w : Fin r → ℝ, w ⬝ᵥ v = 0) : v = 0 := by
  have hvv := h v
  dsimp [dotProduct] at hvv
  simp_rw [← sq] at hvv
  ext i
  have h_zero : (v i) ^ 2 = 0 := by
    have h_sum := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j))).mp hvv
    exact h_sum i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp h_zero

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
  refine ⟨hsym, ?_⟩
  intro z hz
  have h_le := hpsd z
  rcases eq_or_lt_of_le h_le with hz0 | hpos
  · exfalso
    have hz0' : z ⬝ᵥ (P *ᵥ z) = 0 := hz0.symm
    have hPz_dot : ∀ w : Fin r → ℝ, w ⬝ᵥ (P *ᵥ z) = 0 := by
      intro w
      have h_quad : ∀ t : ℝ, 0 ≤ 2 * t * (w ⬝ᵥ (P *ᵥ z)) + t ^ 2 * (w ⬝ᵥ (P *ᵥ w)) := by
        intro t
        rw [← quad_add_smul_expand hsym z w t hz0']
        exact hpsd (z + t • w)
      exact linear_quad_nonneg_imp_zero (w ⬝ᵥ (P *ᵥ z)) (w ⬝ᵥ (P *ᵥ w)) h_quad
    have hPz : P *ᵥ z = 0 := mulVec_eq_zero_of_forall_dotProduct_eq_zero hPz_dot
    have hdet0 : P.det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      exact ⟨z, hz, hPz⟩
    rw [hdet] at hdet0
    exact one_ne_zero hdet0
  · exact hpos

/-- A `ForsterPosDef` matrix has nonzero determinant: a vanishing
determinant gives a nonzero kernel vector
(`Matrix.exists_mulVec_eq_zero_iff`), whose quadratic value `0` contradicts
positive definiteness. -/
lemma forsterPosDef_det_ne_zero {r : ℕ} {B : Matrix (Fin r) (Fin r) ℝ}
    (hB : ForsterPosDef B) : B.det ≠ 0 := by
  intro hdet
  have h_ex := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨z, hz_ne, hz_zero⟩ := h_ex
  have h_pos := hB.2 z hz_ne
  rw [hz_zero, dotProduct_zero] at h_pos
  exact lt_irrefl 0 h_pos

private theorem norm_sq_eq_local {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    ‖(WithLp.equiv 2 _).symm v‖^2 = ∑ i, v i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

private theorem forsterQuad_single {r : ℕ} (P : Matrix (Fin r) (Fin r) ℝ) (i : Fin r) :
    forsterQuad P (EuclideanSpace.single i (1 : ℝ)) = P i i := by
  dsimp [forsterQuad]
  have h1 : (WithLp.equiv 2 _ (EuclideanSpace.single i (1 : ℝ))) = (Pi.single i (1 : ℝ) : Fin r → ℝ) := rfl
  rw [h1]
  rw [mulVec_single]
  simp only [MulOpposite.op_one, one_smul]
  rw [single_dotProduct]
  dsimp [col]
  ring

private theorem norm_single_one {r : ℕ} (i : Fin r) :
    ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
  have h_sq : ‖EuclideanSpace.single i (1 : ℝ)‖^2 = 1 := by
    have h_symm : EuclideanSpace.single i (1 : ℝ) = (WithLp.equiv 2 _).symm (Pi.single i (1 : ℝ) : Fin r → ℝ) := rfl
    rw [h_symm, norm_sq_eq_local]
    have h_sum : ∑ k, ((Pi.single i (1 : ℝ) : Fin r → ℝ) k) ^ 2 = 1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · intro hb
        exact False.elim (hb (Finset.mem_univ i))
    exact h_sum
  have h_pos : 0 ≤ ‖EuclideanSpace.single i (1 : ℝ)‖ := norm_nonneg _
  nlinarith

private theorem forsterQuad_pair_add {r : ℕ} (P : Matrix (Fin r) (Fin r) ℝ)
    (hsym : ∀ i j, P i j = P j i) (i j : Fin r) :
    forsterQuad P ((Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ))) =
      (P i i + P j j + 2 * P i j) / 2 := by
  dsimp [forsterQuad]
  have h1 : (WithLp.equiv 2 (Fin r → ℝ) ((Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ))))
      = (Real.sqrt 2)⁻¹ • ((Pi.single i (1 : ℝ) : Fin r → ℝ) + (Pi.single j (1 : ℝ) : Fin r → ℝ)) := rfl
  rw [h1]
  rw [mulVec_smul, dotProduct_smul, smul_dotProduct, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
  rw [mulVec_single, mulVec_single]
  simp only [MulOpposite.op_one, one_smul]
  rw [single_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
  dsimp [col]
  rw [one_mul, one_mul, one_mul, one_mul]
  rw [hsym j i]
  have hsqrt : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (Real.sqrt 2 * Real.sqrt 2)⁻¹ := (mul_inv _ _).symm
    rw [h3, h2]
    norm_num
  calc (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ * (P i i + P i j + (P i j + P j j)))
    _ = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * (P i i + P j j + 2 * P i j) := by ring
    _ = (1 / 2 : ℝ) * (P i i + P j j + 2 * P i j) := by rw [hsqrt]
    _ = (P i i + P j j + 2 * P i j) / 2 := by ring

private theorem forsterQuad_pair_sub {r : ℕ} (P : Matrix (Fin r) (Fin r) ℝ)
    (hsym : ∀ i j, P i j = P j i) (i j : Fin r) :
    forsterQuad P ((Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ))) =
      (P i i + P j j - 2 * P i j) / 2 := by
  dsimp [forsterQuad]
  have h1 : (WithLp.equiv 2 (Fin r → ℝ) ((Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ))))
      = (Real.sqrt 2)⁻¹ • ((Pi.single i (1 : ℝ) : Fin r → ℝ) - (Pi.single j (1 : ℝ) : Fin r → ℝ)) := rfl
  rw [h1]
  rw [mulVec_smul, dotProduct_smul, smul_dotProduct, mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
  rw [mulVec_single, mulVec_single]
  simp only [MulOpposite.op_one, one_smul]
  rw [single_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
  dsimp [col]
  rw [one_mul, one_mul, one_mul, one_mul]
  rw [hsym j i]
  have hsqrt : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (Real.sqrt 2 * Real.sqrt 2)⁻¹ := (mul_inv _ _).symm
    rw [h3, h2]
    norm_num
  calc (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ * (P i i - P i j - (P i j - P j j)))
    _ = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * (P i i + P j j - 2 * P i j) := by ring
    _ = (1 / 2 : ℝ) * (P i i + P j j - 2 * P i j) := by rw [hsqrt]
    _ = (P i i + P j j - 2 * P i j) / 2 := by ring

private theorem norm_pair_add_one {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    ‖(Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ))‖ = 1 := by
  have h_sq : ‖(Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ))‖^2 = 1 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [h2]
    have h_norm2 : ‖EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ)‖^2 = 2 := by
      have h_symm : EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ) =
          (WithLp.equiv 2 _).symm ((Pi.single i (1 : ℝ) : Fin r → ℝ) + (Pi.single j (1 : ℝ) : Fin r → ℝ)) := rfl
      rw [h_symm, norm_sq_eq_local]
      rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
      · simp [hij, hij.symm]
        ring
      · intro k _ ⟨hki, hkj⟩
        simp [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]
    rw [h_norm2]
    norm_num
  have h_pos : 0 ≤ ‖(Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ))‖ := norm_nonneg _
  nlinarith

private theorem norm_pair_sub_one {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    ‖(Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ))‖ = 1 := by
  have h_sq : ‖(Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ))‖^2 = 1 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [h2]
    have h_norm2 : ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖^2 = 2 := by
      have h_symm : EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ) =
          (WithLp.equiv 2 _).symm ((Pi.single i (1 : ℝ) : Fin r → ℝ) - (Pi.single j (1 : ℝ) : Fin r → ℝ)) := rfl
      rw [h_symm, norm_sq_eq_local]
      rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
      · simp [hij, hij.symm]
        ring
      · intro k _ ⟨hki, hkj⟩
        simp [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]
    rw [h_norm2]
    norm_num
  have h_pos : 0 ≤ ‖(Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ))‖ := norm_nonneg _
  nlinarith

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
  intro i j
  have hPii : P i i ≤ C := by
    have h_quad := forsterQuad_single P i
    have h_norm := norm_single_one i
    have h_bound := hdiag (EuclideanSpace.single i (1 : ℝ)) h_norm
    rwa [h_quad] at h_bound
  have hPjj : P j j ≤ C := by
    have h_quad := forsterQuad_single P j
    have h_norm := norm_single_one j
    have h_bound := hdiag (EuclideanSpace.single j (1 : ℝ)) h_norm
    rwa [h_quad] at h_bound
  by_cases hij : i = j
  · rw [hij]
    have hnonneg : 0 ≤ P j j := by
      have h_psd := hpsd (Pi.single j (1 : ℝ))
      rw [mulVec_single] at h_psd
      simp only [MulOpposite.op_one, one_smul] at h_psd
      rw [single_dotProduct] at h_psd
      dsimp [col] at h_psd
      linarith
    rw [abs_of_nonneg hnonneg]
    exact hPjj
  · have h_add_quad := forsterQuad_pair_add P hsym i j
    have h_add_norm := norm_pair_add_one i j hij
    have h_add_bound := hdiag _ h_add_norm
    rw [h_add_quad] at h_add_bound
    have h_sub_quad := forsterQuad_pair_sub P hsym i j
    have h_sub_norm := norm_pair_sub_one i j hij
    have h_sub_bound := hdiag _ h_sub_norm
    rw [h_sub_quad] at h_sub_bound
    have h_add_psd : 0 ≤ (P i i + P j j + 2 * P i j) / 2 := by
      have h1 : forsterQuad P ((Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ))) ≥ 0 := by
        dsimp [forsterQuad]
        exact hpsd _
      rwa [h_add_quad] at h1
    have h_sub_psd : 0 ≤ (P i i + P j j - 2 * P i j) / 2 := by
      have h1 : forsterQuad P ((Real.sqrt 2)⁻¹ • (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ))) ≥ 0 := by
        dsimp [forsterQuad]
        exact hpsd _
      rwa [h_sub_quad] at h1
    rw [abs_le]
    constructor
    · linarith
    · linarith

private lemma continuous_forsterQuad {r : ℕ} (z : EuclideanSpace ℝ (Fin r)) :
    Continuous (fun (P : Matrix (Fin r) (Fin r) ℝ) => forsterQuad P z) := by
  dsimp [forsterQuad, dotProduct, mulVec]
  refine continuous_finsetSum _ (fun i _ => ?_)
  refine Continuous.mul continuous_const ?_
  refine continuous_finsetSum _ (fun j _ => ?_)
  refine Continuous.mul ?_ continuous_const
  exact Continuous.comp (continuous_apply j) (continuous_apply i)

/-- Continuity of the Forster potential where all quadratic values are
positive: each `P ↦ forsterQuad P (u x)` is a polynomial in the entries of
`P` (finite sums of products), hence continuous; `Real.log` is continuous
at nonzero points; combine `ContinuousOn.sum`, `ContinuousAt.continuousOn`,
`Real.continuousAt_log`. -/
lemma continuousOn_forsterPotential {r : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → EuclideanSpace ℝ (Fin r)) :
    ContinuousOn (forsterPotential u)
      {P : Matrix (Fin r) (Fin r) ℝ | ∀ x, 0 < forsterQuad P (u x)} := by
  change ContinuousOn (fun P => ∑ x, Real.log (forsterQuad P (u x))) _
  refine continuousOn_finsetSum _ (fun x _ => ?_)
  refine ContinuousOn.comp Real.continuousOn_log (continuous_forsterQuad (u x)).continuousOn ?_
  intro P hP
  exact Ne.symm (ne_of_lt (hP x))

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
  let A : Set (Matrix (Fin r) (Fin r) ℝ) :=
    {P | (∀ i j, P i j = P j i) ∧
      (∀ z : EuclideanSpace ℝ (Fin r), 0 ≤ forsterQuad P z) ∧ P.det = 1}
  let K : Set (Matrix (Fin r) (Fin r) ℝ) :=
    {P | P ∈ A ∧ forsterPotential u P ≤ 0}
  have hsym_closed : IsClosed
      {P : Matrix (Fin r) (Fin r) ℝ | ∀ i j, P i j = P j i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
      isClosed_eq (continuous_id.matrix_elem i j) (continuous_id.matrix_elem j i)
  have hpsd_closed : IsClosed
      {P : Matrix (Fin r) (Fin r) ℝ |
        ∀ z : EuclideanSpace ℝ (Fin r), 0 ≤ forsterQuad P z} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun z ↦
      isClosed_le continuous_const (continuous_forsterQuad z)
  have hdet_closed : IsClosed
      {P : Matrix (Fin r) (Fin r) ℝ | P.det = 1} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  have hA_closed : IsClosed A := by
    rw [show A =
        {P : Matrix (Fin r) (Fin r) ℝ | ∀ i j, P i j = P j i} ∩
          ({P | ∀ z : EuclideanSpace ℝ (Fin r), 0 ≤ forsterQuad P z} ∩
          {P | P.det = 1}) by ext P; simp only [A, Set.mem_setOf_eq, Set.mem_inter_iff]]
    exact hsym_closed.inter (hpsd_closed.inter hdet_closed)
  have hA_posDef : ∀ P ∈ A, ForsterPosDef P := by
    intro P hP
    exact forsterPosDef_of_psd_det_one hP.1
      (fun z ↦ hP.2.1 ((WithLp.equiv 2 (Fin r → ℝ)).symm z)) hP.2.2
  have hA_quad_pos : ∀ P ∈ A, ∀ x, 0 < forsterQuad P (u x) := by
    intro P hP x
    have hu_ne : WithLp.equiv 2 (Fin r → ℝ) (u x) ≠ 0 := by
      intro hx
      have hx' : u x = 0 :=
        (WithLp.equiv 2 (Fin r → ℝ)).injective (by simpa using hx)
      have := hu x
      rw [hx', norm_zero] at this
      exact zero_ne_one this
    exact (hA_posDef P hP).2 _ hu_ne
  have hpot_cont_A : ContinuousOn (forsterPotential u) A :=
    (continuousOn_forsterPotential u).mono fun P hP ↦ hA_quad_pos P hP
  have hK_closed : IsClosed K := by
    exact hA_closed.isClosed_le hpot_cont_A continuousOn_const
  obtain ⟨δ, hδ, hcoercive⟩ := forsterPotential_coercive hr hcard hu hgen
  let C : ℝ := Real.exp
    ((0 - 2 * Fintype.card ι * Real.log δ) / (Fintype.card ι - r))
  have hcard_real : (r : ℝ) < Fintype.card ι := by exact_mod_cast hcard
  have hden : 0 < (Fintype.card ι : ℝ) - r := sub_pos.mpr hcard_real
  have hC_pos : 0 < C := Real.exp_pos _
  have hK_subset_box : K ⊆ (Set.Icc (-C) C).matrix := by
    intro P hPK
    have hPA : P ∈ A := hPK.1
    have hPpos := hA_posDef P hPA
    have hdiag : ∀ z : EuclideanSpace ℝ (Fin r), ‖z‖ = 1 →
        forsterQuad P z ≤ C := by
      intro z hz
      refine (hcoercive P hPpos hPA.2.2 z hz).trans ?_
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff_of_pos_right hden).mpr
      exact sub_le_sub_right hPK.2 _
    have hentry : ∀ i j, |P i j| ≤ C :=
      forster_entry_bound hPA.1
        (fun z ↦ hPA.2.1 ((WithLp.equiv 2 (Fin r → ℝ)).symm z)) hdiag
    rw [Set.mem_matrix]
    intro i j
    exact abs_le.mp (hentry i j)
  have hK_compact : IsCompact K :=
    (isCompact_Icc.matrix).of_isClosed_subset hK_closed hK_subset_box
  have hquad_one : ∀ x, forsterQuad (1 : Matrix (Fin r) (Fin r) ℝ) (u x) = 1 := by
    intro x
    dsimp [forsterQuad]
    rw [Matrix.one_mulVec]
    have hnorm := norm_sq_eq_local (WithLp.equiv 2 (Fin r → ℝ) (u x))
    simp only [Equiv.symm_apply_apply, hu x, one_pow] at hnorm
    rw [dotProduct]
    calc
      (∑ i, (WithLp.equiv 2 (Fin r → ℝ) (u x)) i *
          (WithLp.equiv 2 (Fin r → ℝ) (u x)) i) =
          ∑ i, (WithLp.equiv 2 (Fin r → ℝ) (u x)) i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [pow_two]
      _ = 1 := hnorm.symm
  have hpot_one : forsterPotential u (1 : Matrix (Fin r) (Fin r) ℝ) = 0 := by
    rw [forsterPotential_eq_sum_log]
    simp [hquad_one]
  have hone_A : (1 : Matrix (Fin r) (Fin r) ℝ) ∈ A := by
    refine ⟨?_, ?_, Matrix.det_one⟩
    · intro i j
      simp [Matrix.one_apply, eq_comm]
    · intro z
      dsimp [forsterQuad]
      rw [Matrix.one_mulVec]
      rw [dotProduct]
      exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hone_K : (1 : Matrix (Fin r) (Fin r) ℝ) ∈ K :=
    ⟨hone_A, hpot_one.le⟩
  have hpot_cont_K : ContinuousOn (forsterPotential u) K :=
    hpot_cont_A.mono fun _ h ↦ h.1
  obtain ⟨P, hPK, hPmin⟩ :=
    hK_compact.exists_isMinOn ⟨(1 : Matrix (Fin r) (Fin r) ℝ), hone_K⟩ hpot_cont_K
  refine ⟨P, hA_posDef P hPK.1, hPK.1.2.2, ?_⟩
  intro Q hQ hQdet
  by_cases hQpot : forsterPotential u Q ≤ 0
  · apply hPmin
    refine ⟨⟨hQ.1, ?_, hQdet⟩, hQpot⟩
    intro z
    by_cases hz : z = 0
    · subst z
      simp [forsterQuad]
    · have hzcoord : WithLp.equiv 2 (Fin r → ℝ) z ≠ 0 := by
        intro hzcoord
        exact hz ((WithLp.equiv 2 (Fin r → ℝ)).injective (by simpa using hzcoord))
      exact (hQ.2 _ hzcoord).le
  · have hP_le_zero : forsterPotential u P ≤ 0 := by
      have hP_le_one : forsterPotential u P ≤
          forsterPotential u (1 : Matrix (Fin r) (Fin r) ℝ) := hPmin hone_K
      simpa [hpot_one] using hP_le_one
    exact hP_le_zero.trans (le_of_lt (lt_of_not_ge hQpot))

/-! ### P5.3b leaf decomposition: first-order condition and the isotropic
transform -/

private lemma forsterQuad_smul {r : ℕ} (P : Matrix (Fin r) (Fin r) ℝ)
    (z : EuclideanSpace ℝ (Fin r)) (c : ℝ) :
    forsterQuad (c • P) z = c * forsterQuad P z := by
  dsimp [forsterQuad]
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Scaling the matrix shifts the potential by `N * log c`:
`forsterQuad (c • P) z = c * forsterQuad P z` (`Matrix.smul_mulVec_assoc`,
`dotProduct_smul`), and `Real.log_mul` term by term (all quadratic values
are nonzero). -/
lemma forsterPotential_smul {r : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → EuclideanSpace ℝ (Fin r)) (P : Matrix (Fin r) (Fin r) ℝ)
    {c : ℝ} (hc : 0 < c) (hq : ∀ x, forsterQuad P (u x) ≠ 0) :
    forsterPotential u (c • P) =
      Fintype.card ι * Real.log c + forsterPotential u P := by
  rw [forsterPotential_eq_sum_log, forsterPotential_eq_sum_log]
  have h_log : ∀ x : ι, Real.log (forsterQuad (c • P) (u x)) =
      Real.log c + Real.log (forsterQuad P (u x)) := by
    intro x
    rw [forsterQuad_smul]
    exact Real.log_mul hc.ne' (hq x)
  simp_rw [h_log, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private lemma continuous_quadForm {r : ℕ} (P : Matrix (Fin r) (Fin r) ℝ) :
    Continuous (fun (u : EuclideanSpace ℝ (Fin r)) => (WithLp.equiv 2 (Fin r → ℝ) u) ⬝ᵥ (P *ᵥ (WithLp.equiv 2 (Fin r → ℝ) u))) := by
  change Continuous (fun (u : EuclideanSpace ℝ (Fin r)) => ∑ i : Fin r, u.ofLp i * ∑ j : Fin r, P i j * u.ofLp j)
  refine continuous_finsetSum _ (fun i _ => ?_)
  refine Continuous.mul (PiLp.continuous_apply 2 _ i) (continuous_finsetSum _ (fun j _ => ?_))
  exact continuous_const.mul (PiLp.continuous_apply 2 _ j)

/-- Positive definiteness survives small symmetric perturbations: on the
compact unit sphere (`isCompact_sphere`, nonempty since `z / ‖z‖` reduces
the general case to it by homogeneity of degree `2`) the form of `P` has a
positive minimum `m` and the form of `X` a finite maximum absolute value
`M` (`IsCompact.exists_isMinOn` / `exists_isMaxOn` with continuity of the
quadratic forms); take `ε := m / (M + 1)`. -/
lemma forsterPosDef_perturb {r : ℕ} {P X : Matrix (Fin r) (Fin r) ℝ}
    (hP : ForsterPosDef P) (hX : ∀ i j, X i j = X j i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ForsterPosDef (P + t • X) := by
  by_cases h_emp : IsEmpty (Fin r)
  · use 1
    refine ⟨zero_lt_one, ?_⟩
    intro t _
    constructor
    · intro i
      exact isEmptyElim i
    · intro z hz
      exfalso
      apply hz
      ext i
      exact isEmptyElim i
  · rw [not_isEmpty_iff] at h_emp
    haveI : Nonempty (Fin r) := h_emp
    let S := sphere (0 : EuclideanSpace ℝ (Fin r)) 1
    have hS_compact : IsCompact S := isCompact_sphere _ _
    have hS_nonempty : S.Nonempty := by simp [S]
    let fP := fun (u : EuclideanSpace ℝ (Fin r)) => (WithLp.equiv 2 (Fin r → ℝ) u) ⬝ᵥ (P *ᵥ (WithLp.equiv 2 (Fin r → ℝ) u))
    let fX := fun (u : EuclideanSpace ℝ (Fin r)) => (WithLp.equiv 2 (Fin r → ℝ) u) ⬝ᵥ (X *ᵥ (WithLp.equiv 2 (Fin r → ℝ) u))
    obtain ⟨u_m, hu_m_S, hu_m_min⟩ := hS_compact.exists_isMinOn hS_nonempty (continuous_quadForm P).continuousOn
    obtain ⟨u_M, hu_M_S, hu_M_max⟩ := hS_compact.exists_isMaxOn hS_nonempty (continuous_quadForm X).abs.continuousOn
    let m := fP u_m
    let M := |fX u_M|
    have hm : 0 < m := by
      have hu_m_norm : ‖u_m‖ = 1 := by simpa [S] using hu_m_S
      have hz_m_ne : (WithLp.equiv 2 (Fin r → ℝ) u_m) ≠ 0 := by
        intro h
        have h_um : u_m = 0 := by
          rw [← Equiv.symm_apply_apply (WithLp.equiv 2 (Fin r → ℝ)) u_m, h]
          rfl
        rw [h_um, norm_zero] at hu_m_norm
        exact zero_ne_one hu_m_norm
      exact hP.2 (WithLp.equiv 2 (Fin r → ℝ) u_m) hz_m_ne
    have hM : 0 ≤ M := abs_nonneg _
    use m / (M + 1)
    have hε_pos : 0 < m / (M + 1) := div_pos hm (by linarith)
    refine ⟨hε_pos, ?_⟩
    intro t ht
    constructor
    · intro i j
      dsimp [Matrix.add_apply, Matrix.smul_apply]
      rw [hP.1 i j, hX i j]
    · intro z hz
      let v : EuclideanSpace ℝ (Fin r) := (WithLp.equiv 2 (Fin r → ℝ)).symm z
      have hv_ne : v ≠ 0 := by
        intro h
        apply hz
        have h1 : (WithLp.equiv 2 (Fin r → ℝ)) v = 0 := by rw [h]; rfl
        rwa [Equiv.apply_symm_apply] at h1
      have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
      have hv_norm_ne : ‖v‖ ≠ 0 := hv_norm_pos.ne'
      let u : EuclideanSpace ℝ (Fin r) := (‖v‖⁻¹ : ℝ) • v
      have hu_norm : ‖u‖ = 1 := by
        dsimp [u]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hv_norm_pos.le), inv_mul_cancel₀ hv_norm_ne]
      have hu_S : u ∈ S := by simpa [S] using hu_norm
      have hu_P : m ≤ fP u := hu_m_min hu_S
      have hu_X : |fX u| ≤ M := hu_M_max hu_S
      have hu_vec : WithLp.equiv 2 (Fin r → ℝ) u = ‖v‖⁻¹ • z := rfl
      have hP_u : fP u = ‖v‖⁻¹ ^ 2 * (z ⬝ᵥ (P *ᵥ z)) := by
        dsimp [fP]
        rw [hu_vec]
        simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
        ring
      have hX_u : fX u = ‖v‖⁻¹ ^ 2 * (z ⬝ᵥ (X *ᵥ z)) := by
        dsimp [fX]
        rw [hu_vec]
        simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
        ring
      have h_inv : ‖v‖⁻¹ ^ 2 * ‖v‖ ^ 2 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hv_norm_ne, one_pow]
      have hP_z : m * ‖v‖ ^ 2 ≤ z ⬝ᵥ (P *ᵥ z) := by
        rw [hP_u] at hu_P
        have h_mul := mul_le_mul_of_nonneg_right hu_P (sq_nonneg ‖v‖)
        have h_eq : (‖v‖⁻¹ ^ 2 * (z ⬝ᵥ (P *ᵥ z))) * ‖v‖ ^ 2 = z ⬝ᵥ (P *ᵥ z) := by
          calc (‖v‖⁻¹ ^ 2 * (z ⬝ᵥ (P *ᵥ z))) * ‖v‖ ^ 2
            _ = (‖v‖⁻¹ ^ 2 * ‖v‖ ^ 2) * (z ⬝ᵥ (P *ᵥ z)) := by ring
            _ = z ⬝ᵥ (P *ᵥ z) := by rw [h_inv, one_mul]
        rwa [h_eq] at h_mul
      have hX_z : |z ⬝ᵥ (X *ᵥ z)| ≤ M * ‖v‖ ^ 2 := by
        rw [hX_u] at hu_X
        rw [abs_mul, abs_of_nonneg (by positivity)] at hu_X
        have h_mul := mul_le_mul_of_nonneg_right hu_X (sq_nonneg ‖v‖)
        have h_eq : (‖v‖⁻¹ ^ 2 * |z ⬝ᵥ (X *ᵥ z)|) * ‖v‖ ^ 2 = |z ⬝ᵥ (X *ᵥ z)| := by
          calc (‖v‖⁻¹ ^ 2 * |z ⬝ᵥ (X *ᵥ z)|) * ‖v‖ ^ 2
            _ = (‖v‖⁻¹ ^ 2 * ‖v‖ ^ 2) * |z ⬝ᵥ (X *ᵥ z)| := by ring
            _ = |z ⬝ᵥ (X *ᵥ z)| := by rw [h_inv, one_mul]
        rwa [h_eq] at h_mul
      have h_add : (P + t • X) *ᵥ z = P *ᵥ z + t • (X *ᵥ z) := by
        rw [Matrix.add_mulVec, smul_mulVec]
      rw [h_add, dotProduct_add, dotProduct_smul]
      change 0 < z ⬝ᵥ P *ᵥ z + t * (z ⬝ᵥ X *ᵥ z)
      have h_bound : - |t| * (M * ‖v‖ ^ 2) ≤ t * (z ⬝ᵥ (X *ᵥ z)) := by
        have h_abs_z := le_abs_self (z ⬝ᵥ (X *ᵥ z))
        have h_neg_abs_z := neg_abs_le (z ⬝ᵥ (X *ᵥ z))
        have ht_le : - |t| ≤ t ∧ t ≤ |t| := ⟨neg_abs_le t, le_abs_self t⟩
        nlinarith [ht_le.1, ht_le.2, hX_z, h_abs_z, h_neg_abs_z]
      have h_main : (m - |t| * M) * ‖v‖ ^ 2 ≤ z ⬝ᵥ (P *ᵥ z) + t * (z ⬝ᵥ (X *ᵥ z)) := by
        linarith
      have ht_bound : |t| * M < m := by
        have ht1 : |t| < m / (M + 1) := ht
        have hM1 : 0 < M + 1 := by linarith
        have ht2 := (lt_div_iff₀ hM1).mp ht1
        calc |t| * M ≤ |t| * (M + 1) := by nlinarith [abs_nonneg t]
        _ < m := ht2
      have h_coeff : 0 < (m - |t| * M) * ‖v‖ ^ 2 := mul_pos (by linarith) (sq_pos_of_ne_zero hv_norm_ne)
      linarith

private lemma forsterQuad_add_smul {r : ℕ} (P X : Matrix (Fin r) (Fin r) ℝ)
    (z : EuclideanSpace ℝ (Fin r)) (t : ℝ) :
    forsterQuad (P + t • X) z = forsterQuad P z + t * forsterQuad X z := by
  dsimp [forsterQuad]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]

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
  have h_fun : (fun t : ℝ => forsterPotential u (P + t • X)) =
      (∑ x, fun t : ℝ => Real.log (forsterQuad (P + t • X) (u x))) := by
    ext t
    rw [Finset.sum_apply]
    rfl
  rw [h_fun]
  apply HasDerivAt.sum
  intro x _
  simp_rw [forsterQuad_add_smul]
  have h_lin : HasDerivAt (fun t : ℝ => forsterQuad P (u x) + t * forsterQuad X (u x))
      (forsterQuad X (u x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * forsterQuad X (u x)) (forsterQuad X (u x)) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (forsterQuad X (u x))
    exact h1.const_add (forsterQuad P (u x))
  have h_ne : forsterQuad P (u x) + 0 * forsterQuad X (u x) ≠ 0 := by
    rw [zero_mul, add_zero]
    exact (hq x).ne'
  simpa using HasDerivAt.log h_lin h_ne

open Polynomial in
private lemma hasDerivAt_det_one_add_smul {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • M).det) (M.trace) 0 := by
  have h_eq : (fun t : ℝ => (1 + t • M).det) =
      fun t : ℝ => 1 + M.trace * t + eval t (1 + (X : ℝ[X]) • M.map (C : ℝ →+* ℝ[X])).det.divX.divX * t ^ 2 := by
    ext t
    exact Matrix.det_one_add_smul t M
  rw [h_eq]
  have h_lin : HasDerivAt (fun t : ℝ => 1 + M.trace * t) (M.trace) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => M.trace * t) (M.trace * 1) 0 := hasDerivAt_id' 0 |>.const_mul M.trace
    rw [mul_one] at h1
    exact h1.const_add 1
  have h_quad : HasDerivAt (fun t : ℝ => eval t (1 + (X : ℝ[X]) • M.map (C : ℝ →+* ℝ[X])).det.divX.divX * t ^ 2) 0 0 := by
    have h_p : HasDerivAt (fun t : ℝ => eval t (1 + (X : ℝ[X]) • M.map (C : ℝ →+* ℝ[X])).det.divX.divX)
        (eval 0 (derivative (1 + (X : ℝ[X]) • M.map (C : ℝ →+* ℝ[X])).det.divX.divX)) 0 :=
      Polynomial.hasDerivAt _ 0
    have h_sq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * 0 ^ (2 - 1)) 0 := hasDerivAt_pow 2 0
    have h_prod := h_p.mul h_sq
    change HasDerivAt (fun t : ℝ => eval t (1 + (X : ℝ[X]) • M.map (C : ℝ →+* ℝ[X])).det.divX.divX * t ^ 2) _ 0 at h_prod
    ring_nf at h_prod ⊢
    exact h_prod
  have h_sum := h_lin.add h_quad
  rw [add_zero] at h_sum
  exact h_sum

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
  have h_inv : IsUnit P.det := by rw [hdet]; exact isUnit_one
  have h_eq : (fun t : ℝ => (P + t • X).det) = fun t : ℝ => (1 + t • (P⁻¹ * X)).det := by
    ext t
    have h_split : (P + t • X) = P * (1 + t • (P⁻¹ * X)) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← mul_assoc, Matrix.mul_nonsing_inv _ h_inv, one_mul]
    rw [h_split, Matrix.det_mul, hdet, one_mul]
  rw [h_eq]
  exact hasDerivAt_det_one_add_smul (P⁻¹ * X)

private lemma forsterPosDef_smul {r : ℕ} {P : Matrix (Fin r) (Fin r) ℝ} {c : ℝ}
    (hP : ForsterPosDef P) (hc : 0 < c) : ForsterPosDef (c • P) := by
  constructor
  · intro i j
    dsimp [Matrix.smul_apply]
    rw [hP.1 i j]
  · intro z hz
    have h1 := hP.2 z hz
    rw [Matrix.smul_mulVec, dotProduct_smul]
    exact mul_pos hc h1

private lemma det_smul_rpow_inv {r : ℕ} (hr : 0 < r) {A : Matrix (Fin r) (Fin r) ℝ}
    (hA : 0 < A.det) :
    (((A.det) ^ (-(1 : ℝ) / (r : ℝ))) • A).det = 1 := by
  rw [Matrix.det_smul, Fintype.card_fin]
  have h_r_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have h_r_ne : (r : ℝ) ≠ 0 := h_r_pos.ne'
  have h1 : ((A.det) ^ (-(1 : ℝ) / (r : ℝ))) ^ r = (A.det) ^ (-(1 : ℝ) / (r : ℝ) * (r : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
  have h2 : -(1 : ℝ) / (r : ℝ) * (r : ℝ) = -1 := by
    rw [div_mul_cancel₀ _ h_r_ne]
  rw [h2, Real.rpow_neg hA.le, Real.rpow_one] at h1
  rw [h1, inv_mul_cancel₀ hA.ne']

private lemma forsterPotential_smul_rpow_inv {r : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → EuclideanSpace ℝ (Fin r)) (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : 0 < A.det) (hqA : ∀ x, forsterQuad A (u x) ≠ 0) :
    forsterPotential u (((A.det) ^ (-(1 : ℝ) / (r : ℝ))) • A) =
      forsterPotential u A - ((Fintype.card ι : ℝ) / (r : ℝ)) * Real.log A.det := by
  have hc : 0 < (A.det) ^ (-(1 : ℝ) / (r : ℝ)) := Real.rpow_pos_of_pos hA _
  rw [forsterPotential_smul u A hc hqA]
  rw [Real.log_rpow hA]
  ring

private lemma eventually_det_pos {r : ℕ} {P X : Matrix (Fin r) (Fin r) ℝ} (hdet : P.det = 1) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → 0 < (P + t • X).det := by
  have h_deriv := hasDerivAt_det_line X hdet
  have h_cont := h_deriv.continuousAt
  have h_open : IsOpen {s : ℝ | 0 < s} := isOpen_Ioi
  have h_mem : (P + (0 : ℝ) • X).det ∈ {s : ℝ | 0 < s} := by
    simp [hdet]
  have h_eventually : ∀ᶠ t in nhds (0 : ℝ), 0 < (P + t • X).det :=
    h_cont.eventually (IsOpen.mem_nhds h_open h_mem)
  rw [Metric.eventually_nhds_iff] at h_eventually
  obtain ⟨ε, hε, h_dist⟩ := h_eventually
  use ε, hε
  intro t ht
  apply h_dist
  rw [Real.dist_0_eq_abs]
  exact ht

private lemma eventually_forsterPosDef_and_det_pos {r : ℕ} {P X : Matrix (Fin r) (Fin r) ℝ}
    (hP : ForsterPosDef P) (hdet : P.det = 1) (hX : ∀ i j, X i j = X j i) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → ForsterPosDef (P + t • X) ∧ 0 < (P + t • X).det := by
  obtain ⟨ε1, hε1, hP1⟩ := forsterPosDef_perturb hP hX
  obtain ⟨ε2, hε2, hdet2⟩ := eventually_det_pos (P := P) (X := X) hdet
  use min ε1 ε2, lt_min hε1 hε2
  intro t ht
  have ht1 : |t| < ε1 := lt_of_lt_of_le ht (min_le_left _ _)
  have ht2 : |t| < ε2 := lt_of_lt_of_le ht (min_le_right _ _)
  exact ⟨hP1 t ht1, hdet2 t ht2⟩

private lemma isLocalMin_g {r : ℕ} {ι : Type*} [Fintype ι]
    (hr : 0 < r) (u : ι → EuclideanSpace ℝ (Fin r)) (hu : ∀ x, ‖u x‖ = 1)
    (P : Matrix (Fin r) (Fin r) ℝ) (hP : ForsterPosDef P) (hdet : P.det = 1)
    (hmin : ∀ Q : Matrix (Fin r) (Fin r) ℝ,
      ForsterPosDef Q → Q.det = 1 →
        forsterPotential u P ≤ forsterPotential u Q)
    (X : Matrix (Fin r) (Fin r) ℝ) (hX : ∀ i j, X i j = X j i) :
    IsLocalMin (fun (t : ℝ) => forsterPotential u (P + t • X) - ((Fintype.card ι : ℝ) / (r : ℝ)) * Real.log (P + t • X).det) 0 := by
  change ∀ᶠ t in nhds (0 : ℝ), forsterPotential u (P + (0 : ℝ) • X) - ((Fintype.card ι : ℝ) / (r : ℝ)) * Real.log (P + (0 : ℝ) • X).det ≤
    forsterPotential u (P + t • X) - ((Fintype.card ι : ℝ) / (r : ℝ)) * Real.log (P + t • X).det
  rw [Metric.eventually_nhds_iff]
  obtain ⟨ε, hε, h_prop⟩ := eventually_forsterPosDef_and_det_pos hP hdet hX
  use ε, hε
  intro t ht
  rw [Real.dist_0_eq_abs] at ht
  have h_t_prop := h_prop t ht
  have hPt_pos := h_t_prop.1
  have hdet_pos := h_t_prop.2
  have hqPt : ∀ x, forsterQuad (P + t • X) (u x) ≠ 0 := by
    intro x
    have hu_ne : (WithLp.equiv 2 (Fin r → ℝ) (u x)) ≠ 0 := by
      intro h
      have h1 : u x = 0 := by
        rw [← Equiv.symm_apply_apply (WithLp.equiv 2 (Fin r → ℝ)) (u x), h]
        rfl
      have h2 : ‖u x‖ = 0 := by rw [h1, norm_zero]
      rw [hu x] at h2
      exact zero_ne_one h2.symm
    exact (hPt_pos.2 (WithLp.equiv 2 (Fin r → ℝ) (u x)) hu_ne).ne'
  set c := ((P + t • X).det) ^ (-(1 : ℝ) / (r : ℝ))
  set Q := c • (P + t • X)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hdet_pos _
  have hQ_pos : ForsterPosDef Q := forsterPosDef_smul hPt_pos hc_pos
  have hQ_det : Q.det = 1 := det_smul_rpow_inv hr hdet_pos
  have h_min_Q := hmin Q hQ_pos hQ_det
  have h_pot_Q := forsterPotential_smul_rpow_inv u (P + t • X) hdet_pos hqPt
  have h_g0 : forsterPotential u (P + (0 : ℝ) • X) - ((Fintype.card ι : ℝ) / (r : ℝ)) * Real.log (P + (0 : ℝ) • X).det = forsterPotential u P := by
    simp [hdet]
  rw [h_g0]
  rw [← h_pot_Q]
  exact h_min_Q

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
  have hq : ∀ x, 0 < forsterQuad P (u x) := by
    intro x
    have hu_ne : (WithLp.equiv 2 (Fin r → ℝ) (u x)) ≠ 0 := by
      intro h
      have h1 : u x = 0 := by
        rw [← Equiv.symm_apply_apply (WithLp.equiv 2 (Fin r → ℝ)) (u x), h]
        rfl
      have h2 : ‖u x‖ = 0 := by rw [h1, norm_zero]
      rw [hu x] at h2
      exact zero_ne_one h2.symm
    exact hP.2 (WithLp.equiv 2 (Fin r → ℝ) (u x)) hu_ne

  have h_deriv_fp := hasDerivAt_forsterPotential u P X hq
  have h_deriv_det := hasDerivAt_det_line X hdet
  have h_det_0 : (P + (0 : ℝ) • X).det = 1 := by
    rw [zero_smul, add_zero, hdet]
  have h_deriv_log : HasDerivAt (fun (t : ℝ) => Real.log (P + t • X).det) ((P⁻¹ * X).trace) 0 := by
    have h_log := HasDerivAt.log h_deriv_det (by rw [h_det_0]; exact one_ne_zero)
    rw [h_det_0, div_one] at h_log
    exact h_log

  have h_deriv_g : HasDerivAt (fun (t : ℝ) => forsterPotential u (P + t • X) - ((Fintype.card ι : ℝ) / (r : ℝ)) * Real.log (P + t • X).det)
      ((∑ x, forsterQuad X (u x) / forsterQuad P (u x)) - ((Fintype.card ι : ℝ) / (r : ℝ)) * (P⁻¹ * X).trace) 0 := by
    exact h_deriv_fp.sub (h_deriv_log.const_mul _)

  have h_is_min := isLocalMin_g hr u hu P hP hdet hmin X hX
  have h_zero := IsLocalMin.hasDerivAt_eq_zero h_is_min h_deriv_g
  linarith

private theorem my_trace_mul_single {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (i j : Fin r) (c : ℝ) :
    (A * single i j c).trace = A j i * c := by
  change (∑ l, (A * single i j c) l l) = A j i * c
  have h_diag : ∀ l, (A * single i j c) l l = if j = l then A j i * c else 0 := by
    intro l
    rw [mul_apply]
    split_ifs with hl
    · subst hl
      rw [Finset.sum_eq_single i]
      · rw [single_apply, if_pos ⟨rfl, rfl⟩]
      · intro b _ hb
        rw [single_apply]
        have h_cond : ¬(i = b ∧ j = j) := fun h => hb h.1.symm
        rw [if_neg h_cond, mul_zero]
      · intro hb; exact False.elim (hb (Finset.mem_univ i))
    · rw [Finset.sum_eq_zero]
      intro b _
      rw [single_apply]
      have h_cond : ¬(i = b ∧ j = l) := fun h => hl h.2
      rw [if_neg h_cond, mul_zero]
  simp_rw [h_diag]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
  · intro hb; exact False.elim (hb (Finset.mem_univ j))

private theorem momrec_forsterQuad_single {r : ℕ} (i j : Fin r) (c : ℝ) (z : EuclideanSpace ℝ (Fin r)) :
    forsterQuad (single i j c) z = c * (WithLp.equiv 2 _ z i) * (WithLp.equiv 2 _ z j) := by
  change ∑ x, (WithLp.equiv 2 _ z) x * ∑ y, (single i j c) x y * (WithLp.equiv 2 _ z) y = _
  have h1 : ∀ x, (∑ y, (single i j c) x y * WithLp.equiv 2 (Fin r → ℝ) z y) =
      if i = x then c * WithLp.equiv 2 (Fin r → ℝ) z j else 0 := by
    intro x
    split_ifs with hx
    · rw [Finset.sum_eq_single j]
      · rw [single_apply, if_pos ⟨hx, rfl⟩]
      · intro b _ hb
        rw [single_apply]
        have h_cond : ¬(i = x ∧ j = b) := fun h => hb h.2.symm
        rw [if_neg h_cond, zero_mul]
      · intro hb; exact False.elim (hb (Finset.mem_univ j))
    · rw [Finset.sum_eq_zero]
      intro b _
      rw [single_apply]
      have h_cond : ¬(i = x ∧ j = b) := fun h => hx h.1
      rw [if_neg h_cond, zero_mul]
  simp_rw [h1]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]; ring
  · intro b _ hb
    rw [if_neg (Ne.symm hb), mul_zero]
  · intro hb; exact False.elim (hb (Finset.mem_univ i))

private theorem forsterQuad_add {r : ℕ} (X Y : Matrix (Fin r) (Fin r) ℝ) (z : EuclideanSpace ℝ (Fin r)) :
    forsterQuad (X + Y) z = forsterQuad X z + forsterQuad Y z := by
  change ∑ x, (WithLp.equiv 2 _ z) x * ∑ y, (X + Y) x y * (WithLp.equiv 2 _ z) y =
    (∑ x, (WithLp.equiv 2 _ z) x * ∑ y, X x y * (WithLp.equiv 2 _ z) y) +
    (∑ x, (WithLp.equiv 2 _ z) x * ∑ y, Y x y * (WithLp.equiv 2 _ z) y)
  simp_rw [Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_add_distrib]

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
  ext i j
  have hP_inv_symm : P⁻¹ j i = P⁻¹ i j := by
    have h_symm : Pᵀ = P := by
      ext a b
      exact hP.1 b a
    have h1 : P⁻¹ᵀ = Pᵀ⁻¹ := transpose_nonsing_inv P
    rw [h_symm] at h1
    have h2 := congr_fun (congr_fun h1 i) j
    exact h2
  rw [Matrix.smul_apply, smul_eq_mul]
  have h_sum_entry : (∑ x, (forsterQuad P (u x))⁻¹ •
        Matrix.vecMulVec (WithLp.equiv 2 _ (u x)) (WithLp.equiv 2 _ (u x))) i j =
      ∑ x, ((forsterQuad P (u x))⁻¹ •
        Matrix.vecMulVec (WithLp.equiv 2 _ (u x)) (WithLp.equiv 2 _ (u x))) i j := by
    exact Matrix.sum_apply i j Finset.univ _
  rw [h_sum_entry]
  simp_rw [Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
  by_cases hij : i = j
  · subst hij
    have hX_symm : ∀ a b, (single i i (1 : ℝ)) a b = (single i i (1 : ℝ)) b a := by
      intro a b
      have h_trans : (single i i (1 : ℝ))ᵀ = single i i (1 : ℝ) := transpose_single i i (1 : ℝ)
      have h_eq := congr_fun (congr_fun h_trans b) a
      exact h_eq
    have h1 := hfo (single i i 1) hX_symm
    have h_q_i : ∀ x, forsterQuad (single i i 1) (u x) = (WithLp.equiv 2 (Fin r → ℝ) (u x) i) * (WithLp.equiv 2 (Fin r → ℝ) (u x) i) := by
      intro x
      rw [momrec_forsterQuad_single i i 1, one_mul]
    have h_tr : (P⁻¹ * single i i 1).trace = P⁻¹ i i := by
      rw [my_trace_mul_single P⁻¹ i i 1, mul_one]
    rw [h_tr] at h1
    simp_rw [h_q_i] at h1
    have h_lhs : ∀ x, (forsterQuad P (u x))⁻¹ * (WithLp.equiv 2 (Fin r → ℝ) (u x) i * WithLp.equiv 2 (Fin r → ℝ) (u x) i) =
        (WithLp.equiv 2 (Fin r → ℝ) (u x) i * WithLp.equiv 2 (Fin r → ℝ) (u x) i) / forsterQuad P (u x) := by
      intro x; ring
    simp_rw [h_lhs]
    exact h1
  · have hX_symm : ∀ a b, (single i j (1 : ℝ) + single j i (1 : ℝ)) a b = (single i j (1 : ℝ) + single j i (1 : ℝ)) b a := by
      intro a b
      rw [Matrix.add_apply, Matrix.add_apply]
      have h1 : single i j (1 : ℝ) a b = single j i (1 : ℝ) b a := by
        have h_trans : (single i j (1 : ℝ))ᵀ = single j i (1 : ℝ) := transpose_single i j (1 : ℝ)
        have h_eq := congr_fun (congr_fun h_trans b) a
        exact h_eq
      have h2 : single j i (1 : ℝ) a b = single i j (1 : ℝ) b a := by
        have h_trans : (single j i (1 : ℝ))ᵀ = single i j (1 : ℝ) := transpose_single j i (1 : ℝ)
        have h_eq := congr_fun (congr_fun h_trans b) a
        exact h_eq
      rw [h1, h2, add_comm]
    have h1 := hfo (single i j 1 + single j i 1) hX_symm
    have h_quad : ∀ z, forsterQuad (single i j 1 + single j i 1) z = 2 * (WithLp.equiv 2 _ z i * WithLp.equiv 2 _ z j) := by
      intro z
      rw [forsterQuad_add, momrec_forsterQuad_single, momrec_forsterQuad_single]
      ring
    have h_trace : (P⁻¹ * (single i j 1 + single j i 1)).trace = 2 * P⁻¹ i j := by
      rw [mul_add, trace_add, my_trace_mul_single P⁻¹, my_trace_mul_single P⁻¹, mul_one, mul_one, hP_inv_symm]
      ring
    rw [h_trace] at h1
    simp_rw [h_quad] at h1
    have h_term : ∀ x, 2 * (WithLp.equiv 2 (Fin r → ℝ) (u x) i * WithLp.equiv 2 (Fin r → ℝ) (u x) j) / forsterQuad P (u x) =
        2 * ((forsterQuad P (u x))⁻¹ * (WithLp.equiv 2 (Fin r → ℝ) (u x) i * WithLp.equiv 2 (Fin r → ℝ) (u x) j)) := by
      intro x; ring
    simp_rw [h_term] at h1
    rw [← Finset.mul_sum] at h1
    have h_rhs : (Fintype.card ι : ℝ) / r * (2 * P⁻¹ i j) = 2 * (((Fintype.card ι : ℝ) / r) * P⁻¹ i j) := by ring
    rw [h_rhs] at h1
    linarith

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
  have hP_herm : Matrix.IsHermitian P := by
    ext i j
    change star (P j i) = P i j
    simp [hP.1 i j]
  let U : Matrix (Fin r) (Fin r) ℝ := hP_herm.eigenvectorUnitary
  let D : Matrix (Fin r) (Fin r) ℝ := diagonal (fun i => Real.sqrt (hP_herm.eigenvalues i))
  let B : Matrix (Fin r) (Fin r) ℝ := U * D * star U
  have heig : ∀ i, 0 < hP_herm.eigenvalues i := by
    intro i
    have heq := hP_herm.eigenvalues_eq i
    change hP_herm.eigenvalues i = ⇑(hP_herm.eigenvectorBasis i) ⬝ᵥ (P *ᵥ ⇑(hP_herm.eigenvectorBasis i)) at heq
    rw [heq]
    apply hP.2
    have hnorm := hP_herm.eigenvectorBasis.orthonormal.1 i
    intro h
    have h2 : hP_herm.eigenvectorBasis i = 0 := by
      ext j
      exact congrFun h j
    rw [h2] at hnorm
    simp at hnorm
  have hB_herm : Matrix.IsHermitian B := by
    dsimp [B]
    change star (U * D * star U) = U * D * star U
    rw [star_mul, star_mul, star_star]
    have hD : star D = D := isHermitian_diagonal (fun i => Real.sqrt (hP_herm.eigenvalues i))
    rw [hD, Matrix.mul_assoc]
  have hB_symm : ∀ i j, B i j = B j i := by
    intro i j
    have h1 := congrFun (congrFun hB_herm i) j
    change star (B j i) = B i j at h1
    simp only [star_trivial] at h1
    exact h1.symm
  use B
  constructor
  · constructor
    · exact hB_symm
    · intro z hz
      dsimp [B]
      have h1 : z ⬝ᵥ ((U * D * star U) *ᵥ z) = z ⬝ᵥ (U *ᵥ (D *ᵥ (star U *ᵥ z))) := by
        rw [mulVec_mulVec, mulVec_mulVec]
      rw [h1]
      have h2 : z ⬝ᵥ (U *ᵥ (D *ᵥ (star U *ᵥ z))) = (z ᵥ* U) ⬝ᵥ (D *ᵥ (star U *ᵥ z)) := by
        exact dotProduct_mulVec z U (D *ᵥ (star U *ᵥ z))
      rw [h2]
      have h3 : z ᵥ* U = star U *ᵥ z := by
        have ht : Uᵀ = star U := by ext i j; rfl
        have h4 := vecMul_transpose Uᵀ z
        rw [transpose_transpose] at h4
        rw [h4, ht]
      rw [h3]
      let w := star U *ᵥ z
      change 0 < w ⬝ᵥ (D *ᵥ w)
      have hw : w ≠ 0 := by
        intro hw0
        have h_zero : U *ᵥ w = 0 := by rw [hw0, Matrix.mulVec_zero]
        change U *ᵥ (star U *ᵥ z) = 0 at h_zero
        have h_zero_2 : (U * star U) *ᵥ z = 0 := by
          have h_eq : (U * star U) *ᵥ z = U *ᵥ (star U *ᵥ z) := by rw [mulVec_mulVec]
          rw [h_eq]
          exact h_zero
        have hU : U * star U = 1 := Unitary.coe_mul_star_self hP_herm.eigenvectorUnitary
        rw [hU, Matrix.one_mulVec] at h_zero_2
        exact hz h_zero_2
      have h_sum : w ⬝ᵥ (D *ᵥ w) = ∑ i, Real.sqrt (hP_herm.eigenvalues i) * (w i) ^ 2 := by
        dsimp [D, dotProduct]
        apply Finset.sum_congr rfl
        intro i _
        have hd : (diagonal (fun i => √(hP_herm.eigenvalues i)) *ᵥ w) i = √(hP_herm.eigenvalues i) * w i := by
          exact mulVec_diagonal (fun i => √(hP_herm.eigenvalues i)) w i
        rw [hd]
        ring
      rw [h_sum]
      have h_pos : 0 < ∑ i, Real.sqrt (hP_herm.eigenvalues i) * (w i) ^ 2 := by
        apply Finset.sum_pos'
        · intro i _
          apply mul_nonneg
          · apply Real.sqrt_nonneg
          · exact sq_nonneg (w i)
        · have hw2 : ∃ i, w i ≠ 0 := by
            by_contra hc
            push Not at hc
            have h_w0 : w = 0 := by ext i; exact hc i
            exact hw h_w0
          rcases hw2 with ⟨k, hk⟩
          use k
          constructor
          · exact Finset.mem_univ k
          · apply mul_pos
            · exact Real.sqrt_pos.mpr (heig k)
            · exact sq_pos_of_ne_zero hk
      exact h_pos
  · show B * B = P
    calc
      B * B = U * D * star U * (U * D * star U) := rfl
      _ = U * D * (star U * U) * D * star U := by simp only [Matrix.mul_assoc]
      _ = U * D * 1 * D * star U := by
        have hU : star U * U = 1 := Unitary.coe_star_mul_self hP_herm.eigenvectorUnitary
        rw [hU]
      _ = U * (D * D) * star U := by simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = U * diagonal (hP_herm.eigenvalues) * star U := by
        have hD_sq : D * D = diagonal (hP_herm.eigenvalues) := by
          dsimp [D]
          rw [diagonal_mul_diagonal]
          congr
          ext i
          exact Real.mul_self_sqrt (le_of_lt (heig i))
        rw [hD_sq]
      _ = P := by
        have hSpec := hP_herm.spectral_theorem
        symm
        change P = U * diagonal (fun i => (hP_herm.eigenvalues i : ℝ)) * star U
        change P = ((Unitary.conjStarAlgAut ℝ (Matrix (Fin r) (Fin r) ℝ)) hP_herm.eigenvectorUnitary) (diagonal (fun i => (hP_herm.eigenvalues i : ℝ)))
        exact hSpec

/-! ### P5.3b normalized-transform decomposition -/

/-- The primal transform used in Forster repositioning. -/
noncomputable def forsterPrimalTransform {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℝ) (z : EuclideanSpace ℝ (Fin r)) :
    EuclideanSpace ℝ (Fin r) :=
  (WithLp.equiv 2 (Fin r → ℝ)).symm (B *ᵥ (WithLp.equiv 2 (Fin r → ℝ) z))

/-- The inverse dual transform paired with `forsterPrimalTransform`. -/
noncomputable def forsterDualTransform {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℝ) (z : EuclideanSpace ℝ (Fin r)) :
    EuclideanSpace ℝ (Fin r) :=
  (WithLp.equiv 2 (Fin r → ℝ)).symm (B⁻¹ *ᵥ (WithLp.equiv 2 (Fin r → ℝ) z))

/-- Normalize the primal transform by its (nonzero) norm. -/
noncomputable def normalizedForsterPrimal {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℝ) (z : EuclideanSpace ℝ (Fin r)) :
    EuclideanSpace ℝ (Fin r) :=
  (‖forsterPrimalTransform B z‖⁻¹ : ℝ) • forsterPrimalTransform B z

/-- Normalize the inverse dual transform by its (nonzero) norm. -/
noncomputable def normalizedForsterDual {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℝ) (z : EuclideanSpace ℝ (Fin r)) :
    EuclideanSpace ℝ (Fin r) :=
  (‖forsterDualTransform B z‖⁻¹ : ℝ) • forsterDualTransform B z

/-- **P5.3b-F8a (unit/sign transform).**  If `B` is positive definite, its
primal action and inverse dual action are injective.  Normalizing both images
therefore gives unit vectors, while symmetry of `B` and
`B * B⁻¹ = 1` show that the unnormalized inner product is unchanged.
The two normalization factors are positive, so every strict sign is
preserved. -/
lemma normalizedForsterTransforms_unit_sign
    {r : ℕ} {ι : Type*} [Fintype ι]
    (u v : ι → EuclideanSpace ℝ (Fin r))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ y, ‖v y‖ = 1)
    (s : ι → ι → ℝ) (hs : ∀ x y, 0 < s x y * ⟪u x, v y⟫_ℝ)
    (B : Matrix (Fin r) (Fin r) ℝ) (hB : ForsterPosDef B) :
    (∀ x, ‖normalizedForsterPrimal B (u x)‖ = 1) ∧
      (∀ y, ‖normalizedForsterDual B (v y)‖ = 1) ∧
      ∀ x y, 0 < s x y *
        ⟪normalizedForsterPrimal B (u x), normalizedForsterDual B (v y)⟫_ℝ := by
  have hB_det : B.det ≠ 0 := forsterPosDef_det_ne_zero hB
  have hB_det_unit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB_det
  have hB_unit : IsUnit B := B.isUnit_iff_isUnit_det.mpr hB_det_unit
  have hB_inv_det_unit : IsUnit B⁻¹.det := B.isUnit_nonsing_inv_det hB_det_unit
  have hB_inv_unit : IsUnit B⁻¹ := B⁻¹.isUnit_iff_isUnit_det.mpr hB_inv_det_unit
  have hB_symm : Bᵀ = B := by
    ext i j
    exact hB.1 j i
  have hu_ne : ∀ x, u x ≠ 0 := by
    intro x hx
    have := hu x
    rw [hx, norm_zero] at this
    exact zero_ne_one this
  have hv_ne : ∀ y, v y ≠ 0 := by
    intro y hy
    have := hv y
    rw [hy, norm_zero] at this
    exact zero_ne_one this
  have hprimal_ne : ∀ x, forsterPrimalTransform B (u x) ≠ 0 := by
    intro x hx
    have hmul : B *ᵥ (WithLp.equiv 2 (Fin r → ℝ) (u x)) = 0 := by
      have := congrArg (WithLp.equiv 2 (Fin r → ℝ)) hx
      simpa [forsterPrimalTransform] using this
    have hmul' : B *ᵥ (WithLp.equiv 2 (Fin r → ℝ) (u x)) = B *ᵥ 0 := by
      simpa using hmul
    have hvec : WithLp.equiv 2 (Fin r → ℝ) (u x) = 0 :=
      (Matrix.mulVec_injective_iff_isUnit.mpr hB_unit) hmul'
    exact hu_ne x ((WithLp.equiv 2 (Fin r → ℝ)).injective hvec)
  have hdual_ne : ∀ y, forsterDualTransform B (v y) ≠ 0 := by
    intro y hy
    have hmul : B⁻¹ *ᵥ (WithLp.equiv 2 (Fin r → ℝ) (v y)) = 0 := by
      have := congrArg (WithLp.equiv 2 (Fin r → ℝ)) hy
      simpa [forsterDualTransform] using this
    have hmul' : B⁻¹ *ᵥ (WithLp.equiv 2 (Fin r → ℝ) (v y)) = B⁻¹ *ᵥ 0 := by
      simpa using hmul
    have hvec : WithLp.equiv 2 (Fin r → ℝ) (v y) = 0 :=
      (Matrix.mulVec_injective_iff_isUnit.mpr hB_inv_unit) hmul'
    exact hv_ne y ((WithLp.equiv 2 (Fin r → ℝ)).injective hvec)
  have hinner : ∀ x y,
      ⟪forsterPrimalTransform B (u x), forsterDualTransform B (v y)⟫_ℝ =
        ⟪u x, v y⟫_ℝ := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct,
      EuclideanSpace.inner_eq_star_dotProduct]
    change
      (B⁻¹ *ᵥ WithLp.equiv 2 (Fin r → ℝ) (v y)) ⬝ᵥ
          (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x)) =
        WithLp.equiv 2 (Fin r → ℝ) (v y) ⬝ᵥ
          WithLp.equiv 2 (Fin r → ℝ) (u x)
    rw [dotProduct_comm (B⁻¹ *ᵥ WithLp.equiv 2 (Fin r → ℝ) (v y)),
      dotProduct_comm (WithLp.equiv 2 (Fin r → ℝ) (v y))]
    calc
      (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ
          (B⁻¹ *ᵥ WithLp.equiv 2 (Fin r → ℝ) (v y)) =
          ((WithLp.equiv 2 (Fin r → ℝ) (u x)) ᵥ* Bᵀ) ⬝ᵥ
            (B⁻¹ *ᵥ WithLp.equiv 2 (Fin r → ℝ) (v y)) := by
              rw [Matrix.vecMul_transpose]
      _ = ((WithLp.equiv 2 (Fin r → ℝ) (u x)) ᵥ* B) ⬝ᵥ
            (B⁻¹ *ᵥ WithLp.equiv 2 (Fin r → ℝ) (v y)) := by rw [hB_symm]
      _ = (((WithLp.equiv 2 (Fin r → ℝ) (u x)) ᵥ* B) ᵥ* B⁻¹) ⬝ᵥ
            WithLp.equiv 2 (Fin r → ℝ) (v y) :=
              Matrix.dotProduct_mulVec _ _ _
      _ = (WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ
            WithLp.equiv 2 (Fin r → ℝ) (v y) := by
              rw [Matrix.vecMul_vecMul, B.mul_nonsing_inv hB_det_unit,
                Matrix.vecMul_one]
  refine ⟨fun x ↦ ?_, fun y ↦ ?_, ?_⟩
  · exact norm_normalize_eq_one (hprimal_ne x)
  · exact norm_normalize_eq_one (hdual_ne y)
  · intro x y
    rw [normalizedForsterPrimal, normalizedForsterDual,
      real_inner_smul_left, real_inner_smul_right, hinner]
    have hp : 0 < ‖forsterPrimalTransform B (u x)‖⁻¹ :=
      inv_pos.mpr (norm_pos_iff.mpr (hprimal_ne x))
    have hd : 0 < ‖forsterDualTransform B (v y)‖⁻¹ :=
      inv_pos.mpr (norm_pos_iff.mpr (hdual_ne y))
    nlinarith [mul_pos (mul_pos hp hd) (hs x y)]

/-- **P5.3b-F8b (isotropy transform).**  Substitute the moment-matrix
identity into the quadratic form of the normalized primal images.  Their
squared norms are `forsterQuad P (u x)` because `B` is symmetric and
`B * B = P`; after summing, `B * P⁻¹ * B = 1` reduces the result to
`(N/r) * ‖w‖²`. -/
lemma normalizedForsterPrimal_isotropic
    {r : ℕ} {ι : Type*} [Fintype ι]
    (hr : 0 < r) (u : ι → EuclideanSpace ℝ (Fin r))
    (hu : ∀ x, ‖u x‖ = 1)
    (P B : Matrix (Fin r) (Fin r) ℝ) (hB : ForsterPosDef B)
    (hBB : B * B = P)
    (hmoment :
      ∑ x, (forsterQuad P (u x))⁻¹ •
          Matrix.vecMulVec (WithLp.equiv 2 _ (u x)) (WithLp.equiv 2 _ (u x)) =
        ((Fintype.card ι : ℝ) / r) • P⁻¹) :
    ∀ w : EuclideanSpace ℝ (Fin r),
      ∑ x, ⟪normalizedForsterPrimal B (u x), w⟫_ℝ ^ 2 =
        (Fintype.card ι : ℝ) / r * ‖w‖ ^ 2 := by
  have hB_det : B.det ≠ 0 := forsterPosDef_det_ne_zero hB
  have hB_det_unit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB_det
  have hB_unit : IsUnit B := B.isUnit_iff_isUnit_det.mpr hB_det_unit
  have hB_symm : Bᵀ = B := by
    ext i j
    exact hB.1 j i
  have hu_ne : ∀ x, u x ≠ 0 := by
    intro x hx
    have := hu x
    rw [hx, norm_zero] at this
    exact zero_ne_one this
  have hprimal_ne : ∀ x, forsterPrimalTransform B (u x) ≠ 0 := by
    intro x hx
    have hmul : B *ᵥ (WithLp.equiv 2 (Fin r → ℝ) (u x)) = 0 := by
      have := congrArg (WithLp.equiv 2 (Fin r → ℝ)) hx
      simpa [forsterPrimalTransform] using this
    have hmul' : B *ᵥ (WithLp.equiv 2 (Fin r → ℝ) (u x)) = B *ᵥ 0 := by
      simpa using hmul
    have hvec : WithLp.equiv 2 (Fin r → ℝ) (u x) = 0 :=
      (Matrix.mulVec_injective_iff_isUnit.mpr hB_unit) hmul'
    exact hu_ne x ((WithLp.equiv 2 (Fin r → ℝ)).injective hvec)
  have hprimal_norm_sq : ∀ x,
      ‖forsterPrimalTransform B (u x)‖ ^ 2 = forsterQuad P (u x) := by
    intro x
    rw [forsterPrimalTransform, norm_sq_eq_local]
    change (∑ i, (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x)) i ^ 2) =
      (WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ
        (P *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x))
    calc
      (∑ i, (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x)) i ^ 2) =
          (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ
            (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x)) := by
              simp [dotProduct, pow_two]
      _ = ((WithLp.equiv 2 (Fin r → ℝ) (u x)) ᵥ* Bᵀ) ⬝ᵥ
            (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x)) := by
              rw [Matrix.vecMul_transpose]
      _ = ((WithLp.equiv 2 (Fin r → ℝ) (u x)) ᵥ* B) ⬝ᵥ
            (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x)) := by rw [hB_symm]
      _ = (WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ
            (B *ᵥ (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x))) := by
              exact (Matrix.dotProduct_mulVec _ _ _).symm
      _ = (WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ
            (P *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x)) := by
              rw [Matrix.mulVec_mulVec, hBB]
  have hinv_norm_sq : ∀ x,
      ‖forsterPrimalTransform B (u x)‖⁻¹ ^ 2 =
        (forsterQuad P (u x))⁻¹ := by
    intro x
    rw [inv_pow, hprimal_norm_sq]
  have hP_unit : IsUnit P := by
    rw [← hBB]
    exact hB_unit.mul hB_unit
  have hP_det_unit : IsUnit P.det := P.isUnit_iff_isUnit_det.mp hP_unit
  have hPB_inv : P * B⁻¹ = B := by
    rw [← hBB, Matrix.mul_assoc, B.mul_nonsing_inv hB_det_unit, Matrix.mul_one]
  have hcancel : B * P⁻¹ * B = 1 := by
    calc
      B * P⁻¹ * B = B * P⁻¹ * (P * B⁻¹) := by rw [hPB_inv]
      _ = B * (P⁻¹ * P) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [P.nonsing_inv_mul hP_det_unit, Matrix.mul_one,
          B.mul_nonsing_inv hB_det_unit]
  intro w
  let z : Fin r → ℝ := B *ᵥ (WithLp.equiv 2 (Fin r → ℝ) w)
  have hinner : ∀ x,
      ⟪forsterPrimalTransform B (u x), w⟫_ℝ =
        (WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ z := by
    intro x
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change
      (WithLp.equiv 2 (Fin r → ℝ) w) ⬝ᵥ
          (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x)) =
        (WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ z
    calc
      (WithLp.equiv 2 (Fin r → ℝ) w) ⬝ᵥ
          (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) (u x)) =
          (WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ
            (Bᵀ *ᵥ WithLp.equiv 2 (Fin r → ℝ) w) :=
              (Matrix.dotProduct_transpose_mulVec B
                (WithLp.equiv 2 (Fin r → ℝ) (u x))
                (WithLp.equiv 2 (Fin r → ℝ) w)).symm
      _ = (WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ z := by rw [hB_symm]
  have hsum_mulVec :
      (∑ x, (forsterQuad P (u x))⁻¹ •
          Matrix.vecMulVec (WithLp.equiv 2 _ (u x)) (WithLp.equiv 2 _ (u x))) *ᵥ z =
        ∑ x, ((forsterQuad P (u x))⁻¹ •
          Matrix.vecMulVec (WithLp.equiv 2 _ (u x)) (WithLp.equiv 2 _ (u x))) *ᵥ z := by
    simpa using Matrix.sum_mulVec Finset.univ
      (fun x ↦ (forsterQuad P (u x))⁻¹ •
        Matrix.vecMulVec (WithLp.equiv 2 _ (u x)) (WithLp.equiv 2 _ (u x))) z
  have hleft :
      z ⬝ᵥ ((∑ x, (forsterQuad P (u x))⁻¹ •
          Matrix.vecMulVec (WithLp.equiv 2 _ (u x)) (WithLp.equiv 2 _ (u x))) *ᵥ z) =
        ∑ x, (forsterQuad P (u x))⁻¹ *
          ((WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ z) ^ 2 := by
    rw [hsum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, dotProduct_smul]
    rw [op_smul_eq_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [dotProduct_comm z (WithLp.equiv 2 (Fin r → ℝ) (u x))]
    ring
  have hquad_cancel : z ⬝ᵥ (P⁻¹ *ᵥ z) = ‖w‖ ^ 2 := by
    change
      (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) w) ⬝ᵥ
          (P⁻¹ *ᵥ (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) w)) = ‖w‖ ^ 2
    calc
      (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) w) ⬝ᵥ
          (P⁻¹ *ᵥ (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) w)) =
          ((WithLp.equiv 2 (Fin r → ℝ) w) ᵥ* Bᵀ) ⬝ᵥ
            (P⁻¹ *ᵥ (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) w)) := by
              rw [Matrix.vecMul_transpose]
      _ = ((WithLp.equiv 2 (Fin r → ℝ) w) ᵥ* B) ⬝ᵥ
            (P⁻¹ *ᵥ (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) w)) := by rw [hB_symm]
      _ = (((WithLp.equiv 2 (Fin r → ℝ) w) ᵥ* B) ᵥ* P⁻¹) ⬝ᵥ
            (B *ᵥ WithLp.equiv 2 (Fin r → ℝ) w) :=
              Matrix.dotProduct_mulVec _ _ _
      _ = ((((WithLp.equiv 2 (Fin r → ℝ) w) ᵥ* B) ᵥ* P⁻¹) ᵥ* B) ⬝ᵥ
            WithLp.equiv 2 (Fin r → ℝ) w := Matrix.dotProduct_mulVec _ _ _
      _ = ((WithLp.equiv 2 (Fin r → ℝ) w) ᵥ* (B * P⁻¹ * B)) ⬝ᵥ
            WithLp.equiv 2 (Fin r → ℝ) w := by
              rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]
              simp only [Matrix.mul_assoc]
      _ = (WithLp.equiv 2 (Fin r → ℝ) w) ⬝ᵥ
            WithLp.equiv 2 (Fin r → ℝ) w := by rw [hcancel, Matrix.vecMul_one]
      _ = ‖w‖ ^ 2 := by
        rw [dotProduct]
        calc
          (∑ i, (WithLp.equiv 2 (Fin r → ℝ) w) i *
              (WithLp.equiv 2 (Fin r → ℝ) w) i) =
              ∑ i, (WithLp.equiv 2 (Fin r → ℝ) w) i ^ 2 := by
                apply Finset.sum_congr rfl
                intro i _
                rw [pow_two]
          _ = ‖(WithLp.equiv 2 (Fin r → ℝ)).symm
              (WithLp.equiv 2 (Fin r → ℝ) w)‖ ^ 2 :=
                (norm_sq_eq_local _).symm
          _ = ‖w‖ ^ 2 := by simp
  have hmoment_quad := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ ↦
    z ⬝ᵥ (M *ᵥ z)) hmoment
  have hweighted :
      ∑ x, (forsterQuad P (u x))⁻¹ *
          ((WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ z) ^ 2 =
        (Fintype.card ι : ℝ) / r * ‖w‖ ^ 2 := by
    rw [hleft] at hmoment_quad
    rw [Matrix.smul_mulVec, dotProduct_smul, hquad_cancel] at hmoment_quad
    simpa [smul_eq_mul] using hmoment_quad
  calc
    (∑ x, ⟪normalizedForsterPrimal B (u x), w⟫_ℝ ^ 2) =
        ∑ x, (forsterQuad P (u x))⁻¹ *
          ((WithLp.equiv 2 (Fin r → ℝ) (u x)) ⬝ᵥ z) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [normalizedForsterPrimal, real_inner_smul_left, hinner,
        mul_pow, hinv_norm_sq]
    _ = (Fintype.card ι : ℝ) / r * ‖w‖ ^ 2 := hweighted

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
  have hfo : ∀ X : Matrix (Fin r) (Fin r) ℝ, (∀ i j, X i j = X j i) →
      ∑ x, forsterQuad X (u x) / forsterQuad P (u x) =
        (Fintype.card ι : ℝ) / r * (P⁻¹ * X).trace := by
    intro X hX
    exact forster_first_order hr u hu P hP hdet hmin X hX
  have hmoment := forster_moment_matrix hr u hu P hP hfo
  obtain ⟨B, hB, hBB⟩ := exists_forster_sqrt P hP
  have hunit_sign := normalizedForsterTransforms_unit_sign u v hu hv s hs B hB
  refine ⟨fun x ↦ normalizedForsterPrimal B (u x),
    fun y ↦ normalizedForsterDual B (v y), hunit_sign.1, hunit_sign.2.1,
    hunit_sign.2.2, ?_⟩
  exact normalizedForsterPrimal_isotropic hr u hu P B hB hBB hmoment

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
