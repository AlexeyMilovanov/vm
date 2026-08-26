import HeadComplexity.TypicalLogCloseness.PowerBlockPartition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Roots

set_option linter.style.header false

/-!
# Singular localization matrix and deformation to legal denominators
-/

namespace HeadComplexity.TypicalLogCloseness

open Finset
open scoped BigOperators Matrix

variable {n : ℕ}

/-- The cleared square matrix, already reindexed by the partition equivalence. -/
noncomputable def clearedMatrix (L : LocalizationData n)
    (B : Fin L.groupCount → AffineForm n) :
    Matrix (Fin L.groupCount × Fin L.blockSize)
      (Fin L.groupCount × Fin L.blockSize) ℝ :=
  fun row col =>
    (L.lagrange col.1 col.2).eval (L.vertex row) *
      ∏ g ∈ (Finset.univ.erase col.1), (B g).eval (L.vertex row)

/-- At the singular denominator tuple, the cleared matrix has nonzero determinant. -/
theorem singular_det_ne_zero (L : LocalizationData n) :
    Matrix.det (clearedMatrix L L.ell) ≠ 0 := by
  classical
  let d : Fin L.groupCount × Fin L.blockSize → ℝ := fun row =>
    ∏ g ∈ (Finset.univ.erase row.1), (L.ell g).eval (L.vertex row)
  have hmatrix : clearedMatrix L L.ell = Matrix.diagonal d := by
    ext row col
    rcases row with ⟨g, k⟩
    rcases col with ⟨g', i⟩
    by_cases hrow : (g, k) = (g', i)
    · cases hrow
      rw [Matrix.diagonal_apply_eq]
      simp only [clearedMatrix, d]
      rw [L.lagrange_delta g k k]
      simp
    · rw [Matrix.diagonal_apply_ne _ hrow]
      by_cases hgroup : g' = g
      · subst g'
        have hindex : i ≠ k := by
          intro hik
          apply hrow
          simp [hik]
        simp only [clearedMatrix]
        rw [L.lagrange_delta g i k, if_neg hindex, zero_mul]
      · have hgmem : g ∈ (Finset.univ.erase g') := by
          exact Finset.mem_erase.mpr ⟨Ne.symm hgroup, Finset.mem_univ g⟩
        have hzero : (L.ell g).eval (L.vertex (g, k)) = 0 :=
          (L.ell_zero_iff g (g, k)).2 rfl
        simp only [clearedMatrix]
        rw [Finset.prod_eq_zero hgmem hzero, mul_zero]
  rw [hmatrix, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun row _ => by
    dsimp [d]
    exact Finset.prod_ne_zero_iff.mpr fun g hg => by
      rw [Finset.mem_erase] at hg
      intro hzero
      exact hg.1 ((L.ell_zero_iff g row).mp hzero)

/-- The legal one-parameter deformation of a localization equation. -/
def legalPath (L : LocalizationData n) (T : ℝ) (g : Fin L.groupCount) :
    AffineForm n :=
  (L.ell g).add ((AffineForm.positiveDirection n).smul T)

private theorem exists_nat_add_pos [Fintype ι] (a : ι → ℝ) :
    ∃ N : ℕ, ∀ i, 0 < a i + N := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ i, |a i|)
  refine ⟨N, fun i => ?_⟩
  have hi : |a i| ≤ ∑ j, |a j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  have hneg := neg_abs_le (a i)
  norm_num at hN ⊢
  linarith

/-- The cleared matrix along the legal path, with polynomial entries. -/
noncomputable def clearedPolynomialMatrix (L : LocalizationData n) :
    Matrix (Fin L.groupCount × Fin L.blockSize)
      (Fin L.groupCount × Fin L.blockSize) (Polynomial ℝ) :=
  fun row col =>
    Polynomial.C ((L.lagrange col.1 col.2).eval (L.vertex row)) *
      ∏ g ∈ Finset.univ.erase col.1,
        (Polynomial.C ((L.ell g).eval (L.vertex row)) +
          Polynomial.X *
            Polynomial.C ((AffineForm.positiveDirection n).eval (L.vertex row)))

/-- The determinant along the legal path, regarded as a univariate polynomial. -/
noncomputable def clearedDetPolynomial (L : LocalizationData n) : Polynomial ℝ :=
  Matrix.det (clearedPolynomialMatrix L)

theorem clearedDetPolynomial_eval (L : LocalizationData n) (T : ℝ) :
    Polynomial.eval T (clearedDetPolynomial L) =
      Matrix.det (clearedMatrix L (legalPath L T)) := by
  classical
  unfold clearedDetPolynomial
  change (Polynomial.evalRingHom T) (Matrix.det (clearedPolynomialMatrix L)) =
    Matrix.det (clearedMatrix L (legalPath L T))
  rw [RingHom.map_det]
  congr 1
  ext row col
  have hprod :
      (∏ g ∈ Finset.univ.erase col.1,
          ((L.ell g).eval (L.vertex row) +
            (AffineForm.positiveDirection n).eval (L.vertex row) * T)) =
        ∏ g ∈ Finset.univ.erase col.1,
          ((L.ell g).eval (L.vertex row) +
            T * (AffineForm.positiveDirection n).eval (L.vertex row)) := by
    apply Finset.prod_congr rfl
    intro g hg
    ring
  simp [clearedPolynomialMatrix, clearedMatrix, legalPath,
    Polynomial.eval_prod, hprod]

theorem clearedDetPolynomial_ne_zero (L : LocalizationData n) :
    clearedDetPolynomial L ≠ 0 := by
  intro hzero
  have heval := congrArg (Polynomial.eval 0) hzero
  rw [clearedDetPolynomial_eval] at heval
  have hpath : legalPath L 0 = L.ell := by
    funext g
    apply AffineForm.ext
    · simp [legalPath, AffineForm.add, AffineForm.smul,
        AffineForm.positiveDirection]
    · intro i
      simp [legalPath, AffineForm.add, AffineForm.smul,
        AffineForm.positiveDirection]
  rw [hpath] at heval
  simp at heval
  exact singular_det_ne_zero L heval

/-- Some large natural parameter simultaneously makes every denominator legal
and keeps the cleared determinant nonzero. -/
theorem exists_legal_fullRank_bank (L : LocalizationData n) :
    ∃ T : ℕ, (∀ g, (legalPath L T g).PositiveCoefficients) ∧
      Matrix.det (clearedMatrix L (legalPath L T)) ≠ 0 := by
  classical
  obtain ⟨Nc, hc⟩ :=
    exists_nat_add_pos (fun g : Fin L.groupCount => (L.ell g).constant)
  obtain ⟨Nl, hl⟩ :=
    exists_nat_add_pos
      (fun z : Fin L.groupCount × Fin n => (L.ell z.1).linear z.2)
  let N := max Nc Nl
  let P := clearedDetPolynomial L
  have hP : P ≠ 0 := clearedDetPolynomial_ne_zero L
  let candidate : Fin (P.natDegree + 1) → ℝ :=
    fun i => ((N + i.1 : ℕ) : ℝ)
  have hcand : Function.Injective candidate := by
    intro i j hij
    apply Fin.ext
    dsimp [candidate] at hij
    exact Nat.add_left_cancel (Nat.cast_injective hij)
  have hex : ∃ i, Polynomial.eval (candidate i) P ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hP
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hcand hnone
    simp
  obtain ⟨i, hi⟩ := hex
  let T : ℕ := N + i.1
  refine ⟨T, ?_, ?_⟩
  · intro g
    constructor
    · have hbase := hc g
      have hNc : Nc ≤ T := by
        dsimp [T, N]
        omega
      norm_num at hbase
      simp only [legalPath, AffineForm.add, AffineForm.smul,
        AffineForm.positiveDirection]
      norm_num
      have hcast : (Nc : ℝ) ≤ T := Nat.cast_le.mpr hNc
      linarith
    · intro j
      have hbase := hl (g, j)
      have hNl : Nl ≤ T := by
        dsimp [T, N]
        omega
      norm_num at hbase
      simp only [legalPath, AffineForm.add, AffineForm.smul,
        AffineForm.positiveDirection]
      norm_num
      have hcast : (Nl : ℝ) ≤ T := Nat.cast_le.mpr hNl
      linarith
  · rw [← clearedDetPolynomial_eval]
    exact hi

/-- The actual fractional evaluation matrix. -/
noncomputable def fractionalMatrix (L : LocalizationData n)
    (B : Fin L.groupCount → AffineForm n) :
    Matrix (Fin L.groupCount × Fin L.blockSize)
      (Fin L.groupCount × Fin L.blockSize) ℝ :=
  fun row col =>
    (L.lagrange col.1 col.2).eval (L.vertex row) /
      (B col.1).eval (L.vertex row)

/-- Row scaling transfers full rank from the cleared to the fractional matrix. -/
theorem fractional_det_ne_zero (L : LocalizationData n)
    (B : Fin L.groupCount → AffineForm n)
    (hB : ∀ g, (B g).StrictLegal)
    (hdet : Matrix.det (clearedMatrix L B) ≠ 0) :
    Matrix.det (fractionalMatrix L B) ≠ 0 := by
  classical
  let rowProduct : (Fin L.groupCount × Fin L.blockSize) → ℝ := fun row =>
    ∏ g, (B g).eval (L.vertex row)
  have hmatrix :
      clearedMatrix L B =
        Matrix.of fun row col =>
          rowProduct row * fractionalMatrix L B row col := by
    ext row col
    have hbc : (B col.1).eval (L.vertex row) ≠ 0 :=
      (B col.1).eval_ne_zero (hB col.1) (L.vertex row)
    simp only [clearedMatrix, fractionalMatrix, rowProduct]
    change (L.lagrange col.1 col.2).eval (L.vertex row) *
        (∏ g ∈ Finset.univ.erase col.1, (B g).eval (L.vertex row)) =
      (∏ g, (B g).eval (L.vertex row)) *
        ((L.lagrange col.1 col.2).eval (L.vertex row) /
          (B col.1).eval (L.vertex row))
    rw [← Finset.mul_prod_erase Finset.univ
      (fun g => (B g).eval (L.vertex row)) (Finset.mem_univ col.1)]
    field_simp
    <;> ring
  have hdeteq :
      Matrix.det (clearedMatrix L B) =
        (∏ row, rowProduct row) * Matrix.det (fractionalMatrix L B) := by
    rw [hmatrix]
    exact Matrix.det_mul_column rowProduct (fractionalMatrix L B)
  intro hfractional
  apply hdet
  rw [hdeteq, hfractional, mul_zero]

/-- Affine numerator obtained by combining the Lagrange basis in one block. -/
noncomputable def lagrangeCombination (L : LocalizationData n)
    (coeff : Fin L.groupCount × Fin L.blockSize → ℝ)
    (g : Fin L.groupCount) : AffineForm n where
  constant := ∑ i, coeff (g, i) * (L.lagrange g i).constant
  linear j := ∑ i, coeff (g, i) * (L.lagrange g i).linear j

@[simp] theorem lagrangeCombination_eval (L : LocalizationData n)
    (coeff : Fin L.groupCount × Fin L.blockSize → ℝ)
    (g : Fin L.groupCount) (x : Cube n) :
    (lagrangeCombination L coeff g).eval x =
      ∑ i, coeff (g, i) * (L.lagrange g i).eval x := by
  simp only [lagrangeCombination, AffineForm.eval]
  simp_rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A legal full-rank bank spans every real truth table. -/
theorem fixedBank_spans (L : LocalizationData n)
    (B : Fin L.groupCount → AffineForm n)
    (_hB : ∀ g, (B g).StrictLegal)
    (hdet : Matrix.det (fractionalMatrix L B) ≠ 0)
    (v : Cube n → ℝ) :
    ∃ A : Fin L.groupCount → AffineForm n,
      ∀ x, v x = ∑ g, (A g).eval x / (B g).eval x := by
  classical
  let M := fractionalMatrix L B
  have hunitDet : IsUnit (Matrix.det M) := isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hunitDet
  obtain ⟨coeff, hcoeff⟩ :=
    (Matrix.mulVec_surjective_iff_isUnit.mpr hunit)
      (fun row => v (L.vertex row))
  refine ⟨lagrangeCombination L coeff, fun x => ?_⟩
  let row := L.vertex.symm x
  have hx : L.vertex row = x := L.vertex.apply_symm_apply x
  have hc :
      v (L.vertex row) =
        ∑ col, fractionalMatrix L B row col * coeff col := by
    simpa [M, Matrix.mulVec, dotProduct] using
      (congr_fun hcoeff row).symm
  rw [← hx]
  calc
    v (L.vertex row) =
        ∑ col, fractionalMatrix L B row col * coeff col := hc
    _ = ∑ g, (lagrangeCombination L coeff g).eval (L.vertex row) /
          (B g).eval (L.vertex row) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro g _
      rw [lagrangeCombination_eval, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      simp only [fractionalMatrix]
      ring

end HeadComplexity.TypicalLogCloseness
