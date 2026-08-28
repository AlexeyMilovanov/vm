import HeadComplexity.Separations.EightBitHammingThreshold.Curvature

set_option linter.style.header false

/-!
# Eight-bit Hamming threshold: two-head normalization
-/

namespace HeadComplexity

open Finset
open scoped BigOperators
open TypicalLogCloseness
open MvPolynomial
open EightBitInternal

private noncomputable def factorA
    (P Q : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : Fin 4 → ℝ :=
  fun a => P a i + Q a i

private noncomputable def factorB
    (P Q : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : Fin 4 → ℝ :=
  fun a => P a i - Q a i

private noncomputable def factorD
    (Q : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : Fin 4 → ℝ :=
  fun a => -2 * Q a i

private noncomputable def factorDelta
    (P Q : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) : ℝ :=
  -4 * splitPair (column4 P j) (column4 Q j)

private noncomputable def factorCurvature
    (P Q : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => 4 *
    (splitPair (column4 P i) (column4 Q j) +
      splitPair (column4 P j) (column4 Q i))

private theorem factorCurvature_quadratic_formula
    (P Q : Matrix (Fin 4) (Fin 4) ℝ) (z : Fin 4 → ℝ) :
    quadraticForm4 (factorCurvature P Q) z =
      8 * splitPair (P.mulVec z) (Q.mulVec z) := by
  simp only [quadraticForm4, factorCurvature, Matrix.mulVec, dotProduct,
    splitPair_formula, column4, Fin.sum_univ_four]
  ring

/-- Exact factor-map output of paper Lemma 3, with the shell information
needed by Lemma 4 and no reference to fractional-atom implementation details. -/
private structure F8FactorData where
  P : Matrix (Fin 4) (Fin 4) ℝ
  Q : Matrix (Fin 4) (Fin 4) ℝ
  r : Fin 4 → ℝ
  curvature : NegativeDefinite4 (factorCurvature P Q)
  transition : ∀ i j, i ≠ j → ∀ ε : Fin 4 → Bool,
    0 < factorDelta P Q j +
      2 * splitPair (factorD Q j) r * hammingSign (ε j) +
      2 * splitPair (factorD Q j) (factorB P Q i) *
        hammingSign (ε i) * hammingSign (ε j) +
      ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
        2 * splitPair (factorD Q j) (factorA P Q k) *
          hammingSign (ε j) * hammingSign (ε k)
  denominator_left_pos : ∀ i, 0 < P 3 i
  denominator_right_pos : ∀ i, 0 < Q 3 i
  denominator_intercept :
    (∑ i, P 3 i) + (∑ i, Q 3 i) < r 3

private theorem f8FactorData_Q_mulVec_injective (D : F8FactorData) :
    Function.Injective D.Q.mulVec := by
  intro x y hxy
  by_contra hne
  have hdiff : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hQ : D.Q.mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hzero :
      quadraticForm4 (factorCurvature D.P D.Q) (x - y) = 0 := by
    rw [factorCurvature_quadratic_formula, hQ]
    simp [splitPair]
  have hneg := D.curvature (x - y) hdiff
  linarith

private theorem f8FactorData_Q_mulVec_surjective (D : F8FactorData) :
    Function.Surjective D.Q.mulVec :=
  Matrix.mulVec_surjective_iff_isUnit.mpr
    (Matrix.mulVec_injective_iff_isUnit.mp (f8FactorData_Q_mulVec_injective D))

private noncomputable def minimizingBit (x : ℝ) : Bool := decide (x < 0)

private theorem mul_hammingSign_minimizingBit (x : ℝ) :
    x * hammingSign (minimizingBit x) = -|x| := by
  by_cases hx : x < 0
  · simp [minimizingBit, hx, abs_of_neg hx]
  · simp [minimizingBit, hx, abs_of_nonneg (le_of_not_gt hx)]

private theorem hammingSign_beq (a b : Bool) :
    hammingSign (a == b) = hammingSign a * hammingSign b := by
  cases a <;> cases b <;> simp [hammingSign]

/-- The finite ±1 minimization step in paper Lemma 4. -/
private theorem f8FactorData_shell_bound (D : F8FactorData) :
    ∀ i j, i ≠ j →
      |2 * splitPair (factorD D.Q j) D.r| +
        |2 * splitPair (factorD D.Q j) (factorB D.P D.Q i)| +
        ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
          |2 * splitPair (factorD D.Q j) (factorA D.P D.Q k)| <
        factorDelta D.P D.Q j := by
  intro i j hij
  set A0 := 2 * splitPair (factorD D.Q j) D.r
  set A1 := 2 * splitPair (factorD D.Q j) (factorB D.P D.Q i)
  set Ak := fun k => 2 * splitPair (factorD D.Q j) (factorA D.P D.Q k)
  set sj := minimizingBit A0
  set ε : Fin 4 → Bool := fun k =>
    if k = j then sj
    else if k = i then (minimizingBit A1 == sj)
    else (minimizingBit (Ak k) == sj)
  have hεj : ε j = sj := by
    dsimp [ε]
    rw [if_pos rfl]
  have hεi : ε i = (minimizingBit A1 == sj) := by
    dsimp [ε]
    rw [if_neg hij, if_pos rfl]
  have hεk (k : Fin 4) (hk : k ≠ i ∧ k ≠ j) : ε k = (minimizingBit (Ak k) == sj) := by
    dsimp [ε]
    rw [if_neg hk.2, if_neg hk.1]
  have hA0 : A0 * hammingSign (ε j) = -|A0| := by
    rw [hεj, mul_hammingSign_minimizingBit]
  have hsj_sq : hammingSign sj * hammingSign sj = 1 := by
    rcases hammingSign_cases sj with h | h <;> rw [h] <;> ring
  have hA1 : A1 * hammingSign (ε i) * hammingSign (ε j) = -|A1| := by
    rw [hεi, hεj, hammingSign_beq]
    have h_assoc : A1 * (hammingSign (minimizingBit A1) * hammingSign sj) * hammingSign sj =
        (A1 * hammingSign (minimizingBit A1)) * (hammingSign sj * hammingSign sj) := by ring
    rw [h_assoc, mul_hammingSign_minimizingBit, hsj_sq, mul_one]
  have hAk (k : Fin 4) (hk : k ≠ i ∧ k ≠ j) :
      Ak k * hammingSign (ε j) * hammingSign (ε k) = -|Ak k| := by
    rw [hεj, hεk k hk, hammingSign_beq]
    have h_assoc : Ak k * hammingSign sj * (hammingSign (minimizingBit (Ak k)) * hammingSign sj) =
        (Ak k * hammingSign (minimizingBit (Ak k))) * (hammingSign sj * hammingSign sj) := by ring
    rw [h_assoc, mul_hammingSign_minimizingBit, hsj_sq, mul_one]
  have htrans := D.transition i j hij ε
  dsimp [A0, A1, Ak] at hA0 hA1 hAk htrans
  rw [hA0, hA1] at htrans
  have hsum :
      (∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
        2 * splitPair (factorD D.Q j) (factorA D.P D.Q k) *
          hammingSign (ε j) * hammingSign (ε k)) =
      - ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
        |2 * splitPair (factorD D.Q j) (factorA D.P D.Q k)| := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_filter] at hk
    exact hAk k hk.2
  rw [hsum] at htrans
  linarith

private theorem f8FactorData_delta_pos (D : F8FactorData) (j : Fin 4) :
    0 < factorDelta D.P D.Q j := by
  obtain ⟨i, hi⟩ := offDiagSet_nonempty j
  have hij : i ≠ j := by
    simpa [offDiagSet] using hi
  have h := f8FactorData_shell_bound D i j hij
  have hnonneg :
      0 ≤ |2 * splitPair (factorD D.Q j) D.r| +
        |2 * splitPair (factorD D.Q j) (factorB D.P D.Q i)| +
        ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
          |2 * splitPair (factorD D.Q j) (factorA D.P D.Q k)| := by
    positivity
  linarith

private noncomputable def factorNormalizedU (D : F8FactorData) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun j i => -4 * splitPair (column4 D.Q j) (column4 D.P i)

private noncomputable def factorNormalizedV (D : F8FactorData) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun j i => -4 * splitPair (column4 D.Q j) (column4 D.Q i)

private noncomputable def factorNormalizedW (D : F8FactorData) : Fin 4 → ℝ :=
  fun j => -4 * splitPair (column4 D.Q j) D.r

private noncomputable def factorNullTarget : Fin 4 → ℝ :=
  ![0, 0, -(1 / 2), 0]

private theorem factorNormalizedU_add_transpose (D : F8FactorData) :
    factorNormalizedU D + (factorNormalizedU D).transpose =
      -factorCurvature D.P D.Q := by
  ext i j
  simp only [factorNormalizedU, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.neg_apply, factorCurvature]
  rw [splitPair_symm (column4 D.Q i) (column4 D.P j),
    splitPair_symm (column4 D.Q j) (column4 D.P i)]
  ring

private theorem factorNormalizedV_isSymm (D : F8FactorData) :
    (factorNormalizedV D).IsSymm := by
  ext i j
  simp only [factorNormalizedV, Matrix.transpose_apply]
  rw [splitPair_symm]

private theorem factorNormalizedU_diag (D : F8FactorData) (j : Fin 4) :
    factorNormalizedU D j j = factorDelta D.P D.Q j := by
  simp only [factorNormalizedU, factorDelta]
  rw [splitPair_symm]

private theorem factorNullTarget_pair (x : Fin 4 → ℝ) :
    splitPair factorNullTarget x = -(x 3) / 4 := by
  rw [splitPair_formula]
  simp [factorNullTarget]
  ring

private theorem factorNormalizedW_eq (D : F8FactorData) (j : Fin 4) :
    2 * splitPair (factorD D.Q j) D.r = factorNormalizedW D j := by
  rw [splitPair_formula]
  simp only [factorD, Fin.isValue, neg_mul, factorNormalizedW]
  rw [splitPair_formula]
  simp only [column4]
  ring

private theorem factorNormalized_sub_eq
    (D : F8FactorData) (i j : Fin 4) :
    2 * splitPair (factorD D.Q j) (factorB D.P D.Q i) =
      factorNormalizedU D j i - factorNormalizedV D j i := by
  rw [splitPair_formula]
  simp only [factorD, Fin.isValue, neg_mul, factorB,
    factorNormalizedU, factorNormalizedV, sub_neg_eq_add]
  rw [splitPair_formula, splitPair_formula]
  simp only [column4]
  ring

private theorem factorNormalized_add_eq
    (D : F8FactorData) (k j : Fin 4) :
    2 * splitPair (factorD D.Q j) (factorA D.P D.Q k) =
      factorNormalizedU D j k + factorNormalizedV D j k := by
  rw [splitPair_formula]
  simp only [factorD, Fin.isValue, neg_mul, factorA,
    factorNormalizedU, factorNormalizedV]
  rw [splitPair_formula, splitPair_formula]
  simp only [column4]
  ring

private theorem factorNormalizedU_pos (D : F8FactorData) :
    PositiveDefinite4
      (factorNormalizedU D + (factorNormalizedU D).transpose) := by
  rw [factorNormalizedU_add_transpose]
  intro z hz
  have h := D.curvature z hz
  have hq :
      quadraticForm4 (-factorCurvature D.P D.Q) z =
        -quadraticForm4 (factorCurvature D.P D.Q) z := by
    unfold quadraticForm4
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.neg_apply]
    ring
  rw [hq]
  linarith

private theorem factorNormalizedU_diag_pos (D : F8FactorData) (j : Fin 4) :
    0 < factorNormalizedU D j j := by
  rw [factorNormalizedU_diag]
  exact f8FactorData_delta_pos D j

private theorem factorNormalized_contraction (D : F8FactorData) :
    ∀ i j, i ≠ j →
      |factorNormalizedW D j| +
        |factorNormalizedU D j i - factorNormalizedV D j i| +
        ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
          |factorNormalizedU D j k + factorNormalizedV D j k| <
        factorNormalizedU D j j := by
  intro i j hij
  simpa only [factorNormalizedW_eq, factorNormalized_sub_eq,
    factorNormalized_add_eq, factorNormalizedU_diag] using
    f8FactorData_shell_bound D i j hij

private theorem factorNormalizedU_transpose_mulVec
    (D : F8FactorData) (μ : Fin 4 → ℝ) (i : Fin 4) :
    ((factorNormalizedU D).transpose.mulVec μ) i =
      -4 * splitPair (D.Q.mulVec μ) (column4 D.P i) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.transpose_apply, factorNormalizedU, splitPair_formula, column4]
  ring

private theorem factorNormalizedV_mulVec
    (D : F8FactorData) (μ : Fin 4 → ℝ) (i : Fin 4) :
    (factorNormalizedV D).mulVec μ i =
      -4 * splitPair (column4 D.Q i) (D.Q.mulVec μ) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    factorNormalizedV, splitPair_formula, column4]
  ring

private theorem factorNormalizedW_dot
    (D : F8FactorData) (μ : Fin 4 → ℝ) :
    dotProduct μ (factorNormalizedW D) =
      -4 * splitPair (D.Q.mulVec μ) D.r := by
  simp only [dotProduct, Fin.sum_univ_four, factorNormalizedW,
    Matrix.mulVec, splitPair_formula, column4]
  ring

private theorem factorNormalizedV_quadratic
    (D : F8FactorData) (μ : Fin 4 → ℝ) :
    quadraticForm4 (factorNormalizedV D) μ =
      -4 * splitPair (D.Q.mulVec μ) (D.Q.mulVec μ) := by
  rw [quadraticForm4]
  simp only [dotProduct, Fin.sum_univ_four, factorNormalizedV,
    Matrix.mulVec, splitPair_formula, column4]
  ring

private theorem f8FactorData_exists_normalizing_mu (D : F8FactorData) :
    ∃ μ : Fin 4 → ℝ, D.Q.mulVec μ = factorNullTarget :=
  f8FactorData_Q_mulVec_surjective D factorNullTarget

private theorem factorNormalizingMu_leftSlope
    (D : F8FactorData) (μ : Fin 4 → ℝ)
    (hμ : D.Q.mulVec μ = factorNullTarget) (i : Fin 4) :
    ((factorNormalizedU D).transpose.mulVec μ) i = D.P 3 i := by
  rw [factorNormalizedU_transpose_mulVec, hμ, factorNullTarget_pair]
  simp only [column4]
  ring

private theorem factorNormalizingMu_rightSlope
    (D : F8FactorData) (μ : Fin 4 → ℝ)
    (hμ : D.Q.mulVec μ = factorNullTarget) (i : Fin 4) :
    (factorNormalizedV D).mulVec μ i = D.Q 3 i := by
  rw [factorNormalizedV_mulVec, hμ, splitPair_symm, factorNullTarget_pair]
  simp only [column4]
  ring

private theorem factorNormalizingMu_null
    (D : F8FactorData) (μ : Fin 4 → ℝ)
    (hμ : D.Q.mulVec μ = factorNullTarget) :
    quadraticForm4 (factorNormalizedV D) μ = 0 := by
  rw [factorNormalizedV_quadratic, hμ, factorNullTarget_pair]
  simp [factorNullTarget]

private theorem factorNormalizingMu_intercept
    (D : F8FactorData) (μ : Fin 4 → ℝ)
    (hμ : D.Q.mulVec μ = factorNullTarget) :
    dotProduct μ (factorNormalizedW D) = D.r 3 := by
  rw [factorNormalizedW_dot, hμ, factorNullTarget_pair]
  ring

private noncomputable def factorPositiveTarget0 : Fin 4 → ℝ :=
  ![1, -1, 0, 0]

private noncomputable def factorPositiveTarget1 : Fin 4 → ℝ :=
  ![0, 0, 1, -1]

private noncomputable def factorNegativeTarget0 : Fin 4 → ℝ :=
  ![1, 1, 0, 0]

private noncomputable def factorNegativeTarget1 : Fin 4 → ℝ :=
  ![0, 0, 1, 1]

private theorem factorPositiveTargets_pair (a b : ℝ) :
    splitPair
        (fun i => a * factorPositiveTarget0 i + b * factorPositiveTarget1 i)
        (fun i => a * factorPositiveTarget0 i + b * factorPositiveTarget1 i) =
      -(a ^ 2 + b ^ 2) := by
  rw [splitPair_formula]
  simp [factorPositiveTarget0, factorPositiveTarget1]
  ring

private theorem factorNegativeTargets_pair (a b : ℝ) :
    splitPair
        (fun i => a * factorNegativeTarget0 i + b * factorNegativeTarget1 i)
        (fun i => a * factorNegativeTarget0 i + b * factorNegativeTarget1 i) =
      a ^ 2 + b ^ 2 := by
  rw [splitPair_formula]
  simp [factorNegativeTarget0, factorNegativeTarget1]
  ring

private theorem factorNormalizedV_neg_quadratic
    (D : F8FactorData) (z : Fin 4 → ℝ) :
    quadraticForm4 (-(factorNormalizedV D)) z =
      4 * splitPair (D.Q.mulVec z) (D.Q.mulVec z) := by
  rw [quadraticForm4]
  simp only [dotProduct, Fin.sum_univ_four, factorNormalizedV,
    Matrix.mulVec, splitPair_formula, column4, Matrix.neg_apply]
  ring

private theorem f8FactorData_V_inertia (D : F8FactorData) :
    InertiaTwoTwo4 (factorNormalizedV D) := by
  obtain ⟨up, hup⟩ :=
    f8FactorData_Q_mulVec_surjective D factorPositiveTarget0
  obtain ⟨vp, hvp⟩ :=
    f8FactorData_Q_mulVec_surjective D factorPositiveTarget1
  obtain ⟨un, hun⟩ :=
    f8FactorData_Q_mulVec_surjective D factorNegativeTarget0
  obtain ⟨vn, hvn⟩ :=
    f8FactorData_Q_mulVec_surjective D factorNegativeTarget1
  refine ⟨factorNormalizedV_isSymm D, ?_, ?_⟩
  · refine ⟨up, vp, ?_⟩
    intro a b hab
    rw [factorNormalizedV_quadratic]
    have hcombo :
        D.Q.mulVec (fun i => a * up i + b * vp i) =
          fun i => a * factorPositiveTarget0 i +
            b * factorPositiveTarget1 i := by
      ext i
      have hu := congr_fun hup i
      have hv := congr_fun hvp i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hu hv ⊢
      linear_combination a * hu + b * hv
    rw [hcombo, factorPositiveTargets_pair]
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha]
    · nlinarith [sq_pos_of_ne_zero hb]
  · refine ⟨un, vn, ?_⟩
    intro a b hab
    rw [factorNormalizedV_neg_quadratic]
    have hcombo :
        D.Q.mulVec (fun i => a * un i + b * vn i) =
          fun i => a * factorNegativeTarget0 i +
            b * factorNegativeTarget1 i := by
      ext i
      have hu := congr_fun hun i
      have hv := congr_fun hvn i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hu hv ⊢
      linear_combination a * hu + b * hv
    rw [hcombo, factorNegativeTargets_pair]
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha]
    · nlinarith [sq_pos_of_ne_zero hb]

private theorem f8FactorData_yield_f8NormalizedSystem
    (D : F8FactorData) : Nonempty F8NormalizedSystem := by
  obtain ⟨μ, hμ⟩ := f8FactorData_exists_normalizing_mu D
  refine ⟨{
    U := factorNormalizedU D
    V := factorNormalizedV D
    w := factorNormalizedW D
    μ := μ
    U_pos := factorNormalizedU_pos D
    V_inertia := f8FactorData_V_inertia D
    diagonal_pos := factorNormalizedU_diag_pos D
    contraction := factorNormalized_contraction D
    leftSlope_pos := ?_
    rightSlope_pos := ?_
    null := factorNormalizingMu_null D μ hμ
    intercept := ?_
  }⟩
  · intro i
    rw [factorNormalizingMu_leftSlope D μ hμ i]
    exact D.denominator_left_pos i
  · intro i
    rw [factorNormalizingMu_rightSlope D μ hμ i]
    exact D.denominator_right_pos i
  · simp_rw [factorNormalizingMu_leftSlope D μ hμ,
      factorNormalizingMu_rightSlope D μ hμ,
      factorNormalizingMu_intercept D μ hμ]
    exact D.denominator_intercept

/-- Denominator clearing polynomial for two linear-fractional atoms. -/
private noncomputable def clearedTwoAtomPoly
    (φ : Fin 2 → FracAtom 8) (c : ℝ) :
    MvPolynomial (Fin 8) ℝ :=
  (C c * (φ 0).denPoly + (φ 0).numPoly) * (φ 1).denPoly +
    (φ 1).numPoly * (φ 0).denPoly

private theorem eval_clearedTwoAtomPoly
    (φ : Fin 2 → FracAtom 8) (c : ℝ) (x : Fin 8 → Bool) :
    eval (cubePoint x) (clearedTwoAtomPoly φ c) =
      eval (cubePoint x) (φ 0).denPoly * eval (cubePoint x) (φ 1).denPoly *
        (c + (φ 0).eval x + (φ 1).eval x) := by
  unfold clearedTwoAtomPoly
  rw [(φ 0).eval_eq_numPoly_div_denPoly, (φ 1).eval_eq_numPoly_div_denPoly]
  simp only [map_add, map_mul, eval_C]
  generalize hd0 : eval (cubePoint x) (φ 0).denPoly = d0
  generalize hd1 : eval (cubePoint x) (φ 1).denPoly = d1
  generalize eval (cubePoint x) (φ 0).numPoly = n0
  generalize eval (cubePoint x) (φ 1).numPoly = n1
  have h0 : d0 ≠ 0 := by
    rw [← hd0]
    exact ((φ 0).denPoly_pos x).ne'
  have h1 : d1 ≠ 0 := by
    rw [← hd1]
    exact ((φ 1).denPoly_pos x).ne'
  have h0_eq : n0 / d0 * d0 = n0 := div_mul_cancel₀ n0 h0
  have h1_eq : n1 / d1 * d1 = n1 := div_mul_cancel₀ n1 h1
  calc
    (c * d0 + n0) * d1 + n1 * d0 =
        d0 * d1 * c + (n0 / d0 * d0) * d1 +
          (n1 / d1 * d1) * d0 := by
      rw [h0_eq, h1_eq]
      ring
    _ = d0 * d1 * (c + n0 / d0 + n1 / d1) := by ring

private theorem clearedTwoAtomPoly_totalDegree_le
    (φ : Fin 2 → FracAtom 8) (c : ℝ) :
    (clearedTwoAtomPoly φ c).totalDegree ≤ 2 := by
  unfold clearedTwoAtomPoly
  have hC : (C c : MvPolynomial (Fin 8) ℝ).totalDegree ≤ 0 :=
    (totalDegree_C c).le
  have hL0 :
      (C c * (φ 0).denPoly + (φ 0).numPoly).totalDegree ≤ 1 := by
    refine (totalDegree_add _ _).trans
      (max_le ?_ (φ 0).numPoly_totalDegree_le)
    refine (totalDegree_mul _ _).trans ?_
    have h0 := (φ 0).denPoly_totalDegree_le
    omega
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    have h1 := (φ 1).denPoly_totalDegree_le
    omega
  · refine (totalDegree_mul _ _).trans ?_
    have h0 := (φ 0).denPoly_totalDegree_le
    have h1 := (φ 1).numPoly_totalDegree_le
    omega

private theorem clearedTwoAtomPoly_signRepresents
    (φ : Fin 2 → FracAtom 8) (c : ℝ)
    (hsign : ∀ x : Fin 8 → Bool,
      0 < c + ∑ h : Fin 2, (φ h).eval x ↔ f8 x = true) :
    SignRepresents (clearedTwoAtomPoly φ c) f8 := by
  intro x
  rw [eval_clearedTwoAtomPoly]
  have hd0 : 0 < eval (cubePoint x) (φ 0).denPoly :=
    (φ 0).denPoly_pos x
  have hd1 : 0 < eval (cubePoint x) (φ 1).denPoly :=
    (φ 1).denPoly_pos x
  have hpos :
      0 < eval (cubePoint x) (φ 0).denPoly *
        eval (cubePoint x) (φ 1).denPoly := mul_pos hd0 hd1
  have hiff :
      0 < c + (φ 0).eval x + (φ 1).eval x ↔ f8 x = true := by
    have hx := hsign x
    rw [Fin.sum_univ_two] at hx
    rw [← add_assoc] at hx
    exact hx
  rw [mul_pos_iff_of_pos_left hpos]
  exact hiff

private theorem clearedTwoAtomPoly_mixed_negative
    (φ : Fin 2 → FracAtom 8) (c : ℝ)
    (hsign : ∀ x : Fin 8 → Bool,
      0 < c + ∑ h : Fin 2, (φ h).eval x ↔ f8 x = true) :
    NegativeDefinite4
      (symmetricPart4 (mixedMatrix4 (toMultilinear (clearedTwoAtomPoly φ c)))) := by
  have hdeg : (toMultilinear (clearedTwoAtomPoly φ c)).totalDegree ≤ 2 :=
    (totalDegree_toMultilinear _).trans
      (clearedTwoAtomPoly_totalDegree_le φ c)
  have hrep :
      SignRepresents (toMultilinear (clearedTwoAtomPoly φ c)) f8 := by
    intro x
    rw [eval_toMultilinear]
    exact clearedTwoAtomPoly_signRepresents φ c hsign x
  exact f8_quadratic_mixed_negative
    (toMultilinear (clearedTwoAtomPoly φ c)) hdeg hrep

private theorem quadraticForm4_symmetricPart (K : Matrix (Fin 4) (Fin 4) ℝ) (z : Fin 4 → ℝ) :
    quadraticForm4 (symmetricPart4 K) z = quadraticForm4 K z := by
  simp only [quadraticForm4, symmetricPart4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

private theorem mulVec_eq_zero_of_neg_def (K : Matrix (Fin 4) (Fin 4) ℝ)
    (hneg : NegativeDefinite4 (symmetricPart4 K)) (z : Fin 4 → ℝ) (hK : K.mulVec z = 0) :
    z = 0 := by
  by_contra hz
  have hq_neg := hneg z hz
  rw [quadraticForm4_symmetricPart K z] at hq_neg
  have hq_zero : quadraticForm4 K z = 0 := by
    simp only [quadraticForm4, hK, dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  linarith

private theorem fracDenominator_linear_eq_zero_iff (φ : FracAtom 8) (i : Fin 8) :
    (fracDenominator φ).linear i = 0 ↔ φ.α = 1 := by
  change φ.ρ i * (φ.α - 1) = 0 ↔ φ.α = 1
  have hρ : φ.ρ i ≠ 0 := (φ.hρ i).ne'
  constructor
  · intro h
    cases mul_eq_zero.mp h with
    | inl h1 => contradiction
    | inr h2 => linarith
  · intro h
    rw [h]
    ring

private theorem slopes_ne_zero_iff (φ : FracAtom 8) :
    (∀ i : Fin 8, (fracDenominator φ).linear i ≠ 0) ↔ φ.α ≠ 1 := by
  constructor
  · intro h hα
    have h0 := (fracDenominator_linear_eq_zero_iff φ 0).mpr hα
    exact h 0 h0
  · intro h i h0
    have hα := (fracDenominator_linear_eq_zero_iff φ i).mp h0
    exact h hα

private theorem exists_nonzero_common_orthogonal (u v : Fin 4 → ℝ) :
    ∃ z : Fin 4 → ℝ, z ≠ 0 ∧ dotProduct u z = 0 ∧ dotProduct v z = 0 := by
  classical
  let F : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    LinearMap.pi (fun i =>
      if i = 0 then dotProductBilin ℝ ℝ u else dotProductBilin ℝ ℝ v)
  have hnot : ¬ Function.Injective F := by
    intro hinj
    have hdim :
        Module.finrank ℝ (Fin 4 → ℝ) ≤ Module.finrank ℝ (Fin 2 → ℝ) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    norm_num [Module.finrank_fin_fun] at hdim
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnot
  have h0 : dotProduct u x = dotProduct u y := by
    have h := congr_fun hxy (0 : Fin 2)
    simpa [F, dotProductBilin] using h
  have h1 : dotProduct v x = dotProduct v y := by
    have h := congr_fun hxy (1 : Fin 2)
    simpa [F, dotProductBilin] using h
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_, ?_⟩
  · rw [dotProduct_sub, h0, sub_self]
  · rw [dotProduct_sub, h1, sub_self]

private def factorFormA (φ : Fin 2 → FracAtom 8) (c : ℝ) : AffineForm 8 where
  constant := c * (fracDenominator (φ 0)).constant + (fracNumerator (φ 0)).constant
  linear i := c * (fracDenominator (φ 0)).linear i + (fracNumerator (φ 0)).linear i

private theorem eval_factorFormA (φ : Fin 2 → FracAtom 8) (c : ℝ) (x : Fin 8 → Bool) :
    (factorFormA φ c).eval x =
      c * (fracDenominator (φ 0)).eval x + (fracNumerator (φ 0)).eval x := by
  dsimp [factorFormA, AffineForm.eval]
  simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

private noncomputable def factorRowForm (φ : Fin 2 → FracAtom 8) (c : ℝ) (row : Fin 4) :
    AffineForm 8 :=
  match row with
  | 0 => factorFormA φ c
  | 1 => fracDenominator (φ 1)
  | 2 => fracNumerator (φ 1)
  | 3 => fracDenominator (φ 0)

private noncomputable def factorOrientation (φ : Fin 2 → FracAtom 8) : ℝ :=
  if ∀ i, 0 < (fracDenominator (φ 0)).linear i then 1 else -1

private theorem factorOrientation_cases (φ : Fin 2 → FracAtom 8) :
    factorOrientation φ = 1 ∨ factorOrientation φ = -1 := by
  dsimp [factorOrientation]
  split_ifs <;> simp

private theorem factorOrientation_pos (φ : Fin 2 → FracAtom 8)
    (h : ∀ i, (fracDenominator (φ 0)).linear i ≠ 0) (k : Fin 8) :
    0 < factorOrientation φ * (fracDenominator (φ 0)).linear k := by
  have hB_orient := fracDenominator_strictlyOriented_of_slopes_ne_zero (φ 0) h
  dsimp [factorOrientation]
  split_ifs with hpos
  · simp only [one_mul]
    exact hpos k
  · simp only [neg_one_mul, neg_pos]
    rcases hB_orient with hpos' | hneg
    · contradiction
    · exact hneg k

private noncomputable def factorR (φ : Fin 2 → FracAtom 8) (c : ℝ) (row : Fin 4) : ℝ :=
  (factorRowForm φ c row).constant + ∑ k : Fin 8, (factorRowForm φ c row).linear k / 2

private noncomputable def factorP (φ : Fin 2 → FracAtom 8) (c : ℝ) (s : ℝ) : Matrix (Fin 4) (Fin
    4) ℝ :=
  fun row i => s * (factorRowForm φ c row).linear (Fin.castAdd 4 i) / 2

private noncomputable def factorQ (φ : Fin 2 → FracAtom 8) (c : ℝ) (s : ℝ) : Matrix (Fin 4) (Fin
    4) ℝ :=
  fun row i => s * (factorRowForm φ c row).linear (Fin.natAdd 4 i) / 2

private noncomputable def orientBit (s : ℝ) (b : Bool) : Bool :=
  if s = 1 then b else !b

private theorem hammingSign_orientBit (s : ℝ) (hs : s = 1 ∨ s = -1) (b : Bool) :
    hammingSign (orientBit s b) = s * hammingSign b := by
  rcases hs with rfl | rfl
  · dsimp [orientBit]; rw [if_pos rfl]; ring
  · dsimp [orientBit]
    have h : ¬(-1 : ℝ) = 1 := by norm_num
    rw [if_neg h]
    cases b <;> norm_num [hammingSign]

private noncomputable def xOriented (s : ℝ) (x : Fin 8 → Bool) : Fin 8 → Bool :=
  fun k => orientBit s (x k)

private theorem f8_xOriented (s : ℝ) (hs : s = 1 ∨ s = -1) (x : Fin 8 → Bool) :
    f8 (xOriented s x) = f8 x := by
  rcases hs with rfl | rfl
  · have h : xOriented 1 x = x := by
      ext k
      dsimp [xOriented, orientBit]
      rw [if_pos rfl]
    rw [h]
  · have h : xOriented (-1) x = (fun k => !x k) := by
      ext k
      dsimp [xOriented, orientBit]
      have hne : ¬(-1 : ℝ) = 1 := by norm_num
      rw [if_neg hne]
    rw [h, f8_complement]

private theorem eval_affineForm_eq_factor (L : AffineForm 8) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (x : Fin 8 → Bool) :
    L.eval (xOriented s x) =
      (L.constant + ∑ k, L.linear k / 2) +
        (∑ i : Fin 4, (s * L.linear (Fin.castAdd 4 i) / 2) * hammingSign (x (Fin.castAdd 4 i))) +
        (∑ i : Fin 4, (s * L.linear (Fin.natAdd 4 i) / 2) * hammingSign (x (Fin.natAdd 4 i))) := by
  dsimp [AffineForm.eval]
  have h_sum1 : (∑ i : Fin 8, L.linear i * bitReal (xOriented s x i)) =
      (∑ i : Fin 4, L.linear (Fin.castAdd 4 i) * bitReal (xOriented s x (Fin.castAdd 4 i))) +
      (∑ i : Fin 4, L.linear (Fin.natAdd 4 i) * bitReal (xOriented s x (Fin.natAdd 4 i))) :=
    Fin.sum_univ_add (fun (k : Fin (4 + 4)) => L.linear k * bitReal (xOriented s x k))
  have h_sum2 : (∑ k : Fin 8, L.linear k / 2) =
      (∑ i : Fin 4, L.linear (Fin.castAdd 4 i) / 2) +
      (∑ i : Fin 4, L.linear (Fin.natAdd 4 i) / 2) :=
    Fin.sum_univ_add (fun (k : Fin (4 + 4)) => L.linear k / 2)
  rw [h_sum1, h_sum2]
  have h_bit (k : Fin 8) : bitReal (xOriented s x k) = (s * hammingSign (x k) + 1) / 2 := by
    dsimp [xOriented]
    rw [bitReal_eq_hammingSign, hammingSign_orientBit s hs]
  simp_rw [h_bit]
  have h1 : (∑ x_1 : Fin 4, L.linear (Fin.castAdd 4 x_1) * ((s * hammingSign (x (Fin.castAdd 4
      x_1)) + 1) / 2)) =
      (∑ x_1 : Fin 4, L.linear (Fin.castAdd 4 x_1) / 2) +
      ∑ x_1 : Fin 4, (s * L.linear (Fin.castAdd 4 x_1) / 2) * hammingSign (x (Fin.castAdd 4
          x_1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have h2 : (∑ x_1 : Fin 4, L.linear (Fin.natAdd 4 x_1) * ((s * hammingSign (x (Fin.natAdd 4
      x_1)) + 1) / 2)) =
      (∑ x_1 : Fin 4, L.linear (Fin.natAdd 4 x_1) / 2) +
      ∑ x_1 : Fin 4, (s * L.linear (Fin.natAdd 4 x_1) / 2) * hammingSign (x (Fin.natAdd 4 x_1))
          := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [h1, h2]
  ring

private theorem eval_blockJoin_single (L : AffineForm 8) (i j : Fin 4)
    (bi bj : Bool) :
    L.eval (blockJoin (fun k => k = i ∧ bi) (fun k => k = j ∧ bj)) =
      L.constant +
        L.linear (Fin.castAdd 4 i) * (if bi then 1 else 0) +
        L.linear (Fin.natAdd 4 j) * (if bj then 1 else 0) := by
  dsimp [AffineForm.eval]
  have h_sum : (∑ k : Fin 8, L.linear k * bitReal (blockJoin (fun k => k = i ∧ bi) (fun k => k =
      j ∧ bj) k)) =
      (∑ x : Fin 4, L.linear (Fin.castAdd 4 x) * bitReal (blockJoin (fun k => k = i ∧ bi) (fun k
          => k = j ∧ bj) (Fin.castAdd 4 x))) +
      (∑ x : Fin 4, L.linear (Fin.natAdd 4 x) * bitReal (blockJoin (fun k => k = i ∧ bi) (fun k
          => k = j ∧ bj) (Fin.natAdd 4 x))) :=
    Fin.sum_univ_add (fun (k : Fin (4 + 4)) => L.linear k * bitReal (blockJoin (fun k => k = i ∧
        bi) (fun k => k = j ∧ bj) k))
  rw [h_sum]
  have hL : (∑ x : Fin 4, L.linear (Fin.castAdd 4 x) * bitReal (blockJoin (fun k => k = i ∧ bi)
      (fun k => k = j ∧ bj) (Fin.castAdd 4 x))) =
      L.linear (Fin.castAdd 4 i) * (if bi then 1 else 0) := by
    simp_rw [blockJoin_castAdd]
    rw [Finset.sum_eq_single i]
    · cases bi <;> simp [bitReal]
    · intro k _ hk
      have h_ne : ¬(k = i) := hk
      cases bi <;> simp [bitReal, h_ne]
    · intro h; exact False.elim (h (Finset.mem_univ i))
  have hR : (∑ x : Fin 4, L.linear (Fin.natAdd 4 x) * bitReal (blockJoin (fun k => k = i ∧ bi)
      (fun k => k = j ∧ bj) (Fin.natAdd 4 x))) =
      L.linear (Fin.natAdd 4 j) * (if bj then 1 else 0) := by
    simp_rw [blockJoin_natAdd]
    rw [Finset.sum_eq_single j]
    · cases bj <;> simp [bitReal]
    · intro k _ hk
      have h_ne : ¬(k = j) := hk
      cases bj <;> simp [bitReal, h_ne]
    · intro h; exact False.elim (h (Finset.mem_univ j))
  rw [hL, hR]
  ring

private theorem mixedMatrix4_clearedTwoAtomPoly (φ : Fin 2 → FracAtom 8) (c : ℝ) (i j : Fin 4) :
    mixedMatrix4 (toMultilinear (clearedTwoAtomPoly φ c)) i j =
      (factorFormA φ c).linear (Fin.castAdd 4 i) * (fracDenominator (φ 1)).linear (Fin.natAdd 4 j) +
      (fracDenominator (φ 1)).linear (Fin.castAdd 4 i) * (factorFormA φ c).linear (Fin.natAdd 4 j) +
      (fracNumerator (φ 1)).linear (Fin.castAdd 4 i) * (fracDenominator (φ 0)).linear
          (Fin.natAdd 4 j) +
      (fracDenominator (φ 0)).linear (Fin.castAdd 4 i) * (fracNumerator (φ 1)).linear
          (Fin.natAdd 4 j) := by
  set P_poly := toMultilinear (clearedTwoAtomPoly φ c)
  have hdeg : P_poly.totalDegree ≤ 2 :=
    (totalDegree_toMultilinear _).trans (clearedTwoAtomPoly_totalDegree_le φ c)
  let x0 : Fin 4 → Bool := fun k => k = i
  let x1 : Fin 4 → Bool := fun _ => false
  let y0 : Fin 4 → Bool := fun k => k = j
  let y1 : Fin 4 → Bool := fun _ => false
  have hdiff : bilinear4 (mixedMatrix4 P_poly) (bitDiff4 x0 x1) (bitDiff4 y0 y1) =
      mixedMatrix4 P_poly i j := by
    unfold bilinear4 bitDiff4
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp [x0, y0, x1, y1, boolToReal]
      · intro k _ hk
        have h_ne : ¬(k = j) := hk
        simp [x0, y0, x1, y1, boolToReal, h_ne]
      · intro h; exact False.elim (h (Finset.mem_univ j))
    · intro k _ hk
      have h_ne : ¬(k = i) := hk
      have h_zero : (∑ j_1 : Fin 4, (boolToReal (x0 k) - boolToReal (x1 k)) * mixedMatrix4
          P_poly k j_1 * (boolToReal (y0 j_1) - boolToReal (y1 j_1))) = 0 := by
        refine Finset.sum_eq_zero (fun k' _ => ?_)
        simp [x0, y0, x1, y1, boolToReal, h_ne]
      exact h_zero
    · intro h; exact False.elim (h (Finset.mem_univ i))
  rw [← hdiff]
  rw [← quadratic_checkerboard_difference P_poly hdeg x0 x1 y0 y1]
  have h_eval (u v : Fin 4 → Bool) :
      eval (cubePoint (blockJoin u v)) P_poly =
        (factorFormA φ c).eval (blockJoin u v) * (fracDenominator (φ 1)).eval (blockJoin u v) +
        (fracNumerator (φ 1)).eval (blockJoin u v) * (fracDenominator (φ 0)).eval (blockJoin u
            v) := by
    rw [eval_toMultilinear, eval_clearedTwoAtomPoly]
    rw [FracAtom.eval_eq_numPoly_div_denPoly (φ 0) (blockJoin u v)]
    rw [FracAtom.eval_eq_numPoly_div_denPoly (φ 1) (blockJoin u v)]
    rw [FracAtom.denPoly_eval (φ 0) (blockJoin u v)]
    rw [FracAtom.denPoly_eval (φ 1) (blockJoin u v)]
    rw [FracAtom.numPoly_eval (φ 0) (blockJoin u v)]
    rw [FracAtom.numPoly_eval (φ 1) (blockJoin u v)]
    rw [← fracDenominator_eval (φ 0) (blockJoin u v)]
    rw [← fracDenominator_eval (φ 1) (blockJoin u v)]
    rw [← fracNumerator_eval (φ 0) (blockJoin u v)]
    rw [← fracNumerator_eval (φ 1) (blockJoin u v)]
    have hd0 : 0 < (fracDenominator (φ 0)).eval (blockJoin u v) := fracDenominator_strictLegal
        (φ 0) _
    have hd1 : 0 < (fracDenominator (φ 1)).eval (blockJoin u v) := fracDenominator_strictLegal
        (φ 1) _
    have h0 : (fracDenominator (φ 0)).eval (blockJoin u v) ≠ 0 := hd0.ne'
    have h1 : (fracDenominator (φ 1)).eval (blockJoin u v) ≠ 0 := hd1.ne'
    generalize h_n0 : (fracNumerator (φ 0)).eval (blockJoin u v) = n0
    generalize h_d0 : (fracDenominator (φ 0)).eval (blockJoin u v) = d0
    generalize h_n1 : (fracNumerator (φ 1)).eval (blockJoin u v) = n1
    generalize h_d1 : (fracDenominator (φ 1)).eval (blockJoin u v) = d1
    have h_alg : d0 * d1 * (c + n0 / d0 + n1 / d1) = (c * d0 + n0) * d1 + n1 * d0 := by
      rw [h_d0] at h0; rw [h_d1] at h1
      field_simp
    rw [h_alg, ← h_d0, ← h_n0, ← h_d1, ← h_n1, eval_factorFormA]
  rw [h_eval x0 y0, h_eval x0 y1, h_eval x1 y0, h_eval x1 y1]
  have h_x0y0_A : (factorFormA φ c).eval (blockJoin x0 y0) = (factorFormA φ c).constant +
      (factorFormA φ c).linear (Fin.castAdd 4 i) + (factorFormA φ c).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (factorFormA φ c) i j true true; simpa using h
  have h_x0y0_D : (fracDenominator (φ 1)).eval (blockJoin x0 y0) = (fracDenominator (φ
      1)).constant + (fracDenominator (φ 1)).linear (Fin.castAdd 4 i) + (fracDenominator (φ
      1)).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracDenominator (φ 1)) i j true true; simpa using h
  have h_x0y0_C : (fracNumerator (φ 1)).eval (blockJoin x0 y0) = (fracNumerator (φ 1)).constant
      + (fracNumerator (φ 1)).linear (Fin.castAdd 4 i) + (fracNumerator (φ 1)).linear
      (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracNumerator (φ 1)) i j true true; simpa using h
  have h_x0y0_B : (fracDenominator (φ 0)).eval (blockJoin x0 y0) = (fracDenominator (φ
      0)).constant + (fracDenominator (φ 0)).linear (Fin.castAdd 4 i) + (fracDenominator (φ
      0)).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracDenominator (φ 0)) i j true true; simpa using h
  have h_x0y1_A : (factorFormA φ c).eval (blockJoin x0 y1) = (factorFormA φ c).constant +
      (factorFormA φ c).linear (Fin.castAdd 4 i) := by
    have h := eval_blockJoin_single (factorFormA φ c) i j true false; simpa using h
  have h_x0y1_D : (fracDenominator (φ 1)).eval (blockJoin x0 y1) = (fracDenominator (φ
      1)).constant + (fracDenominator (φ 1)).linear (Fin.castAdd 4 i) := by
    have h := eval_blockJoin_single (fracDenominator (φ 1)) i j true false; simpa using h
  have h_x0y1_C : (fracNumerator (φ 1)).eval (blockJoin x0 y1) = (fracNumerator (φ 1)).constant
      + (fracNumerator (φ 1)).linear (Fin.castAdd 4 i) := by
    have h := eval_blockJoin_single (fracNumerator (φ 1)) i j true false; simpa using h
  have h_x0y1_B : (fracDenominator (φ 0)).eval (blockJoin x0 y1) = (fracDenominator (φ
      0)).constant + (fracDenominator (φ 0)).linear (Fin.castAdd 4 i) := by
    have h := eval_blockJoin_single (fracDenominator (φ 0)) i j true false; simpa using h
  have h_x1y0_A : (factorFormA φ c).eval (blockJoin x1 y0) = (factorFormA φ c).constant +
      (factorFormA φ c).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (factorFormA φ c) i j false true; simpa using h
  have h_x1y0_D : (fracDenominator (φ 1)).eval (blockJoin x1 y0) = (fracDenominator (φ
      1)).constant + (fracDenominator (φ 1)).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracDenominator (φ 1)) i j false true; simpa using h
  have h_x1y0_C : (fracNumerator (φ 1)).eval (blockJoin x1 y0) = (fracNumerator (φ 1)).constant
      + (fracNumerator (φ 1)).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracNumerator (φ 1)) i j false true; simpa using h
  have h_x1y0_B : (fracDenominator (φ 0)).eval (blockJoin x1 y0) = (fracDenominator (φ
      0)).constant + (fracDenominator (φ 0)).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracDenominator (φ 0)) i j false true; simpa using h
  have h_x1y1_A : (factorFormA φ c).eval (blockJoin x1 y1) = (factorFormA φ c).constant := by
    have h := eval_blockJoin_single (factorFormA φ c) i j false false; simpa using h
  have h_x1y1_D : (fracDenominator (φ 1)).eval (blockJoin x1 y1) = (fracDenominator (φ
      1)).constant := by
    have h := eval_blockJoin_single (fracDenominator (φ 1)) i j false false; simpa using h
  have h_x1y1_C : (fracNumerator (φ 1)).eval (blockJoin x1 y1) = (fracNumerator (φ 1)).constant
      := by
    have h := eval_blockJoin_single (fracNumerator (φ 1)) i j false false; simpa using h
  have h_x1y1_B : (fracDenominator (φ 0)).eval (blockJoin x1 y1) = (fracDenominator (φ
      0)).constant := by
    have h := eval_blockJoin_single (fracDenominator (φ 0)) i j false false; simpa using h
  rw [h_x0y0_A, h_x0y0_D, h_x0y0_C, h_x0y0_B]
  rw [h_x0y1_A, h_x0y1_D, h_x0y1_C, h_x0y1_B]
  rw [h_x1y0_A, h_x1y0_D, h_x1y0_C, h_x1y0_B]
  rw [h_x1y1_A, h_x1y1_D, h_x1y1_C, h_x1y1_B]
  ring

/-- Paper Lemma 3, nondegeneracy part: negative mixed curvature rules out a
constant denominator. Since every `FracAtom` denominator has one common slope
factor and strictly positive coordinate weights, all eight slopes of each
nonconstant denominator are nonzero. -/
private theorem clearedTwoAtom_denominator_slopes_ne_zero
    (φ : Fin 2 → FracAtom 8) (c : ℝ)
    (hneg : NegativeDefinite4
      (symmetricPart4
        (mixedMatrix4 (toMultilinear (clearedTwoAtomPoly φ c))))) :
    (∀ i, (fracDenominator (φ 0)).linear i ≠ 0) ∧
      (∀ i, (fracDenominator (φ 1)).linear i ≠ 0) := by
  refine ⟨(slopes_ne_zero_iff (φ 0)).2 ?_, (slopes_ne_zero_iff (φ 1)).2 ?_⟩
  · intro hα0
    have hden0 (k : Fin 8) : (fracDenominator (φ 0)).linear k = 0 :=
      (fracDenominator_linear_eq_zero_iff (φ 0) k).2 hα0
    let u : Fin 4 → ℝ :=
      fun j => (fracDenominator (φ 1)).linear (Fin.natAdd 4 j)
    let v : Fin 4 → ℝ :=
      fun j => (factorFormA φ c).linear (Fin.natAdd 4 j)
    obtain ⟨z, hz, hu, hv⟩ := exists_nonzero_common_orthogonal u v
    dsimp [u, v] at hu hv
    have hKz :
        (mixedMatrix4 (toMultilinear (clearedTwoAtomPoly φ c))).mulVec z = 0 := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      simp_rw [mixedMatrix4_clearedTwoAtomPoly φ c]
      simp_rw [hden0]
      simp only [mul_zero, zero_mul, add_zero]
      simp only [dotProduct, Fin.sum_univ_four] at hu hv
      simp only [Fin.sum_univ_four]
      linear_combination
        (factorFormA φ c).linear (Fin.castAdd 4 i) * hu +
        (fracDenominator (φ 1)).linear (Fin.castAdd 4 i) * hv
    exact hz (mulVec_eq_zero_of_neg_def _ hneg z hKz)
  · intro hα1
    have hden1 (k : Fin 8) : (fracDenominator (φ 1)).linear k = 0 :=
      (fracDenominator_linear_eq_zero_iff (φ 1) k).2 hα1
    let u : Fin 4 → ℝ :=
      fun j => (fracDenominator (φ 0)).linear (Fin.natAdd 4 j)
    let v : Fin 4 → ℝ :=
      fun j => (fracNumerator (φ 1)).linear (Fin.natAdd 4 j)
    obtain ⟨z, hz, hu, hv⟩ := exists_nonzero_common_orthogonal u v
    dsimp [u, v] at hu hv
    have hKz :
        (mixedMatrix4 (toMultilinear (clearedTwoAtomPoly φ c))).mulVec z = 0 := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      simp_rw [mixedMatrix4_clearedTwoAtomPoly φ c]
      simp_rw [hden1]
      simp only [mul_zero, zero_mul, add_zero]
      simp only [dotProduct, Fin.sum_univ_four] at hu hv
      simp only [Fin.sum_univ_four]
      linear_combination
        (fracNumerator (φ 1)).linear (Fin.castAdd 4 i) * hu +
        (fracDenominator (φ 0)).linear (Fin.castAdd 4 i) * hv
    exact hz (mulVec_eq_zero_of_neg_def _ hneg z hKz)

private theorem factorCurvature_eq_clearedTwoAtomPoly_mixed
    (φ : Fin 2 → FracAtom 8) (c : ℝ) :
    factorCurvature (factorP φ c (factorOrientation φ)) (factorQ φ c (factorOrientation φ)) =
      symmetricPart4 (mixedMatrix4 (toMultilinear (clearedTwoAtomPoly φ c))) := by
  ext i j
  dsimp [factorCurvature, symmetricPart4, splitPair, column4, factorP, factorQ, factorRowForm]
  rw [splitJ_pair_formula, splitJ_pair_formula]
  rw [mixedMatrix4_clearedTwoAtomPoly φ c i j, mixedMatrix4_clearedTwoAtomPoly φ c j i]
  dsimp [column4, factorP, factorQ, factorRowForm]
  have hs_sq : (factorOrientation φ) ^ 2 = 1 := by
    rcases factorOrientation_cases φ with h | h <;> rw [h] <;> ring
  linear_combination (1 / 2 * hs_sq) *
    ((factorFormA φ c).linear (Fin.castAdd 4 i) * (fracDenominator (φ 1)).linear (Fin.natAdd 4 j) +
     (fracDenominator (φ 1)).linear (Fin.castAdd 4 i) * (factorFormA φ c).linear (Fin.natAdd 4 j) +
     (fracNumerator (φ 1)).linear (Fin.castAdd 4 i) * (fracDenominator (φ 0)).linear (Fin.natAdd
         4 j) +
     (fracDenominator (φ 0)).linear (Fin.castAdd 4 i) * (fracNumerator (φ 1)).linear (Fin.natAdd
         4 j) +
     (factorFormA φ c).linear (Fin.castAdd 4 j) * (fracDenominator (φ 1)).linear (Fin.natAdd 4 i) +
     (fracDenominator (φ 1)).linear (Fin.castAdd 4 j) * (factorFormA φ c).linear (Fin.natAdd 4 i) +
     (fracNumerator (φ 1)).linear (Fin.castAdd 4 j) * (fracDenominator (φ 0)).linear (Fin.natAdd
         4 i) +
     (fracDenominator (φ 0)).linear (Fin.castAdd 4 j) * (fracNumerator (φ 1)).linear (Fin.natAdd
         4 i))

private noncomputable def defect1 (i : Fin 4) (ε : Fin 4 → Bool) : Fin 8 → Bool :=
  blockJoin ε (fun k => if k = i then !ε i else ε k)

private noncomputable def defect2 (i j : Fin 4) (ε : Fin 4 → Bool) : Fin 8 → Bool :=
  blockJoin ε (fun k => if k = i ∨ k = j then !ε k else ε k)

private theorem f8_defect1 (i : Fin 4) (ε : Fin 4 → Bool) :
    f8 (defect1 i ε) = false := by
  rw [f8_apply]
  dsimp [hammingDist, defect1]
  simp only [leftBits_blockJoin, rightBits_blockJoin]
  simp only [decide_eq_false_iff_not, not_le]
  have hset : (Finset.univ.filter (fun x : Fin 4 => ε x ≠ if x = i then !ε i else ε x)) = {i} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hne
      rw [if_neg hne] at h
      exact h rfl
    · intro hx
      subst hx
      rw [if_pos rfl]
      cases ε x <;> decide
  rw [hset, Finset.card_singleton]
  norm_num

private theorem f8_defect2 (i j : Fin 4) (hij : i ≠ j) (ε : Fin 4 → Bool) :
    f8 (defect2 i j ε) = true := by
  rw [f8_apply]
  dsimp [hammingDist, defect2]
  simp only [leftBits_blockJoin, rightBits_blockJoin]
  simp only [decide_eq_true_eq]
  have hset : (Finset.univ.filter (fun x : Fin 4 => ε x ≠ if x = i ∨ x = j then !ε x else ε x))
      = {i, j} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
    constructor
    · intro h
      by_contra hne
      push Not at hne
      rw [if_neg (by simp [hne])] at h
      exact h rfl
    · rintro (hx | hx) <;> subst hx
      · rw [if_pos (Or.inl rfl)]
        cases ε x <;> decide
      · rw [if_pos (Or.inr rfl)]
        cases ε x <;> decide
  rw [hset, Finset.card_pair hij]


private noncomputable def factorValue
    (P Q : Matrix (Fin 4) (Fin 4) ℝ) (r : Fin 4 → ℝ)
    (x : Fin 8 → Bool) : Fin 4 → ℝ :=
  fun row => r row +
    (∑ k : Fin 4, P row k * hammingSign (x (Fin.castAdd 4 k))) +
    (∑ k : Fin 4, Q row k * hammingSign (x (Fin.natAdd 4 k)))

private theorem factor_transition_of_defects
    (P Q : Matrix (Fin 4) (Fin 4) ℝ) (r : Fin 4 → ℝ)
    (i j : Fin 4) (hij : i ≠ j) (ε : Fin 4 → Bool)
    (hdiff : 0 <
      splitPair (factorValue P Q r (defect2 i j ε))
          (factorValue P Q r (defect2 i j ε)) -
        splitPair (factorValue P Q r (defect1 i ε))
          (factorValue P Q r (defect1 i ε))) :
    0 < factorDelta P Q j +
      2 * splitPair (factorD Q j) r * hammingSign (ε j) +
      2 * splitPair (factorD Q j) (factorB P Q i) *
        hammingSign (ε i) * hammingSign (ε j) +
      ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
        2 * splitPair (factorD Q j) (factorA P Q k) *
          hammingSign (ε j) * hammingSign (ε k) := by
  have h_hs_not (b : Bool) : hammingSign (!b) = -hammingSign b := by
    cases b <;> simp [hammingSign]
  fin_cases i <;> fin_cases j
  all_goals try contradiction
  all_goals
    have h0 : (hammingSign (ε 0)) ^ 2 = 1 := by
      rcases hammingSign_cases (ε 0) with h | h <;> rw [h] <;> ring
    have h1 : (hammingSign (ε 1)) ^ 2 = 1 := by
      rcases hammingSign_cases (ε 1) with h | h <;> rw [h] <;> ring
    have h2 : (hammingSign (ε 2)) ^ 2 = 1 := by
      rcases hammingSign_cases (ε 2) with h | h <;> rw [h] <;> ring
    have h3 : (hammingSign (ε 3)) ^ 2 = 1 := by
      rcases hammingSign_cases (ε 3) with h | h <;> rw [h] <;> ring
    simp only [factorDelta] at hdiff ⊢
    simp_rw [splitPair_formula] at hdiff ⊢
    simp only [factorD, factorA, factorB, column4] at hdiff ⊢
    simp only [factorValue, defect1, defect2, blockJoin_castAdd,
      blockJoin_natAdd] at hdiff
    simp_rw [Finset.sum_filter, Fin.sum_univ_four] at hdiff ⊢
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      zero_ne_one, one_ne_zero, Fin.reduceEq, or_false, or_true, or_self,
      ↓reduceIte, h_hs_not, mul_neg, sub_pos, neg_mul, ne_eq,
      not_true_eq_false, not_false_eq_true, and_true, and_false, and_self,
      add_zero, zero_add, gt_iff_lt] at hdiff ⊢
    first
    | linear_combination hdiff -
        (2 * (P 0 0 * Q 1 0 + Q 0 0 * P 1 0 + P 2 0 * Q 3 0 + Q 2 0 * P 3 0)) * h0
    | linear_combination hdiff -
        (2 * (P 0 1 * Q 1 1 + Q 0 1 * P 1 1 + P 2 1 * Q 3 1 + Q 2 1 * P 3 1)) * h1
    | linear_combination hdiff -
        (2 * (P 0 2 * Q 1 2 + Q 0 2 * P 1 2 + P 2 2 * Q 3 2 + Q 2 2 * P 3 2)) * h2
    | linear_combination hdiff -
        (2 * (P 0 3 * Q 1 3 + Q 0 3 * P 1 3 + P 2 3 * Q 3 3 + Q 2 3 * P 3 3)) * h3
private theorem clearedTwoAtomPoly_eval_eq_splitPair
    (φ : Fin 2 → FracAtom 8) (c : ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1) (x : Fin 8 → Bool) :
    eval (cubePoint (xOriented s x)) (clearedTwoAtomPoly φ c) =
      splitPair
        (fun row => (factorR φ c row) +
          (∑ i : Fin 4, (factorP φ c s) row i * hammingSign (x (Fin.castAdd 4 i))) +
          (∑ i : Fin 4, (factorQ φ c s) row i * hammingSign (x (Fin.natAdd 4 i))))
        (fun row => (factorR φ c row) +
          (∑ i : Fin 4, (factorP φ c s) row i * hammingSign (x (Fin.castAdd 4 i))) +
          (∑ i : Fin 4, (factorQ φ c s) row i * hammingSign (x (Fin.natAdd 4 i)))) := by
  have h_eval_poly : eval (cubePoint (xOriented s x)) (clearedTwoAtomPoly φ c) =
      (factorFormA φ c).eval (xOriented s x) * (fracDenominator (φ 1)).eval (xOriented s x) +
      (fracNumerator (φ 1)).eval (xOriented s x) * (fracDenominator (φ 0)).eval (xOriented s x)
          := by
    rw [eval_clearedTwoAtomPoly]
    rw [FracAtom.eval_eq_numPoly_div_denPoly (φ 0) (xOriented s x)]
    rw [FracAtom.eval_eq_numPoly_div_denPoly (φ 1) (xOriented s x)]
    rw [FracAtom.denPoly_eval (φ 0) (xOriented s x)]
    rw [FracAtom.denPoly_eval (φ 1) (xOriented s x)]
    rw [FracAtom.numPoly_eval (φ 0) (xOriented s x)]
    rw [FracAtom.numPoly_eval (φ 1) (xOriented s x)]
    rw [← fracDenominator_eval (φ 0) (xOriented s x)]
    rw [← fracDenominator_eval (φ 1) (xOriented s x)]
    rw [← fracNumerator_eval (φ 0) (xOriented s x)]
    rw [← fracNumerator_eval (φ 1) (xOriented s x)]
    have hd0 : 0 < (fracDenominator (φ 0)).eval (xOriented s x) := fracDenominator_strictLegal
        (φ 0) _
    have hd1 : 0 < (fracDenominator (φ 1)).eval (xOriented s x) := fracDenominator_strictLegal
        (φ 1) _
    have h0 : (fracDenominator (φ 0)).eval (xOriented s x) ≠ 0 := hd0.ne'
    have h1 : (fracDenominator (φ 1)).eval (xOriented s x) ≠ 0 := hd1.ne'
    generalize h_n0 : (fracNumerator (φ 0)).eval (xOriented s x) = n0
    generalize h_d0 : (fracDenominator (φ 0)).eval (xOriented s x) = d0
    generalize h_n1 : (fracNumerator (φ 1)).eval (xOriented s x) = n1
    generalize h_d1 : (fracDenominator (φ 1)).eval (xOriented s x) = d1
    have h_alg : d0 * d1 * (c + n0 / d0 + n1 / d1) = (c * d0 + n0) * d1 + n1 * d0 := by
      rw [h_d0] at h0; rw [h_d1] at h1
      field_simp
    rw [h_alg, ← h_d0, ← h_n0, ← h_d1, ← h_n1, eval_factorFormA]
  rw [h_eval_poly, splitPair_formula]
  have hA := eval_affineForm_eq_factor (factorFormA φ c) s hs x
  have hD := eval_affineForm_eq_factor (fracDenominator (φ 1)) s hs x
  have hC := eval_affineForm_eq_factor (fracNumerator (φ 1)) s hs x
  have hB := eval_affineForm_eq_factor (fracDenominator (φ 0)) s hs x
  dsimp [factorR, factorP, factorQ, factorRowForm] at hA hD hC hB ⊢
  rw [← hA, ← hD, ← hC, ← hB]
  ring

/-- Paper Lemma 3 after the rank obstruction: two nonconstant, strictly
oriented denominators supply the exact factor map and shell transitions. -/
private theorem nondegenerate_twoAtoms_yield_f8FactorData
    (φ : Fin 2 → FracAtom 8) (c : ℝ)
    (hsign : ∀ x : Fin 8 → Bool,
      0 < c + ∑ h : Fin 2, (φ h).eval x ↔ f8 x = true)
    (hneg : NegativeDefinite4
      (symmetricPart4
        (mixedMatrix4 (toMultilinear (clearedTwoAtomPoly φ c)))))
    (hslopes :
      (∀ i, (fracDenominator (φ 0)).linear i ≠ 0) ∧
        (∀ i, (fracDenominator (φ 1)).linear i ≠ 0)) :
    Nonempty F8FactorData := by
  set s := factorOrientation φ
  have hs : s = 1 ∨ s = -1 := factorOrientation_cases φ
  refine ⟨{
    P := factorP φ c s
    Q := factorQ φ c s
    r := factorR φ c
    curvature := by
      rw [factorCurvature_eq_clearedTwoAtomPoly_mixed]
      exact hneg
    denominator_left_pos := by
      intro i
      dsimp [factorP, factorRowForm]
      exact div_pos (factorOrientation_pos φ hslopes.1 _) (by norm_num)
    denominator_right_pos := by
      intro i
      dsimp [factorQ, factorRowForm]
      exact div_pos (factorOrientation_pos φ hslopes.1 _) (by norm_num)
    denominator_intercept := by
      have h_int := strictLegal_sign_intercept (fracDenominator (φ 0))
          (fracDenominator_strictLegal (φ 0)) s hs
      dsimp [factorR, factorP, factorQ, factorRowForm]
      have h1 : (∑ i : Fin 4, s * (fracDenominator (φ 0)).linear (Fin.castAdd 4 i) / 2) +
          (∑ i : Fin 4, s * (fracDenominator (φ 0)).linear (Fin.natAdd 4 i) / 2) =
          ∑ i : Fin 8, s * (fracDenominator (φ 0)).linear i / 2 :=
        (Fin.sum_univ_add (fun (k : Fin (4 + 4)) => s * (fracDenominator (φ 0)).linear k / 2)).symm
      rw [h1]
      exact h_int
    transition := by
      intro i j hij ε
      set x1 := defect1 i ε
      set x2 := defect2 i j ε
      have hf1 : f8 x1 = false := f8_defect1 i ε
      have hf2 : f8 x2 = true := f8_defect2 i j hij ε
      set z1 := xOriented s x1
      set z2 := xOriented s x2
      have hfz1 : f8 z1 = false := by rw [f8_xOriented s hs]; exact hf1
      have hfz2 : f8 z2 = true := by rw [f8_xOriented s hs]; exact hf2
      have hsc1 : eval (cubePoint z1) (clearedTwoAtomPoly φ c) ≤ 0 := by
        by_contra h
        push Not at h
        have ht := (clearedTwoAtomPoly_signRepresents φ c hsign z1).mp h
        rw [hfz1] at ht
        exact absurd ht (by decide)
      have hsc2 : 0 < eval (cubePoint z2) (clearedTwoAtomPoly φ c) :=
        (clearedTwoAtomPoly_signRepresents φ c hsign z2).mpr hfz2
      have hdiff : 0 < eval (cubePoint z2) (clearedTwoAtomPoly φ c) - eval (cubePoint z1)
          (clearedTwoAtomPoly φ c) :=
        sub_pos.mpr (lt_of_le_of_lt hsc1 hsc2)
      rw [clearedTwoAtomPoly_eval_eq_splitPair φ c s hs x1, clearedTwoAtomPoly_eval_eq_splitPair
          φ c s hs x2] at hdiff
      change 0 <
        splitPair
            (factorValue (factorP φ c s) (factorQ φ c s) (factorR φ c) (defect2 i j ε))
            (factorValue (factorP φ c s) (factorQ φ c s) (factorR φ c) (defect2 i j ε)) -
          splitPair
            (factorValue (factorP φ c s) (factorQ φ c s) (factorR φ c) (defect1 i ε))
            (factorValue (factorP φ c s) (factorQ φ c s) (factorR φ c) (defect1 i ε)) at hdiff
      exact factor_transition_of_defects
        (factorP φ c s) (factorQ φ c s) (factorR φ c) i j hij ε hdiff
  }⟩

/-- Paper Lemma 4 is now a proved direct-algebra consequence of the factor
data; this wrapper composes it with the remaining Lemma 3 extraction. -/
private theorem nondegenerate_twoAtoms_yield_f8NormalizedSystem
    (φ : Fin 2 → FracAtom 8) (c : ℝ)
    (hsign : ∀ x : Fin 8 → Bool,
      0 < c + ∑ h : Fin 2, (φ h).eval x ↔ f8 x = true)
    (hneg : NegativeDefinite4
      (symmetricPart4
        (mixedMatrix4 (toMultilinear (clearedTwoAtomPoly φ c)))))
    (hslopes :
      (∀ i, (fracDenominator (φ 0)).linear i ≠ 0) ∧
        (∀ i, (fracDenominator (φ 1)).linear i ≠ 0)) :
    Nonempty F8NormalizedSystem := by
  obtain ⟨D⟩ :=
    nondegenerate_twoAtoms_yield_f8FactorData φ c hsign hneg hslopes
  exact f8FactorData_yield_f8NormalizedSystem D
/-- Paper Lemmas 3 and 4: a two-head realization supplies the normalized
system. -/
theorem two_heads_yield_f8NormalizedSystem
    (h : computableWithHeadsN 8 2 f8) :
    Nonempty F8NormalizedSystem := by
  have hfrac : fracComputable 8 2 f8 :=
    (computableWithHeadsN_iff_fracComputable 2 f8).mp h
  obtain ⟨φ, c, hsign⟩ := hfrac
  have hneg := clearedTwoAtomPoly_mixed_negative φ c hsign
  have hslopes :=
    clearedTwoAtom_denominator_slopes_ne_zero φ c hneg
  exact nondegenerate_twoAtoms_yield_f8NormalizedSystem
    φ c hsign hneg hslopes

end HeadComplexity
