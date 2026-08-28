import HeadComplexity.Separations.DistanceThreshold
import HeadComplexity.TypicalLogCloseness.FracAtomBridge
import HeadComplexity.Atoms.TwoHeadClearing
import HeadComplexity.Separations.SignRankBridge

set_option linter.style.header false

/-!
# Eight-bit Hamming threshold: core definitions
-/

namespace HeadComplexity

open Finset
open scoped BigOperators
open TypicalLogCloseness

/-- The radius-one Hamming-ball threshold on two four-bit strings. -/
def f8 : (Fin 8 → Bool) → Bool :=
  distThreshold 4

theorem f8_apply (z : Fin 8 → Bool) :
    f8 z = decide
      (2 ≤ hammingDist (leftBits 4 4 z) (rightBits 4 4 z)) := by
  rfl

namespace EightBitInternal

/-- Complementing all eight bits preserves the Hamming threshold. -/
theorem f8_complement (x : Fin 8 → Bool) :
    f8 (fun i => !x i) = f8 x := by
  dsimp [f8, distThreshold, hammingDist, leftBits, rightBits]
  congr 2
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases x (Fin.castAdd 4 i) <;> cases x (Fin.natAdd 4 i) <;> decide

/-- Nonzero native denominator slopes have one strict common orientation. -/
theorem fracDenominator_strictlyOriented_of_slopes_ne_zero
    (φ : FracAtom 8)
    (h : ∀ i, (fracDenominator φ).linear i ≠ 0) :
    (fracDenominator φ).StrictlyOriented := by
  have hα : φ.α ≠ 1 := by
    intro hα
    apply h 0
    change φ.ρ 0 * (φ.α - 1) = 0
    rw [hα, sub_self, mul_zero]
  rcases lt_or_gt_of_ne hα with hlt | hgt
  · right
    intro i
    change φ.ρ i * (φ.α - 1) < 0
    exact mul_neg_of_pos_of_neg (φ.hρ i) (sub_neg.mpr hlt)
  · left
    intro i
    change 0 < φ.ρ i * (φ.α - 1)
    exact mul_pos (φ.hρ i) (sub_pos.mpr hgt)

/-- Strict legality gives the sign-coordinate intercept margin in either orientation. -/
theorem strictLegal_sign_intercept
    (L : AffineForm 8) (hL : L.StrictLegal)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (∑ i, s * L.linear i / 2) <
      L.constant + ∑ i, L.linear i / 2 := by
  have hfalse := hL (fun _ => false)
  have htrue := hL (fun _ => true)
  simp only [AffineForm.eval, bitReal_false, mul_zero, Finset.sum_const_zero,
    add_zero] at hfalse
  simp only [AffineForm.eval, bitReal_true, mul_one] at htrue
  rcases hs with rfl | rfl
  · simp only [one_mul]
    linarith
  · simp only [neg_one_mul, neg_div]
    rw [Finset.sum_neg_distrib]
    rw [← Finset.sum_div]
    linarith

/-- The ±1 coordinate attached to a Boolean bit. -/
def hammingSign (b : Bool) : ℝ :=
  if b then 1 else -1

@[simp] theorem hammingSign_false : hammingSign false = -1 := rfl
@[simp] theorem hammingSign_true : hammingSign true = 1 := rfl

theorem hammingSign_cases (b : Bool) :
    hammingSign b = 1 ∨ hammingSign b = -1 := by
  cases b <;> simp

theorem bitReal_eq_hammingSign (b : Bool) :
    bitReal b = (hammingSign b + 1) / 2 := by
  cases b <;> norm_num [bitReal, hammingSign]

/-- The split quadratic form q(z)=z₀z₁+z₂z₃ used by the two-factor map. -/
noncomputable def splitJ : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![0, 1 / 2, 0, 0], ![1 / 2, 0, 0, 0],
    ![0, 0, 0, 1 / 2], ![0, 0, 1 / 2, 0]]

theorem splitJ_isSymm : splitJ.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [splitJ, Matrix.transpose_apply]

theorem splitJ_pair_formula (x y : Fin 4 → ℝ) :
    dotProduct x (splitJ.mulVec y) =
      (x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2) / 2 := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  simp [splitJ]
  ring

theorem splitJ_quadratic_formula (z : Fin 4 → ℝ) :
    dotProduct z (splitJ.mulVec z) = z 0 * z 1 + z 2 * z 3 := by
  rw [splitJ_pair_formula]
  ring

def column4 (M : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) : Fin 4 → ℝ :=
  fun i => M i j

noncomputable def splitPair (x y : Fin 4 → ℝ) : ℝ :=
  dotProduct x (splitJ.mulVec y)

theorem splitPair_formula (x y : Fin 4 → ℝ) :
    splitPair x y =
      (x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2) / 2 :=
  splitJ_pair_formula x y

theorem splitPair_symm (x y : Fin 4 → ℝ) :
    splitPair x y = splitPair y x := by
  rw [splitPair_formula, splitPair_formula]
  ring

end EightBitInternal

open EightBitInternal

/-- The quadratic distance polynomial gives the upper threshold-degree bound. -/
theorem f8_thresholdDegLE_two : ThresholdDegLE f8 2 := by
  classical
  open MvPolynomial in
  set P : MvPolynomial (Fin 8) ℝ :=
    (∑ i : Fin 4, (X (Fin.castAdd 4 i) + X (Fin.natAdd 4 i)
      - C 2 * (X (Fin.castAdd 4 i) * X (Fin.natAdd 4 i)))) - C (3 / 2) with hP
  refine ⟨P, ?_, ?_⟩
  · rw [hP]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine totalDegree_finsetSum_le (fun i _ => ?_)
      refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_add _ _).trans
          (max_le (by rw [totalDegree_X]; norm_num) (by rw [totalDegree_X]; norm_num))
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_C, zero_add]
        refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X, totalDegree_X]
    · rw [totalDegree_C]; norm_num
  · intro z
    have hbool : ∀ a b : Bool,
        boolToReal a + boolToReal b - 2 * (boolToReal a * boolToReal b)
          = if a ≠ b then (1 : ℝ) else 0 := by
      intro a b; cases a <;> cases b <;> norm_num [boolToReal]
    have hpair : ∀ i : Fin 4,
        eval (cubePoint z) (X (Fin.castAdd 4 i) + X (Fin.natAdd 4 i)
          - C 2 * (X (Fin.castAdd 4 i) * X (Fin.natAdd 4 i)))
          = if leftBits 4 4 z i ≠ rightBits 4 4 z i then (1 : ℝ) else 0 := by
      intro i
      simp only [map_sub, map_add, map_mul, eval_C, eval_X, cubePoint]
      exact hbool (z (Fin.castAdd 4 i)) (z (Fin.natAdd 4 i))
    have hsum : eval (cubePoint z) P
        = (hammingDist (leftBits 4 4 z) (rightBits 4 4 z) : ℝ) - 3 / 2 := by
      rw [hP, map_sub, eval_C, map_sum]
      congr 1
      unfold hammingDist
      rw [Finset.card_filter]
      push_cast
      exact Finset.sum_congr rfl (fun i _ => hpair i)
    rw [hsum, f8_apply, decide_eq_true_eq]
    set D := hammingDist (leftBits 4 4 z) (rightBits 4 4 z) with hD
    constructor
    · intro h
      have hD1 : 3 < 2 * (D : ℝ) := by linarith
      have hD2 : 3 < 2 * D := by exact_mod_cast hD1
      omega
    · intro h
      have hD_real : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast h
      linarith

/-- A two-coordinate checkerboard restriction excludes affine threshold
representations. -/
theorem f8_not_thresholdDegLE_one : ¬ ThresholdDegLE f8 1 := by
  intro hLTF1
  rw [ThresholdDegLE_one_iff_isLTF] at hLTF1
  obtain ⟨c, cs, hsign⟩ := hLTF1
  let x0 : Fin 4 → Bool := ![false, false, false, false]
  let x1 : Fin 4 → Bool := ![true, false, false, false]
  let y0 : Fin 4 → Bool := ![false, true, false, false]
  let y1 : Fin 4 → Bool := ![true, true, false, false]
  let z00 := blockJoin x0 y0
  let z11 := blockJoin x1 y1
  let z01 := blockJoin x0 y1
  let z10 := blockJoin x1 y0
  have hpt : ∀ j : Fin (4 + 4),
      boolToReal (z00 j) + boolToReal (z11 j) =
        boolToReal (z01 j) + boolToReal (z10 j) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [z00, z11, z01, z10, blockJoin_castAdd]
    · simp only [z00, z11, z01, z10, blockJoin_natAdd]
      ring
  have hsid : (∑ j, cs j * boolToReal (z00 j)) + (∑ j, cs j * boolToReal (z11 j)) =
              (∑ j, cs j * boolToReal (z01 j)) + (∑ j, cs j * boolToReal (z10 j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← mul_add, ← mul_add, hpt j]
  have h_z00 : f8 z00 = false := rfl
  have h_z11 : f8 z11 = false := rfl
  have h_z01 : f8 z01 = true := rfl
  have h_z10 : f8 z10 = true := rfl
  have hpos_01 : 0 < c + ∑ i, cs i * boolToReal (z01 i) := (hsign _).mpr h_z01
  have hpos_10 : 0 < c + ∑ i, cs i * boolToReal (z10 i) := (hsign _).mpr h_z10
  have hneg_00 : c + ∑ i, cs i * boolToReal (z00 i) ≤ 0 := by
    by_contra h; push Not at h
    have := (hsign _).mp h; rw [h_z00] at this; exact absurd this (by decide)
  have hneg_11 : c + ∑ i, cs i * boolToReal (z11 i) ≤ 0 := by
    by_contra h; push Not at h
    have := (hsign _).mp h; rw [h_z11] at this; exact absurd this (by decide)
  linarith

theorem thresholdDeg_f8 : thresholdDeg f8 = 2 := by
  have hle := thresholdDeg_le_of f8_thresholdDegLE_two
  have hlt := lt_thresholdDeg_of f8_not_thresholdDegLE_one
  omega

/-- Mixed coefficient matrix between the left and right four-bit blocks. -/
noncomputable def mixedMatrix4
    (P : MvPolynomial (Fin 8) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    MvPolynomial.coeff
      (Finsupp.single (Fin.castAdd 4 i) 1 +
        Finsupp.single (Fin.natAdd 4 j) 1) P

/-- Symmetric part of a square matrix. -/
noncomputable def symmetricPart4 (K : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (K i j + K j i) / 2

/-- Quadratic form convention used by the spectral lower bound. -/
noncomputable def quadraticForm4 (M : Matrix (Fin 4) (Fin 4) ℝ)
    (z : Fin 4 → ℝ) : ℝ :=
  dotProduct z (M.mulVec z)

/-- Elementary negative-definiteness predicate, avoiding any dependence on a
particular eigenvalue API. -/
def NegativeDefinite4 (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ z, z ≠ 0 → quadraticForm4 M z < 0

/-- Elementary positive-definiteness predicate. -/
def PositiveDefinite4 (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ z, z ≠ 0 → 0 < quadraticForm4 M z

/-- The form is positive on a two-dimensional subspace, encoded by two
generators and all their nontrivial linear combinations. -/
def PositiveIndexAtLeastTwo4 (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃ u v : Fin 4 → ℝ, ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
    0 < quadraticForm4 M (fun i => a * u i + b * v i)

/-- Inertia `(2,2)` in dimension four. -/
def InertiaTwoTwo4 (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  M.IsSymm ∧ PositiveIndexAtLeastTwo4 M ∧ PositiveIndexAtLeastTwo4 (-M)

open MvPolynomial

/-- The normalized pointwise system forced by a hypothetical two-head score. -/
structure F8NormalizedSystem where
  U : Matrix (Fin 4) (Fin 4) ℝ
  V : Matrix (Fin 4) (Fin 4) ℝ
  w : Fin 4 → ℝ
  μ : Fin 4 → ℝ
  U_pos : PositiveDefinite4 (U + U.transpose)
  V_inertia : InertiaTwoTwo4 V
  diagonal_pos : ∀ j, 0 < U j j
  contraction : ∀ i j, i ≠ j →
    |w j| + |U j i - V j i| +
      ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
        |U j k + V j k| < U j j
  leftSlope_pos : ∀ i, 0 < (U.transpose.mulVec μ) i
  rightSlope_pos : ∀ i, 0 < (V.mulVec μ) i
  null : quadraticForm4 V μ = 0
  intercept :
    (∑ i, (U.transpose.mulVec μ) i) +
      (∑ i, (V.mulVec μ) i) < dotProduct μ w

/-- The spectral hypothesis used in the paper: a positive diagonal left
multiplier symmetrizes `M`, and the resulting symmetric form has positive
index at least two. Encoding the index on the symmetrized matrix avoids any
choice of a nonsymmetric eigenvalue API. -/
def DiagonallySymmetrizableWithPositiveIndexTwo4
    (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃ d : Fin 4 → ℝ, (∀ i, 0 < d i) ∧
    ((Matrix.diagonal d) * M).IsSymm ∧
    PositiveIndexAtLeastTwo4 ((Matrix.diagonal d) * M)

namespace EightBitInternal

def offDiagSet (j : Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => i ≠ j)

lemma offDiagSet_nonempty (j : Fin 4) : (offDiagSet j).Nonempty := by
  change (Finset.univ.filter (fun i => i ≠ j)).Nonempty
  fin_cases j
  · use 1; simp
  · use 0; simp
  · use 0; simp
  · use 0; simp

lemma sum_fin4 (f : Fin 4 → ℝ) :
    ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_four]

lemma diag_mul_apply (d : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    ((Matrix.diagonal d) * M) i j = d i * M i j := by
  rw [Matrix.mul_apply, sum_fin4]
  fin_cases i <;> fin_cases j <;> simp

end EightBitInternal

end HeadComplexity
