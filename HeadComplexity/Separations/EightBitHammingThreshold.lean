import HeadComplexity.Separations.DistanceThreshold
import HeadComplexity.TypicalLogCloseness.FracAtomBridge
import HeadComplexity.Atoms.TwoHeadClearing
import HeadComplexity.Separations.SignRankBridge

set_option linter.style.header false

/-!
# Theorem 189: the eight-bit Hamming-threshold separation

This file freezes the complete theorem statement and the proof interfaces used
by the paper proof: quadratic mixed curvature, the normalized two-head system,
the four-dimensional column-max spectral obstruction, and the explicit integer
three-head certificate.
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

/-- Complementing all eight bits preserves the Hamming threshold. -/
private theorem f8_complement (x : Fin 8 → Bool) :
    f8 (fun i => !x i) = f8 x := by
  dsimp [f8, distThreshold, hammingDist, leftBits, rightBits]
  congr 2
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases x (Fin.castAdd 4 i) <;> cases x (Fin.natAdd 4 i) <;> decide

/-- Nonzero native denominator slopes have one strict common orientation. -/
private theorem fracDenominator_strictlyOriented_of_slopes_ne_zero
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
private theorem strictLegal_sign_intercept
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
private def hammingSign (b : Bool) : ℝ :=
  if b then 1 else -1

@[simp] private theorem hammingSign_false : hammingSign false = -1 := rfl
@[simp] private theorem hammingSign_true : hammingSign true = 1 := rfl

private theorem hammingSign_cases (b : Bool) :
    hammingSign b = 1 ∨ hammingSign b = -1 := by
  cases b <;> simp

private theorem bitReal_eq_hammingSign (b : Bool) :
    bitReal b = (hammingSign b + 1) / 2 := by
  cases b <;> norm_num [bitReal, hammingSign]

/-- The split quadratic form q(z)=z₀z₁+z₂z₃ used by the two-factor map. -/
private noncomputable def splitJ : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![0, 1 / 2, 0, 0], ![1 / 2, 0, 0, 0],
    ![0, 0, 0, 1 / 2], ![0, 0, 1 / 2, 0]]

private theorem splitJ_isSymm : splitJ.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [splitJ, Matrix.transpose_apply]

private theorem splitJ_pair_formula (x y : Fin 4 → ℝ) :
    dotProduct x (splitJ.mulVec y) =
      (x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2) / 2 := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  simp [splitJ]
  ring

private theorem splitJ_quadratic_formula (z : Fin 4 → ℝ) :
    dotProduct z (splitJ.mulVec z) = z 0 * z 1 + z 2 * z 3 := by
  rw [splitJ_pair_formula]
  ring

private def column4 (M : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) : Fin 4 → ℝ :=
  fun i => M i j

private noncomputable def splitPair (x y : Fin 4 → ℝ) : ℝ :=
  dotProduct x (splitJ.mulVec y)

private theorem splitPair_formula (x y : Fin 4 → ℝ) :
    splitPair x y =
      (x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2) / 2 :=
  splitJ_pair_formula x y

private theorem splitPair_symm (x y : Fin 4 → ℝ) :
    splitPair x y = splitPair y x := by
  rw [splitPair_formula, splitPair_formula]
  ring

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

/-- 4-point checkerboard second difference helper: mixed term evaluation identity. -/
private theorem checkerboard_second_diff_term (u u' v v' : Fin 4 → Bool) (i j : Fin 4) :
    boolToReal (u' i) * boolToReal (v' j) - boolToReal (u' i) * boolToReal (v j) -
      boolToReal (u i) * boolToReal (v' j) + boolToReal (u i) * boolToReal (v j) =
    (boolToReal (u' i) - boolToReal (u i)) * (boolToReal (v' j) - boolToReal (v j)) := by
  ring

private noncomputable def bilinear4 (K : Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * K i j * v j

private def bitDiff4 (x₀ x₁ : Fin 4 → Bool) : Fin 4 → ℝ :=
  fun i => boolToReal (x₀ i) - boolToReal (x₁ i)

private theorem fin_castAdd_ne_natAdd (i j : Fin 4) : Fin.castAdd 4 i ≠ Fin.natAdd 4 j := by
  intro h
  have hval := congr_arg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

private theorem fin_natAdd_ne_castAdd (j i : Fin 4) : Fin.natAdd 4 j ≠ Fin.castAdd 4 i :=
  (fin_castAdd_ne_natAdd i j).symm

/-- A degree-at-most-two exponent vector either lives in one four-variable
block or is exactly one linear variable from each block. -/
private theorem fin8_degree_le_two_block_classification
    (s : Fin 8 →₀ ℕ) (hs : s.sum (fun _ e => e) ≤ 2) :
    (∀ j : Fin 4, s (Fin.natAdd 4 j) = 0) ∨
      (∀ i : Fin 4, s (Fin.castAdd 4 i) = 0) ∨
      ∃ i j : Fin 4,
        s = Finsupp.single (Fin.castAdd 4 i) 1 +
          Finsupp.single (Fin.natAdd 4 j) 1 := by
  by_cases hR : ∀ j : Fin 4, s (Fin.natAdd 4 j) = 0
  · left; exact hR
  · right
    by_cases hL : ∀ i : Fin 4, s (Fin.castAdd 4 i) = 0
    · left; exact hL
    · right
      push Not at hR hL
      rcases hR with ⟨j, hj⟩
      rcases hL with ⟨i, hi⟩
      use i, j
      have hj_pos : 1 ≤ s (Fin.natAdd 4 j) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj)
      have hi_pos : 1 ≤ s (Fin.castAdd 4 i) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi)
      have hsum : (∑ k : Fin 8, s k) ≤ 2 := by
        rw [← Finsupp.sum_fintype s (fun _ e => e) (fun _ => rfl)]
        exact hs
      have hsum_split : (∑ k : Fin 4, s (Fin.castAdd 4 k)) + (∑ k : Fin 4, s (Fin.natAdd 4 k)) ≤ 2 := by
        have h := Fin.sum_univ_add (fun (k : Fin (4 + 4)) => s k)
        rw [← h]
        exact hsum
      have hL_sum : s (Fin.castAdd 4 i) ≤ ∑ k : Fin 4, s (Fin.castAdd 4 k) :=
        Finset.single_le_sum (f := fun k => s (Fin.castAdd 4 k)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hR_sum : s (Fin.natAdd 4 j) ≤ ∑ k : Fin 4, s (Fin.natAdd 4 k) :=
        Finset.single_le_sum (f := fun k => s (Fin.natAdd 4 k)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h_eq_i : s (Fin.castAdd 4 i) = 1 := by omega
      have h_eq_j : s (Fin.natAdd 4 j) = 1 := by omega
      have hL_other (i' : Fin 4) (hne : i' ≠ i) : s (Fin.castAdd 4 i') = 0 := by
        have : s (Fin.castAdd 4 i) + s (Fin.castAdd 4 i') ≤ ∑ k : Fin 4, s (Fin.castAdd 4 k) := by
          have hpair : {i, i'} ⊆ (Finset.univ : Finset (Fin 4)) := Finset.subset_univ _
          have hsum_pair := Finset.sum_le_sum_of_subset (f := fun k => s (Fin.castAdd 4 k)) hpair
          rw [Finset.sum_insert (by simp [hne.symm]), Finset.sum_singleton] at hsum_pair
          exact hsum_pair
        omega
      have hR_other (j' : Fin 4) (hne : j' ≠ j) : s (Fin.natAdd 4 j') = 0 := by
        have : s (Fin.natAdd 4 j) + s (Fin.natAdd 4 j') ≤ ∑ k : Fin 4, s (Fin.natAdd 4 k) := by
          have hpair : {j, j'} ⊆ (Finset.univ : Finset (Fin 4)) := Finset.subset_univ _
          have hsum_pair := Finset.sum_le_sum_of_subset (f := fun k => s (Fin.natAdd 4 k)) hpair
          rw [Finset.sum_insert (by simp [hne.symm]), Finset.sum_singleton] at hsum_pair
          exact hsum_pair
        omega
      ext (k : Fin (4 + 4))
      refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
      · simp only [Finsupp.add_apply, Finsupp.single_apply]
        have h_neq : Fin.natAdd 4 j ≠ Fin.castAdd 4 k' := fin_natAdd_ne_castAdd j k'
        simp only [h_neq, if_false, add_zero]
        by_cases hk : Fin.castAdd 4 i = Fin.castAdd 4 k'
        · have hk' : i = k' := Fin.castAdd_inj.mp hk
          subst hk'
          rw [if_pos rfl, h_eq_i]
        · rw [if_neg hk]
          have hk' : k' ≠ i := by
            intro h_eq
            subst h_eq
            exact hk rfl
          exact hL_other k' hk'
      · simp only [Finsupp.add_apply, Finsupp.single_apply]
        have h_neq : Fin.castAdd 4 i ≠ Fin.natAdd 4 k' := fin_castAdd_ne_natAdd i k'
        simp only [h_neq, if_false, zero_add]
        by_cases hk : Fin.natAdd 4 j = Fin.natAdd 4 k'
        · have hk' : j = k' := (Fin.natAdd_inj 4).mp hk
          subst hk'
          rw [if_pos rfl, h_eq_j]
        · rw [if_neg hk]
          have hk' : k' ≠ j := by
            intro h_eq
            subst h_eq
            exact hk rfl
          exact hR_other k' hk'

/-- The checkerboard identity for one bounded-degree monomial.  This is the
only place where the eight-coordinate exponent vector is classified. -/
private theorem bounded_monomial_checkerboard_difference
    (s : Fin 8 →₀ ℕ) (a : ℝ)
    (hs : s.sum (fun _ e => e) ≤ 2)
    (x₀ x₁ y₀ y₁ : Fin 4 → Bool) :
    eval (cubePoint (blockJoin x₀ y₀)) (monomial s a) -
        eval (cubePoint (blockJoin x₀ y₁)) (monomial s a) -
        eval (cubePoint (blockJoin x₁ y₀)) (monomial s a) +
        eval (cubePoint (blockJoin x₁ y₁)) (monomial s a) =
      bilinear4 (mixedMatrix4 (monomial s a))
        (bitDiff4 x₀ x₁) (bitDiff4 y₀ y₁) := by
  rcases fin8_degree_le_two_block_classification s hs with hL | hR | ⟨i, j, hs_eq⟩
  · have h1 : eval (cubePoint (blockJoin x₀ y₀)) (monomial s a) = eval (cubePoint (blockJoin x₀ y₁)) (monomial s a) := by
      simp only [eval_monomial, cubePoint]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
      · simp only [blockJoin_castAdd]
      · simp only [blockJoin_natAdd, hL k', pow_zero]
    have h2 : eval (cubePoint (blockJoin x₁ y₀)) (monomial s a) = eval (cubePoint (blockJoin x₁ y₁)) (monomial s a) := by
      simp only [eval_monomial, cubePoint]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
      · simp only [blockJoin_castAdd]
      · simp only [blockJoin_natAdd, hL k', pow_zero]
    rw [h1, h2]
    have h3 : mixedMatrix4 (monomial s a) = 0 := by
      ext i' j'
      unfold mixedMatrix4
      rw [coeff_monomial]
      split_ifs with h_eq
      · exfalso
        have hj := Finsupp.ext_iff.mp h_eq (Fin.natAdd 4 j')
        rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne] at hj
        · have hj0 := hL j'
          rw [hj] at hj0
          contradiction
        · intro h_ne
          have hval := congr_arg Fin.val h_ne
          dsimp at hval
          omega
      · rfl
    rw [h3]
    unfold bilinear4
    simp
  · have h1 : eval (cubePoint (blockJoin x₀ y₀)) (monomial s a) = eval (cubePoint (blockJoin x₁ y₀)) (monomial s a) := by
      simp only [eval_monomial, cubePoint]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
      · simp only [blockJoin_castAdd, hR k', pow_zero]
      · simp only [blockJoin_natAdd]
    have h2 : eval (cubePoint (blockJoin x₀ y₁)) (monomial s a) = eval (cubePoint (blockJoin x₁ y₁)) (monomial s a) := by
      simp only [eval_monomial, cubePoint]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
      · simp only [blockJoin_castAdd, hR k', pow_zero]
      · simp only [blockJoin_natAdd]
    rw [h1, h2]
    have h3 : mixedMatrix4 (monomial s a) = 0 := by
      ext i' j'
      unfold mixedMatrix4
      rw [coeff_monomial]
      split_ifs with h_eq
      · exfalso
        have hi := Finsupp.ext_iff.mp h_eq (Fin.castAdd 4 i')
        rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne] at hi
        · have hi0 := hR i'
          rw [hi] at hi0
          contradiction
        · intro h_ne
          have hval := congr_arg Fin.val h_ne
          dsimp at hval
          omega
      · rfl
    rw [h3]
    unfold bilinear4
    simp
  · rw [hs_eq]
    have h_eval (u : Fin 4 → Bool) (v : Fin 4 → Bool) :
        eval (cubePoint (blockJoin u v)) (monomial (Finsupp.single (Fin.castAdd 4 i) 1 + Finsupp.single (Fin.natAdd 4 j) 1) a) =
          a * boolToReal (u i) * boolToReal (v j) := by
      rw [eval_monomial]
      dsimp [cubePoint]
      have h_prod := Finsupp.prod_add_index'
        (f := Finsupp.single (Fin.castAdd 4 i) 1)
        (g := Finsupp.single (Fin.natAdd 4 j) 1)
        (h := fun (x : Fin 8) (e : ℕ) => boolToReal (blockJoin u v x) ^ e)
        (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
      rw [h_prod]
      rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
      simp only [pow_one, blockJoin_castAdd, blockJoin_natAdd]
      ring
    rw [h_eval x₀ y₀, h_eval x₀ y₁, h_eval x₁ y₀, h_eval x₁ y₁]
    have h_mix : mixedMatrix4 (monomial (Finsupp.single (Fin.castAdd 4 i) 1 + Finsupp.single (Fin.natAdd 4 j) 1) a) =
        fun i' j' => if i' = i ∧ j' = j then a else 0 := by
      ext i' j'
      unfold mixedMatrix4
      rw [coeff_monomial]
      by_cases h_ij : i' = i ∧ j' = j
      · rw [if_pos h_ij, if_pos]
        rw [h_ij.1, h_ij.2]
      · rw [if_neg h_ij, if_neg]
        intro h_eq
        apply h_ij
        have h1_ext := Finsupp.ext_iff.mp h_eq
        have hi' := h1_ext (Fin.castAdd 4 i')
        have hj' := h1_ext (Fin.natAdd 4 j')
        rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply] at hi' hj'
        have h_ca2 : ¬Fin.natAdd 4 j = Fin.castAdd 4 i' := by
          intro h_ne; have hval := congr_arg Fin.val h_ne; dsimp at hval; omega
        have h_ca3 : ¬Fin.natAdd 4 j' = Fin.castAdd 4 i' := by
          intro h_ne; have hval := congr_arg Fin.val h_ne; dsimp at hval; omega
        have h_na1 : ¬Fin.castAdd 4 i = Fin.natAdd 4 j' := by
          intro h_ne; have hval := congr_arg Fin.val h_ne; dsimp at hval; omega
        have h_na3 : ¬Fin.castAdd 4 i' = Fin.natAdd 4 j' := by
          intro h_ne; have hval := congr_arg Fin.val h_ne; dsimp at hval; omega
        have h_i : i' = i := by
          by_contra h_ne
          have h_ca1 : ¬Fin.castAdd 4 i = Fin.castAdd 4 i' := by
            intro h; exact h_ne (Fin.ext (by have hval := congr_arg Fin.val h; dsimp at hval; exact hval)).symm
          rw [if_neg h_ca1, if_neg h_ca2, if_pos rfl, if_neg h_ca3] at hi'
          contradiction
        have h_j : j' = j := by
          by_contra h_ne
          have h_na2 : ¬Fin.natAdd 4 j = Fin.natAdd 4 j' := by
            intro h; exact h_ne (Fin.ext (by have hval := congr_arg Fin.val h; dsimp at hval; omega)).symm
          rw [if_neg h_na1, if_neg h_na2, if_neg h_na3, if_pos rfl] at hj'
          contradiction
        exact ⟨h_i, h_j⟩
    rw [h_mix]
    unfold bilinear4 bitDiff4
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp only [and_self, if_true]
        have h_diff := checkerboard_second_diff_term x₁ x₀ y₁ y₀ i j
        linear_combination a * h_diff
      · intro k _ hk
        have h_and : ¬(i = i ∧ k = j) := by rintro ⟨_, rfl⟩; exact hk rfl
        dsimp
        rw [if_neg h_and]
        ring
      · intro h
        exact False.elim (h (Finset.mem_univ j))
    · intro k _ hk
      have h_sum_zero : (∑ j_1 : Fin 4, (boolToReal (x₀ k) - boolToReal (x₁ k)) * (if k = i ∧ j_1 = j then a else 0) * (boolToReal (y₀ j_1) - boolToReal (y₁ j_1))) = 0 := by
        refine Finset.sum_eq_zero (fun k' _ => ?_)
        have h_and : ¬(k = i ∧ k' = j) := by rintro ⟨rfl, _⟩; exact hk rfl
        rw [if_neg h_and]
        ring
      exact h_sum_zero
    · intro h
      exact False.elim (h (Finset.mem_univ i))

/-- Degree-two checkerboard differences retain exactly the mixed block. -/
private theorem quadratic_checkerboard_difference
    (P : MvPolynomial (Fin 8) ℝ) (hdeg : P.totalDegree ≤ 2)
    (x₀ x₁ y₀ y₁ : Fin 4 → Bool) :
    eval (cubePoint (blockJoin x₀ y₀)) P -
        eval (cubePoint (blockJoin x₀ y₁)) P -
        eval (cubePoint (blockJoin x₁ y₀)) P +
        eval (cubePoint (blockJoin x₁ y₁)) P =
      bilinear4 (mixedMatrix4 P) (bitDiff4 x₀ x₁) (bitDiff4 y₀ y₁) := by
  have hP : P = ∑ s ∈ P.support, monomial s (coeff s P) := P.as_sum
  have h_eval (z : Fin 8 → ℝ) : eval z P = ∑ s ∈ P.support, eval z (monomial s (coeff s P)) := by
    nth_rw 1 [hP]
    exact map_sum (eval z) (fun s => monomial s (coeff s P)) P.support
  rw [h_eval (cubePoint (blockJoin x₀ y₀)), h_eval (cubePoint (blockJoin x₀ y₁)),
      h_eval (cubePoint (blockJoin x₁ y₀)), h_eval (cubePoint (blockJoin x₁ y₁))]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have h_mono : ∀ s ∈ P.support,
      eval (cubePoint (blockJoin x₀ y₀)) (monomial s (coeff s P)) -
          eval (cubePoint (blockJoin x₀ y₁)) (monomial s (coeff s P)) -
          eval (cubePoint (blockJoin x₁ y₀)) (monomial s (coeff s P)) +
          eval (cubePoint (blockJoin x₁ y₁)) (monomial s (coeff s P)) =
        bilinear4 (mixedMatrix4 (monomial s (coeff s P)))
          (bitDiff4 x₀ x₁) (bitDiff4 y₀ y₁) := by
    intro s hs
    have hdeg_s : s.sum (fun _ e => e) ≤ 2 := (le_totalDegree hs).trans hdeg
    exact bounded_monomial_checkerboard_difference s (coeff s P) hdeg_s x₀ x₁ y₀ y₁
  rw [Finset.sum_congr rfl h_mono]
  dsimp [bilinear4, mixedMatrix4]
  conv_rhs => rw [hP]
  simp_rw [coeff_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext i
  rw [Finset.sum_comm]

/-- A simultaneous signed coordinate permutation. The Boolean action
complements flipped coordinates on both blocks, so it preserves Hamming
distance. -/
private structure SignedPerm4 where
  perm : Equiv.Perm (Fin 4)
  flip : Fin 4 → Bool

private def SignedPerm4.act (T : SignedPerm4) (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => if T.flip i then -z (T.perm i) else z (T.perm i)

private def SignedPerm4.actBool (T : SignedPerm4)
    (x : Fin 4 → Bool) : Fin 4 → Bool :=
  fun i => if T.flip i then !(x (T.perm i)) else x (T.perm i)

/-- Boolean signed permutations transport checkerboard difference vectors. -/
private theorem bitDiff4_actBool (T : SignedPerm4)
    (x₀ x₁ : Fin 4 → Bool) :
    bitDiff4 (T.actBool x₀) (T.actBool x₁) =
      T.act (bitDiff4 x₀ x₁) := by
  funext i
  cases hflip : T.flip i <;>
    cases hx0 : x₀ (T.perm i) <;>
    cases hx1 : x₁ (T.perm i) <;>
    simp [SignedPerm4.actBool, SignedPerm4.act, bitDiff4,
      hflip, hx0, hx1, boolToReal]

/-- Swapping the two four-bit blocks preserves the distance threshold. -/
private theorem f8_blockJoin_swap (x y : Fin 4 → Bool) :
    f8 (blockJoin x y) = f8 (blockJoin y x) := by
  simp [f8, distThreshold, hammingDist, ne_comm]

/-- Applying the same signed permutation to both blocks preserves f8. -/
private theorem f8_blockJoin_actBool (T : SignedPerm4)
    (x y : Fin 4 → Bool) :
    f8 (blockJoin (T.actBool x) (T.actBool y)) =
      f8 (blockJoin x y) := by
  let x' : Fin 4 → Bool := fun i => x (T.perm i)
  let y' : Fin 4 → Bool := fun i => y (T.perm i)
  let twist : ∀ _ : Fin 4, Bool → Bool :=
    fun i b => if T.flip i then !b else b
  have htwist : ∀ i, Function.Injective (twist i) := by
    intro i a b hab
    cases hflip : T.flip i <;>
      cases a <;> cases b <;> simp_all [twist]
  have hact (z : Fin 4 → Bool) :
      T.actBool z = fun i => twist i (z (T.perm i)) := by
    funext i
    cases hflip : T.flip i <;>
      simp [SignedPerm4.actBool, twist, hflip]
  have hcomp :
      hammingDist (T.actBool x) (T.actBool y) =
        hammingDist x' y' := by
    rw [hact x, hact y]
    simpa [x', y'] using
      (hammingDist_comp twist (x := x') (y := y') htwist)
  have hreindex : hammingDist x' y' = hammingDist x y := by
    unfold hammingDist
    let S := Finset.univ.filter (fun i : Fin 4 => x i ≠ y i)
    have hfilter :
        Finset.univ.filter (fun i : Fin 4 => x' i ≠ y' i) =
          S.map T.perm.symm.toEmbedding := by
      ext i
      simp [S, x', y']
    rw [hfilter, Finset.card_map]
  simp [f8, distThreshold, hcomp.trans hreindex]

/-- Bilinear evaluation on the symmetric part is the average of both orders. -/
private theorem bilinear4_symmetricPart
    (K : Matrix (Fin 4) (Fin 4) ℝ) (u v : Fin 4 → ℝ) :
    bilinear4 (symmetricPart4 K) u v =
      (bilinear4 K u v + bilinear4 K v u) / 2 := by
  unfold bilinear4 symmetricPart4
  simp only [Fin.sum_univ_four]
  ring

/-- One negative-positive-positive-negative rectangle controls the symmetric
mixed bilinear form in its two checkerboard directions. -/
private theorem checkerboard_symmetric_sign_neg
    (P : MvPolynomial (Fin 8) ℝ) (hdeg : P.totalDegree ≤ 2)
    (hrep : SignRepresents P f8)
    (x₀ x₁ y₀ y₁ : Fin 4 → Bool)
    (h00 : f8 (blockJoin x₀ y₀) = false)
    (h01 : f8 (blockJoin x₀ y₁) = true)
    (h10 : f8 (blockJoin x₁ y₀) = true)
    (h11 : f8 (blockJoin x₁ y₁) = false) :
    bilinear4 (symmetricPart4 (mixedMatrix4 P))
      (bitDiff4 x₀ x₁) (bitDiff4 y₀ y₁) < 0 := by
  have hnonpos (a b : Fin 4 → Bool)
      (hf : f8 (blockJoin a b) = false) :
      eval (cubePoint (blockJoin a b)) P ≤ 0 := by
    by_contra h
    push Not at h
    have ht := (hrep (blockJoin a b)).mp h
    rw [hf] at ht
    exact absurd ht (by decide)
  have hpos (a b : Fin 4 → Bool)
      (ht : f8 (blockJoin a b) = true) :
      0 < eval (cubePoint (blockJoin a b)) P :=
    (hrep (blockJoin a b)).mpr ht
  have huv : bilinear4 (mixedMatrix4 P)
      (bitDiff4 x₀ x₁) (bitDiff4 y₀ y₁) < 0 := by
    have hid := quadratic_checkerboard_difference P hdeg x₀ x₁ y₀ y₁
    linarith [hnonpos x₀ y₀ h00, hpos x₀ y₁ h01,
      hpos x₁ y₀ h10, hnonpos x₁ y₁ h11]
  have h00' : f8 (blockJoin y₀ x₀) = false := by
    rw [f8_blockJoin_swap]
    exact h00
  have h01' : f8 (blockJoin y₀ x₁) = true := by
    rw [f8_blockJoin_swap]
    exact h10
  have h10' : f8 (blockJoin y₁ x₀) = true := by
    rw [f8_blockJoin_swap]
    exact h01
  have h11' : f8 (blockJoin y₁ x₁) = false := by
    rw [f8_blockJoin_swap]
    exact h11
  have hvu : bilinear4 (mixedMatrix4 P)
      (bitDiff4 y₀ y₁) (bitDiff4 x₀ x₁) < 0 := by
    have hid := quadratic_checkerboard_difference P hdeg y₀ y₁ x₀ x₁
    linarith [hnonpos y₀ x₀ h00', hpos y₀ x₁ h01',
      hpos y₁ x₀ h10', hnonpos y₁ x₁ h11']
  rw [bilinear4_symmetricPart]
  linarith

/-- The preceding rectangle inequality transports through every simultaneous
signed coordinate permutation. -/
private theorem checkerboard_symmetric_sign_neg_act
    (P : MvPolynomial (Fin 8) ℝ) (hdeg : P.totalDegree ≤ 2)
    (hrep : SignRepresents P f8)
    (x₀ x₁ y₀ y₁ : Fin 4 → Bool)
    (h00 : f8 (blockJoin x₀ y₀) = false)
    (h01 : f8 (blockJoin x₀ y₁) = true)
    (h10 : f8 (blockJoin x₁ y₀) = true)
    (h11 : f8 (blockJoin x₁ y₁) = false)
    (T : SignedPerm4) :
    bilinear4 (symmetricPart4 (mixedMatrix4 P))
      (T.act (bitDiff4 x₀ x₁)) (T.act (bitDiff4 y₀ y₁)) < 0 := by
  rw [← bitDiff4_actBool T x₀ x₁, ← bitDiff4_actBool T y₀ y₁]
  apply checkerboard_symmetric_sign_neg P hdeg hrep
  · rw [f8_blockJoin_actBool]
    exact h00
  · rw [f8_blockJoin_actBool]
    exact h01
  · rw [f8_blockJoin_actBool]
    exact h10
  · rw [f8_blockJoin_actBool]
    exact h11

private def prefix1 : Fin 4 → ℝ := ![1, 0, 0, 0]
private def prefix2 : Fin 4 → ℝ := ![1, 1, 0, 0]
private def prefix3 : Fin 4 → ℝ := ![1, 1, 1, 0]
private def prefix4 : Fin 4 → ℝ := ![1, 1, 1, 1]
private def q2 : Fin 4 → ℝ := ![1, 0, 1, 1]
private def q3 : Fin 4 → ℝ := ![1, 1, 0, 1]
private def r2 : Fin 4 → ℝ := ![1, 1, 0, 0]
private def r3 : Fin 4 → ℝ := ![1, 0, 1, 0]
private def r4 : Fin 4 → ℝ := ![1, 0, 0, 1]

/-- The signed-permutation closure of the finite curvature certificate used
in paper Lemma 2. The only uncontrolled prefix cross term is `(p₁,p₄)`;
the `q` and `r` fields control it in the two possible coefficient orders. -/
private structure F8CurvatureCertificate
    (S : Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  p1p1 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix1) (T.act prefix1) < 0
  p2p2 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix2) (T.act prefix2) < 0
  p3p3 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix3) (T.act prefix3) < 0
  p4p4 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix4) (T.act prefix4) < 0
  p1p2 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix1) (T.act prefix2) < 0
  p1p3 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix1) (T.act prefix3) < 0
  p2p3 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix2) (T.act prefix3) < 0
  p2p4 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix2) (T.act prefix4) < 0
  p3p4 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix3) (T.act prefix4) < 0
  p1q2 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix1) (T.act q2) < 0
  p1q3 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix1) (T.act q3) < 0
  p4r2 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix4) (T.act r2) < 0
  p4r3 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix4) (T.act r3) < 0
  p4r4 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix4) (T.act r4) < 0

private theorem SignedPerm4.act_add (T : SignedPerm4) (u v : Fin 4 → ℝ) :
    T.act (fun i => u i + v i) = fun i => T.act u i + T.act v i := by
  ext i
  dsimp [SignedPerm4.act]
  split_ifs <;> ring

private theorem SignedPerm4.act_smul (T : SignedPerm4) (c : ℝ) (u : Fin 4 → ℝ) :
    T.act (fun i => c * u i) = fun i => c * T.act u i := by
  ext i
  dsimp [SignedPerm4.act]
  split_ifs <;> ring

private theorem bilinear4_add_right (S : Matrix (Fin 4) (Fin 4) ℝ) (u v1 v2 : Fin 4 → ℝ) :
    bilinear4 S u (fun i => v1 i + v2 i) = bilinear4 S u v1 + bilinear4 S u v2 := by
  dsimp [bilinear4]
  simp only [Fin.sum_univ_four]
  ring

private theorem bilinear4_smul_right (S : Matrix (Fin 4) (Fin 4) ℝ) (c : ℝ) (u v : Fin 4 → ℝ) :
    bilinear4 S u (fun i => c * v i) = c * bilinear4 S u v := by
  dsimp [bilinear4]
  simp only [Fin.sum_univ_four]
  ring

/-- The fourteen exact checkerboards, transported by simultaneous signed
coordinate permutations, yield the abstract curvature certificate. -/
private theorem f8_has_curvatureCertificate
    (P : MvPolynomial (Fin 8) ℝ)
    (hdeg : P.totalDegree ≤ 2)
    (hrep : SignRepresents P f8) :
    F8CurvatureCertificate (symmetricPart4 (mixedMatrix4 P)) := by
  set S := symmetricPart4 (mixedMatrix4 P)
  have h_p1p1 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix1) (T.act prefix1) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, false, false, false] ![false, false, false, false]
      ![true, false, false, true] ![false, false, false, true]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, false, false, false] ![false, false, false, false]))
      (T.act (bitDiff4 ![true, false, false, true] ![false, false, false, true])) < 0 at h
    have hx : bitDiff4 ![true, false, false, false] ![false, false, false, false] = prefix1 := by
      ext i; fin_cases i <;> (dsimp [prefix1, bitDiff4, boolToReal]; ring)
    have hy : bitDiff4 ![true, false, false, true] ![false, false, false, true] = prefix1 := by
      ext i; fin_cases i <;> (dsimp [prefix1, bitDiff4, boolToReal]; ring)
    rw [hx, hy] at h
    exact h
  have h_p2p2 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix2) (T.act prefix2) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, true, false, false] ![false, false, false, false]
      ![true, true, false, false] ![false, false, false, false]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, true, false, false] ![false, false, false, false]))
      (T.act (bitDiff4 ![true, true, false, false] ![false, false, false, false])) < 0 at h
    have hx : bitDiff4 ![true, true, false, false] ![false, false, false, false] = prefix2 := by
      ext i; fin_cases i <;> (dsimp [prefix2, bitDiff4, boolToReal]; ring)
    rw [hx] at h
    exact h
  have h_p3p3 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix3) (T.act prefix3) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, true, true, false] ![false, false, false, false]
      ![true, true, true, false] ![false, false, false, false]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, true, true, false] ![false, false, false, false]))
      (T.act (bitDiff4 ![true, true, true, false] ![false, false, false, false])) < 0 at h
    have hx : bitDiff4 ![true, true, true, false] ![false, false, false, false] = prefix3 := by
      ext i; fin_cases i <;> (dsimp [prefix3, bitDiff4, boolToReal]; ring)
    rw [hx] at h
    exact h
  have h_p4p4 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix4) (T.act prefix4) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, true, true, true] ![false, false, false, false]
      ![true, true, true, true] ![false, false, false, false]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, true, true, true] ![false, false, false, false]))
      (T.act (bitDiff4 ![true, true, true, true] ![false, false, false, false])) < 0 at h
    have hx : bitDiff4 ![true, true, true, true] ![false, false, false, false] = prefix4 := by
      ext i; fin_cases i <;> (dsimp [prefix4, bitDiff4, boolToReal]; ring)
    rw [hx] at h
    exact h
  have h_p1p3 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix1) (T.act prefix3) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, false, true, false] ![false, false, true, false]
      ![true, true, true, false] ![false, false, false, false]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, false, true, false] ![false, false, true, false]))
      (T.act (bitDiff4 ![true, true, true, false] ![false, false, false, false])) < 0 at h
    have hx : bitDiff4 ![true, false, true, false] ![false, false, true, false] = prefix1 := by
      ext i; fin_cases i <;> (dsimp [prefix1, bitDiff4, boolToReal]; ring)
    have hy : bitDiff4 ![true, true, true, false] ![false, false, false, false] = prefix3 := by
      ext i; fin_cases i <;> (dsimp [prefix3, bitDiff4, boolToReal]; ring)
    rw [hx, hy] at h
    exact h
  have h_p2p3 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix2) (T.act prefix3) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, true, false, false] ![false, false, false, false]
      ![true, true, true, false] ![false, false, false, false]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, true, false, false] ![false, false, false, false]))
      (T.act (bitDiff4 ![true, true, true, false] ![false, false, false, false])) < 0 at h
    have hx : bitDiff4 ![true, true, false, false] ![false, false, false, false] = prefix2 := by
      ext i; fin_cases i <;> (dsimp [prefix2, bitDiff4, boolToReal]; ring)
    have hy : bitDiff4 ![true, true, true, false] ![false, false, false, false] = prefix3 := by
      ext i; fin_cases i <;> (dsimp [prefix3, bitDiff4, boolToReal]; ring)
    rw [hx, hy] at h
    exact h
  have h_p2p4 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix2) (T.act prefix4) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, true, false, true] ![false, false, false, true]
      ![true, true, true, true] ![false, false, false, false]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, true, false, true] ![false, false, false, true]))
      (T.act (bitDiff4 ![true, true, true, true] ![false, false, false, false])) < 0 at h
    have hx : bitDiff4 ![true, true, false, true] ![false, false, false, true] = prefix2 := by
      ext i; fin_cases i <;> (dsimp [prefix2, bitDiff4, boolToReal]; ring)
    have hy : bitDiff4 ![true, true, true, true] ![false, false, false, false] = prefix4 := by
      ext i; fin_cases i <;> (dsimp [prefix4, bitDiff4, boolToReal]; ring)
    rw [hx, hy] at h
    exact h
  have h_p3p4 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix3) (T.act prefix4) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, true, true, false] ![false, false, false, false]
      ![true, true, true, true] ![false, false, false, false]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, true, true, false] ![false, false, false, false]))
      (T.act (bitDiff4 ![true, true, true, true] ![false, false, false, false])) < 0 at h
    have hx : bitDiff4 ![true, true, true, false] ![false, false, false, false] = prefix3 := by
      ext i; fin_cases i <;> (dsimp [prefix3, bitDiff4, boolToReal]; ring)
    have hy : bitDiff4 ![true, true, true, true] ![false, false, false, false] = prefix4 := by
      ext i; fin_cases i <;> (dsimp [prefix4, bitDiff4, boolToReal]; ring)
    rw [hx, hy] at h
    exact h
  have h_p1p2 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix1) (T.act prefix2) < 0 := by
    intro T
    have h_aux := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, false, false, false] ![false, false, false, false]
      ![true, true, false, false] ![false, false, true, false]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, false, false, false] ![false, false, false, false]))
      (T.act (bitDiff4 ![true, true, false, false] ![false, false, true, false])) < 0 at h_aux
    have hx : bitDiff4 ![true, false, false, false] ![false, false, false, false] = prefix1 := by
      ext i; fin_cases i <;> (dsimp [prefix1, bitDiff4, boolToReal]; ring)
    have hy : bitDiff4 ![true, true, false, false] ![false, false, true, false] = (![1, 1, -1, 0] : Fin 4 → ℝ) := by
      ext i; fin_cases i <;> (dsimp [bitDiff4, boolToReal]; ring)
    rw [hx, hy] at h_aux
    have h13 := h_p1p3 T
    have h_sum :
        bilinear4 S (T.act prefix1) (T.act (![1, 1, -1, 0] : Fin 4 → ℝ)) +
          bilinear4 S (T.act prefix1) (T.act prefix3) < 0 := add_neg h_aux h13
    have h_add_bilin :=
      (bilinear4_add_right S (T.act prefix1) (T.act (![1, 1, -1, 0] : Fin 4 → ℝ))
        (T.act prefix3)).symm
    rw [h_add_bilin] at h_sum
    have h_act_add :=
      (SignedPerm4.act_add T (![1, 1, -1, 0] : Fin 4 → ℝ) prefix3).symm
    rw [h_act_add] at h_sum
    have h_id :
        (fun i => (![1, 1, -1, 0] : Fin 4 → ℝ) i + prefix3 i) =
          fun i => 2 * prefix2 i := by
      ext i; fin_cases i <;> (dsimp [prefix3, prefix2]; ring)
    rw [h_id] at h_sum
    have h_act_smul := SignedPerm4.act_smul T 2 prefix2
    rw [h_act_smul] at h_sum
    have h_smul_bilin :=
      bilinear4_smul_right S 2 (T.act prefix1) (T.act prefix2)
    rw [h_smul_bilin] at h_sum
    linarith
  have h_p1q2 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix1) (T.act q2) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, false, false, true] ![false, false, false, true]
      ![true, false, true, true] ![false, false, false, false]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, false, false, true] ![false, false, false, true]))
      (T.act (bitDiff4 ![true, false, true, true] ![false, false, false, false])) < 0 at h
    have hx : bitDiff4 ![true, false, false, true] ![false, false, false, true] = prefix1 := by
      ext i; fin_cases i <;> (dsimp [prefix1, bitDiff4, boolToReal]; ring)
    have hy : bitDiff4 ![true, false, true, true] ![false, false, false, false] = q2 := by
      ext i; fin_cases i <;> (dsimp [q2, bitDiff4, boolToReal]; ring)
    rw [hx, hy] at h
    exact h
  have h_p1q3 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix1) (T.act q3) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, false, false, true] ![false, false, false, true]
      ![true, true, false, true] ![false, false, false, false]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, false, false, true] ![false, false, false, true]))
      (T.act (bitDiff4 ![true, true, false, true] ![false, false, false, false])) < 0 at h
    have hx : bitDiff4 ![true, false, false, true] ![false, false, false, true] = prefix1 := by
      ext i; fin_cases i <;> (dsimp [prefix1, bitDiff4, boolToReal]; ring)
    have hy : bitDiff4 ![true, true, false, true] ![false, false, false, false] = q3 := by
      ext i; fin_cases i <;> (dsimp [q3, bitDiff4, boolToReal]; ring)
    rw [hx, hy] at h
    exact h
  have h_p4r2 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix4) (T.act r2) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, true, true, true] ![false, false, false, false]
      ![true, true, false, true] ![false, false, false, true]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, true, true, true] ![false, false, false, false]))
      (T.act (bitDiff4 ![true, true, false, true] ![false, false, false, true])) < 0 at h
    have hx : bitDiff4 ![true, true, true, true] ![false, false, false, false] = prefix4 := by
      ext i; fin_cases i <;> (dsimp [prefix4, bitDiff4, boolToReal]; ring)
    have hy : bitDiff4 ![true, true, false, true] ![false, false, false, true] = r2 := by
      ext i; fin_cases i <;> (dsimp [r2, bitDiff4, boolToReal]; ring)
    rw [hx, hy] at h
    exact h
  have h_p4r3 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix4) (T.act r3) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, true, true, true] ![false, false, false, false]
      ![true, false, true, true] ![false, false, false, true]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, true, true, true] ![false, false, false, false]))
      (T.act (bitDiff4 ![true, false, true, true] ![false, false, false, true])) < 0 at h
    have hx : bitDiff4 ![true, true, true, true] ![false, false, false, false] = prefix4 := by
      ext i; fin_cases i <;> (dsimp [prefix4, bitDiff4, boolToReal]; ring)
    have hy : bitDiff4 ![true, false, true, true] ![false, false, false, true] = r3 := by
      ext i; fin_cases i <;> (dsimp [r3, bitDiff4, boolToReal]; ring)
    rw [hx, hy] at h
    exact h
  have h_p4r4 : ∀ T : SignedPerm4, bilinear4 S (T.act prefix4) (T.act r4) < 0 := by
    intro T
    have h := checkerboard_symmetric_sign_neg_act P hdeg hrep
      ![true, true, true, true] ![false, false, false, false]
      ![true, false, true, true] ![false, false, true, false]
      rfl rfl rfl rfl T
    change bilinear4 S (T.act (bitDiff4 ![true, true, true, true] ![false, false, false, false]))
      (T.act (bitDiff4 ![true, false, true, true] ![false, false, true, false])) < 0 at h
    have hx : bitDiff4 ![true, true, true, true] ![false, false, false, false] = prefix4 := by
      ext i; fin_cases i <;> (dsimp [prefix4, bitDiff4, boolToReal]; ring)
    have hy : bitDiff4 ![true, false, true, true] ![false, false, true, false] = r4 := by
      ext i; fin_cases i <;> (dsimp [r4, bitDiff4, boolToReal]; ring)
    rw [hx, hy] at h
    exact h
  exact ⟨h_p1p1, h_p2p2, h_p3p3, h_p4p4, h_p1p2, h_p1p3, h_p2p3, h_p2p4,
    h_p3p4, h_p1q2, h_p1q3, h_p4r2, h_p4r3, h_p4r4⟩

private theorem symmetricPart4_isSymm (K : Matrix (Fin 4) (Fin 4) ℝ) :
    (symmetricPart4 K).IsSymm := by
  ext i j
  simp [symmetricPart4, Matrix.transpose_apply]
  ring

private lemma exists_perm_sort4 (x : Fin 4 → ℝ) :
    ∃ p : Equiv.Perm (Fin 4),
      x (p 0) ≥ x (p 1) ∧ x (p 1) ≥ x (p 2) ∧ x (p 2) ≥ x (p 3) := by
  let p := Tuple.sort (fun i => -x i)
  have hmono := Tuple.monotone_sort (fun i => -x i)
  use p
  have h01 := hmono (by decide : (0 : Fin 4) ≤ 1)
  have h12 := hmono (by decide : (1 : Fin 4) ≤ 2)
  have h23 := hmono (by decide : (2 : Fin 4) ≤ 3)
  dsimp [Function.comp] at h01 h12 h23
  exact ⟨by linarith, by linarith, by linarith⟩

private def SignedPerm4.inv (T : SignedPerm4) : SignedPerm4 where
  perm := T.perm.symm
  flip := fun i => T.flip (T.perm.symm i)

private theorem SignedPerm4.act_inv (T : SignedPerm4) (z : Fin 4 → ℝ) :
    (T.inv).act (T.act z) = z := by
  ext i
  dsimp [SignedPerm4.act, SignedPerm4.inv]
  rw [Equiv.apply_symm_apply]
  split_ifs <;> ring

private theorem exists_signedPerm_sorted (z : Fin 4 → ℝ) :
    ∃ T : SignedPerm4,
      (T.act z) 0 ≥ (T.act z) 1 ∧
      (T.act z) 1 ≥ (T.act z) 2 ∧
      (T.act z) 2 ≥ (T.act z) 3 ∧
      (T.act z) 3 ≥ 0 := by
  obtain ⟨p, hp01, hp12, hp23⟩ := exists_perm_sort4 (fun i => |z i|)
  let T : SignedPerm4 := ⟨p, fun i => decide (z (p i) < 0)⟩
  use T
  have hT (i : Fin 4) : T.act z i = |z (p i)| := by
    dsimp [T, SignedPerm4.act]
    split_ifs with h
    · rw [decide_eq_true_iff] at h
      linarith [abs_of_neg h]
    · have h' : 0 ≤ z (p i) := by
        by_contra h_neg; push Not at h_neg
        have : decide (z (p i) < 0) = true := decide_eq_true h_neg
        contradiction
      linarith [abs_of_nonneg h']
  rw [hT 0, hT 1, hT 2, hT 3]
  refine ⟨hp01, hp12, hp23, abs_nonneg _⟩

private lemma SignedPerm4.act_add_pi (T : SignedPerm4) (u v : Fin 4 → ℝ) :
    T.act (u + v) = T.act u + T.act v := by
  ext i; dsimp [SignedPerm4.act]; split_ifs <;> ring

private lemma SignedPerm4.act_smul_pi (T : SignedPerm4) (c : ℝ) (u : Fin 4 → ℝ) :
    T.act (c • u) = c • T.act u := by
  ext i; dsimp [SignedPerm4.act]; split_ifs <;> ring

private lemma prefix_expansion (w : Fin 4 → ℝ) :
    w = (w 0 - w 1) • prefix1 + (w 1 - w 2) • prefix2 + (w 2 - w 3) • prefix3 + w 3 • prefix4 := by
  ext i
  fin_cases i <;> (dsimp [prefix1, prefix2, prefix3, prefix4]; ring)

private lemma act_prefix_expansion (T' : SignedPerm4) (w : Fin 4 → ℝ) :
    T'.act w = (w 0 - w 1) • T'.act prefix1 + (w 1 - w 2) • T'.act prefix2 +
      (w 2 - w 3) • T'.act prefix3 + w 3 • T'.act prefix4 := by
  have h := prefix_expansion w
  have h' := congr_arg T'.act h
  rw [h']
  rw [SignedPerm4.act_add_pi, SignedPerm4.act_add_pi, SignedPerm4.act_add_pi]
  rw [SignedPerm4.act_smul_pi, SignedPerm4.act_smul_pi, SignedPerm4.act_smul_pi, SignedPerm4.act_smul_pi]

private lemma quadraticForm4_eq_bilinear4 (S : Matrix (Fin 4) (Fin 4) ℝ) (z : Fin 4 → ℝ) :
    quadraticForm4 S z = bilinear4 S z z := by
  unfold quadraticForm4 bilinear4
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

private lemma q_relation : q2 + q3 + prefix3 = prefix1 + (2 : ℝ) • prefix4 := by
  ext i; fin_cases i <;> (dsimp [q2, q3, prefix1, prefix3, prefix4]; ring)

private lemma r_relation : r2 + r3 + r4 = (2 : ℝ) • prefix1 + prefix4 := by
  ext i; fin_cases i <;> (dsimp [r2, r3, r4, prefix1, prefix4]; ring)

private lemma bilinear4_add_right_pi (S : Matrix (Fin 4) (Fin 4) ℝ) (u v w : Fin 4 → ℝ) :
    bilinear4 S u (v + w) = bilinear4 S u v + bilinear4 S u w := by
  unfold bilinear4; simp_rw [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma bilinear4_smul_right_pi (S : Matrix (Fin 4) (Fin 4) ℝ) (c : ℝ) (u v : Fin 4 → ℝ) :
    bilinear4 S u (c • v) = c * bilinear4 S u v := by
  unfold bilinear4
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  ring

private lemma bilinear4_expand4 (S : Matrix (Fin 4) (Fin 4) ℝ) (hsymm : S.IsSymm)
    (v1 v2 v3 v4 : Fin 4 → ℝ) (a1 a2 a3 a4 : ℝ) :
    bilinear4 S (a1 • v1 + a2 • v2 + a3 • v3 + a4 • v4) (a1 • v1 + a2 • v2 + a3 • v3 + a4 • v4) =
      a1 ^ 2 * bilinear4 S v1 v1 +
      a2 ^ 2 * bilinear4 S v2 v2 +
      a3 ^ 2 * bilinear4 S v3 v3 +
      a4 ^ 2 * bilinear4 S v4 v4 +
      2 * a1 * a2 * bilinear4 S v1 v2 +
      2 * a1 * a3 * bilinear4 S v1 v3 +
      2 * a2 * a3 * bilinear4 S v2 v3 +
      2 * a2 * a4 * bilinear4 S v2 v4 +
      2 * a3 * a4 * bilinear4 S v3 v4 +
      2 * a1 * a4 * bilinear4 S v1 v4 := by
  unfold bilinear4
  rw [Fin.sum_univ_four]
  simp_rw [Fin.sum_univ_four]
  have hS (i j : Fin 4) : S j i = S i j := (congr_fun (congr_fun hsymm j) i).symm
  simp only [hS 1 0, hS 2 0, hS 3 0, hS 2 1, hS 3 1, hS 3 2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma bilinear4_q_rel (S : Matrix (Fin 4) (Fin 4) ℝ) (T' : SignedPerm4) :
    2 * bilinear4 S (T'.act prefix1) (T'.act prefix4) =
      bilinear4 S (T'.act prefix1) (T'.act q2) +
      bilinear4 S (T'.act prefix1) (T'.act q3) +
      bilinear4 S (T'.act prefix1) (T'.act prefix3) -
      bilinear4 S (T'.act prefix1) (T'.act prefix1) := by
  have hq : bilinear4 S (T'.act prefix1) (T'.act (q2 + q3 + prefix3)) =
      bilinear4 S (T'.act prefix1) (T'.act (prefix1 + (2 : ℝ) • prefix4)) := by
    rw [q_relation]
  rw [SignedPerm4.act_add_pi, SignedPerm4.act_add_pi, SignedPerm4.act_add_pi, SignedPerm4.act_smul_pi] at hq
  rw [bilinear4_add_right_pi, bilinear4_add_right_pi, bilinear4_add_right_pi, bilinear4_smul_right_pi] at hq
  linarith

private lemma bilinear4_r_rel (S : Matrix (Fin 4) (Fin 4) ℝ) (hsymm : S.IsSymm) (T' : SignedPerm4) :
    2 * bilinear4 S (T'.act prefix1) (T'.act prefix4) =
      bilinear4 S (T'.act prefix4) (T'.act r2) +
      bilinear4 S (T'.act prefix4) (T'.act r3) +
      bilinear4 S (T'.act prefix4) (T'.act r4) -
      bilinear4 S (T'.act prefix4) (T'.act prefix4) := by
  have hr : bilinear4 S (T'.act prefix4) (T'.act (r2 + r3 + r4)) =
      bilinear4 S (T'.act prefix4) (T'.act ((2 : ℝ) • prefix1 + prefix4)) := by
    rw [r_relation]
  rw [SignedPerm4.act_add_pi, SignedPerm4.act_add_pi, SignedPerm4.act_add_pi, SignedPerm4.act_smul_pi] at hr
  rw [bilinear4_add_right_pi, bilinear4_add_right_pi, bilinear4_add_right_pi, bilinear4_smul_right_pi] at hr
  have h_symm : bilinear4 S (T'.act prefix4) (T'.act prefix1) =
      bilinear4 S (T'.act prefix1) (T'.act prefix4) := by
    unfold bilinear4; rw [Fin.sum_univ_four]; simp_rw [Fin.sum_univ_four]
    have hS (i j : Fin 4) : S j i = S i j := (congr_fun (congr_fun hsymm j) i).symm
    simp_rw [hS]; ring
  rw [h_symm] at hr
  linarith

/-- The real-algebraic half of paper Lemma 2: the finite certificate covers
every cone of vectors after sorting absolute coordinates. -/
private theorem curvatureCertificate_negative
    (S : Matrix (Fin 4) (Fin 4) ℝ) (hsymm : S.IsSymm)
    (hcert : F8CurvatureCertificate S) :
    NegativeDefinite4 S := by
  intro z hz
  rw [quadraticForm4_eq_bilinear4]
  obtain ⟨T, hz0, hz1, hz2, hz3⟩ := exists_signedPerm_sorted z
  set w := T.act z
  set T' := T.inv
  have hz_eq : z = T'.act w := (SignedPerm4.act_inv T z).symm
  rw [hz_eq]
  set a1 := w 0 - w 1
  set a2 := w 1 - w 2
  set a3 := w 2 - w 3
  set a4 := w 3
  have ha1 : 0 ≤ a1 := by linarith
  have ha2 : 0 ≤ a2 := by linarith
  have ha3 : 0 ≤ a3 := by linarith
  have ha4 : 0 ≤ a4 := by linarith
  have hw_act : T'.act w = a1 • T'.act prefix1 + a2 • T'.act prefix2 +
      a3 • T'.act prefix3 + a4 • T'.act prefix4 := act_prefix_expansion T' w
  rw [hw_act]
  set B11 := bilinear4 S (T'.act prefix1) (T'.act prefix1)
  set B22 := bilinear4 S (T'.act prefix2) (T'.act prefix2)
  set B33 := bilinear4 S (T'.act prefix3) (T'.act prefix3)
  set B44 := bilinear4 S (T'.act prefix4) (T'.act prefix4)
  set B12 := bilinear4 S (T'.act prefix1) (T'.act prefix2)
  set B13 := bilinear4 S (T'.act prefix1) (T'.act prefix3)
  set B23 := bilinear4 S (T'.act prefix2) (T'.act prefix3)
  set B24 := bilinear4 S (T'.act prefix2) (T'.act prefix4)
  set B34 := bilinear4 S (T'.act prefix3) (T'.act prefix4)
  set B14 := bilinear4 S (T'.act prefix1) (T'.act prefix4)
  set B1q2 := bilinear4 S (T'.act prefix1) (T'.act q2)
  set B1q3 := bilinear4 S (T'.act prefix1) (T'.act q3)
  set B4r2 := bilinear4 S (T'.act prefix4) (T'.act r2)
  set B4r3 := bilinear4 S (T'.act prefix4) (T'.act r3)
  set B4r4 := bilinear4 S (T'.act prefix4) (T'.act r4)
  have hexp : bilinear4 S (a1 • T'.act prefix1 + a2 • T'.act prefix2 +
      a3 • T'.act prefix3 + a4 • T'.act prefix4) (a1 • T'.act prefix1 + a2 • T'.act prefix2 +
      a3 • T'.act prefix3 + a4 • T'.act prefix4) =
      a1 ^ 2 * B11 + a2 ^ 2 * B22 + a3 ^ 2 * B33 + a4 ^ 2 * B44 +
      2 * a1 * a2 * B12 + 2 * a1 * a3 * B13 + 2 * a2 * a3 * B23 +
      2 * a2 * a4 * B24 + 2 * a3 * a4 * B34 + 2 * a1 * a4 * B14 :=
    bilinear4_expand4 S hsymm (T'.act prefix1) (T'.act prefix2) (T'.act prefix3) (T'.act prefix4) a1 a2 a3 a4
  have hp1p1 : B11 < 0 := hcert.p1p1 T'
  have hp2p2 : B22 < 0 := hcert.p2p2 T'
  have hp3p3 : B33 < 0 := hcert.p3p3 T'
  have hp4p4 : B44 < 0 := hcert.p4p4 T'
  have hp1p2 : B12 < 0 := hcert.p1p2 T'
  have hp1p3 : B13 < 0 := hcert.p1p3 T'
  have hp2p3 : B23 < 0 := hcert.p2p3 T'
  have hp2p4 : B24 < 0 := hcert.p2p4 T'
  have hp3p4 : B34 < 0 := hcert.p3p4 T'
  have hp1q2 : B1q2 < 0 := hcert.p1q2 T'
  have hp1q3 : B1q3 < 0 := hcert.p1q3 T'
  have hp4r2 : B4r2 < 0 := hcert.p4r2 T'
  have hp4r3 : B4r3 < 0 := hcert.p4r3 T'
  have hp4r4 : B4r4 < 0 := hcert.p4r4 T'
  have hw_ne : w ≠ 0 := by
    intro hw0
    have : z = 0 := by
      rw [hz_eq, hw0]
      ext i
      dsimp [SignedPerm4.act]
      split_ifs <;> ring
    exact hz this
  have hw0_pos : 0 < w 0 := by
    by_contra h; push Not at h
    have : w = 0 := by
      ext i
      fin_cases i
      · change w 0 = 0; linarith
      · change w 1 = 0; linarith
      · change w 2 = 0; linarith
      · change w 3 = 0; linarith
    exact hw_ne this
  have h14_prod : 0 ≤ a1 * a4 := mul_nonneg ha1 ha4
  have hprod_nonpos (x y : ℝ) (hx : 0 ≤ x) (hy : y < 0) :
      x * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hx hy.le
  have hprod_neg (x y : ℝ) (hx : 0 < x) (hy : y < 0) :
      x * y < 0 :=
    mul_neg_of_pos_of_neg hx hy
  rcases le_total a4 a1 with h14 | h41
  · have hq_rel : 2 * B14 = B1q2 + B1q3 + B13 - B11 := bilinear4_q_rel S T'
    have h_step2 : a1 ^ 2 * B11 + a2 ^ 2 * B22 + a3 ^ 2 * B33 + a4 ^ 2 * B44 +
        2 * a1 * a2 * B12 + 2 * a1 * a3 * B13 + 2 * a2 * a3 * B23 +
        2 * a2 * a4 * B24 + 2 * a3 * a4 * B34 + 2 * a1 * a4 * B14 =
        a1 * (a1 - a4) * B11 + a2 ^ 2 * B22 + a3 ^ 2 * B33 + a4 ^ 2 * B44 +
        2 * a1 * a2 * B12 + (2 * a1 * a3 + a1 * a4) * B13 + 2 * a2 * a3 * B23 +
        2 * a2 * a4 * B24 + 2 * a3 * a4 * B34 + a1 * a4 * B1q2 + a1 * a4 * B1q3 := by
      linear_combination a1 * a4 * hq_rel
    rw [hexp, h_step2]
    have t1 : a1 * (a1 - a4) * B11 ≤ 0 :=
      hprod_nonpos _ _ (mul_nonneg ha1 (sub_nonneg.mpr h14)) hp1p1
    have t3 : a3 ^ 2 * B33 ≤ 0 :=
      hprod_nonpos _ _ (sq_nonneg a3) hp3p3
    have t4 : a4 ^ 2 * B44 ≤ 0 :=
      hprod_nonpos _ _ (sq_nonneg a4) hp4p4
    have t6 : (2 * a1 * a3 + a1 * a4) * B13 ≤ 0 := by
      apply hprod_nonpos _ _ ?_ hp1p3
      exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha1) ha3) h14_prod
    have t7 : 2 * a2 * a3 * B23 ≤ 0 :=
      hprod_nonpos _ _ (mul_nonneg (mul_nonneg (by norm_num) ha2) ha3) hp2p3
    have t8 : 2 * a2 * a4 * B24 ≤ 0 :=
      hprod_nonpos _ _ (mul_nonneg (mul_nonneg (by norm_num) ha2) ha4) hp2p4
    have t9 : 2 * a3 * a4 * B34 ≤ 0 :=
      hprod_nonpos _ _ (mul_nonneg (mul_nonneg (by norm_num) ha3) ha4) hp3p4
    have t10 : a1 * a4 * B1q2 ≤ 0 :=
      hprod_nonpos _ _ h14_prod hp1q2
    have t11 : a1 * a4 * B1q3 ≤ 0 :=
      hprod_nonpos _ _ h14_prod hp1q3
    rcases lt_or_eq_of_le ha2 with ha2_lt | ha2_eq
    · have t2 : a2 ^ 2 * B22 < 0 :=
        hprod_neg _ _ (sq_pos_of_ne_zero (ne_of_gt ha2_lt)) hp2p2
      have t5 : 2 * a1 * a2 * B12 ≤ 0 :=
        hprod_nonpos _ _ (mul_nonneg (mul_nonneg (by norm_num) ha1) ha2) hp1p2
      linarith
    · have h20 : a2 = 0 := ha2_eq.symm
      rw [h20]
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero]
      rcases lt_or_eq_of_le ha3 with ha3_lt | ha3_eq
      · have t3_strict : a3 ^ 2 * B33 < 0 :=
          hprod_neg _ _ (sq_pos_of_ne_zero (ne_of_gt ha3_lt)) hp3p3
        linarith
      · have h30 : a3 = 0 := ha3_eq.symm
        rw [h30]
        simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, zero_add]
        rcases lt_or_eq_of_le ha4 with ha4_lt | ha4_eq
        · have t4_strict : a4 ^ 2 * B44 < 0 :=
            hprod_neg _ _ (sq_pos_of_ne_zero (ne_of_gt ha4_lt)) hp4p4
          have t6' : a1 * a4 * B13 ≤ 0 :=
            hprod_nonpos _ _ h14_prod hp1p3
          linarith
        · have h40 : a4 = 0 := ha4_eq.symm
          rw [h40]
          simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, sub_zero]
          have ha1_pos : 0 < a1 := by linarith [hw0_pos]
          have t1_strict : a1 ^ 2 * B11 < 0 :=
            hprod_neg _ _ (sq_pos_of_ne_zero (ne_of_gt ha1_pos)) hp1p1
          linarith
  · have hr_rel : 2 * B14 = B4r2 + B4r3 + B4r4 - B44 := bilinear4_r_rel S hsymm T'
    have h_step2 : a1 ^ 2 * B11 + a2 ^ 2 * B22 + a3 ^ 2 * B33 + a4 ^ 2 * B44 +
        2 * a1 * a2 * B12 + 2 * a1 * a3 * B13 + 2 * a2 * a3 * B23 +
        2 * a2 * a4 * B24 + 2 * a3 * a4 * B34 + 2 * a1 * a4 * B14 =
        a1 ^ 2 * B11 + a2 ^ 2 * B22 + a3 ^ 2 * B33 + a4 * (a4 - a1) * B44 +
        2 * a1 * a2 * B12 + 2 * a1 * a3 * B13 + 2 * a2 * a3 * B23 +
        2 * a2 * a4 * B24 + 2 * a3 * a4 * B34 + a1 * a4 * B4r2 +
        a1 * a4 * B4r3 + a1 * a4 * B4r4 := by
      linear_combination a1 * a4 * hr_rel
    rw [hexp, h_step2]
    have t1 : a1 ^ 2 * B11 ≤ 0 :=
      hprod_nonpos _ _ (sq_nonneg a1) hp1p1
    have t3 : a3 ^ 2 * B33 ≤ 0 :=
      hprod_nonpos _ _ (sq_nonneg a3) hp3p3
    have t4 : a4 * (a4 - a1) * B44 ≤ 0 :=
      hprod_nonpos _ _ (mul_nonneg ha4 (sub_nonneg.mpr h41)) hp4p4
    have t5 : 2 * a1 * a2 * B12 ≤ 0 :=
      hprod_nonpos _ _ (mul_nonneg (mul_nonneg (by norm_num) ha1) ha2) hp1p2
    have t6 : 2 * a1 * a3 * B13 ≤ 0 :=
      hprod_nonpos _ _ (mul_nonneg (mul_nonneg (by norm_num) ha1) ha3) hp1p3
    have t7 : 2 * a2 * a3 * B23 ≤ 0 :=
      hprod_nonpos _ _ (mul_nonneg (mul_nonneg (by norm_num) ha2) ha3) hp2p3
    have t8 : 2 * a2 * a4 * B24 ≤ 0 :=
      hprod_nonpos _ _ (mul_nonneg (mul_nonneg (by norm_num) ha2) ha4) hp2p4
    have t9 : 2 * a3 * a4 * B34 ≤ 0 :=
      hprod_nonpos _ _ (mul_nonneg (mul_nonneg (by norm_num) ha3) ha4) hp3p4
    have t10 : a1 * a4 * B4r2 ≤ 0 :=
      hprod_nonpos _ _ h14_prod hp4r2
    have t11 : a1 * a4 * B4r3 ≤ 0 :=
      hprod_nonpos _ _ h14_prod hp4r3
    have t12 : a1 * a4 * B4r4 ≤ 0 :=
      hprod_nonpos _ _ h14_prod hp4r4
    rcases lt_or_eq_of_le ha2 with ha2_lt | ha2_eq
    · have t2_strict : a2 ^ 2 * B22 < 0 :=
        hprod_neg _ _ (sq_pos_of_ne_zero (ne_of_gt ha2_lt)) hp2p2
      linarith
    · have h20 : a2 = 0 := ha2_eq.symm
      rw [h20]
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero]
      rcases lt_or_eq_of_le ha3 with ha3_lt | ha3_eq
      · have t3_strict : a3 ^ 2 * B33 < 0 :=
          hprod_neg _ _ (sq_pos_of_ne_zero (ne_of_gt ha3_lt)) hp3p3
        linarith
      · have h30 : a3 = 0 := ha3_eq.symm
        rw [h30]
        simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero]
        rcases lt_or_eq_of_le ha1 with ha1_lt | ha1_eq
        · have t1_strict : a1 ^ 2 * B11 < 0 :=
            hprod_neg _ _ (sq_pos_of_ne_zero (ne_of_gt ha1_lt)) hp1p1
          linarith
        · have h10 : a1 = 0 := ha1_eq.symm
          rw [h10]
          simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero, zero_add, sub_zero]
          have ha4_pos : 0 < a4 := by linarith [hw0_pos]
          have t4_strict : a4 ^ 2 * B44 < 0 :=
            hprod_neg _ _ (sq_pos_of_ne_zero (ne_of_gt ha4_pos)) hp4p4
          linarith

/-- Paper Lemma 2: every quadratic sign representation of `f8` has strictly
negative symmetric mixed curvature. -/
theorem f8_quadratic_mixed_negative
    (P : MvPolynomial (Fin 8) ℝ)
    (hdeg : P.totalDegree ≤ 2)
    (hrep : SignRepresents P f8) :
    NegativeDefinite4 (symmetricPart4 (mixedMatrix4 P)) := by
  exact curvatureCertificate_negative _
    (symmetricPart4_isSymm (mixedMatrix4 P))
    (f8_has_curvatureCertificate P hdeg hrep)

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

/-- The spectral hypothesis used in the paper: a positive diagonal left
multiplier symmetrizes `M`, and the resulting symmetric form has positive
index at least two. Encoding the index on the symmetrized matrix avoids any
choice of a nonsymmetric eigenvalue API. -/
def DiagonallySymmetrizableWithPositiveIndexTwo4
    (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃ d : Fin 4 → ℝ, (∀ i, 0 < d i) ∧
    ((Matrix.diagonal d) * M).IsSymm ∧
    PositiveIndexAtLeastTwo4 ((Matrix.diagonal d) * M)

private def offDiagSet (j : Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => i ≠ j)

private lemma offDiagSet_nonempty (j : Fin 4) : (offDiagSet j).Nonempty := by
  change (Finset.univ.filter (fun i => i ≠ j)).Nonempty
  fin_cases j
  · use 1; simp
  · use 0; simp
  · use 0; simp
  · use 0; simp

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
  simp [factorD, factorNormalizedW]
  rw [splitPair_formula]
  simp only [column4]
  ring

private theorem factorNormalized_sub_eq
    (D : F8FactorData) (i j : Fin 4) :
    2 * splitPair (factorD D.Q j) (factorB D.P D.Q i) =
      factorNormalizedU D j i - factorNormalizedV D j i := by
  rw [splitPair_formula]
  simp [factorD, factorB, factorNormalizedU, factorNormalizedV]
  rw [splitPair_formula, splitPair_formula]
  simp only [column4]
  ring

private theorem factorNormalized_add_eq
    (D : F8FactorData) (k j : Fin 4) :
    2 * splitPair (factorD D.Q j) (factorA D.P D.Q k) =
      factorNormalizedU D j k + factorNormalizedV D j k := by
  rw [splitPair_formula]
  simp [factorD, factorA, factorNormalizedU, factorNormalizedV]
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

private lemma sum_fin4 (f : Fin 4 → ℝ) :
    ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_four]

private lemma diag_mul_apply (d : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    ((Matrix.diagonal d) * M) i j = d i * M i j := by
  rw [Matrix.mul_apply, sum_fin4]
  fin_cases i <;> fin_cases j <;> simp

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

private lemma quadraticForm4_sub_rankOne (C : Matrix (Fin 4) (Fin 4) ℝ) (g z : Fin 4 → ℝ) (sigma : ℝ) :
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
    have hpos_term : 0 < (1 / sigma) * ((∑ i, q i * g i ^ 2) + 2 * ∑ j, q (pick j) * g (pick j) * g j) := by
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

private noncomputable def factorRowForm (φ : Fin 2 → FracAtom 8) (c : ℝ) (row : Fin 4) : AffineForm 8 :=
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

private noncomputable def factorP (φ : Fin 2 → FracAtom 8) (c : ℝ) (s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun row i => s * (factorRowForm φ c row).linear (Fin.castAdd 4 i) / 2

private noncomputable def factorQ (φ : Fin 2 → FracAtom 8) (c : ℝ) (s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
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
  have h1 : (∑ x_1 : Fin 4, L.linear (Fin.castAdd 4 x_1) * ((s * hammingSign (x (Fin.castAdd 4 x_1)) + 1) / 2)) =
      (∑ x_1 : Fin 4, L.linear (Fin.castAdd 4 x_1) / 2) +
      ∑ x_1 : Fin 4, (s * L.linear (Fin.castAdd 4 x_1) / 2) * hammingSign (x (Fin.castAdd 4 x_1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have h2 : (∑ x_1 : Fin 4, L.linear (Fin.natAdd 4 x_1) * ((s * hammingSign (x (Fin.natAdd 4 x_1)) + 1) / 2)) =
      (∑ x_1 : Fin 4, L.linear (Fin.natAdd 4 x_1) / 2) +
      ∑ x_1 : Fin 4, (s * L.linear (Fin.natAdd 4 x_1) / 2) * hammingSign (x (Fin.natAdd 4 x_1)) := by
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
  have h_sum : (∑ k : Fin 8, L.linear k * bitReal (blockJoin (fun k => k = i ∧ bi) (fun k => k = j ∧ bj) k)) =
      (∑ x : Fin 4, L.linear (Fin.castAdd 4 x) * bitReal (blockJoin (fun k => k = i ∧ bi) (fun k => k = j ∧ bj) (Fin.castAdd 4 x))) +
      (∑ x : Fin 4, L.linear (Fin.natAdd 4 x) * bitReal (blockJoin (fun k => k = i ∧ bi) (fun k => k = j ∧ bj) (Fin.natAdd 4 x))) :=
    Fin.sum_univ_add (fun (k : Fin (4 + 4)) => L.linear k * bitReal (blockJoin (fun k => k = i ∧ bi) (fun k => k = j ∧ bj) k))
  rw [h_sum]
  have hL : (∑ x : Fin 4, L.linear (Fin.castAdd 4 x) * bitReal (blockJoin (fun k => k = i ∧ bi) (fun k => k = j ∧ bj) (Fin.castAdd 4 x))) =
      L.linear (Fin.castAdd 4 i) * (if bi then 1 else 0) := by
    simp_rw [blockJoin_castAdd]
    rw [Finset.sum_eq_single i]
    · cases bi <;> simp [bitReal]
    · intro k _ hk
      have h_ne : ¬(k = i) := hk
      cases bi <;> simp [bitReal, h_ne]
    · intro h; exact False.elim (h (Finset.mem_univ i))
  have hR : (∑ x : Fin 4, L.linear (Fin.natAdd 4 x) * bitReal (blockJoin (fun k => k = i ∧ bi) (fun k => k = j ∧ bj) (Fin.natAdd 4 x))) =
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
      (fracNumerator (φ 1)).linear (Fin.castAdd 4 i) * (fracDenominator (φ 0)).linear (Fin.natAdd 4 j) +
      (fracDenominator (φ 0)).linear (Fin.castAdd 4 i) * (fracNumerator (φ 1)).linear (Fin.natAdd 4 j) := by
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
      have h_zero : (∑ j_1 : Fin 4, (boolToReal (x0 k) - boolToReal (x1 k)) * mixedMatrix4 P_poly k j_1 * (boolToReal (y0 j_1) - boolToReal (y1 j_1))) = 0 := by
        refine Finset.sum_eq_zero (fun k' _ => ?_)
        simp [x0, y0, x1, y1, boolToReal, h_ne]
      exact h_zero
    · intro h; exact False.elim (h (Finset.mem_univ i))
  rw [← hdiff]
  rw [← quadratic_checkerboard_difference P_poly hdeg x0 x1 y0 y1]
  have h_eval (u v : Fin 4 → Bool) :
      eval (cubePoint (blockJoin u v)) P_poly =
        (factorFormA φ c).eval (blockJoin u v) * (fracDenominator (φ 1)).eval (blockJoin u v) +
        (fracNumerator (φ 1)).eval (blockJoin u v) * (fracDenominator (φ 0)).eval (blockJoin u v) := by
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
    have hd0 : 0 < (fracDenominator (φ 0)).eval (blockJoin u v) := fracDenominator_strictLegal (φ 0) _
    have hd1 : 0 < (fracDenominator (φ 1)).eval (blockJoin u v) := fracDenominator_strictLegal (φ 1) _
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
  have h_x0y0_A : (factorFormA φ c).eval (blockJoin x0 y0) = (factorFormA φ c).constant + (factorFormA φ c).linear (Fin.castAdd 4 i) + (factorFormA φ c).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (factorFormA φ c) i j true true; simpa using h
  have h_x0y0_D : (fracDenominator (φ 1)).eval (blockJoin x0 y0) = (fracDenominator (φ 1)).constant + (fracDenominator (φ 1)).linear (Fin.castAdd 4 i) + (fracDenominator (φ 1)).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracDenominator (φ 1)) i j true true; simpa using h
  have h_x0y0_C : (fracNumerator (φ 1)).eval (blockJoin x0 y0) = (fracNumerator (φ 1)).constant + (fracNumerator (φ 1)).linear (Fin.castAdd 4 i) + (fracNumerator (φ 1)).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracNumerator (φ 1)) i j true true; simpa using h
  have h_x0y0_B : (fracDenominator (φ 0)).eval (blockJoin x0 y0) = (fracDenominator (φ 0)).constant + (fracDenominator (φ 0)).linear (Fin.castAdd 4 i) + (fracDenominator (φ 0)).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracDenominator (φ 0)) i j true true; simpa using h

  have h_x0y1_A : (factorFormA φ c).eval (blockJoin x0 y1) = (factorFormA φ c).constant + (factorFormA φ c).linear (Fin.castAdd 4 i) := by
    have h := eval_blockJoin_single (factorFormA φ c) i j true false; simpa using h
  have h_x0y1_D : (fracDenominator (φ 1)).eval (blockJoin x0 y1) = (fracDenominator (φ 1)).constant + (fracDenominator (φ 1)).linear (Fin.castAdd 4 i) := by
    have h := eval_blockJoin_single (fracDenominator (φ 1)) i j true false; simpa using h
  have h_x0y1_C : (fracNumerator (φ 1)).eval (blockJoin x0 y1) = (fracNumerator (φ 1)).constant + (fracNumerator (φ 1)).linear (Fin.castAdd 4 i) := by
    have h := eval_blockJoin_single (fracNumerator (φ 1)) i j true false; simpa using h
  have h_x0y1_B : (fracDenominator (φ 0)).eval (blockJoin x0 y1) = (fracDenominator (φ 0)).constant + (fracDenominator (φ 0)).linear (Fin.castAdd 4 i) := by
    have h := eval_blockJoin_single (fracDenominator (φ 0)) i j true false; simpa using h

  have h_x1y0_A : (factorFormA φ c).eval (blockJoin x1 y0) = (factorFormA φ c).constant + (factorFormA φ c).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (factorFormA φ c) i j false true; simpa using h
  have h_x1y0_D : (fracDenominator (φ 1)).eval (blockJoin x1 y0) = (fracDenominator (φ 1)).constant + (fracDenominator (φ 1)).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracDenominator (φ 1)) i j false true; simpa using h
  have h_x1y0_C : (fracNumerator (φ 1)).eval (blockJoin x1 y0) = (fracNumerator (φ 1)).constant + (fracNumerator (φ 1)).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracNumerator (φ 1)) i j false true; simpa using h
  have h_x1y0_B : (fracDenominator (φ 0)).eval (blockJoin x1 y0) = (fracDenominator (φ 0)).constant + (fracDenominator (φ 0)).linear (Fin.natAdd 4 j) := by
    have h := eval_blockJoin_single (fracDenominator (φ 0)) i j false true; simpa using h

  have h_x1y1_A : (factorFormA φ c).eval (blockJoin x1 y1) = (factorFormA φ c).constant := by
    have h := eval_blockJoin_single (factorFormA φ c) i j false false; simpa using h
  have h_x1y1_D : (fracDenominator (φ 1)).eval (blockJoin x1 y1) = (fracDenominator (φ 1)).constant := by
    have h := eval_blockJoin_single (fracDenominator (φ 1)) i j false false; simpa using h
  have h_x1y1_C : (fracNumerator (φ 1)).eval (blockJoin x1 y1) = (fracNumerator (φ 1)).constant := by
    have h := eval_blockJoin_single (fracNumerator (φ 1)) i j false false; simpa using h
  have h_x1y1_B : (fracDenominator (φ 0)).eval (blockJoin x1 y1) = (fracDenominator (φ 0)).constant := by
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
     (fracNumerator (φ 1)).linear (Fin.castAdd 4 i) * (fracDenominator (φ 0)).linear (Fin.natAdd 4 j) +
     (fracDenominator (φ 0)).linear (Fin.castAdd 4 i) * (fracNumerator (φ 1)).linear (Fin.natAdd 4 j) +
     (factorFormA φ c).linear (Fin.castAdd 4 j) * (fracDenominator (φ 1)).linear (Fin.natAdd 4 i) +
     (fracDenominator (φ 1)).linear (Fin.castAdd 4 j) * (factorFormA φ c).linear (Fin.natAdd 4 i) +
     (fracNumerator (φ 1)).linear (Fin.castAdd 4 j) * (fracDenominator (φ 0)).linear (Fin.natAdd 4 i) +
     (fracDenominator (φ 0)).linear (Fin.castAdd 4 j) * (fracNumerator (φ 1)).linear (Fin.natAdd 4 i))

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
  have hset : (Finset.univ.filter (fun x : Fin 4 => ε x ≠ if x = i ∨ x = j then !ε x else ε x)) = {i, j} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
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
    simp [h_hs_not] at hdiff ⊢
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
      (fracNumerator (φ 1)).eval (xOriented s x) * (fracDenominator (φ 0)).eval (xOriented s x) := by
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
    have hd0 : 0 < (fracDenominator (φ 0)).eval (xOriented s x) := fracDenominator_strictLegal (φ 0) _
    have hd1 : 0 < (fracDenominator (φ 1)).eval (xOriented s x) := fracDenominator_strictLegal (φ 1) _
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
      have h_int := strictLegal_sign_intercept (fracDenominator (φ 0)) (fracDenominator_strictLegal (φ 0)) s hs
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
      have hdiff : 0 < eval (cubePoint z2) (clearedTwoAtomPoly φ c) - eval (cubePoint z1) (clearedTwoAtomPoly φ c) :=
        sub_pos.mpr (lt_of_le_of_lt hsc1 hsc2)
      rw [clearedTwoAtomPoly_eval_eq_splitPair φ c s hs x1, clearedTwoAtomPoly_eval_eq_splitPair φ c s hs x2] at hdiff
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
    simp_all [offDiagSet, Finset.sum_filter, Fin.sum_univ_four]
  all_goals rcases hsign with hs | hs
  all_goals simp [hs] at *
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
    have h1 : s i * (sys.μ i * (sys.V.mulVec sys.μ) i) = (s i * sys.μ i) * (sys.V.mulVec sys.μ) i := by ring
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
        (s j * r j) * sys.V j j * (s j * r j) + (s j * ((s j * r j) * (sys.V.mulVec sys.μ) j) - (s j * r j) * (sys.V.mulVec sys.μ) j)
          = (s j ^ 2 * r j) * r j * sys.V j j + (s j ^ 2 * r j - s j * r j) * (sys.V.mulVec sys.μ) j := by ring
        _ = (1 * r j) * r j * sys.V j j + (1 * r j - s j * r j) * (sys.V.mulVec sys.μ) j := by rw [hsq]
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

  have h_s_a (j : Fin 4) : s j * (sys.U.transpose.mulVec sys.μ) j ≤ (sys.U.transpose.mulVec sys.μ) j := by
    have ha_pos := sys.leftSlope_pos j
    rcases hs_or j with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, neg_one_mul]
      linarith

  have h_sum_s_a : ∑ j, s j * (sys.U.transpose.mulVec sys.μ) j ≤ ∑ j, (sys.U.transpose.mulVec sys.μ) j := by
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
    simp [offDiagSet, Finset.sum_filter, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
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
    Filter.Tendsto α (nhds 0) (nhds 0) ∧ ∀ᶠ t in nhds 0, quadraticForm4 sys.V (sys.μ + t • h + (α t) • Pi.single k 1) = 0 := by
  intro A B C Δ α
  have hB0 : B 0 = 2 * (sys.V.mulVec sys.μ) k := by dsimp [B]; ring
  have hB0_pos : 0 < B 0 := by rw [hB0]; linarith
  have hC0 : C 0 = 0 := by dsimp [C]; ring
  have hcontB : Continuous B := by
    dsimp [B]
    exact continuous_const.add ((continuous_const.mul continuous_id).mul continuous_const)
  have hcontC : Continuous C := by
    dsimp [C]
    exact ((continuous_const.mul continuous_id).mul continuous_const).add ((continuous_id.pow 2).mul continuous_const)
  have hcontΔ : Continuous Δ := by
    dsimp [Δ]
    exact (hcontB.pow 2).sub (continuous_const.mul hcontC)
  have hΔ0 : Δ 0 = (B 0) ^ 2 := by
    dsimp [Δ]
    rw [hC0, mul_zero, sub_zero]
  have hΔ0_pos : 0 < Δ 0 := by rw [hΔ0]; positivity
  have hB_evt : ∀ᶠ t in nhds 0, 0 < B t := hcontB.tendsto 0 (Ioi_mem_nhds hB0_pos)
  have hΔ_evt : ∀ᶠ t in nhds 0, 0 ≤ Δ t := hcontΔ.tendsto 0 (mem_nhds_iff.mpr ⟨Set.Ioi 0, Set.Ioi_subset_Ici_self, isOpen_Ioi, hΔ0_pos⟩)
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
      have hdiv2 : Filter.Tendsto (fun t => (- B t + Real.sqrt (Δ t)) * (1 / (2 * A))) (nhds 0) (nhds (0 * (1 / (2 * A)))) :=
        Filter.Tendsto.mul_const (1 / (2 * A)) hnum
      rw [zero_mul] at hdiv2
      have h_eq : (fun t => (- B t + Real.sqrt (Δ t)) / (2 * A)) = (fun t => (- B t + Real.sqrt (Δ t)) * (1 / (2 * A))) := by
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
    set C : ℝ → ℝ := fun t => 2 * t * dotProduct (sys.V.mulVec sys.μ) h + t ^ 2 * quadraticForm4 sys.V h
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
        have h2_sub := Filter.Tendsto.smul hα_lim (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => Pi.single k (1:ℝ)) (nhds 0) (nhds (Pi.single k 1)))
        change Filter.Tendsto (fun t => (α t) • Pi.single k 1) (nhds 0) (nhds ((0:ℝ) • Pi.single k 1)) at h2_sub
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
        (∑ i, (sys.U.transpose.mulVec (ν t)) i) + (∑ i, (sys.V.mulVec (ν t)) i) < dotProduct (ν t) sys.w := by
      have h_cont : Continuous (fun v : Fin 4 → ℝ =>
          (∑ i, (sys.U.transpose.mulVec v) i) + (∑ i, (sys.V.mulVec v) i) - dotProduct v sys.w) := by
        dsimp [Matrix.mulVec, dotProduct]
        have c1 : Continuous (fun v : Fin 4 → ℝ => ∑ i : Fin 4, ∑ j : Fin 4, sys.U.transpose i j * v j) :=
          continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j)))
        have c2 : Continuous (fun v : Fin 4 → ℝ => ∑ i : Fin 4, ∑ j : Fin 4, sys.V i j * v j) :=
          continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j)))
        have c3 : Continuous (fun v : Fin 4 → ℝ => ∑ i : Fin 4, v i * sys.w i) :=
          continuous_finsetSum _ (fun i _ => (continuous_apply i).mul continuous_const)
        exact (c1.add c2).sub c3
      have h_init : (∑ i, (sys.U.transpose.mulVec sys.μ) i) + (∑ i, (sys.V.mulVec sys.μ) i) - dotProduct sys.μ sys.w < 0 :=
        sub_neg.mpr sys.intercept
      have h_evt := h_cont.tendsto sys.μ |>.comp hν_lim (Iio_mem_nhds h_init)
      filter_upwards [h_evt] with t ht
      change (∑ i, (sys.U.transpose.mulVec (ν t)) i) + (∑ i, (sys.V.mulVec (ν t)) i) - dotProduct (ν t) sys.w < 0 at ht
      linarith
    have h_ne_k_evt : ∀ᶠ t in nhds 0, (ν t) k ≠ 0 := by
      have h_cont : Continuous (fun v : Fin 4 → ℝ => v k) := continuous_apply k
      exact h_cont.tendsto sys.μ |>.comp hν_lim (isOpen_ne.mem_nhds hk)
    have h_pos_freq : ∃ᶠ t in nhds (0 : ℝ), 0 < t := frequently_gt_nhds 0
    have h_all_evt : ∀ᶠ t in nhds (0 : ℝ),
        quadraticForm4 sys.V (ν t) = 0 ∧
        (∀ i, 0 < (sys.U.transpose.mulVec (ν t)) i) ∧
        (∀ i, 0 < (sys.V.mulVec (ν t)) i) ∧
        ((∑ i, (sys.U.transpose.mulVec (ν t)) i) + (∑ i, (sys.V.mulVec (ν t)) i) < dotProduct (ν t) sys.w) ∧
        (ν t) k ≠ 0 :=
      hα_null.and (h_left_evt.and (h_right_evt.and (h_intercept_evt.and h_ne_k_evt)))
    have h_freq_all : ∃ t : ℝ, 0 < t ∧
        quadraticForm4 sys.V (ν t) = 0 ∧
        (∀ i, 0 < (sys.U.transpose.mulVec (ν t)) i) ∧
        (∀ i, 0 < (sys.V.mulVec (ν t)) i) ∧
        ((∑ i, (sys.U.transpose.mulVec (ν t)) i) + (∑ i, (sys.V.mulVec (ν t)) i) < dotProduct (ν t) sys.w) ∧
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

/-- Build an eight-variable affine form from integer certificate data. -/
def integerAffine8 (constant : ℤ) (linear : Fin 8 → ℤ) :
    AffineForm 8 where
  constant := constant
  linear i := linear i

def f8D1 : AffineForm 8 :=
  integerAffine8 34 ![-1, -6, -1, -8, -1, -1, -1, -1]

def f8D2 : AffineForm 8 :=
  integerAffine8 31 ![-4, -1, -3, -7, -5, -6, -3, -1]

def f8D3 : AffineForm 8 :=
  integerAffine8 32 ![-1, -1, -6, -1, -1, -6, -6, -4]

def f8A1 : AffineForm 8 :=
  integerAffine8 (-476)
    ![1794, 2403, 2934, 132, 1890, -4130, 2868, -661]

def f8A2 : AffineForm 8 :=
  integerAffine8 622
    ![-2333, -1471, 188, 3074, -2633, 2202, 208, -1392]

def f8A3 : AffineForm 8 :=
  integerAffine8 (-1006)
    ![1501, -577, -1950, -4044, 1799, 1406, -1914, 2472]

/-- Denominator-cleared value of the published three-head score with bias one. -/
noncomputable def f8ClearedScore (z : Fin 8 → Bool) : ℝ :=
  f8D1.eval z * f8D2.eval z * f8D3.eval z +
  f8A1.eval z * f8D2.eval z * f8D3.eval z +
  f8A2.eval z * f8D1.eval z * f8D3.eval z +
  f8A3.eval z * f8D1.eval z * f8D2.eval z

def boolSign (b : Bool) : ℝ := if b then 1 else -1

private theorem StrictLegal_of_neg_slopes (L : AffineForm 8)
    (h_lin : ∀ i, L.linear i ≤ 0)
    (h_sum : 0 < L.constant + ∑ i, L.linear i) :
    L.StrictLegal := by
  intro x
  have h : ∑ i, L.linear i ≤ ∑ i, L.linear i * bitReal (x i) := by
    apply Finset.sum_le_sum
    intro i _
    have h1 : bitReal (x i) ≤ 1 := by cases x i <;> norm_num [bitReal]
    have h2 : L.linear i ≤ 0 := h_lin i
    nlinarith
  dsimp [AffineForm.eval]
  linarith

private theorem f8D1_strictLegal : f8D1.StrictLegal := by
  apply StrictLegal_of_neg_slopes
  · intro i; fin_cases i <;> norm_num [f8D1, integerAffine8]
  · rw [Fin.sum_univ_eight]
    dsimp [f8D1, integerAffine8]
    norm_num

private theorem f8D1_strictlyOriented : f8D1.StrictlyOriented := by
  right
  intro i
  fin_cases i <;> norm_num [f8D1, integerAffine8]

private theorem f8D2_strictLegal : f8D2.StrictLegal := by
  apply StrictLegal_of_neg_slopes
  · intro i; fin_cases i <;> norm_num [f8D2, integerAffine8]
  · rw [Fin.sum_univ_eight]
    dsimp [f8D2, integerAffine8]
    norm_num

private theorem f8D2_strictlyOriented : f8D2.StrictlyOriented := by
  right
  intro i
  fin_cases i <;> norm_num [f8D2, integerAffine8]

private theorem f8D3_strictLegal : f8D3.StrictLegal := by
  apply StrictLegal_of_neg_slopes
  · intro i; fin_cases i <;> norm_num [f8D3, integerAffine8]
  · rw [Fin.sum_univ_eight]
    dsimp [f8D3, integerAffine8]
    norm_num

private theorem f8D3_strictlyOriented : f8D3.StrictlyOriented := by
  right
  intro i
  fin_cases i <;> norm_num [f8D3, integerAffine8]

/-- All three published denominators are exact native denominators. -/
theorem f8_denominators_admissible :
    f8D1.StrictAdmissible ∧
      f8D2.StrictAdmissible ∧ f8D3.StrictAdmissible := by
  refine ⟨⟨f8D1_strictLegal, f8D1_strictlyOriented⟩,
    ⟨f8D2_strictLegal, f8D2_strictlyOriented⟩,
    ⟨f8D3_strictLegal, f8D3_strictlyOriented⟩⟩

private def evalFormInt (c : ℤ) (l : Fin 8 → ℤ) (z : Fin 8 → Bool) : ℤ :=
  c + l 0 * (if z 0 then 1 else 0) + l 1 * (if z 1 then 1 else 0) +
  l 2 * (if z 2 then 1 else 0) + l 3 * (if z 3 then 1 else 0) +
  l 4 * (if z 4 then 1 else 0) + l 5 * (if z 5 then 1 else 0) +
  l 6 * (if z 6 then 1 else 0) + l 7 * (if z 7 then 1 else 0)

private def f8ClearedScoreInt (z : Fin 8 → Bool) : ℤ :=
  let d1 := evalFormInt 34 ![-1, -6, -1, -8, -1, -1, -1, -1] z
  let d2 := evalFormInt 31 ![-4, -1, -3, -7, -5, -6, -3, -1] z
  let d3 := evalFormInt 32 ![-1, -1, -6, -1, -1, -6, -6, -4] z
  let a1 := evalFormInt (-476) ![1794, 2403, 2934, 132, 1890, -4130, 2868, -661] z
  let a2 := evalFormInt 622 ![-2333, -1471, 188, 3074, -2633, 2202, 208, -1392] z
  let a3 := evalFormInt (-1006) ![1501, -577, -1950, -4044, 1799, 1406, -1914, 2472] z
  d1 * d2 * d3 + a1 * d2 * d3 + a2 * d1 * d3 + a3 * d1 * d2

private def boolSignInt (b : Bool) : ℤ := if b then 1 else -1

private theorem eval_integerAffine8_eq_int (c : ℤ) (l : Fin 8 → ℤ) (z : Fin 8 → Bool) :
    (integerAffine8 c l).eval z = (evalFormInt c l z : ℝ) := by
  dsimp [integerAffine8, TypicalLogCloseness.AffineForm.eval, evalFormInt, TypicalLogCloseness.bitReal]
  rw [Fin.sum_univ_eight]
  push_cast
  ring

private theorem f8ClearedScore_eq_int (z : Fin 8 → Bool) :
    f8ClearedScore z = (f8ClearedScoreInt z : ℝ) := by
  dsimp [f8ClearedScore, f8ClearedScoreInt, f8D1, f8D2, f8D3, f8A1, f8A2, f8A3]
  rw [eval_integerAffine8_eq_int, eval_integerAffine8_eq_int, eval_integerAffine8_eq_int,
      eval_integerAffine8_eq_int, eval_integerAffine8_eq_int, eval_integerAffine8_eq_int]
  push_cast
  rfl

private theorem boolSign_eq_int (b : Bool) :
    boolSign b = (boolSignInt b : ℝ) := by
  dsimp [boolSign, boolSignInt]
  split_ifs <;> norm_num

private theorem exists_fracAtom_eval_eq_neg {n : ℕ} (A B : AffineForm n)
    (hB_neg : ∀ i, B.linear i < 0)
    (hB_all1 : 0 < B.constant + ∑ i, B.linear i) :
    ∃ φ : HeadComplexity.FracAtom n,
      ∀ x, φ.eval x = A.eval x / B.eval x := by
  classical
  let S : ℝ := ∑ i, B.linear i
  let C : ℝ := B.constant
  have hS_le : S ≤ 0 := Finset.sum_nonpos fun i _ => (hB_neg i).le
  have hC : 0 < C := by linarith
  let k : ℝ := if S = 0 then 2 else (1 + C / (-S)) / 2
  have hk1 : 1 < k := by
    dsimp [k]
    split_ifs with hS0
    · norm_num
    · have hS_lt : S < 0 := lt_of_le_of_ne hS_le hS0
      have h_div : 1 < C / (-S) := by
        rw [lt_div_iff₀ (by linarith)]
        linarith
      linarith
  have hkS : 0 < C + k * S := by
    dsimp [k]
    split_ifs with hS0
    · simp [hS0, hC]
    · have hS_lt : S < 0 := lt_of_le_of_ne hS_le hS0
      have hnegS : 0 < -S := by linarith
      have hk_lt : (1 + C / (-S)) / 2 < C / (-S) := by
        have h_div : 1 < C / (-S) := by
          rw [lt_div_iff₀ hnegS]
          linarith
        linarith
      have h1 : ((1 + C / (-S)) / 2) * (-S) < C := (lt_div_iff₀ hnegS).mp hk_lt
      have h_ring : k * S = - (((1 + C / (-S)) / 2) * (-S)) := by dsimp [k]; rw [if_neg hS0]; ring
      linarith
  let α : ℝ := 1 - 1 / k
  have hα0 : 0 < α := by
    dsimp [α]
    rw [sub_pos, div_lt_iff₀ (by linarith)]
    linarith
  have hα_sub : α - 1 = -1 / k := by dsimp [α]; ring
  have hα_sub_neg : α - 1 < 0 := by
    rw [hα_sub]
    exact div_neg_of_neg_of_pos (by norm_num) (by linarith)
  let φ : HeadComplexity.FracAtom n := {
    η := A.constant + k * ∑ i, A.linear i
    δ := 0
    γ := C + k * S
    α := α
    ρ i := B.linear i / (α - 1)
    m i := A.linear i / B.linear i
    hγ := hkS
    hα := hα0
    hρ i := div_pos_of_neg_of_neg (hB_neg i) hα_sub_neg
  }
  have hden : TypicalLogCloseness.fracDenominator φ = B := by
    ext i
    · simp only [TypicalLogCloseness.fracDenominator, φ]
      change C + k * S + ∑ j, B.linear j / (α - 1) = C
      rw [← Finset.sum_div, show (∑ j, B.linear j) = S from rfl]
      rw [hα_sub]
      have hk0 : k ≠ 0 := (by linarith)
      field_simp
      ring
    · simp only [TypicalLogCloseness.fracDenominator, φ]
      have h_ne : α - 1 ≠ 0 := hα_sub_neg.ne
      field_simp
  have hnum : TypicalLogCloseness.fracNumerator φ = A := by
    ext i
    · simp only [TypicalLogCloseness.fracNumerator, φ]
      have h_sum : (∑ j, (B.linear j / (α - 1)) * (A.linear j / B.linear j)) =
          -k * ∑ j, A.linear j := by
        rw [hα_sub]
        have hk0 : k ≠ 0 := (by linarith)
        have h_term : ∀ j, (B.linear j / (-1 / k)) *
            (A.linear j / B.linear j) = -k * A.linear j := by
          intro j
          have hBj : B.linear j ≠ 0 := (hB_neg j).ne
          field_simp
        simp_rw [h_term]
        rw [← Finset.mul_sum]
      rw [h_sum]
      ring
    · simp only [TypicalLogCloseness.fracNumerator, φ]
      have h_ne : α - 1 ≠ 0 := hα_sub_neg.ne
      have hBi : B.linear i ≠ 0 := (hB_neg i).ne
      have hk0 : k ≠ 0 := (by linarith)
      dsimp [α]
      field_simp
      ring
  refine ⟨φ, fun x => ?_⟩
  rw [TypicalLogCloseness.fracAtom_eval_eq_affine, hden, hnum]

/-- Exact audit target for the integer certificate: the minimum signed cleared
margin over all 256 vertices is at least 58. -/
theorem f8_integer_certificate_margin (z : Fin 8 → Bool) :
    58 ≤ boolSign (f8 z) * f8ClearedScore z := by
  rw [boolSign_eq_int, f8ClearedScore_eq_int]
  norm_cast
  have hz : z = ![z 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7] := by
    ext i
    fin_cases i <;> rfl
  rw [hz]
  cases z 0 <;> cases z 1 <;> cases z 2 <;> cases z 3 <;> cases z 4 <;> cases z 5 <;> cases z 6 <;> cases z 7
  all_goals
    dsimp [f8ClearedScoreInt, evalFormInt, boolSignInt, f8, distThreshold, hammingDist, leftBits, rightBits]
    decide

/-- Paper Lemma 7: the explicit certificate realizes `f8` with three heads. -/
theorem f8_computableWithHeadsN_three :
    computableWithHeadsN 8 3 f8 := by
  rw [computableWithHeadsN_iff_fracComputable]
  have hD1_neg : ∀ i, f8D1.linear i < 0 := by
    intro i; fin_cases i <;> (unfold f8D1 integerAffine8; norm_num)
  have hD2_neg : ∀ i, f8D2.linear i < 0 := by
    intro i; fin_cases i <;> (unfold f8D2 integerAffine8; norm_num)
  have hD3_neg : ∀ i, f8D3.linear i < 0 := by
    intro i; fin_cases i <;> (unfold f8D3 integerAffine8; norm_num)
  have hsum1 : (∑ i, f8D1.linear i) = -20 := by
    rw [Fin.sum_univ_eight]; dsimp [f8D1, integerAffine8]; norm_num
  have hsum2 : (∑ i, f8D2.linear i) = -30 := by
    rw [Fin.sum_univ_eight]; dsimp [f8D2, integerAffine8]; norm_num
  have hsum3 : (∑ i, f8D3.linear i) = -26 := by
    rw [Fin.sum_univ_eight]; dsimp [f8D3, integerAffine8]; norm_num
  have hD1_all1 : 0 < f8D1.constant + ∑ i, f8D1.linear i := by
    rw [hsum1]; norm_num [f8D1, integerAffine8]
  have hD2_all1 : 0 < f8D2.constant + ∑ i, f8D2.linear i := by
    rw [hsum2]; norm_num [f8D2, integerAffine8]
  have hD3_all1 : 0 < f8D3.constant + ∑ i, f8D3.linear i := by
    rw [hsum3]; norm_num [f8D3, integerAffine8]
  obtain ⟨φ1, hφ1⟩ := exists_fracAtom_eval_eq_neg f8A1 f8D1 hD1_neg hD1_all1
  obtain ⟨φ2, hφ2⟩ := exists_fracAtom_eval_eq_neg f8A2 f8D2 hD2_neg hD2_all1
  obtain ⟨φ3, hφ3⟩ := exists_fracAtom_eval_eq_neg f8A3 f8D3 hD3_neg hD3_all1
  let φ : Fin 3 → FracAtom 8 := fun i =>
    match i with
    | ⟨0, _⟩ => φ1
    | ⟨1, _⟩ => φ2
    | ⟨2, _⟩ => φ3
  refine ⟨φ, 1, fun z => ?_⟩
  have hsum : ∑ h : Fin 3, (φ h).eval z = (φ 0).eval z + (φ 1).eval z + (φ 2).eval z := by
    rw [Fin.sum_univ_three]
  rw [hsum]
  dsimp [φ]
  rw [hφ1, hφ2, hφ3]
  have hD1 : 0 < f8D1.eval z := f8_denominators_admissible.1.1 z
  have hD2 : 0 < f8D2.eval z := f8_denominators_admissible.2.1.1 z
  have hD3 : 0 < f8D3.eval z := f8_denominators_admissible.2.2.1 z
  have hD_prod : 0 < f8D1.eval z * f8D2.eval z * f8D3.eval z := by positivity
  have h_cleared : 1 + (f8A1.eval z / f8D1.eval z +
      f8A2.eval z / f8D2.eval z + f8A3.eval z / f8D3.eval z) =
      f8ClearedScore z / (f8D1.eval z * f8D2.eval z * f8D3.eval z) := by
    unfold f8ClearedScore
    have hD1_ne : f8D1.eval z ≠ 0 := hD1.ne'
    have hD2_ne : f8D2.eval z ≠ 0 := hD2.ne'
    have hD3_ne : f8D3.eval z ≠ 0 := hD3.ne'
    field_simp
    ring
  rw [h_cleared]
  have h_div_pos : 0 < f8ClearedScore z /
      (f8D1.eval z * f8D2.eval z * f8D3.eval z) ↔ 0 < f8ClearedScore z := by
    constructor
    · intro h
      have hm := mul_pos h hD_prod
      rwa [div_mul_cancel₀ _ hD_prod.ne'] at hm
    · intro h
      exact div_pos h hD_prod
  rw [h_div_pos]
  have hm := f8_integer_certificate_margin z
  cases hfz : f8 z
  · unfold boolSign at hm
    rw [hfz] at hm
    dsimp at hm
    constructor
    · intro hpos; linarith
    · intro htrue; cases htrue
  · unfold boolSign at hm
    rw [hfz] at hm
    dsimp at hm
    constructor
    · intro _; rfl
    · intro _; linarith

private theorem HStar_f8_ge_three : 3 ≤ HStar 8 f8 := by
  by_contra hlt
  have hcomp := HStar_computable f8
  rcases (by omega : HStar 8 f8 = 0 ∨ HStar 8 f8 = 1 ∨ HStar 8 f8 = 2) with h0 | h1 | h2
  · have hconst : ∀ x y, f8 x = f8 y := (computableWithHeadsN_zero_iff f8).mp (h0 ▸ hcomp)
    have hF : f8 (fun _ => false) = false := rfl
    have hT : f8 ![true, true, false, false, false, false, false, false] = true := rfl
    have hEQ := hconst (fun _ => false) ![true, true, false, false, false, false, false, false]
    rw [hF, hT] at hEQ
    contradiction
  · have hdeg : ThresholdDegLE f8 1 := signReprDegLe_of_computableWithHeadsN (h1 ▸ hcomp)
    exact f8_not_thresholdDegLE_one hdeg
  · exact f8_not_computableWithHeadsN_two (h2 ▸ hcomp)

theorem HStar_f8 : HStar 8 f8 = 3 := by
  classical
  have h3 : computableWithHeadsN 8 3 f8 := f8_computableWithHeadsN_three
  have hex : ∃ k, computableWithHeadsN 8 k f8 := ⟨3, h3⟩
  have hle : HStar 8 f8 ≤ 3 := by
    unfold HStar
    rw [dif_pos hex]
    exact Nat.find_min' hex h3
  have hge : 3 ≤ HStar 8 f8 := HStar_f8_ge_three
  omega

/-- The complete theorem 189. -/
theorem theorem189_eight_bit_hamming_threshold :
    thresholdDeg f8 = 2 ∧ HStar 8 f8 = 3 ∧
      thresholdDeg f8 < HStar 8 f8 := by
  rw [thresholdDeg_f8, HStar_f8]
  norm_num

end HeadComplexity
