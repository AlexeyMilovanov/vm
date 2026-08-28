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
  sorry

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

/-- The fourteen exact checkerboards, transported by simultaneous signed
coordinate permutations, yield the abstract curvature certificate. -/
private theorem f8_has_curvatureCertificate
    (P : MvPolynomial (Fin 8) ℝ)
    (hdeg : P.totalDegree ≤ 2)
    (hrep : SignRepresents P f8) :
    F8CurvatureCertificate (symmetricPart4 (mixedMatrix4 P)) := by
  sorry

private theorem symmetricPart4_isSymm (K : Matrix (Fin 4) (Fin 4) ℝ) :
    (symmetricPart4 K).IsSymm := by
  ext i j
  simp [symmetricPart4, Matrix.transpose_apply]
  ring

/-- The real-algebraic half of paper Lemma 2: the finite certificate covers
every cone of vectors after sorting absolute coordinates. -/
private theorem curvatureCertificate_negative
    (S : Matrix (Fin 4) (Fin 4) ℝ) (hsymm : S.IsSymm)
    (hcert : F8CurvatureCertificate S) :
    NegativeDefinite4 S := by
  sorry

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
  sorry

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
      push_neg at hab_zero
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
  push_neg at h_le
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
  sorry

/-- Paper Lemmas 3 and 4 after the rank obstruction has supplied two
nonconstant, strictly oriented denominators. This is the factor-map and shell
transition part of the normalization argument. -/
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
  sorry
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


/-- The algebraic part of paper Lemma 6. Once every null-vector coordinate is
nonzero, rowwise contraction and the column-max spectral inequality contradict
the strict intercept inequality. -/
private theorem f8NormalizedSystem_false_of_mu_ne_zero
    (sys : F8NormalizedSystem) (hμ : ∀ i, sys.μ i ≠ 0) : False := by
  sorry

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
  sorry

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
