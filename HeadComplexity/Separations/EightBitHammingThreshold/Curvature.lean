import HeadComplexity.Separations.EightBitHammingThreshold.Core

set_option linter.style.header false

/-!
# Eight-bit Hamming threshold: curvature obstruction
-/

namespace HeadComplexity

open Finset
open scoped BigOperators
open TypicalLogCloseness
open MvPolynomial
open EightBitInternal

/-- 4-point checkerboard second difference helper: mixed term evaluation identity. -/
private theorem checkerboard_second_diff_term (u u' v v' : Fin 4 → Bool) (i j : Fin 4) :
    boolToReal (u' i) * boolToReal (v' j) - boolToReal (u' i) * boolToReal (v j) -
      boolToReal (u i) * boolToReal (v' j) + boolToReal (u i) * boolToReal (v j) =
    (boolToReal (u' i) - boolToReal (u i)) * (boolToReal (v' j) - boolToReal (v j)) := by
  ring

noncomputable def EightBitInternal.bilinear4 (K : Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * K i j * v j

def EightBitInternal.bitDiff4 (x₀ x₁ : Fin 4 → Bool) : Fin 4 → ℝ :=
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
      have hsum_split : (∑ k : Fin 4, s (Fin.castAdd 4 k)) + (∑ k : Fin 4, s (Fin.natAdd 4 k)) ≤
          2 := by
        have h := Fin.sum_univ_add (fun (k : Fin (4 + 4)) => s k)
        rw [← h]
        exact hsum
      have hL_sum : s (Fin.castAdd 4 i) ≤ ∑ k : Fin 4, s (Fin.castAdd 4 k) :=
        Finset.single_le_sum (f := fun k => s (Fin.castAdd 4 k)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
      have hR_sum : s (Fin.natAdd 4 j) ≤ ∑ k : Fin 4, s (Fin.natAdd 4 k) :=
        Finset.single_le_sum (f := fun k => s (Fin.natAdd 4 k)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ j)
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
  · have h1 : eval (cubePoint (blockJoin x₀ y₀)) (monomial s a) = eval (cubePoint (blockJoin x₀
      y₁)) (monomial s a) := by
      simp only [eval_monomial, cubePoint]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
      · simp only [blockJoin_castAdd]
      · simp only [blockJoin_natAdd, hL k', pow_zero]
    have h2 : eval (cubePoint (blockJoin x₁ y₀)) (monomial s a) = eval (cubePoint (blockJoin x₁
        y₁)) (monomial s a) := by
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
  · have h1 : eval (cubePoint (blockJoin x₀ y₀)) (monomial s a) = eval (cubePoint (blockJoin x₁
      y₀)) (monomial s a) := by
      simp only [eval_monomial, cubePoint]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
      · simp only [blockJoin_castAdd, hR k', pow_zero]
      · simp only [blockJoin_natAdd]
    have h2 : eval (cubePoint (blockJoin x₀ y₁)) (monomial s a) = eval (cubePoint (blockJoin x₁
        y₁)) (monomial s a) := by
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
        eval (cubePoint (blockJoin u v)) (monomial (Finsupp.single (Fin.castAdd 4 i) 1 +
            Finsupp.single (Fin.natAdd 4 j) 1) a) =
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
    have h_mix : mixedMatrix4 (monomial (Finsupp.single (Fin.castAdd 4 i) 1 + Finsupp.single
        (Fin.natAdd 4 j) 1) a) =
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
        rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
            Finsupp.single_apply, Finsupp.single_apply] at hi' hj'
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
            intro h
            exact h_ne (Fin.ext (by
              have hval := congr_arg Fin.val h
              dsimp at hval
              exact hval)).symm
          rw [if_neg h_ca1, if_neg h_ca2, if_pos rfl, if_neg h_ca3] at hi'
          contradiction
        have h_j : j' = j := by
          by_contra h_ne
          have h_na2 : ¬Fin.natAdd 4 j = Fin.natAdd 4 j' := by
            intro h
            exact h_ne (Fin.ext (by
              have hval := congr_arg Fin.val h
              dsimp at hval
              omega)).symm
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
      have h_sum_zero : (∑ j_1 : Fin 4, (boolToReal (x₀ k) - boolToReal (x₁ k)) * (if k = i ∧
          j_1 = j then a else 0) * (boolToReal (y₀ j_1) - boolToReal (y₁ j_1))) = 0 := by
        refine Finset.sum_eq_zero (fun k' _ => ?_)
        have h_and : ¬(k = i ∧ k' = j) := by rintro ⟨rfl, _⟩; exact hk rfl
        rw [if_neg h_and]
        ring
      exact h_sum_zero
    · intro h
      exact False.elim (h (Finset.mem_univ i))

/-- Degree-two checkerboard differences retain exactly the mixed block. -/
theorem EightBitInternal.quadratic_checkerboard_difference
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
    have hy : bitDiff4 ![true, true, false, false] ![false, false, true, false] = (![1, 1, -1,
        0] : Fin 4 → ℝ) := by
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
  rw [SignedPerm4.act_smul_pi, SignedPerm4.act_smul_pi, SignedPerm4.act_smul_pi,
      SignedPerm4.act_smul_pi]

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
  simp only [hS 1 0, hS 2 0, hS 3 0, hS 2 1, hS 3 1, hS 3 2, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
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
  rw [SignedPerm4.act_add_pi, SignedPerm4.act_add_pi, SignedPerm4.act_add_pi,
      SignedPerm4.act_smul_pi] at hq
  rw [bilinear4_add_right_pi, bilinear4_add_right_pi, bilinear4_add_right_pi,
      bilinear4_smul_right_pi] at hq
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
  rw [SignedPerm4.act_add_pi, SignedPerm4.act_add_pi, SignedPerm4.act_add_pi,
      SignedPerm4.act_smul_pi] at hr
  rw [bilinear4_add_right_pi, bilinear4_add_right_pi, bilinear4_add_right_pi,
      bilinear4_smul_right_pi] at hr
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
    bilinear4_expand4 S hsymm (T'.act prefix1) (T'.act prefix2) (T'.act prefix3) (T'.act
        prefix4) a1 a2 a3 a4
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

end HeadComplexity
