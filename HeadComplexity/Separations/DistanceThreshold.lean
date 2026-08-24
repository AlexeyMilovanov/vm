import HeadComplexity.Separations.SignRankBridge
import HeadComplexity.Separations.Forster
import HeadComplexity.Separations.ThresholdDegAux
import HeadComplexity.Polynomial.ParityThresholdDegree
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.header false

/-!
# Theorem A: constant degree, unboundedly many heads

The base family of `audit/sources/EXPLICIT_GAP.md`: for odd `m`, on `m + m` bits,

  `F_m(x, y) = 1 [ Δ(x, y) ≥ (m + 1) / 2 ]`

(majority of disagreements).  Its threshold degree is exactly `2`, while its
two-block sign matrix is the XOR-pattern of `MAJ_m`, whose spectral norm is
`2 · C(m-1, (m-1)/2)`.  Forster then gives sign-rank at least
`γ_m = 2^(m-1) / C(m-1, (m-1)/2) ~ √(πm/2)`, so by the sign-rank bridge
`H*(F_m) ≥ log₂(γ_m + 2) - 1 → ∞` at constant degree.  First explicit point
beating the corpus's 3-head ceiling: `m = 127`, where `γ > 14` forces
`H* ≥ 4`.
-/

namespace HeadComplexity

/-- The distance-majority function `F_m` on `m + m` bits. -/
def distThreshold (m : ℕ) : (Fin (m + m) → Bool) → Bool :=
  fun z => decide ((m + 1) / 2 ≤ hammingDist (leftBits m m z) (rightBits m m z))

/-- The Forster ratio `γ_m = 2^(m-1) / C(m-1, (m-1)/2)` of the family:
`2^m / specNorm` of its sign matrix.  Asymptotically `√(π m / 2)`. -/
noncomputable def forsterRatio (m : ℕ) : ℝ :=
  2 ^ (m - 1) / ((m - 1).choose ((m - 1) / 2))

/-- The Forster ratio is strictly positive (numerator `2^(m-1)` and the central
binomial denominator are both positive). -/
theorem forsterRatio_pos (m : ℕ) : 0 < forsterRatio m := by
  rw [forsterRatio]
  apply div_pos
  · positivity
  · exact_mod_cast Nat.choose_pos (Nat.div_le_self _ _)

open MvPolynomial in
/-- Upper half of the degree computation: `Δ(x,y) - m/2` is a quadratic sign
polynomial for `F_m` (never zero since `m` is odd).  PROOFS.md P7.1. -/
theorem thresholdDegLE_distThreshold {m : ℕ} (hm : Odd m) :
    ThresholdDegLE (distThreshold m) 2 := by
  classical
  have hm1 : 1 ≤ m := by have := Nat.odd_iff.mp hm; omega
  set P : MvPolynomial (Fin (m + m)) ℝ :=
    (∑ i : Fin m, (X (Fin.castAdd m i) + X (Fin.natAdd m i)
      - C 2 * (X (Fin.castAdd m i) * X (Fin.natAdd m i)))) - C ((m : ℝ) / 2) with hP
  refine ⟨P, ?_, ?_⟩
  · -- total degree ≤ 2 (each pair gadget is quadratic; constant absorbs)
    rw [hP]
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
  · -- sign representation: `eval P (cubePoint z) = hammingDist - m/2`
    intro z
    have hbool : ∀ a b : Bool,
        boolToReal a + boolToReal b - 2 * (boolToReal a * boolToReal b)
          = if a ≠ b then (1 : ℝ) else 0 := by
      intro a b; cases a <;> cases b <;> norm_num [boolToReal]
    have hpair : ∀ i : Fin m,
        eval (cubePoint z) (X (Fin.castAdd m i) + X (Fin.natAdd m i)
          - C 2 * (X (Fin.castAdd m i) * X (Fin.natAdd m i)))
          = if leftBits m m z i ≠ rightBits m m z i then (1 : ℝ) else 0 := by
      intro i
      simp only [map_sub, map_add, map_mul, eval_C, eval_X, cubePoint]
      exact hbool (z (Fin.castAdd m i)) (z (Fin.natAdd m i))
    have hsum : eval (cubePoint z) P
        = (hammingDist (leftBits m m z) (rightBits m m z) : ℝ) - (m : ℝ) / 2 := by
      rw [hP, map_sub, eval_C, map_sum]
      congr 1
      unfold hammingDist
      rw [Finset.card_filter]
      push_cast
      exact Finset.sum_congr rfl (fun i _ => hpair i)
    rw [hsum, distThreshold, decide_eq_true_eq]
    have hodd := Nat.odd_iff.mp hm
    set D := hammingDist (leftBits m m z) (rightBits m m z) with hD
    constructor
    · intro h
      have hmD : (m : ℝ) < 2 * (D : ℝ) := by linarith
      have hmD' : m < 2 * D := by exact_mod_cast hmD
      omega
    · intro h
      have hmD' : m < 2 * D := by omega
      have hmD : (m : ℝ) < 2 * (D : ℝ) := by exact_mod_cast hmD'
      linarith

theorem not_thresholdDegLE_one_distThreshold {m : ℕ} (hm : Odd m) :
    ¬ ThresholdDegLE (distThreshold m) 1 := by
  intro hLTF1
  rw [ThresholdDegLE_one_iff_isLTF] at hLTF1
  obtain ⟨c, cs, hsign⟩ := hLTF1
  have hm1 : 1 ≤ m := by have := Nat.odd_iff.mp hm; omega
  set k := (m - 1) / 2
  have hk : m = 2 * k + 1 := by
    have hmod : m % 2 = 1 := Nat.odd_iff.mp hm
    omega
  have hm_half : (m + 1) / 2 = k + 1 := by omega

  set i0 : Fin m := ⟨0, by omega⟩
  set a_base : Fin m → Bool := fun i => decide (0 < i.val ∧ i.val ≤ k)
  
  let e0 : Fin m → Bool := fun i => if i = i0 then false else a_base i
  let e1 : Fin m → Bool := fun i => if i = i0 then true else a_base i
  
  have he0 : e0 = a_base := by
    ext i
    by_cases hi : i = i0
    · subst hi; simp [e0, a_base, i0]
    · simp [e0, a_base, hi]
    
  have he1_0 : e1 i0 = true := by simp [e1]
  have he1_ne : ∀ i, i ≠ i0 → e1 i = a_base i := by
    intro i hi
    simp [e1, hi]

  have h_a_base : hammingDist a_base (fun _ => false) = k := by
    rw [hammingDist]
    have h1 : (Finset.univ.filter (fun i => a_base i ≠ false)) = Finset.univ.filter (fun i => a_base i) := by
      ext i; simp
    rw [h1]
    have H : (Finset.univ.filter (fun i => a_base i)).card = (Finset.Ioc 0 k).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, a_base, decide_eq_true_eq] at ha
        simp [ha.1, ha.2]
      · intro a b ha hb hab
        exact Fin.ext hab
      · intro b hb
        simp only [Finset.mem_Ioc] at hb
        have hbm : b < m := by omega
        refine ⟨⟨b, hbm⟩, ?_, rfl⟩
        simp [a_base, hb.1, hb.2]
    rw [H, Nat.card_Ioc, Nat.sub_zero]
    
  have h_e0 : hammingDist e0 (fun _ => false) = k := by
    rw [he0, h_a_base]

  have h_e1 : hammingDist e1 (fun i => if i = i0 then true else false) = k := by
    rw [hammingDist]
    have h1 : (Finset.univ.filter (fun i => e1 i ≠ (if i = i0 then true else false))) = Finset.univ.filter (fun i => a_base i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi : i = i0
      · subst hi; simp [he1_0, a_base, i0]
      · simp [he1_ne i hi, hi, a_base, i0]
    rw [h1]
    have h2 : (Finset.univ.filter (fun i => a_base i)).card = k := by
      have : hammingDist a_base (fun _ => false) = k := h_a_base
      rw [hammingDist] at this
      have h3 : (Finset.univ.filter (fun i => a_base i ≠ false)) = Finset.univ.filter (fun i => a_base i) := by
        ext i; simp
      rw [h3] at this
      exact this
    exact h2

  have h_e01 : hammingDist e0 (fun i => if i = i0 then true else false) = k + 1 := by
    rw [hammingDist]
    have h1 : (Finset.univ.filter (fun i => e0 i ≠ (if i = i0 then true else false))) = insert i0 (Finset.univ.filter (fun i => a_base i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hi : i = i0
      · subst hi; simp [he0, a_base, i0]
      · simp [he0, hi, a_base, i0]
    rw [h1, Finset.card_insert_of_notMem]
    · have h2 : (Finset.univ.filter (fun i => a_base i)).card = k := by
        have : hammingDist a_base (fun _ => false) = k := h_a_base
        rw [hammingDist] at this
        have h3 : (Finset.univ.filter (fun i => a_base i ≠ false)) = Finset.univ.filter (fun i => a_base i) := by
          ext i; simp
        rw [h3] at this
        exact this
      rw [h2]
    · simp [a_base, i0]
      
  have h_e10 : hammingDist e1 (fun _ => false) = k + 1 := by
    rw [hammingDist]
    have h1 : (Finset.univ.filter (fun i => e1 i ≠ false)) = insert i0 (Finset.univ.filter (fun i => a_base i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hi : i = i0
      · subst hi; simp [he1_0, a_base, i0]
      · simp [he1_ne i hi, hi, a_base, i0]
    rw [h1, Finset.card_insert_of_notMem]
    · have h2 : (Finset.univ.filter (fun i => a_base i)).card = k := by
        have : hammingDist a_base (fun _ => false) = k := h_a_base
        rw [hammingDist] at this
        have h3 : (Finset.univ.filter (fun i => a_base i ≠ false)) = Finset.univ.filter (fun i => a_base i) := by
          ext i; simp
        rw [h3] at this
        exact this
      rw [h2]
    · simp [a_base, i0]

  let z00 := blockJoin e0 (fun _ : Fin m => false)
  let z11 := blockJoin e1 (fun i : Fin m => if i = i0 then true else false)
  let z01 := blockJoin e0 (fun i : Fin m => if i = i0 then true else false)
  let z10 := blockJoin e1 (fun _ : Fin m => false)
  
  have hpt : ∀ j, boolToReal (z00 j) + boolToReal (z11 j) = boolToReal (z01 j) + boolToReal (z10 j) := by
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
    
  have h_z00 : distThreshold m z00 = false := by
    rw [distThreshold, decide_eq_false_iff_not, not_le, hm_half]
    simp only [z00, leftBits_blockJoin, rightBits_blockJoin, h_e0]
    exact Nat.lt_succ_self k
  have h_z11 : distThreshold m z11 = false := by
    rw [distThreshold, decide_eq_false_iff_not, not_le, hm_half]
    simp only [z11, leftBits_blockJoin, rightBits_blockJoin, h_e1]
    exact Nat.lt_succ_self k
  have h_z01 : distThreshold m z01 = true := by
    rw [distThreshold, decide_eq_true_eq, hm_half]
    simp only [z01, leftBits_blockJoin, rightBits_blockJoin, h_e01]
    exact Nat.le_refl (k + 1)
  have h_z10 : distThreshold m z10 = true := by
    rw [distThreshold, decide_eq_true_eq, hm_half]
    simp only [z10, leftBits_blockJoin, rightBits_blockJoin, h_e10]
    exact Nat.le_refl (k + 1)
  
  have hpos_01 : 0 < c + ∑ i, cs i * boolToReal (z01 i) := (hsign _).mpr h_z01
  have hpos_10 : 0 < c + ∑ i, cs i * boolToReal (z10 i) := (hsign _).mpr h_z10
  have hneg_00 : c + ∑ i, cs i * boolToReal (z00 i) ≤ 0 := by
    by_contra h; push Not at h
    have := (hsign _).mp h; rw [h_z00] at this; exact absurd this (by decide)
  have hneg_11 : c + ∑ i, cs i * boolToReal (z11 i) ≤ 0 := by
    by_contra h; push Not at h
    have := (hsign _).mp h; rw [h_z11] at this; exact absurd this (by decide)
    
  linarith

/-- Exact degree: restricting all but one disagreement pair to fixed
disagreement leaves a 2-bit XOR, so degree `2` is also necessary. -/
theorem thresholdDeg_distThreshold {m : ℕ} (hm : Odd m) :
    thresholdDeg (distThreshold m) = 2 := by
  have hle := thresholdDeg_le_of (thresholdDegLE_distThreshold hm)
  have hlt := lt_thresholdDeg_of (not_thresholdDegLE_one_distThreshold hm)
  omega

/-- Fourier character `χ_S(x) = ∏_{i ∈ S} (-1)^{x_i}` on the Boolean cube,
valued in `{±1}`.  The `2^m` characters form the eigenbasis that diagonalizes the
distance-majority sign matrix (PROOFS.md §4). -/
def charFn {m : ℕ} (S : Finset (Fin m)) (x : Fin m → Bool) : ℝ :=
  ∏ i ∈ S, (if x i then (-1 : ℝ) else 1)

/-- The majority sign `s(u) = +1` iff the Hamming weight `|u|` reaches the
threshold `(m+1)/2`, else `-1`.  The two-block sign matrix of `F_m` is
`s(x ⊕ y)` (PROOFS.md §4). -/
def distSign (m : ℕ) (u : Fin m → Bool) : ℝ :=
  if (m + 1) / 2 ≤ hammingDist u (fun _ => false) then 1 else -1

/-- Characters are multiplicative under XOR: `χ_S(x ⊕ y) = χ_S(x) · χ_S(y)`
(PROOFS.md P4.1), the mod-2 additivity of the exponent.  This is the key step
that makes each `χ_S` an eigenvector of the convolution matrix `s(x ⊕ y)`. -/
theorem charFn_xor {m : ℕ} (S : Finset (Fin m)) (x y : Fin m → Bool) :
    charFn S (fun i => xor (x i) (y i)) = charFn S x * charFn S y := by
  have key : ∀ a b : Bool,
      (if xor a b then (-1 : ℝ) else 1) = (if a then -1 else 1) * (if b then -1 else 1) := by
    intro a b; cases a <;> cases b <;> simp
  unfold charFn
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => key (x i) (y i)

private theorem charFn_eq_prod_univ {m : ℕ} (S : Finset (Fin m)) (x : Fin m → Bool) :
    charFn S x = ∏ i : Fin m, if i ∈ S then (if x i then (-1 : ℝ) else 1) else 1 := by
  unfold charFn
  have h := Finset.prod_subset (s₁ := S) (s₂ := Finset.univ)
    (f := fun i => if i ∈ S then (if x i then (-1 : ℝ) else 1) else 1)
    (Finset.subset_univ S) (fun i _ hi => if_neg hi)
  rw [← h]
  exact Finset.prod_congr rfl (fun i hi => (if_pos hi).symm)

/-- **Character orthogonality** (PROOFS.md P4.3): the `2^m` characters are
pairwise orthogonal with squared norm `2^m`, i.e.
`∑_x χ_S(x) χ_T(x) = if S = T then 2^m else 0`.  Proof: write the summand as
`∏_i cᵢ(xᵢ)` and apply `Finset.prod_univ_sum` (sum/product interchange over the
cube); each coordinate factor `∑_b cᵢ(b)` is `2` off `S △ T` and `0` on it, so
the whole product vanishes unless `S = T`. -/
theorem charFn_orthogonal {m : ℕ} (S T : Finset (Fin m)) :
    ∑ x : Fin m → Bool, charFn S x * charFn T x = if S = T then (2 : ℝ) ^ m else 0 := by
  have h_prod : ∀ x : Fin m → Bool, charFn S x * charFn T x =
      ∏ i : Fin m, ((if i ∈ S then (if x i then (-1 : ℝ) else 1) else 1) *
                   (if i ∈ T then (if x i then (-1 : ℝ) else 1) else 1)) := by
    intro x
    rw [charFn_eq_prod_univ S x, charFn_eq_prod_univ T x, ← Finset.prod_mul_distrib]
  simp_rw [h_prod]
  have h_cube : (Finset.univ : Finset (Fin m → Bool)) =
      Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset Bool)) := by
    ext x; simp [Fintype.mem_piFinset]
  have h_sum : (∑ x : Fin m → Bool, ∏ i : Fin m, ((if i ∈ S then (if x i then (-1 : ℝ) else 1) else 1) *
                   (if i ∈ T then (if x i then (-1 : ℝ) else 1) else 1))) =
      ∏ i : Fin m, (((if i ∈ S then (-1 : ℝ) else 1) * (if i ∈ T then (-1 : ℝ) else 1)) + 1) := by
    have h2 := (Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset Bool))
      (fun i (b : Bool) => (if i ∈ S then (if b then (-1 : ℝ) else 1) else 1) *
                           (if i ∈ T then (if b then (-1 : ℝ) else 1) else 1))).symm
    rw [h_cube, h2]
    congr 1; ext i
    rw [Fintype.sum_bool]
    simp
  rw [h_sum]
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl]
    have h_term : (∀ i : Fin m, (((if i ∈ S then (-1 : ℝ) else 1) *
                    (if i ∈ S then (-1 : ℝ) else 1)) + 1) = 2) := by
      intro i
      split_ifs <;> norm_num
    rw [Finset.prod_congr rfl (fun i _ => h_term i)]
    simp
  · rw [if_neg hST]
    have h_ne : ∃ i : Fin m, (i ∈ S ∧ i ∉ T) ∨ (i ∉ S ∧ i ∈ T) := by
      contrapose! hST
      ext i
      exact ⟨fun hS => (hST i).1 hS, fun hT => by_contra fun hS => (hST i).2 hS hT⟩
    obtain ⟨i, hi⟩ := h_ne
    apply Finset.prod_eq_zero (i := i) (by simp)
    rcases hi with ⟨hS, hT⟩ | ⟨hS, hT⟩
    · simp [hS, hT]
    · simp [hS, hT]

/-- The two-block sign matrix of `F_m` is the majority sign of the XOR
(PROOFS.md P4.1): `signMatrix m m (distThreshold m) x y = s(x ⊕ y)`.  Unfold
`signMatrix`/`distThreshold` and use `hammingDist x y = hammingDist (x ⊕ y) 0`
(both count `{i : x i ≠ y i}`). -/
theorem signMatrix_distThreshold_apply {m : ℕ} (x y : Fin m → Bool) :
    signMatrix m m (distThreshold m) x y = distSign m (fun i => xor (x i) (y i)) := by
  have hd : hammingDist x y
      = hammingDist (fun i => xor (x i) (y i)) (fun _ => false) := by
    unfold hammingDist
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    cases x i <;> cases y i <;> simp
  have hL : distThreshold m (blockJoin x y)
      = decide ((m + 1) / 2 ≤ hammingDist (fun i => xor (x i) (y i)) (fun _ => false)) := by
    unfold distThreshold
    simp only [leftBits_blockJoin, rightBits_blockJoin]
    rw [hd]
  rw [signMatrix_apply, hL, distSign]
  by_cases h : (m + 1) / 2 ≤ hammingDist (fun i => xor (x i) (y i)) (fun _ => false)
  · simp [h]
  · simp [h]

open Matrix in
/-- **Character eigen-action** (PROOFS.md P4.1): each character is an
eigenvector of the sign matrix, `M χ_S = λ_S χ_S`, with eigenvalue
`λ_S = ∑_u s(u) χ_S(u)`.  Proof: `(M χ_S)(x) = ∑_y s(x ⊕ y) χ_S(y)`; substitute
`u = x ⊕ y` (a bijection of the cube via `fun y => x ⊕ y`) and use
`charFn_xor` to pull out `χ_S(x)`.  Uses `signMatrix_distThreshold_apply`. -/
theorem signMatrix_mulVec_charFn {m : ℕ} (S : Finset (Fin m)) :
    signMatrix m m (distThreshold m) *ᵥ charFn S
      = (∑ u : Fin m → Bool, distSign m u * charFn S u) • charFn S := by
  ext x
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  let e : (Fin m → Bool) ≃ (Fin m → Bool) :=
    { toFun := fun u i => xor (x i) (u i)
      invFun := fun u i => xor (x i) (u i)
      left_inv := fun u => by ext i; dsimp; cases x i <;> cases u i <;> rfl
      right_inv := fun u => by ext i; dsimp; cases x i <;> cases u i <;> rfl }
  rw [← e.sum_comp]
  have h_dist : ∀ u : Fin m → Bool,
      signMatrix m m (distThreshold m) x (e u) = distSign m u := by
    intro u
    rw [signMatrix_distThreshold_apply]
    congr 1
    ext i
    dsimp [e]
    cases x i <;> cases u i <;> rfl
  have h_char : ∀ u : Fin m → Bool,
      charFn S (e u) = charFn S x * charFn S u := by
    intro u
    exact charFn_xor S x u
  have h_summand : ∀ u : Fin m → Bool,
      signMatrix m m (distThreshold m) x (e u) * charFn S (e u)
        = (distSign m u * charFn S u) * charFn S x := by
    intro u
    rw [h_dist u, h_char u]
    ring
  rw [Finset.sum_congr rfl (fun u _ => h_summand u)]
  rw [← Finset.sum_mul]

/-- The bit-complement involution `u ↦ ū` on the Boolean cube (PROOFS.md P4.2). -/
private def compEquiv (m : ℕ) : (Fin m → Bool) ≃ (Fin m → Bool) where
  toFun u := fun i => !u i
  invFun u := fun i => !u i
  left_inv u := by ext i; simp
  right_inv u := by ext i; simp

/-- The complement flips the majority sign for odd `m` (PROOFS.md P4.2): since
`|ū| = m - |u|` and exactly one of `|u|, m - |u|` reaches `(m+1)/2`, we get
`s(ū) = -s(u)`. -/
private theorem distSign_not (m : ℕ) (hm : Odd m) (u : Fin m → Bool) :
    distSign m (fun i => !u i) = - distSign m u := by
  unfold distSign
  have hm_odd : m % 2 = 1 := Nat.odd_iff.mp hm
  have h1 : hammingDist (fun i => !u i) (fun _ => false)
      = m - hammingDist u (fun _ => false) := by
    unfold hammingDist
    have h1' : (Finset.univ.filter (fun i => (!u i) ≠ false)).card =
        (Finset.univ.filter (fun i => u i = false)).card := by
      congr 1; ext i; simp
    rw [h1']
    set A := (Finset.univ.filter (fun i => u i ≠ false)).card
    set B := (Finset.univ.filter (fun i => u i = false)).card
    have hsum : A + B = m := by
      have hsum' : A + B = (Finset.univ : Finset (Fin m)).card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext i; simp
        · rw [Finset.disjoint_filter]; intro i _ h1 h2; exact h1 h2
      rw [hsum', Finset.card_univ, Fintype.card_fin]
    omega
  rw [h1]
  set D := hammingDist u (fun _ => false)
  have hD_le : D ≤ m := by
    dsimp [D, hammingDist]
    have hle := Finset.card_le_card (Finset.filter_subset (fun i => u i ≠ false) Finset.univ)
    rw [Finset.card_univ, Fintype.card_fin] at hle
    exact hle
  split_ifs with h2 h3
  · omega
  · norm_num
  · norm_num
  · omega

/-- The level-`0` eigenvalue vanishes (PROOFS.md P4.2, consequence 3):
`λ_∅ = ∑_u s(u) = 0` for odd `m`.  Proof: the complement involution `u ↦ ū`
is fixed-point-free (`m` odd) and flips the sign, `s(ū) = -s(u)` (exactly one of
`|u|, m - |u|` reaches `(m+1)/2`), so the sum cancels in pairs. -/
theorem distSign_sum_eq_zero {m : ℕ} (hm : Odd m) :
    ∑ u : Fin m → Bool, distSign m u = 0 := by
  have h1 : ∑ u : Fin m → Bool, distSign m u
      = ∑ u : Fin m → Bool, distSign m (compEquiv m u) :=
    (Equiv.sum_comp (compEquiv m) (fun u => distSign m u)).symm
  have h2 : ∀ u, distSign m (compEquiv m u) = - distSign m u := fun u => distSign_not m hm u
  simp_rw [h2] at h1
  rw [Finset.sum_neg_distrib] at h1
  linarith

/-- **Level-1 eigenvalue** (PROOFS.md P4.2, consequence 2): for a singleton
`S = {i}` the Fourier eigenvalue `λ_{i} = ∑_u s(u) χ_{i}(u)` equals
`-2 · C(m-1, (m-1)/2)`.  Proof: pair `u` (with `u_i = 0`) against `u ⊕ e_i`;
since `χ_{i}` flips, the pair contributes `s(u) - s(u ⊕ e_i)`, which is `0`
unless the weight crosses the threshold at `|u| = (m-1)/2`, where it is `-2`;
the crossing points are the `C(m-1, (m-1)/2)` middle-slice vectors with
`u_i = 0`.  (Sign check `m = 1`: the sum is `-2 = -2·C(0,0)`.) -/
theorem distEigenvalue_singleton {m : ℕ} (hm : Odd m) (i : Fin m) :
    ∑ u : Fin m → Bool, distSign m u * charFn {i} u
      = -(2 * ((m - 1).choose ((m - 1) / 2))) := by
  let e : (Fin m → Bool) ≃ Finset (Fin m) :=
    { toFun := fun u => Finset.univ.filter fun j => u j
      invFun := fun s j => decide (j ∈ s)
      left_inv := by
        intro u
        funext j
        simp
      right_inv := by
        intro s
        ext j
        simp }
  let q := (m - 1) / 2
  let g : Finset (Fin m) → ℝ := fun s =>
    (if (m + 1) / 2 ≤ s.card then 1 else -1) * (if i ∈ s then -1 else 1)
  have hm_odd : m % 2 = 1 := Nat.odd_iff.mp hm
  have hthreshold : (m + 1) / 2 = q + 1 := by
    dsimp [q]
    omega
  have hdist (u : Fin m → Bool) :
      distSign m u = if (m + 1) / 2 ≤ (e u).card then 1 else -1 := by
    unfold distSign
    congr 2
    unfold hammingDist
    change (Finset.univ.filter fun j => u j ≠ false).card = _
    congr 1
    ext j
    simp [e]
  have hchar (u : Fin m → Bool) :
      charFn {i} u = if i ∈ e u then -1 else 1 := by
    simp [charFn, e]
  have hto_g :
      (∑ u : Fin m → Bool, distSign m u * charFn {i} u) =
        ∑ s : Finset (Fin m), g s := by
    calc
      (∑ u : Fin m → Bool, distSign m u * charFn {i} u) =
          ∑ u : Fin m → Bool, g (e u) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [hdist u, hchar u]
      _ = ∑ s : Finset (Fin m), g s := e.sum_comp g
  rw [hto_g]
  rw [← Finset.powerset_univ]
  rw [← Finset.insert_erase (Finset.mem_univ i)]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ)]
  rw [← Finset.sum_add_distrib]
  have hpair (s : Finset (Fin m))
      (hs : s ∈ (Finset.univ.erase i).powerset) :
      g s + g (insert i s) = if s.card = q then -2 else 0 := by
    have hsub : s ⊆ Finset.univ.erase i := Finset.mem_powerset.mp hs
    have hi : i ∉ s := by
      intro his
      have := hsub his
      simp at this
    have hcard : (insert i s).card = s.card + 1 := Finset.card_insert_of_notMem hi
    unfold g
    rw [hcard, if_neg hi, if_pos (Finset.mem_insert_self i s), hthreshold]
    split_ifs <;> norm_num <;> omega
  rw [Finset.sum_congr rfl hpair]
  calc
    (∑ s ∈ (Finset.univ.erase i).powerset, if s.card = q then (-2 : ℝ) else 0) =
        (-2 : ℝ) * ∑ s ∈ (Finset.univ.erase i).powerset,
          if s.card = q then 1 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> norm_num
    _ = (-2 : ℝ) *
        (((Finset.univ.erase i).powerset.filter fun s => s.card = q).card : ℝ) := by
      rw [Finset.sum_boole]
    _ = (-2 : ℝ) * (((Finset.univ.erase i).powersetCard q).card : ℝ) := by
      rw [Finset.powersetCard_eq_filter]
    _ = -(2 * ((m - 1).choose ((m - 1) / 2))) := by
      rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]
      simp [q]

/-- **Level-1 eigenvalue bound** (PROOFS.md P4.2, consequence 1): every Fourier
eigenvalue `λ_S = ∑_u s(u) χ_S(u)` has `|λ_S| ≤ 2 · C(m-1, (m-1)/2)`.  Proof:
for `S ≠ ∅` pick `i ∈ S`; the boundary pairing gives
`λ_S = -2 · ∑_{u' : |u'| = (m-1)/2} χ_{S∖{i}}(u')`, a signed sum of
`C(m-1, (m-1)/2)` unit terms, so the triangle inequality bounds it; for `S = ∅`,
`λ_∅ = 0` by `distSign_sum_eq_zero`.  This is the eigenvalue side of the
spectral-norm computation; combined with `distEigenvalue_singleton` (equality at
level 1) it pins `max_S |λ_S| = 2·C(m-1,(m-1)/2)`. -/
theorem distEigenvalue_le {m : ℕ} (hm : Odd m) (S : Finset (Fin m)) :
    |∑ u : Fin m → Bool, distSign m u * charFn S u|
      ≤ 2 * ((m - 1).choose ((m - 1) / 2)) := by
  by_cases hS : S = ∅
  · subst S
    simp [charFn, distSign_sum_eq_zero hm]
  · obtain ⟨i, hiS⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    let e : (Fin m → Bool) ≃ Finset (Fin m) :=
      { toFun := fun u => Finset.univ.filter fun j => u j
        invFun := fun s j => decide (j ∈ s)
        left_inv := by
          intro u
          funext j
          simp
        right_inv := by
          intro s
          ext j
          simp }
    let q := (m - 1) / 2
    let c : Finset (Fin m) → ℝ := fun s =>
      ∏ j ∈ S, if j ∈ s then -1 else 1
    let g : Finset (Fin m) → ℝ := fun s =>
      (if (m + 1) / 2 ≤ s.card then 1 else -1) * c s
    have hm_odd : m % 2 = 1 := Nat.odd_iff.mp hm
    have hthreshold : (m + 1) / 2 = q + 1 := by
      dsimp [q]
      omega
    have hdist (u : Fin m → Bool) :
        distSign m u = if (m + 1) / 2 ≤ (e u).card then 1 else -1 := by
      unfold distSign
      congr 2
      unfold hammingDist
      change (Finset.univ.filter fun j => u j ≠ false).card = _
      congr 1
      ext j
      simp [e]
    have hchar (u : Fin m → Bool) : charFn S u = c (e u) := by
      unfold charFn c
      apply Finset.prod_congr rfl
      intro j _
      simp [e]
    have hto_g :
        (∑ u : Fin m → Bool, distSign m u * charFn S u) =
          ∑ s : Finset (Fin m), g s := by
      calc
        (∑ u : Fin m → Bool, distSign m u * charFn S u) =
            ∑ u : Fin m → Bool, g (e u) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [hdist u, hchar u]
        _ = ∑ s : Finset (Fin m), g s := e.sum_comp g
    rw [hto_g]
    rw [← Finset.powerset_univ]
    rw [← Finset.insert_erase (Finset.mem_univ i)]
    rw [Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ)]
    rw [← Finset.sum_add_distrib]
    have hc_insert (s : Finset (Fin m)) (hi : i ∉ s) :
        c (insert i s) = -c s := by
      unfold c
      rw [← Finset.insert_erase hiS]
      rw [Finset.prod_insert (Finset.notMem_erase i S),
        Finset.prod_insert (Finset.notMem_erase i S)]
      simp only [Finset.mem_insert, true_or, ↓reduceIte, hi]
      rw [one_mul, neg_mul]
      simp only [one_mul]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [hji]
    have hpair (s : Finset (Fin m))
        (hs : s ∈ (Finset.univ.erase i).powerset) :
        g s + g (insert i s) = if s.card = q then -2 * c s else 0 := by
      have hsub : s ⊆ Finset.univ.erase i := Finset.mem_powerset.mp hs
      have hi : i ∉ s := by
        intro his
        have := hsub his
        simp at this
      have hcard : (insert i s).card = s.card + 1 :=
        Finset.card_insert_of_notMem hi
      unfold g
      rw [hcard, hc_insert s hi, hthreshold]
      split_ifs <;> (first | omega | ring)
    rw [Finset.sum_congr rfl hpair]
    calc
      |∑ s ∈ (Finset.univ.erase i).powerset,
          if s.card = q then -2 * c s else 0| ≤
          ∑ s ∈ (Finset.univ.erase i).powerset,
            |if s.card = q then -2 * c s else 0| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s ∈ (Finset.univ.erase i).powerset,
          if s.card = q then (2 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s.card = q
        · rw [if_pos hs, if_pos hs, abs_mul]
          have hc_abs : |c s| = 1 := by
            unfold c
            rw [Finset.abs_prod]
            apply Finset.prod_eq_one
            intro j hj
            split_ifs <;> norm_num
          rw [hc_abs]
          norm_num
        · simp [hs]
      _ = (2 : ℝ) * ∑ s ∈ (Finset.univ.erase i).powerset,
          if s.card = q then 1 else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        split_ifs <;> norm_num
      _ = (2 : ℝ) *
          (((Finset.univ.erase i).powerset.filter fun s => s.card = q).card : ℝ) := by
        rw [Finset.sum_boole]
      _ = (2 : ℝ) * (((Finset.univ.erase i).powersetCard q).card : ℝ) := by
        rw [Finset.powersetCard_eq_filter]
      _ = 2 * ((m - 1).choose ((m - 1) / 2)) := by
        rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]

/-- **Parseval upper bound** (PROOFS.md P4.3): expand an arbitrary vector in the
orthogonal character basis (`charFn_orthogonal`), use
`signMatrix_mulVec_charFn` to diagonalize the distance-threshold matrix, and
bound every eigenvalue by `distEigenvalue_le`. -/
lemma sum_charFn {m : ℕ} (u : Fin m → Bool) :
    ∑ S : Finset (Fin m), charFn S u = if u = (fun _ => false) then (2 : ℝ)^m else 0 := by
  have h_powerset : (Finset.univ : Finset (Finset (Fin m))) = (Finset.univ : Finset (Fin m)).powerset := by
    ext x
    simp
  have H : ∑ S : Finset (Fin m), charFn S u =
      ∏ i : Fin m, (1 + if u i then (-1 : ℝ) else 1) := by
    calc ∑ S : Finset (Fin m), charFn S u
      _ = ∑ S : Finset (Fin m), ∏ i ∈ S, (if u i then (-1 : ℝ) else 1) := rfl
      _ = ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, ∏ i ∈ S, (if u i then (-1 : ℝ) else 1) := by rw [←h_powerset]
      _ = ∏ i ∈ (Finset.univ : Finset (Fin m)), (1 + if u i then (-1 : ℝ) else 1) := (Finset.prod_one_add Finset.univ).symm
      _ = ∏ i : Fin m, (1 + if u i then (-1 : ℝ) else 1) := rfl
  rw [H]
  by_cases h : u = fun _ => false
  · rw [if_pos h]
    have : ∀ i, (1 + if u i then (-1 : ℝ) else 1) = 2 := by
      intro i
      have hi : u i = false := congr_fun h i
      rw [hi, if_neg (by decide)]
      ring
    rw [Finset.prod_congr rfl (fun i _ => this i)]
    simp
  · rw [if_neg h]
    have : ∃ i, u i = true := by
      by_contra hc
      push Not at hc
      apply h
      ext i
      simp [hc i]
    rcases this with ⟨i, hi⟩
    apply Finset.prod_eq_zero (i := i) (by simp)
    rw [hi]
    simp

lemma sum_charFn_charFn {m : ℕ} (x y : Fin m → Bool) :
    ∑ S : Finset (Fin m), charFn S x * charFn S y = if x = y then (2 : ℝ)^m else 0 := by
  have : ∀ S, charFn S x * charFn S y = charFn S (fun i => xor (x i) (y i)) := by
    intro S
    rw [charFn_xor]
  simp_rw [this]
  have H := sum_charFn (fun i => xor (x i) (y i))
  have H2 : (fun i => xor (x i) (y i)) = (fun _ => false) ↔ x = y := by
    constructor
    · intro h
      ext i
      have hi := congr_fun h i
      cases hx : x i <;> cases hy : y i <;> simp_all
    · intro h
      subst h
      ext i
      simp
  by_cases hxy : x = y
  · rw [if_pos hxy]
    rw [if_pos (H2.mpr hxy)] at H
    exact H
  · rw [if_neg hxy]
    have hn : ¬((fun i => x i ^^ y i) = fun x => false) := by
      intro hc; exact hxy (H2.mp hc)
    rw [if_neg hn] at H
    exact H

lemma M_symm {m : ℕ} (x y : Fin m → Bool) :
    signMatrix m m (distThreshold m) x y = signMatrix m m (distThreshold m) y x := by
  rw [signMatrix_distThreshold_apply, signMatrix_distThreshold_apply]
  have : (fun i => xor (x i) (y i)) = (fun i => xor (y i) (x i)) := by
    ext i
    rw [Bool.xor_comm]
  rw [this]

lemma L2_ident {m : ℕ} (w : (Fin m → Bool) → ℝ) :
    ∑ S : Finset (Fin m), (∑ x, w x * charFn S x)^2 = (2:ℝ)^m * ∑ x, (w x)^2 := by
  have H1 : ∑ S : Finset (Fin m), (∑ x, w x * charFn S x)^2 =
      ∑ S : Finset (Fin m), ∑ x, ∑ y, w x * w y * charFn S x * charFn S y := by
    apply Finset.sum_congr rfl
    intro S _
    rw [pow_two]
    have : (∑ x, w x * charFn S x) * (∑ y, w y * charFn S y) =
        ∑ x, ∑ y, w x * charFn S x * (w y * charFn S y) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    rw [this]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [H1]
  have H2 : (∑ S : Finset (Fin m), ∑ x, ∑ y, w x * w y * charFn S x * charFn S y) =
      ∑ x, ∑ y, ∑ S : Finset (Fin m), w x * w y * charFn S x * charFn S y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
  rw [H2]
  have H3 : (∑ x, ∑ y, ∑ S : Finset (Fin m), w x * w y * charFn S x * charFn S y) =
      ∑ x, ∑ y, w x * w y * ∑ S : Finset (Fin m), charFn S x * charFn S y := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    have h_assoc : ∀ S, w x * w y * charFn S x * charFn S y =
        (w x * w y) * (charFn S x * charFn S y) := by intro S; ring
    simp_rw [h_assoc]
    rw [←Finset.mul_sum]
  rw [H3]
  simp_rw [sum_charFn_charFn]
  have H4 : (∑ x, ∑ y, w x * w y * if x = y then (2:ℝ)^m else 0) =
      ∑ x, w x * w x * (2:ℝ)^m := by
    apply Finset.sum_congr rfl
    intro x _
    have eq1 : (∑ y, w x * w y * if x = y then (2:ℝ)^m else 0) =
        w x * w x * (2:ℝ)^m := by
      have : (∑ y, w x * w y * if x = y then (2:ℝ)^m else 0) =
          ∑ y, if y = x then w x * w x * (2:ℝ)^m else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        have hyx : x = y ↔ y = x := eq_comm
        by_cases h : y = x
        · rw [if_pos h, if_pos (hyx.mpr h)]
          have : y = x := h
          subst this
          rfl
        · rw [if_neg h, if_neg (hyx.not.mpr h)]
          ring
      rw [this]
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy
        simp [hy]
      · intro hx
        exfalso
        apply hx
        simp
    rw [eq1]
  rw [H4]
  have H5 : (∑ x, w x * w x * (2:ℝ)^m) = (2:ℝ)^m * ∑ x, (w x)^2 := by
    have eq2 : (∑ x, w x * w x * (2:ℝ)^m) = ∑ x, (2:ℝ)^m * (w x)^2 := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [eq2, ←Finset.mul_sum]
  rw [H5]

theorem specNorm_signMatrix_distThreshold_le {m : ℕ} (hm : Odd m) :
    specNorm (signMatrix m m (distThreshold m)) ≤
      2 * ((m - 1).choose ((m - 1) / 2)) := by
  let C : ℝ := 2 * ((m - 1).choose ((m - 1) / 2))
  have hC : 0 ≤ C := by positivity
  let M := signMatrix m m (distThreshold m)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  let w : (Fin m → Bool) → ℝ := fun x => v x
  have hv : ‖v‖^2 = ∑ x, (w x)^2 := EuclideanSpace.real_norm_sq_eq v
  let Mv : (Fin m → Bool) → ℝ := fun x => (Matrix.mulVec M w) x
  have hMv : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M v‖^2 = ∑ x, (Mv x)^2 := by
    have : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M v‖^2 =
        ∑ x, ((Matrix.toEuclideanCLM (𝕜 := ℝ) M v) x)^2 :=
      EuclideanSpace.real_norm_sq_eq _
    rw [this]
    rfl

  have hMv_S : ∀ S : Finset (Fin m), ∑ x, Mv x * charFn S x =
      (∑ u, distSign m u * charFn S u) * ∑ y, w y * charFn S y := by
    intro S
    have eq1 : ∑ x, Mv x * charFn S x = ∑ x, (∑ y, M x y * w y) * charFn S x := rfl
    rw [eq1]
    have eq2 : (∑ x, (∑ y, M x y * w y) * charFn S x) =
        ∑ x, ∑ y, M y x * w y * charFn S x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      have : M x y = M y x := M_symm x y
      rw [this]
    rw [eq2]
    have eq3 : (∑ x, ∑ y, M y x * w y * charFn S x) =
        ∑ y, ∑ x, M y x * w y * charFn S x := Finset.sum_comm
    rw [eq3]
    have eq4 : (∑ y, ∑ x, M y x * w y * charFn S x) =
        ∑ y, w y * ∑ x, M y x * charFn S x := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [eq4]
    have eq5 : (∑ y, w y * ∑ x, M y x * charFn S x) =
        ∑ y, w y * ((∑ u, distSign m u * charFn S u) * charFn S y) := by
      apply Finset.sum_congr rfl
      intro y _
      have : ∑ x, M y x * charFn S x = (Matrix.mulVec M (charFn S)) y := rfl
      rw [this, signMatrix_mulVec_charFn]
      rfl
    rw [eq5]
    have eq6 : (∑ y, w y * ((∑ u, distSign m u * charFn S u) * charFn S y)) =
        (∑ u, distSign m u * charFn S u) * ∑ y, w y * charFn S y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [eq6]
  have h_bound : ∑ S : Finset (Fin m), (∑ x, Mv x * charFn S x)^2 ≤
      C^2 * ∑ S : Finset (Fin m), (∑ y, w y * charFn S y)^2 := by
    calc ∑ S : Finset (Fin m), (∑ x, Mv x * charFn S x)^2
      _ = ∑ S : Finset (Fin m), ((∑ u, distSign m u * charFn S u) * ∑ y, w y * charFn S y)^2
        := by
        apply Finset.sum_congr rfl
        intro S _
        rw [hMv_S]
      _ = ∑ S : Finset (Fin m), (∑ u, distSign m u * charFn S u)^2 * (∑ y, w y * charFn S y)^2
        := by
        apply Finset.sum_congr rfl
        intro S _
        ring
      _ ≤ ∑ S : Finset (Fin m), C^2 * (∑ y, w y * charFn S y)^2 := by
        apply Finset.sum_le_sum
        intro S _
        apply mul_le_mul_of_nonneg_right
        · have hle := distEigenvalue_le hm S
          have hs1 : |∑ u, distSign m u * charFn S u| ≤ |C| := by
            rw [abs_of_nonneg hC]
            exact hle
          exact sq_le_sq.mpr hs1
        · positivity
      _ = C^2 * ∑ S : Finset (Fin m), (∑ y, w y * charFn S y)^2 := by
        rw [←Finset.mul_sum]
  have H_Mv_L2 := L2_ident Mv
  have H_w_L2 := L2_ident w
  rw [H_Mv_L2, H_w_L2] at h_bound
  have h2m : 0 < (2:ℝ)^m := by positivity
  have h_bound2 : (2:ℝ)^m * ∑ x, (Mv x)^2 ≤ (2:ℝ)^m * (C^2 * ∑ x, (w x)^2) := by
    calc (2:ℝ)^m * ∑ x, (Mv x)^2
      _ ≤ C^2 * ((2:ℝ)^m * ∑ x, (w x)^2) := h_bound
      _ = (2:ℝ)^m * (C^2 * ∑ x, (w x)^2) := by ring
  have h_bound3 : ∑ x, (Mv x)^2 ≤ C^2 * ∑ x, (w x)^2 :=
    le_of_mul_le_mul_left h_bound2 h2m
  rw [←hMv, ←hv] at h_bound3
  have h_bound4 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M v‖^2 ≤ (C * ‖v‖)^2 := by
    calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M v‖^2
      _ ≤ C^2 * ‖v‖^2 := h_bound3
      _ = (C * ‖v‖)^2 := by ring
  have h_nonneg : 0 ≤ C * ‖v‖ := by positivity
  have hs1 : Real.sqrt (‖Matrix.toEuclideanCLM (𝕜 := ℝ) M v‖^2) ≤
      Real.sqrt ((C * ‖v‖)^2) := Real.sqrt_le_sqrt h_bound4
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq h_nonneg] at hs1
  exact hs1


/-- **Level-1 spectral witness** (PROOFS.md P4.3): the singleton character is
a nonzero eigenvector with eigenvalue `-2 · C(m-1,(m-1)/2)`, so its norm ratio
gives the matching lower bound on the operator norm. -/
private theorem le_specNorm_signMatrix_distThreshold {m : ℕ} (hm : Odd m) :
    (2 : ℝ) * ((m - 1).choose ((m - 1) / 2)) ≤
      specNorm (signMatrix m m (distThreshold m)) := by
  have hm1 : 1 ≤ m := by
    have := Nat.odd_iff.mp hm
    omega
  let i : Fin m := ⟨0, hm1⟩
  let M := signMatrix m m (distThreshold m)
  let C : ℝ := 2 * ((m - 1).choose ((m - 1) / 2))
  let v : EuclideanSpace ℝ (Fin m → Bool) :=
    (WithLp.equiv 2 _).symm (charFn {i})
  have hv_ne : v ≠ 0 := by
    intro hv
    have hvf := congrArg (WithLp.equiv 2 ((Fin m → Bool) → ℝ)) hv
    have hv0 := congrFun hvf (fun _ => false)
    simp [v, charFn] at hv0
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have h_action : Matrix.toEuclideanCLM (𝕜 := ℝ) M v = (-C) • v := by
    dsimp [M, C]
    change (WithLp.equiv 2 _).symm
        (Matrix.mulVec (signMatrix m m (distThreshold m)) (charFn {i})) =
      (-((2 : ℝ) * ((m - 1).choose ((m - 1) / 2)))) •
        (WithLp.equiv 2 _).symm (charFn {i})
    rw [signMatrix_mulVec_charFn, distEigenvalue_singleton hm i]
    rfl
  have hop := ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) M) v
  rw [h_action, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ C)] at hop
  change C * ‖v‖ ≤ specNorm M * ‖v‖ at hop
  exact le_of_mul_le_mul_right hop hv_pos

/-- The two-block sign matrix of `F_m` is the XOR-pattern of `MAJ_m`; the
characters diagonalize it, the top eigenvalue sits at Fourier level `1`, and
equals `2 · C(m-1, (m-1)/2)`. -/
theorem specNorm_signMatrix_distThreshold {m : ℕ} (hm : Odd m) :
    specNorm (signMatrix m m (distThreshold m)) =
      2 * ((m - 1).choose ((m - 1) / 2)) := by
  exact le_antisymm (specNorm_signMatrix_distThreshold_le hm)
    (le_specNorm_signMatrix_distThreshold hm)

/-- Forster's lower bound instantiated on the family: `γ_m ≤ signRank`
(PROOFS.md P7.3).  Compose Forster's theorem `N ≤ signRank · specNorm` with the
spectral-norm value `specNorm = 2·C(m-1,(m-1)/2)` and `N = 2^m`, then divide by
the positive binomial. -/
theorem forsterRatio_le_signRank {m : ℕ} (hm : Odd m) :
    forsterRatio m ≤ (signRank (signMatrix m m (distThreshold m)) : ℝ) := by
  have hm1 : 1 ≤ m := by have := Nat.odd_iff.mp hm; omega
  set M := signMatrix m m (distThreshold m) with hMdef
  -- `M` is a ±1 matrix
  have hM : ∀ i j, M i j = 1 ∨ M i j = -1 := by
    intro i j
    rw [hMdef, signMatrix]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hforster := forster M hM
  -- `card (Fin m → Bool) = 2 ^ m`
  have hcard : (Fintype.card (Fin m → Bool) : ℝ) = 2 ^ m := by
    have : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
    rw [this]; push_cast; ring
  rw [hcard, specNorm_signMatrix_distThreshold hm] at hforster
  -- positivity of the central binomial
  set C : ℝ := ((m - 1).choose ((m - 1) / 2) : ℝ) with hCdef
  have hC : 0 < C := by
    rw [hCdef]
    exact_mod_cast Nat.choose_pos (Nat.div_le_self _ _)
  -- `2 ^ m = 2 * 2 ^ (m - 1)`
  have h2m : (2 : ℝ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [mul_comm, ← pow_succ]
    congr 1
    omega
  rw [forsterRatio, div_le_iff₀ hC]
  -- goal: 2 ^ (m - 1) ≤ signRank M * C
  have hmul : (signRank M : ℝ) * (2 * C) = 2 * ((signRank M : ℝ) * C) := by ring
  rw [hmul] at hforster
  nlinarith [hforster, h2m]

/-- **Theorem A** (`audit/sources/EXPLICIT_GAP.md`): the family `F_m` has threshold
degree `2` while `γ_m ≤ 2 ^ (H* + 1) - 2`, hence
`H*(F_m) ≥ log₂(γ_m + 2) - 1 = (1/2) log₂ m - O(1)` grows without bound at
constant degree. -/
theorem theoremA {m : ℕ} (hm : Odd m) :
    thresholdDeg (distThreshold m) = 2 ∧
      forsterRatio m ≤ (2 : ℝ) ^ (HStar (m + m) (distThreshold m) + 1) - 2 := by
  have hm1 : 1 ≤ m := by have := Nat.odd_iff.mp hm; omega
  refine ⟨thresholdDeg_distThreshold hm, ?_⟩
  -- Non-constancy of `F_m`: all-agree ↦ false, all-disagree ↦ true.
  have hz1 : distThreshold m (blockJoin (fun _ => true) (fun _ => false)) = true := by
    simp only [distThreshold, leftBits_blockJoin, rightBits_blockJoin]
    have hd : hammingDist (fun _ : Fin m => true) (fun _ : Fin m => false) = m := by
      unfold hammingDist
      rw [Finset.filter_true_of_mem (fun i _ => by simp)]
      simp
    rw [hd]
    simp only [decide_eq_true_eq]
    omega
  have hz0 : distThreshold m (blockJoin (fun _ => false) (fun _ => false)) = false := by
    simp only [distThreshold, leftBits_blockJoin, rightBits_blockJoin]
    have hd : hammingDist (fun _ : Fin m => false) (fun _ : Fin m => false) = 0 :=
      hammingDist_self _
    rw [hd]
    simp only [decide_eq_false_iff_not, not_le]
    omega
  have hH : 1 ≤ HStar (m + m) (distThreshold m) := by
    rcases Nat.eq_zero_or_pos (HStar (m + m) (distThreshold m)) with h0 | hpos
    · exfalso
      have hconst := (HStar_eq_zero_iff (distThreshold m)).mp h0
      have hcontra := hconst (blockJoin (fun _ => true) (fun _ => false))
        (blockJoin (fun _ => false) (fun _ => false))
      rw [hz1, hz0] at hcontra
      exact absurd hcontra (by decide)
    · exact hpos
  -- Sign-rank bridge, cast to `ℝ` (`H ≥ 1 ⇒ 2^(H+1) ≥ 2`).
  have hbridge := signRank_le_pow_HStar m m (distThreshold m) hH
  have h2 : (2 : ℕ) ≤ 2 ^ (HStar (m + m) (distThreshold m) + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (HStar (m + m) (distThreshold m) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcast : ((signRank (signMatrix m m (distThreshold m))) : ℝ)
      ≤ (2 : ℝ) ^ (HStar (m + m) (distThreshold m) + 1) - 2 := by
    have hc := (Nat.cast_le (α := ℝ)).mpr hbridge
    rw [Nat.cast_sub h2] at hc
    push_cast at hc
    exact hc
  exact (forsterRatio_le_signRank hm).trans hcast

/-- Central-binomial estimate (PROOFS.md P7.5): `2t · C(2t,t)² ≤ 16^t`.
Proved from the sharper decreasing invariant `(3t+1)·C(2t,t)² ≤ 16^t`
(equality at `t = 0`), whose inductive step uses
`(n+1)·C(2n+2,n+1) = 2(2n+1)·C(2n,n)` and the polynomial identity
`16(n+1)²(3n+1) = 4(3n+4)(2n+1)² + 4n`. -/
theorem two_mul_centralBinom_sq_le (t : ℕ) :
    2 * t * (Nat.centralBinom t) ^ 2 ≤ 16 ^ t := by
  have key : ∀ n : ℕ, (3 * n + 1) * (Nat.centralBinom n) ^ 2 ≤ 16 ^ n := by
    intro n
    induction n with
    | zero => simp [Nat.centralBinom_zero]
    | succ n ih =>
      have hrec := Nat.succ_mul_centralBinom_succ n
      have hpoly : (3 * n + 4) * 4 * (2 * n + 1) ^ 2 ≤ 16 * (n + 1) ^ 2 * (3 * n + 1) := by
        have hid : 16 * (n + 1) ^ 2 * (3 * n + 1)
            = (3 * n + 4) * 4 * (2 * n + 1) ^ 2 + 4 * n := by ring
        rw [hid]; exact Nat.le_add_right _ _
      have hstep : (n + 1) ^ 2 * ((3 * (n + 1) + 1) * (Nat.centralBinom (n + 1)) ^ 2)
          ≤ (n + 1) ^ 2 * 16 ^ (n + 1) := by
        have e1 : (n + 1) ^ 2 * ((3 * (n + 1) + 1) * (Nat.centralBinom (n + 1)) ^ 2)
            = (3 * n + 4) * ((n + 1) * Nat.centralBinom (n + 1)) ^ 2 := by ring
        rw [e1, hrec]
        have e2 : (3 * n + 4) * (2 * (2 * n + 1) * Nat.centralBinom n) ^ 2
            = ((3 * n + 4) * 4 * (2 * n + 1) ^ 2) * (Nat.centralBinom n) ^ 2 := by ring
        rw [e2]
        calc ((3 * n + 4) * 4 * (2 * n + 1) ^ 2) * (Nat.centralBinom n) ^ 2
            ≤ (16 * (n + 1) ^ 2 * (3 * n + 1)) * (Nat.centralBinom n) ^ 2 :=
              mul_le_mul_left hpoly _
          _ = (n + 1) ^ 2 * 16 * ((3 * n + 1) * (Nat.centralBinom n) ^ 2) := by ring
          _ ≤ (n + 1) ^ 2 * 16 * 16 ^ n := mul_le_mul_right ih _
          _ = (n + 1) ^ 2 * 16 ^ (n + 1) := by rw [pow_succ]; ring
      exact Nat.le_of_mul_le_mul_left hstep (by positivity)
  calc 2 * t * (Nat.centralBinom t) ^ 2 ≤ (3 * t + 1) * (Nat.centralBinom t) ^ 2 :=
        mul_le_mul_left (by omega) _
    _ ≤ 16 ^ t := key t

/-- Quantitative growth of the Forster ratio: `γ_m ≥ √(m - 1)` for odd
`m ≥ 3` (central binomial estimate).  PROOFS.md P7.5. -/
theorem sqrt_le_forsterRatio {m : ℕ} (hm : Odd m) (h3 : 3 ≤ m) :
    Real.sqrt ((m : ℝ) - 1) ≤ forsterRatio m := by
  obtain ⟨t, rfl⟩ := hm
  have hexp : forsterRatio (2 * t + 1) = (4 : ℝ) ^ t / (Nat.centralBinom t : ℝ) := by
    rw [forsterRatio]
    congr 1
    · rw [show 2 * t + 1 - 1 = 2 * t by omega, pow_mul]; norm_num
    · rw [show 2 * t + 1 - 1 = 2 * t by omega, show 2 * t / 2 = t by omega,
        Nat.centralBinom_eq_two_mul_choose]
  rw [hexp]
  have hcast : ((2 * t + 1 : ℕ) : ℝ) - 1 = 2 * (t : ℝ) := by push_cast; ring
  rw [hcast]
  set cb : ℝ := (Nat.centralBinom t : ℝ) with hcb
  have hcbpos : (0 : ℝ) < cb := by rw [hcb]; exact_mod_cast Nat.centralBinom_pos t
  have hy : (0 : ℝ) ≤ (4 : ℝ) ^ t / cb := by positivity
  have hNatR : 2 * (t : ℝ) * cb ^ 2 ≤ (16 : ℝ) ^ t := by
    have h := two_mul_centralBinom_sq_le t
    rw [hcb]
    calc 2 * (t : ℝ) * ((Nat.centralBinom t : ℝ)) ^ 2
        = ((2 * t * (Nat.centralBinom t) ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((16 ^ t : ℕ) : ℝ) := by exact_mod_cast h
      _ = (16 : ℝ) ^ t := by push_cast; ring
  have hkey2 : 2 * (t : ℝ) ≤ ((4 : ℝ) ^ t / cb) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity : (0 : ℝ) < cb ^ 2)]
    calc 2 * (t : ℝ) * cb ^ 2 ≤ (16 : ℝ) ^ t := hNatR
      _ = ((4 : ℝ) ^ t) ^ 2 := by rw [← pow_mul, mul_comm t 2, pow_mul]; norm_num
  calc Real.sqrt (2 * (t : ℝ))
      ≤ Real.sqrt (((4 : ℝ) ^ t / cb) ^ 2) := Real.sqrt_le_sqrt hkey2
    _ = (4 : ℝ) ^ t / cb := Real.sqrt_sq hy

/-- **Theorem A, explicit point**: at `m = 127` (254 input bits) the Forster
ratio exceeds `14 = 2^4 - 2`, so four heads are necessary — the first explicit
bound beyond the corpus's 3-head frontier.  (`m = 125` gives only `13.98`;
`127` is minimal for this route.) -/
theorem four_le_HStar_distThreshold_127 :
    4 ≤ HStar (127 + 127) (distThreshold 127) := by
  have hm : Odd 127 := by decide
  have hratio : (14 : ℝ) < forsterRatio 127 := by
    rw [forsterRatio]
    norm_num [Nat.choose]
  have hA := (theoremA hm).2
  by_contra h4
  have hH : HStar (127 + 127) (distThreshold 127) ≤ 3 := by omega
  have hp : (2 : ℝ) ^ (HStar (127 + 127) (distThreshold 127) + 1) ≤ 16 := by
    have hn : 2 ^ (HStar (127 + 127) (distThreshold 127) + 1) ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hn
  linarith

end HeadComplexity
