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
  sorry

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

/-- The level-`0` eigenvalue vanishes (PROOFS.md P4.2, consequence 3):
`λ_∅ = ∑_u s(u) = 0` for odd `m`.  Proof: the complement involution `u ↦ ū`
is fixed-point-free (`m` odd) and flips the sign, `s(ū) = -s(u)` (exactly one of
`|u|, m - |u|` reaches `(m+1)/2`), so the sum cancels in pairs. -/
theorem distSign_sum_eq_zero {m : ℕ} (hm : Odd m) :
    ∑ u : Fin m → Bool, distSign m u = 0 := by
  sorry

/-- The two-block sign matrix of `F_m` is the XOR-pattern of `MAJ_m`; the
characters diagonalize it, the top eigenvalue sits at Fourier level `1`, and
equals `2 · C(m-1, (m-1)/2)`. -/
theorem specNorm_signMatrix_distThreshold {m : ℕ} (hm : Odd m) :
    specNorm (signMatrix m m (distThreshold m)) =
      2 * ((m - 1).choose ((m - 1) / 2)) := by
  sorry

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
