import HeadComplexity.Separations.EightBitHammingThreshold.Core

set_option linter.style.header false

/-!
# Eight-bit Hamming threshold: explicit three-head certificate
-/

namespace HeadComplexity

open Finset
open scoped BigOperators
open TypicalLogCloseness
open MvPolynomial
open EightBitInternal

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
  dsimp [integerAffine8, TypicalLogCloseness.AffineForm.eval, evalFormInt,
      TypicalLogCloseness.bitReal]
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
  cases z 0 <;> cases z 1 <;> cases z 2 <;> cases z 3 <;> cases z 4 <;> cases z 5 <;> cases z 6
      <;> cases z 7
  all_goals
    dsimp [f8ClearedScoreInt, evalFormInt, boolSignInt, f8, distThreshold, hammingDist,
        leftBits, rightBits]
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

end HeadComplexity
