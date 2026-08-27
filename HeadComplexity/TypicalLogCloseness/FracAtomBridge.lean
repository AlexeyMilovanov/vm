import HeadComplexity.TypicalLogCloseness.POIC
import HeadComplexity.Results.FractionalNormalForm

set_option linter.style.header false

/-!
# Bridge from H* fractional atoms to POIC₂

The first part of this file is an exact algebraic normalization: every
`FracAtom` is a quotient of two affine forms and its denominator is strictly
positive on the cube.  The final bridge also absorbs the free global bias and
uses a finite-cube perturbation to make all signs strict.
-/

namespace HeadComplexity.TypicalLogCloseness

open Finset
open scoped BigOperators

/-- Affine denominator underlying a one-head fractional atom. -/
def fracDenominator (φ : HeadComplexity.FracAtom n) : AffineForm n where
  constant := φ.γ + ∑ i, φ.ρ i
  linear i := φ.ρ i * (φ.α - 1)

/-- Affine numerator underlying a one-head fractional atom. -/
def fracNumerator (φ : HeadComplexity.FracAtom n) : AffineForm n where
  constant := φ.η + ∑ i, φ.ρ i * φ.m i
  linear i := φ.ρ i * (φ.α * (φ.m i + φ.δ) - φ.m i)

private theorem wt_affine (φ : HeadComplexity.FracAtom n) (x : Cube n)
    (i : Fin n) :
    φ.wt x i =
      φ.ρ i + φ.ρ i * (φ.α - 1) * bitReal (x i) := by
  cases hx : x i <;> simp [HeadComplexity.FracAtom.wt, bitReal, hx] <;> ring

private theorem numerator_summand_affine
    (φ : HeadComplexity.FracAtom n) (x : Cube n) (i : Fin n) :
    φ.wt x i * (φ.m i + (if x i then φ.δ else 0)) =
      φ.ρ i * φ.m i +
        (φ.ρ i * (φ.α * (φ.m i + φ.δ) - φ.m i)) * bitReal (x i) := by
  cases hx : x i <;>
    simp [HeadComplexity.FracAtom.wt, bitReal, hx] <;> ring

@[simp] theorem fracDenominator_eval (φ : HeadComplexity.FracAtom n)
    (x : Cube n) :
    (fracDenominator φ).eval x = φ.γ + ∑ i, φ.wt x i := by
  simp only [AffineForm.eval, fracDenominator]
  simp_rw [wt_affine φ x]
  rw [Finset.sum_add_distrib]
  ring

@[simp] theorem fracNumerator_eval (φ : HeadComplexity.FracAtom n)
    (x : Cube n) :
    (fracNumerator φ).eval x =
      φ.η + ∑ i, φ.wt x i *
        (φ.m i + (if x i then φ.δ else 0)) := by
  simp only [AffineForm.eval, fracNumerator]
  simp_rw [numerator_summand_affine φ x]
  rw [Finset.sum_add_distrib]
  ring

theorem fracDenominator_strictLegal (φ : HeadComplexity.FracAtom n) :
    (fracDenominator φ).StrictLegal := by
  intro x
  rw [fracDenominator_eval]
  exact φ.denom_pos x

@[simp] theorem fracAtom_eval_eq_affine (φ : HeadComplexity.FracAtom n)
    (x : Cube n) :
    φ.eval x = (fracNumerator φ).eval x / (fracDenominator φ).eval x := by
  unfold HeadComplexity.FracAtom.eval
  rw [fracNumerator_eval, fracDenominator_eval]

/-- Conversely, an arbitrary affine numerator over a coefficientwise-positive
affine denominator is one fractional atom.  Choosing a sufficiently large
common `α` makes the residual `γ` positive. -/
theorem exists_fracAtom_eval_eq (A B : AffineForm n)
    (hB : B.PositiveCoefficients) :
    ∃ φ : HeadComplexity.FracAtom n,
      ∀ x, φ.eval x = A.eval x / B.eval x := by
  classical
  let S : ℝ := ∑ i, B.linear i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => (hB.2 i).le
  have hbc : 0 < B.constant := hB.1
  let d : ℝ := 1 + S / B.constant
  have hd : 0 < d := by
    dsimp [d]
    exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hS hbc.le)
  have hdcalc : B.constant * d = B.constant + S := by
    dsimp [d]
    field_simp [hbc.ne']
  have hγ : 0 < B.constant - S / d := by
    rw [sub_pos, div_lt_iff₀ hd]
    rw [hdcalc]
    linarith
  let φ : HeadComplexity.FracAtom n := {
    η := A.constant -
      ∑ i, (B.linear i / d) * (A.linear i / B.linear i)
    δ := 0
    γ := B.constant - S / d
    α := d + 1
    ρ i := B.linear i / d
    m i := A.linear i / B.linear i
    hγ := hγ
    hα := by linarith
    hρ i := div_pos (hB.2 i) hd
  }
  have hden : fracDenominator φ = B := by
    ext i
    · simp only [fracDenominator, φ]
      change B.constant - S / d + ∑ i, B.linear i / d = B.constant
      rw [← Finset.sum_div, show (∑ i, B.linear i) = S from rfl]
      ring
    · simp only [fracDenominator, φ]
      have hdn : d ≠ 0 := hd.ne'
      field_simp
      <;> ring
  have hnum : fracNumerator φ = A := by
    ext i
    · simp only [fracNumerator, φ]
      ring
    · simp only [fracNumerator, φ]
      have hdn : d ≠ 0 := hd.ne'
      have hlin : B.linear i ≠ 0 := (hB.2 i).ne'
      field_simp
      <;> ring
  refine ⟨φ, fun x => ?_⟩
  rw [fracAtom_eval_eq_affine, hden, hnum]

/-- Any explicit fractional representation bounds H*. -/
theorem HStar_le_of_fracComputable {H : ℕ} {f : BoolFn n}
    (h : HeadComplexity.fracComputable n H f) :
    HeadComplexity.HStar n f ≤ H := by
  classical
  rw [HeadComplexity.HStar_eq_Lfrac]
  unfold HeadComplexity.Lfrac
  have hex : ∃ k, HeadComplexity.fracComputable n k f := ⟨H, h⟩
  rw [dif_pos hex]
  exact Nat.find_min' hex h

private theorem exists_uniform_strict_margin
    (p : Cube n → Prop) (a : Cube n → ℝ)
    (ha : ∀ x, p x → 0 < a x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, p x → ε < a x := by
  classical
  let S : Finset ℝ := (Finset.univ.filter p).image a
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : 0 < m := by
      rw [Finset.lt_min'_iff]
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact ha x (Finset.mem_filter.mp hx).2
    refine ⟨m / 2, by positivity, ?_⟩
    intro x hpx
    have hmem : a x ∈ S := by
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hpx⟩, rfl⟩
    have hmin : m ≤ a x := Finset.min'_le S (a x) hmem
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hpx
    exfalso
    apply hS
    refine ⟨a x, ?_⟩
    exact Finset.mem_image.mpr
      ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hpx⟩, rfl⟩

/-- The exact H*→POIC₂ bridge.  The proof packages singleton incidences,
absorbs the global bias into one numerator when the atom family is nonempty,
and perturbs the bias on the finite cube so false vertices are strictly
negative without changing any true sign. -/
theorem fracComputable_hasCertificate {H : ℕ} {f : BoolFn n}
    (h : HeadComplexity.fracComputable n H f) :
    HasCertificate n H f := by
  classical
  rcases h with ⟨φ, c, hrep⟩
  by_cases hH : H = 0
  · subst H
    left
    by_cases hc : 0 < c
    · refine ⟨true, fun x => ?_⟩
      apply (hrep x).mp
      simpa using hc
    · refine ⟨false, fun x => ?_⟩
      cases hx : f x
      · rfl
      · exfalso
        apply hc
        have hs := (hrep x).mpr hx
        simpa using hs
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    let i0 : Fin H := ⟨0, hHpos⟩
    let score : Cube n → ℝ := fun x => c + ∑ t, (φ t).eval x
    have hscore : ∀ x, f x = true → 0 < score x := by
      intro x hx
      exact (hrep x).mpr hx
    obtain ⟨ε, hε, hmargin⟩ :=
      exists_uniform_strict_margin (fun x => f x = true) score hscore
    let shiftedBias : ℝ := c - ε
    let T : Topology := {
      denominatorCount := H
      termCount := H
      incidence t := {
        denoms := {t}
        nonempty := Finset.singleton_nonempty t
        card_le_two := by simp
      }
    }
    let C : Certificate n T := {
      denominators t := fracDenominator (φ t)
      numerators t :=
        (fracNumerator (φ t)).add
          ((fracDenominator (φ t)).smul
            (if t = i0 then shiftedBias else 0))
      legal t := fracDenominator_strictLegal (φ t)
    }
    have hEval : ∀ x, C.eval x = score x - ε := by
      intro x
      have hquot : ∀ t,
          (C.numerators t).eval x / C.termDenominator t x =
            (φ t).eval x + (if t = i0 then shiftedBias else 0) := by
        intro t
        have hden :
            C.termDenominator t x = (fracDenominator (φ t)).eval x := by
          simp [Certificate.termDenominator, C, T]
        rw [hden]
        simp only [C, AffineForm.eval_add, AffineForm.eval_smul,
          fracAtom_eval_eq_affine]
        have hnz := (fracDenominator_strictLegal (φ t) x).ne'
        field_simp
      unfold Certificate.eval
      rw [Finset.sum_congr rfl (fun t _ => hquot t)]
      rw [Finset.sum_add_distrib]
      simp [score, shiftedBias, i0]
      ring
    right
    refine ⟨T, C, ?_, ?_⟩
    · simp [T, Topology.score]
    · intro x
      constructor
      · intro hx
        rw [hEval]
        exact sub_pos.mpr (hmargin x hx)
      · intro hx
        rw [hEval]
        have hnonpos : score x ≤ 0 := by
          apply le_of_not_gt
          intro hpos
          have htrue : f x = true := (hrep x).mp hpos
          simp [hx] at htrue
        linarith

/-- Totality of the relaxed POIC₂ complexity follows from the established
finite H* normal form and the preceding bridge. -/
theorem exists_hasCertificate (f : BoolFn n) :
    ∃ Q, HasCertificate n Q f := by
  rcases HeadComplexity.exists_computable f with ⟨H, hH⟩
  refine ⟨H, fracComputable_hasCertificate ?_⟩
  exact (HeadComplexity.computableWithHeadsN_iff_fracComputable H f).mp hH

end HeadComplexity.TypicalLogCloseness
