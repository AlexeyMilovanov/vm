import HeadComplexity.TypicalLogCloseness.CanonicalPOIC
import HeadComplexity.Polynomial.ModelToPolynomial
import HeadComplexity.Separations.ThresholdDegAux

set_option linter.style.header false

/-!
# Threshold degree versus POIC₂

Clearing the common positive denominator pool of a relaxed POIC₂ certificate
gives a polynomial in the Boolean input variables.  Its degree is bounded by
the pool size, so this module supplies the missing left side of the canonical
comparison chain.
-/

namespace HeadComplexity.TypicalLogCloseness

open MvPolynomial Finset
open scoped BigOperators

variable {n : ℕ} {T : Topology}

/-- The polynomial in cube variables associated with an affine form. -/
noncomputable def AffineForm.toCubeMvPolynomial (L : AffineForm n) :
    MvPolynomial (Fin n) ℝ :=
  C L.constant + ∑ i, C (L.linear i) * X i

@[simp] theorem AffineForm.eval_toCubeMvPolynomial (L : AffineForm n) (x : Cube n) :
    MvPolynomial.eval (HeadComplexity.cubePoint x) L.toCubeMvPolynomial = L.eval x := by
  simp only [AffineForm.toCubeMvPolynomial, map_add, map_sum, map_mul, eval_C, eval_X,
    AffineForm.eval, HeadComplexity.cubePoint]
  congr 1

theorem AffineForm.totalDegree_toCubeMvPolynomial_le (L : AffineForm n) :
    L.toCubeMvPolynomial.totalDegree ≤ 1 := by
  unfold AffineForm.toCubeMvPolynomial
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_C]
    exact Nat.zero_le _
  · refine totalDegree_finsetSum_le (fun i _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X, Nat.zero_add]

/-- One numerator multiplied by every denominator absent from its incidence. -/
noncomputable def Certificate.clearedTermCubePolynomial (Crt : Certificate n T)
    (t : Fin T.termCount) : MvPolynomial (Fin n) ℝ :=
  (Crt.numerators t).toCubeMvPolynomial *
    ∏ j ∈ Finset.univ \ (T.incidence t).denoms,
      (Crt.denominators j).toCubeMvPolynomial

/-- The certificate score after clearing the common positive denominator. -/
noncomputable def Certificate.clearedCubePolynomial (Crt : Certificate n T) :
    MvPolynomial (Fin n) ℝ :=
  ∑ t, Crt.clearedTermCubePolynomial t

private theorem Certificate.eval_clearedTermCubePolynomial (Crt : Certificate n T)
    (t : Fin T.termCount) (x : Cube n) :
    MvPolynomial.eval (HeadComplexity.cubePoint x) (Crt.clearedTermCubePolynomial t) =
      (Crt.numerators t).eval x *
        ∏ j ∈ Finset.univ \ (T.incidence t).denoms, (Crt.denominators j).eval x := by
  simp [Certificate.clearedTermCubePolynomial]

/-- Evaluation after clearing denominators is the original rational score
times the product of the complete positive denominator pool. -/
theorem Certificate.eval_clearedCubePolynomial (Crt : Certificate n T) (x : Cube n) :
    MvPolynomial.eval (HeadComplexity.cubePoint x) Crt.clearedCubePolynomial =
      Crt.eval x * ∏ j, (Crt.denominators j).eval x := by
  unfold Certificate.clearedCubePolynomial Certificate.eval
  rw [map_sum]
  simp_rw [Certificate.eval_clearedTermCubePolynomial]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  have hsplit : (∏ j : Fin T.denominatorCount, (Crt.denominators j).eval x) =
      Crt.termDenominator t x *
        ∏ j ∈ (Finset.univ : Finset (Fin T.denominatorCount)) \ (T.incidence t).denoms,
          (Crt.denominators j).eval x := by
    unfold Certificate.termDenominator
    rw [← Finset.prod_sdiff (Finset.subset_univ _)]
    ring
  rw [hsplit, ← mul_assoc]
  have hne : Crt.termDenominator t x ≠ 0 := (Crt.termDenominator_pos t x).ne'
  rw [div_mul_cancel₀ _ hne]

private theorem Certificate.totalDegree_clearedTermCubePolynomial_le
    (Crt : Certificate n T) (t : Fin T.termCount) :
    (Crt.clearedTermCubePolynomial t).totalDegree ≤ T.denominatorCount := by
  unfold Certificate.clearedTermCubePolynomial
  refine (totalDegree_mul _ _).trans ?_
  have hnum : (Crt.numerators t).toCubeMvPolynomial.totalDegree ≤ 1 :=
    AffineForm.totalDegree_toCubeMvPolynomial_le _
  have hprod :
      (∏ j ∈ Finset.univ \ (T.incidence t).denoms,
        (Crt.denominators j).toCubeMvPolynomial).totalDegree ≤
      (Finset.univ \ (T.incidence t).denoms).card :=
    HeadComplexity.totalDegree_prod_le_card _ _
      (fun j => AffineForm.totalDegree_toCubeMvPolynomial_le _)
  have hsum := Nat.add_le_add hnum hprod
  refine hsum.trans ?_
  have hcard_pos : 1 ≤ (T.incidence t).denoms.card := (T.incidence t).nonempty.card_pos
  have hcard_le : (T.incidence t).denoms.card ≤ T.denominatorCount := by
    simpa using Finset.card_le_card (Finset.subset_univ (T.incidence t).denoms)
  have hsdiff : (Finset.univ \ (T.incidence t).denoms).card =
      T.denominatorCount - (T.incidence t).denoms.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  rw [hsdiff]
  omega

/-- Nonempty incidences make the cleared polynomial degree at most the size
of the shared denominator pool. -/
theorem Certificate.totalDegree_clearedCubePolynomial_le (Crt : Certificate n T) :
    Crt.clearedCubePolynomial.totalDegree ≤ T.denominatorCount := by
  unfold Certificate.clearedCubePolynomial
  exact totalDegree_finsetSum_le fun t _ =>
    Crt.totalDegree_clearedTermCubePolynomial_le t

/-- Clearing positive denominators preserves the represented strict sign. -/
theorem Certificate.clearedCubePolynomial_signRepresents
    (Crt : Certificate n T) {f : BoolFn n} (hC : Crt.Represents f) :
    HeadComplexity.SignRepresents Crt.clearedCubePolynomial f := by
  intro x
  rw [Crt.eval_clearedCubePolynomial]
  have hprod : 0 < ∏ j, (Crt.denominators j).eval x :=
    Finset.prod_pos fun j _ => (Crt.denominators j).eval_pos (Crt.legal j) x
  constructor
  · intro hpos
    cases hfx : f x
    · have hneg : Crt.eval x < 0 := (hC x).2 hfx
      have hcleared :
          Crt.eval x * ∏ j, (Crt.denominators j).eval x < 0 :=
        mul_neg_of_neg_of_pos hneg hprod
      linarith
    · rfl
  · intro hfx
    exact mul_pos ((hC x).1 hfx) hprod

private theorem thresholdDegLE_of_isConstant {Q : ℕ} {f : BoolFn n}
    (hf : IsConstant f) : HeadComplexity.ThresholdDegLE f Q := by
  rcases hf with ⟨b, hb⟩
  cases b
  · refine ⟨C (-1), ?_, ?_⟩
    · simp
    · intro x
      simp [hb x]
  · refine ⟨C 1, ?_, ?_⟩
    · simp
    · intro x
      simp [hb x]

/-- Every relaxed POIC₂ certificate of cost `Q` gives threshold degree at
most `Q`. -/
theorem thresholdDegLE_of_hasCertificate {Q : ℕ} {f : BoolFn n}
    (h : HasCertificate n Q f) : HeadComplexity.ThresholdDegLE f Q := by
  rcases h with hf | ⟨T, Crt, hscore, hrep⟩
  · exact thresholdDegLE_of_isConstant hf
  · refine HeadComplexity.ThresholdDegLE.mono
      ⟨Crt.clearedCubePolynomial, Crt.totalDegree_clearedCubePolynomial_le,
        Crt.clearedCubePolynomial_signRepresents hrep⟩ ?_
    exact (Nat.le_max_left _ _).trans hscore

/-- The stronger relaxed left bridge. -/
theorem thresholdDeg_le_relaxedPOIC2 (f : BoolFn n) :
    HeadComplexity.thresholdDeg f ≤ RelaxedPOIC2 n f := by
  apply HeadComplexity.thresholdDeg_le_of
  exact thresholdDegLE_of_hasCertificate
    (hasCertificate_at_relaxedPOIC2 (exists_hasCertificate f))

/-- The canonical left bridge requested by the POIC₂ sandwich. -/
theorem thresholdDeg_le_POIC2 (f : BoolFn n) :
    HeadComplexity.thresholdDeg f ≤ POIC2 n f :=
  (thresholdDeg_le_relaxedPOIC2 f).trans (relaxedPOIC2_le_POIC2 f)

/-- Complete canonical sandwich, retaining the stronger relaxed intermediate. -/
theorem thresholdDeg_le_relaxedPOIC2_le_POIC2_le_HStar (f : BoolFn n) :
    HeadComplexity.thresholdDeg f ≤ RelaxedPOIC2 n f ∧
      RelaxedPOIC2 n f ≤ POIC2 n f ∧
      POIC2 n f ≤ HeadComplexity.HStar n f :=
  ⟨thresholdDeg_le_relaxedPOIC2 f, relaxedPOIC2_le_POIC2 f, POIC2_le_HStar f⟩

end HeadComplexity.TypicalLogCloseness
