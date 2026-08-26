import HeadComplexity.TypicalLogCloseness.FracAtomBridge
import HeadComplexity.TypicalLogCloseness.AbstractCounting
import HeadComplexity.Separations.Warren

set_option linter.style.header false

/-!
# Fixed-topology Warren model decomposition

Decomposition of `fixedTopology_warren_model` into modular helper declarations.
-/

namespace HeadComplexity.TypicalLogCloseness

open MvPolynomial Finset

/-- Fixed-topology parameter count. -/
def topologyParameterCount (n : ℕ) (T : Topology) : ℕ :=
  (T.denominatorCount + T.termCount) * (n + 1)

/-- A fixed enumeration of the Boolean cube. -/
noncomputable def cubeIndexEquiv (n : ℕ) : Fin (2 ^ n) ≃ Cube n :=
  (Fintype.equivFinOfCardEq (by simp [Cube])).symm

/-- The exact interface between a fixed certificate topology and Warren:
the polynomials have the advertised degree and cover every strictly represented
truth table after the fixed cube reindexing. -/
structure FixedTopologyWarrenModel (n : ℕ) (T : Topology) where
  polynomial : Fin (2 ^ n) →
    MvPolynomial (Fin (topologyParameterCount n T)) ℝ
  degree_le : ∀ i, (polynomial i).totalDegree ≤ T.denominatorCount
  covers : ∀ (C : Certificate n T) (f : BoolFn n), C.Represents f →
    (fun i => f (cubeIndexEquiv n i)) ∈
      HeadComplexity.signPatterns polynomial

/-- Parametric coefficient index equivalence mapping variable indices in
`Fin (topologyParameterCount n T)` to denominator/numerator affine coefficients. -/
def paramIndexEquiv (n : ℕ) (T : Topology) :
    Fin (topologyParameterCount n T) ≃
      ((Fin T.denominatorCount × Fin (n + 1)) ⊕ (Fin T.termCount × Fin (n + 1))) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr finSumFinEquiv.symm (Equiv.refl (Fin (n + 1)))).trans
      (Equiv.sumProdDistrib (Fin T.denominatorCount) (Fin T.termCount) (Fin (n + 1))))

/-- Converts certificate denominator and numerator coefficients into an evaluation point
in parameter space `Fin (topologyParameterCount n T) → ℝ`. -/
noncomputable def certToPoint (n : ℕ) (T : Topology) (C : Certificate n T) :
    Fin (topologyParameterCount n T) → ℝ :=
  fun idx =>
    match paramIndexEquiv n T idx with
    | Sum.inl (j, c) => Fin.cases (C.denominators j).constant (C.denominators j).linear c
    | Sum.inr (t, c) => Fin.cases (C.numerators t).constant (C.numerators t).linear c

/-- Affine polynomial in parameter space representing a denominator evaluation on `x`. -/
noncomputable def denomMvPoly (n : ℕ) (T : Topology) (j : Fin T.denominatorCount)
    (x : Cube n) : MvPolynomial (Fin (topologyParameterCount n T)) ℝ :=
  X ((paramIndexEquiv n T).symm (Sum.inl (j, 0))) +
    ∑ i : Fin n, X ((paramIndexEquiv n T).symm (Sum.inl (j, i.succ))) * C (bitReal (x i))

/-- Affine polynomial in parameter space representing a numerator evaluation on `x`. -/
noncomputable def numMvPoly (n : ℕ) (T : Topology) (t : Fin T.termCount)
    (x : Cube n) : MvPolynomial (Fin (topologyParameterCount n T)) ℝ :=
  X ((paramIndexEquiv n T).symm (Sum.inr (t, 0))) +
  ∑ i : Fin n, X ((paramIndexEquiv n T).symm (Sum.inr (t, i.succ))) * C (bitReal (x i))

/-- Evaluation identity for denominator polynomial in parameter space. -/
theorem denomMvPoly_eval (n : ℕ) (T : Topology) (C : Certificate n T)
    (j : Fin T.denominatorCount) (x : Cube n) :
    eval (certToPoint n T C) (denomMvPoly n T j x) = (C.denominators j).eval x := by
  sorry

/-- Evaluation identity for numerator polynomial in parameter space. -/
theorem numMvPoly_eval (n : ℕ) (T : Topology) (C : Certificate n T)
    (t : Fin T.termCount) (x : Cube n) :
    eval (certToPoint n T C) (numMvPoly n T t x) = (C.numerators t).eval x := by
  unfold numMvPoly certToPoint AffineForm.eval
  simp only [map_add, map_sum, map_mul, eval_X, eval_C, Equiv.apply_symm_apply]
  rfl

private theorem totalDegree_X_le {σ : Type*} (v : σ) :
    (X v : MvPolynomial σ ℝ).totalDegree ≤ 1 := by
  rw [totalDegree_X]

private theorem totalDegree_X_mul_C_le {σ : Type*} (v : σ) (c : ℝ) :
    (X v * C c : MvPolynomial σ ℝ).totalDegree ≤ 1 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X, totalDegree_C, add_zero]

private theorem totalDegree_X_le {σ : Type*} (v : σ) :
    (X v : MvPolynomial σ ℝ).totalDegree ≤ 1 := by
  rw [totalDegree_X]

private theorem totalDegree_X_mul_C_le {σ : Type*} (v : σ) (c : ℝ) :
    (X v * C c : MvPolynomial σ ℝ).totalDegree ≤ 1 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X, totalDegree_C, add_zero]

private theorem totalDegree_sum_X_mul_C_le {ι σ : Type*} (s : Finset ι) (v : ι → σ) (c : ι → ℝ) :
    (∑ i ∈ s, X (v i) * C (c i) : MvPolynomial σ ℝ).totalDegree ≤ 1 := by
  classical
  exact totalDegree_finsetSum_le (fun i _ => totalDegree_X_mul_C_le (v i) (c i))

/-- Total degree of denominator MvPolynomial is at most 1. -/
theorem denomMvPoly_totalDegree_le (n : ℕ) (T : Topology)
    (j : Fin T.denominatorCount) (x : Cube n) :
    (denomMvPoly n T j x).totalDegree ≤ 1 := by
  unfold denomMvPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact totalDegree_X_le _
  · refine totalDegree_finsetSum_le (fun i _ => ?_)
    exact totalDegree_X_mul_C_le _ _

/-- Total degree of numerator MvPolynomial is at most 1. -/
theorem numMvPoly_totalDegree_le (n : ℕ) (T : Topology)
    (t : Fin T.termCount) (x : Cube n) :
    (numMvPoly n T t x).totalDegree ≤ 1 := by
  unfold numMvPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact totalDegree_X_le _
  · exact totalDegree_sum_X_mul_C_le _ _ _

/-- Cleared term polynomial multiplying the numerator by missing denominators. -/
noncomputable def clearedTermMvPoly (n : ℕ) (T : Topology) (t : Fin T.termCount)
    (x : Cube n) : MvPolynomial (Fin (topologyParameterCount n T)) ℝ :=
  numMvPoly n T t x * ∏ j ∈ Finset.univ \ (T.incidence t).denoms, denomMvPoly n T j x

/-- Cleared score polynomial representing the cleared common denominator sum for `x`. -/
noncomputable def clearedScoreMvPoly (n : ℕ) (T : Topology) (x : Cube n) :
    MvPolynomial (Fin (topologyParameterCount n T)) ℝ :=
  ∑ t, clearedTermMvPoly n T t x

private theorem certToPoint_inl (n : ℕ) (T : Topology) (C : Certificate n T)
    (j : Fin T.denominatorCount) (c : Fin (n + 1)) :
    certToPoint n T C ((paramIndexEquiv n T).symm (Sum.inl (j, c))) =
      Fin.cases (C.denominators j).constant (C.denominators j).linear c := by
  unfold certToPoint
  rw [Equiv.apply_symm_apply]

private theorem certToPoint_inr (n : ℕ) (T : Topology) (C : Certificate n T)
    (t : Fin T.termCount) (c : Fin (n + 1)) :
    certToPoint n T C ((paramIndexEquiv n T).symm (Sum.inr (t, c))) =
      Fin.cases (C.numerators t).constant (C.numerators t).linear c := by
  unfold certToPoint
  rw [Equiv.apply_symm_apply]

private theorem denomMvPoly_eval_private (n : ℕ) (T : Topology) (C : Certificate n T)
    (j : Fin T.denominatorCount) (x : Cube n) :
    eval (certToPoint n T C) (denomMvPoly n T j x) = (C.denominators j).eval x := by
  unfold denomMvPoly AffineForm.eval
  simp only [eval_add, eval_X, eval_sum, eval_mul, eval_C]
  rw [certToPoint_inl n T C j 0]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [certToPoint_inl n T C j i.succ]
  rfl

private theorem numMvPoly_eval_private (n : ℕ) (T : Topology) (C : Certificate n T)
    (t : Fin T.termCount) (x : Cube n) :
    eval (certToPoint n T C) (numMvPoly n T t x) = (C.numerators t).eval x := by
  unfold numMvPoly AffineForm.eval
  simp only [eval_add, eval_X, eval_sum, eval_mul, eval_C]
  rw [certToPoint_inr n T C t 0]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [certToPoint_inr n T C t i.succ]
  rfl

private theorem clearedTermMvPoly_eval (n : ℕ) (T : Topology) (C : Certificate n T)
    (t : Fin T.termCount) (x : Cube n) :
    eval (certToPoint n T C) (clearedTermMvPoly n T t x) =
      (C.numerators t).eval x *
        ∏ j ∈ Finset.univ \ (T.incidence t).denoms, (C.denominators j).eval x := by
  unfold clearedTermMvPoly
  simp only [eval_mul, eval_prod, numMvPoly_eval_private, denomMvPoly_eval_private]

/-- Evaluation identity for the cleared score polynomial. -/
theorem clearedScoreMvPoly_eval (n : ℕ) (T : Topology) (C : Certificate n T)
    (x : Cube n) :
    eval (certToPoint n T C) (clearedScoreMvPoly n T x) =
      C.eval x * ∏ j, (C.denominators j).eval x := by
  unfold clearedScoreMvPoly Certificate.eval
  rw [eval_sum]
  simp_rw [clearedTermMvPoly_eval]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  have hsplit : (∏ j : Fin T.denominatorCount, (C.denominators j).eval x) =
      C.termDenominator t x *
        ∏ j ∈ (Finset.univ : Finset (Fin T.denominatorCount)) \ (T.incidence t).denoms,
          (C.denominators j).eval x := by
    unfold Certificate.termDenominator
    rw [← Finset.prod_sdiff
      (s₁ := (T.incidence t).denoms) (s₂ := Finset.univ) (Finset.subset_univ _)]
    ring
  rw [hsplit, ← mul_assoc]
  have hne : C.termDenominator t x ≠ 0 := (C.termDenominator_pos t x).ne'
  rw [div_mul_cancel₀ _ hne]

private theorem denomMvPoly_totalDegree_le' (n : ℕ) (T : Topology)
    (j : Fin T.denominatorCount) (x : Cube n) :
    (denomMvPoly n T j x).totalDegree ≤ 1 := by
  unfold denomMvPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]
  · refine totalDegree_finsetSum_le (fun i _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, totalDegree_C, add_zero]

private theorem numMvPoly_totalDegree_le' (n : ℕ) (T : Topology)
    (t : Fin T.termCount) (x : Cube n) :
    (numMvPoly n T t x).totalDegree ≤ 1 := by
  unfold numMvPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]
  · refine totalDegree_finsetSum_le (fun i _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, totalDegree_C, add_zero]

private theorem denomMvPoly_prod_totalDegree_le' {ι : Type*} (s : Finset ι) (n : ℕ)
    (T : Topology) (g : ι → Fin T.denominatorCount) (x : Cube n) :
    (∏ j ∈ s, denomMvPoly n T (g j) x).totalDegree ≤ s.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1
    (fun j _ => denomMvPoly_totalDegree_le' n T (g j) x)).trans ?_
  rw [smul_eq_mul, mul_one]

private theorem clearedTermMvPoly_totalDegree_le' (n : ℕ) (T : Topology)
    (t : Fin T.termCount) (x : Cube n) :
    (clearedTermMvPoly n T t x).totalDegree ≤ T.denominatorCount := by
  unfold clearedTermMvPoly
  refine (totalDegree_mul _ _).trans ?_
  have hnum := numMvPoly_totalDegree_le' n T t x
  have hprod := denomMvPoly_prod_totalDegree_le'
    (Finset.univ \ (T.incidence t).denoms) n T id x
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

/-- Total degree of cleared score polynomial is at most `T.denominatorCount` using
nonempty incidence data. -/
theorem clearedScoreMvPoly_totalDegree_le (n : ℕ) (T : Topology) (x : Cube n) :
    (clearedScoreMvPoly n T x).totalDegree ≤ T.denominatorCount := by
  unfold clearedScoreMvPoly
  refine totalDegree_finsetSum_le (fun t _ => ?_)
  exact clearedTermMvPoly_totalDegree_le' n T t x

/-- Strict sign equivalence between cleared score evaluation and truth table `f x`. -/
theorem strict_sign_transfer (n : ℕ) (T : Topology) (C : Certificate n T)
    (f : BoolFn n) (hC : C.Represents f) (x : Cube n) :
    decide (0 < eval (certToPoint n T C) (clearedScoreMvPoly n T x)) = f x := by
  rw [clearedScoreMvPoly_eval]
  have hprod : 0 < ∏ j, (C.denominators j).eval x :=
    Finset.prod_pos (fun j _ => (C.denominators j).eval_pos (C.legal j) x)
  cases hfx : f x
  · have hneg : C.eval x < 0 := (hC x).2 hfx
    have hneg2 : C.eval x * ∏ j, (C.denominators j).eval x < 0 :=
      mul_neg_of_neg_of_pos hneg hprod
    have hnot : ¬ 0 < C.eval x * ∏ j, (C.denominators j).eval x := by linarith
    simp [hnot]
  · have hpos : 0 < C.eval x := (hC x).1 hfx
    have hpos2 : 0 < C.eval x * ∏ j, (C.denominators j).eval x :=
      mul_pos hpos hprod
    simp [hpos2]

/-- Packaging helper: constructs a `FixedTopologyWarrenModel n T`. -/
theorem fixedTopology_warren_model_helper (n : ℕ) (T : Topology) :
    Nonempty (FixedTopologyWarrenModel n T) := by
  refine ⟨⟨fun i => clearedScoreMvPoly n T (cubeIndexEquiv n i), ?_, ?_⟩⟩
  · intro i
    exact clearedScoreMvPoly_totalDegree_le n T (cubeIndexEquiv n i)
  · intro C f hC
    simp only [HeadComplexity.signPatterns, Set.mem_setOf_eq]
    use certToPoint n T C
    refine ⟨fun i => ?_, fun i => (strict_sign_transfer n T C f hC (cubeIndexEquiv n i)).symm⟩
    rw [clearedScoreMvPoly_eval]
    apply mul_ne_zero
    · exact Certificate.eval_ne_zero_of_represents hC _
    · apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact (C.denominators j).eval_pos (C.legal j) _ |>.ne'

end HeadComplexity.TypicalLogCloseness
