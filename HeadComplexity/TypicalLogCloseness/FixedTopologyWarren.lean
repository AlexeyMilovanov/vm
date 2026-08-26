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
  sorry

/-- Total degree of denominator MvPolynomial is at most 1. -/
theorem denomMvPoly_totalDegree_le (n : ℕ) (T : Topology)
    (j : Fin T.denominatorCount) (x : Cube n) :
    (denomMvPoly n T j x).totalDegree ≤ 1 := by
  sorry

/-- Total degree of numerator MvPolynomial is at most 1. -/
theorem numMvPoly_totalDegree_le (n : ℕ) (T : Topology)
    (t : Fin T.termCount) (x : Cube n) :
    (numMvPoly n T t x).totalDegree ≤ 1 := by
  sorry

/-- Cleared term polynomial multiplying the numerator by missing denominators. -/
noncomputable def clearedTermMvPoly (n : ℕ) (T : Topology) (t : Fin T.termCount)
    (x : Cube n) : MvPolynomial (Fin (topologyParameterCount n T)) ℝ :=
  numMvPoly n T t x * ∏ j ∈ Finset.univ \ (T.incidence t).denoms, denomMvPoly n T j x

/-- Cleared score polynomial representing the cleared common denominator sum for `x`. -/
noncomputable def clearedScoreMvPoly (n : ℕ) (T : Topology) (x : Cube n) :
    MvPolynomial (Fin (topologyParameterCount n T)) ℝ :=
  ∑ t, clearedTermMvPoly n T t x

/-- Evaluation identity for the cleared score polynomial. -/
theorem clearedScoreMvPoly_eval (n : ℕ) (T : Topology) (C : Certificate n T)
    (x : Cube n) :
    eval (certToPoint n T C) (clearedScoreMvPoly n T x) =
      C.eval x * ∏ j, (C.denominators j).eval x := by
  sorry

/-- Total degree of cleared score polynomial is at most `T.denominatorCount` using
nonempty incidence data. -/
theorem clearedScoreMvPoly_totalDegree_le (n : ℕ) (T : Topology) (x : Cube n) :
    (clearedScoreMvPoly n T x).totalDegree ≤ T.denominatorCount := by
  sorry

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
