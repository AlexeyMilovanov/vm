import HeadComplexity.TypicalLogCloseness.FracAtomBridge
import HeadComplexity.TypicalLogCloseness.AbstractCounting
import HeadComplexity.Separations.Warren

set_option linter.style.header false

/-!
# POIC₂ sublevel counting via Warren
-/

namespace HeadComplexity.TypicalLogCloseness

open MvPolynomial

/-- The H* normal form supplies a finite POIC₂ certificate for every truth table. -/
theorem poic2_total (f : BoolFn n) : ∃ Q, HasCertificate n Q f :=
  exists_hasCertificate f

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

/-- Clearing the common positive denominator pool produces the fixed-topology
Warren model.  Coefficients of all affine numerators and denominators are the
continuous parameters; incidence data remain discrete. -/
theorem fixedTopology_warren_model (n : ℕ) (T : Topology) :
    Nonempty (FixedTopologyWarrenModel n T) := by
  sorry

/-- Warren's theorem applied to the polynomial model of one fixed topology. -/
theorem FixedTopologyWarrenModel.pattern_card_le
    (M : FixedTopologyWarrenModel n T) :
    ((HeadComplexity.signPatterns M.polynomial).ncard : ℝ) ≤
      (8 * ((T.denominatorCount : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^
        (topologyParameterCount n T) :=
  HeadComplexity.warren_sign_patterns_weak M.polynomial M.degree_le

/-- Safe padded overcount of all labeled singleton/doubleton topologies. -/
def topologyCountBound (Q : ℕ) : ℕ :=
  (Q + 1) ^ 2 * (Q ^ 2 + Q + 1) ^ Q

/-- The Warren sublevel estimate used by the abstract counting theorem. -/
theorem poic2_sublevel_card_le (n Q : ℕ) (hn : 2 ≤ n)
    (hQ0 : 1 ≤ Q) (hQN : Q ≤ 2 ^ n) :
    (sublevel (POIC2 n) Q).card ≤ 2 ^ (64 * n ^ 2 * Q) := by
  sorry

end HeadComplexity.TypicalLogCloseness
