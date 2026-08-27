import HeadComplexity.TypicalLogCloseness.FixedTopologyWarren
import HeadComplexity.TypicalLogCloseness.POICSublevel

set_option linter.style.header false

/-!
# POIC₂ sublevel counting via Warren
-/

namespace HeadComplexity.TypicalLogCloseness

open MvPolynomial

/-- The H* normal form supplies a finite relaxed POIC₂ certificate for every truth table. -/
theorem relaxed_poic2_total (f : BoolFn n) : ∃ Q, HasCertificate n Q f :=
  exists_hasCertificate f

/-- Clearing the common positive denominator pool produces the fixed-topology
Warren model.  Coefficients of all affine numerators and denominators are the
continuous parameters; incidence data remain discrete. -/
theorem fixedTopology_warren_model (n : ℕ) (T : Topology) :
    Nonempty (FixedTopologyWarrenModel n T) :=
  fixedTopology_warren_model_helper n T

/-- Warren's theorem applied to the polynomial model of one fixed topology. -/
theorem FixedTopologyWarrenModel.pattern_card_le
    (M : FixedTopologyWarrenModel n T) :
    ((HeadComplexity.signPatterns M.polynomial).ncard : ℝ) ≤
      (8 * ((T.denominatorCount : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^
        (topologyParameterCount n T) :=
  HeadComplexity.warren_sign_patterns_weak M.polynomial M.degree_le

/-- The Warren sublevel estimate used by the abstract counting theorem. -/
theorem relaxed_poic2_sublevel_card_le (n Q : ℕ) (hn : 2 ≤ n)
    (hQ0 : 1 ≤ Q) (hQN : Q ≤ 2 ^ n) :
    (sublevel (RelaxedPOIC2 n) Q).card ≤ 2 ^ (64 * n ^ 2 * Q) :=
  relaxed_poic2_sublevel_card_le_helper n Q hn hQ0 hQN

end HeadComplexity.TypicalLogCloseness
