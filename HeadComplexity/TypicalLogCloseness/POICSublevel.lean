import HeadComplexity.TypicalLogCloseness.FixedTopologyWarren

set_option linter.style.header false

/-!
# POIC₂ sublevel counting helper declarations

Decomposition of `poic2_sublevel_card_le` into modular helper declarations.
-/

namespace HeadComplexity.TypicalLogCloseness

open Finset

/-- Safe padded overcount of all labeled singleton/doubleton topologies. -/
def topologyCountBound (Q : ℕ) : ℕ :=
  (Q + 1) ^ 2 * (Q ^ 2 + Q + 1) ^ Q

/-- Bundled finite record of a topology with bounded score at most `Q`. -/
structure BoundedTopology (Q : ℕ) where
  denominatorCount : ℕ
  termCount : ℕ
  incidence : Fin termCount → Incidence denominatorCount
  score_le : max denominatorCount termCount ≤ Q

private noncomputable instance incidenceFintype (s : ℕ) : Fintype (Incidence s) :=
  Fintype.ofInjective (fun inc => inc.denoms) (fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => by cases h; rfl)

private def toTarget (Q : ℕ) (bt : BoundedTopology Q) :
    (d : Fin (Q + 1)) × (t : Fin (Q + 1)) × (Fin t.val → Incidence d.val) :=
  ⟨⟨bt.denominatorCount, Nat.lt_succ_of_le (le_trans (le_max_left _ _) bt.score_le)⟩,
   ⟨bt.termCount, Nat.lt_succ_of_le (le_trans (le_max_right _ _) bt.score_le)⟩,
   bt.incidence⟩

private theorem toTarget_inj (Q : ℕ) : Function.Injective (toTarget Q) := by
  rintro ⟨d1, t1, i1, s1⟩ ⟨d2, t2, i2, s2⟩ h
  dsimp [toTarget] at h
  injection h with hd hrest
  have hd_val : d1 = d2 := Fin.ext_iff.mp hd
  subst hd_val
  injection hrest with ht hi
  have ht_val : t1 = t2 := Fin.ext_iff.mp ht
  subst ht_val
  have hi_eq : i1 = i2 := eq_of_heq hi
  subst hi_eq
  rfl

/-- Fintype instance for `BoundedTopology Q`. -/
noncomputable instance boundedTopologyFintype (Q : ℕ) : Fintype (BoundedTopology Q) :=
  Fintype.ofInjective (toTarget Q) (toTarget_inj Q)

/-- Cardinality of `BoundedTopology Q` is bounded by `topologyCountBound Q`. -/
theorem boundedTopology_card_le (Q : ℕ) :
    Fintype.card (BoundedTopology Q) ≤ topologyCountBound Q := by
  sorry

/-- Cube index reindexing maps representable truth tables injectively into sign patterns. -/
theorem cubeIndexEquiv_inj (n : ℕ) :
    Function.Injective (fun (f : BoolFn n) (i : Fin (2 ^ n)) => f (cubeIndexEquiv n i)) := by
  intro f g h
  ext x
  have h_eq := congr_fun h ((cubeIndexEquiv n).symm x)
  simp only [(cubeIndexEquiv n).apply_symm_apply] at h_eq
  exact h_eq

/-- Represented truth tables embed into sign patterns of a `FixedTopologyWarrenModel`. -/
theorem represented_truthTables_embedding (n : ℕ) (T : Topology)
    (M : FixedTopologyWarrenModel n T) :
    ∃ (S : Finset (BoolFn n)),
      (∀ f, f ∈ S ↔ ∃ C : Certificate n T, C.Represents f) ∧
      S.card ≤ (HeadComplexity.signPatterns M.polynomial).ncard := by
  sorry

/-- Real-to-Nat rounding bound for Warren sign pattern card bound. -/
theorem warren_pattern_card_nat_le (n : ℕ) (T : Topology) (M : FixedTopologyWarrenModel n T) :
    (HeadComplexity.signPatterns M.polynomial).ncard ≤
      Nat.floor ((8 * ((T.denominatorCount : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^
        (topologyParameterCount n T)) := by
  sorry

/-- Upper bound on denominatorCount and parameterCount when score is at most Q. -/
theorem topology_param_degree_le (n Q : ℕ) (T : Topology) (hT : T.score ≤ Q) :
    T.denominatorCount ≤ Q ∧ topologyParameterCount n T ≤ 2 * Q * (n + 1) := by
  sorry

/-- Cardinality of truth tables representable by one topology `T` with score at most `Q`. -/
theorem truthTables_per_topology_card_le (n Q : ℕ) (T : Topology) (hT : T.score ≤ Q) :
    haveI : DecidablePred (fun (f : BoolFn n) => ∃ C : Certificate n T, C.Represents f) :=
      Classical.decPred _
    (Finset.univ.filter (fun (f : BoolFn n) => ∃ C : Certificate n T, C.Represents f)).card ≤
      Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) := by
  sorry

/-- The union bound estimate for non-constant certificates with score at most Q. -/
theorem nonconstant_sublevel_card_le (n Q : ℕ) (hn : 2 ≤ n) (hQ0 : 1 ≤ Q) (hQN : Q ≤ 2 ^ n) :
    haveI : DecidablePred (fun (f : BoolFn n) =>
      ∃ (T : Topology) (C : Certificate n T), T.score ≤ Q ∧ C.Represents f) :=
      Classical.decPred _
    (Finset.univ.filter (fun (f : BoolFn n) =>
      ∃ (T : Topology) (C : Certificate n T), T.score ≤ Q ∧ C.Represents f)).card ≤
        topologyCountBound Q *
          Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) := by
  sorry

/-- Constant truth tables sublevel cardinality bound. -/
theorem constant_sublevel_card_le (n : ℕ) :
    haveI : DecidablePred (fun (f : BoolFn n) => IsConstant f) := Classical.decPred _
    (Finset.univ.filter (fun (f : BoolFn n) => IsConstant f)).card ≤ 2 := by
  sorry

/-- Elementary exponential inequality 1: topology count in the scale needed by the
final sublevel estimate. -/
theorem exp_ineq_topologyCountBound (n Q : ℕ) (hn : 2 ≤ n) (hQ0 : 1 ≤ Q)
    (hQN : Q ≤ 2 ^ n) :
    (topologyCountBound Q : ℝ) ≤ 2 ^ (16 * n ^ 2 * Q) := by
  sorry

/-- Elementary exponential inequality 2: bound on Warren term per topology. -/
theorem exp_ineq_warrenTerm (n Q : ℕ) (hn : 2 ≤ n) (hQ0 : 1 ≤ Q) (hQN : Q ≤ 2 ^ n) :
    (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1)) ≤
      2 ^ (32 * n ^ 2 * Q) := by
  sorry

/-- Combination of exponential bounds into the padded 2^(64 * n^2 * Q) bound. -/
theorem sublevel_exp_bound_combination (n Q : ℕ) (hn : 2 ≤ n) (hQ0 : 1 ≤ Q) (hQN : Q ≤ 2 ^ n)
    (N : ℕ) (hN : (N : ℝ) ≤ 2 + (topologyCountBound Q : ℝ) *
      (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) :
    N ≤ 2 ^ (64 * n ^ 2 * Q) := by
  sorry

/-- Final sublevel packaging helper. -/
theorem poic2_sublevel_card_le_helper (n Q : ℕ) (hn : 2 ≤ n)
    (hQ0 : 1 ≤ Q) (hQN : Q ≤ 2 ^ n) :
    (sublevel (POIC2 n) Q).card ≤ 2 ^ (64 * n ^ 2 * Q) := by
  sorry

end HeadComplexity.TypicalLogCloseness
