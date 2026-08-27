import HeadComplexity.TypicalLogCloseness.FixedTopologyWarren

set_option linter.style.header false

/-!
# POIC₂ sublevel counting helper declarations

Decomposition of `relaxed_poic2_sublevel_card_le` into modular helper declarations.
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

private abbrev TargetType (Q : ℕ) : Type :=
  (Fin (Q + 1) × Fin (Q + 1)) × (Fin Q → Fin (Q ^ 2 + Q + 1))

private theorem denoms_eq_of_min_max {s : ℕ} (d : Finset (Fin s)) (hne : d.Nonempty)
    (hle : d.card ≤ 2) : d = {d.min' hne, d.max' hne} := by
  ext x
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hx
    have h1 : d.min' hne ≤ x := min'_le d x hx
    have h2 : x ≤ d.max' hne := le_max' d x hx
    rcases le_iff_eq_or_lt.mp h1 with rfl | h1'
    · left; rfl
    · rcases le_iff_eq_or_lt.mp h2 with rfl | h2'
      · right; rfl
      · have h_min_x : d.min' hne ≠ x := ne_of_lt h1'
        have h_x_max : x ≠ d.max' hne := ne_of_lt h2'
        have h_min_max : d.min' hne ≠ d.max' hne := lt_trans h1' h2' |>.ne
        have hsub : {d.min' hne, x, d.max' hne} ⊆ d := by
          intro y hy
          simp only [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact min'_mem d hne
          · exact hx
          · exact max'_mem d hne
        have hcard : ({d.min' hne, x, d.max' hne} : Finset (Fin s)).card ≤ d.card :=
          Finset.card_le_card hsub
        have hcard3 : ({d.min' hne, x, d.max' hne} : Finset (Fin s)).card = 3 := by
          have h_x_max' : x ∉ ({d.max' hne} : Finset (Fin s)) := by simp [h_x_max]
          have h_min_insert : d.min' hne ∉ ({x, d.max' hne} : Finset (Fin s)) := by simp [h_min_x, h_min_max]
          rw [card_insert_of_notMem h_min_insert, card_insert_of_notMem h_x_max', card_singleton]
        omega
  · rintro (rfl | rfl)
    · exact min'_mem d hne
    · exact max'_mem d hne

private def incCode (Q : ℕ) (s : ℕ) (hs : s ≤ Q) (inc : Incidence s) : Fin (Q ^ 2 + Q + 1) :=
  let a := (inc.denoms.min' inc.nonempty).val
  let b := (inc.denoms.max' inc.nonempty).val
  have ha : a < Q := (inc.denoms.min' inc.nonempty).isLt.trans_le hs
  have hb : b < Q := (inc.denoms.max' inc.nonempty).isLt.trans_le hs
  have hcode : a * Q + b < Q ^ 2 + Q + 1 := by nlinarith
  ⟨a * Q + b, hcode⟩

private theorem incCode_inj (Q s : ℕ) (hs : s ≤ Q) : Function.Injective (incCode Q s hs) := by
  intro i1 i2 h
  have h_val : (incCode Q s hs i1).val = (incCode Q s hs i2).val := congr_arg Fin.val h
  dsimp [incCode] at h_val
  have hb1 : (i1.denoms.max' i1.nonempty).val < Q := (i1.denoms.max' i1.nonempty).isLt.trans_le hs
  have hb2 : (i2.denoms.max' i2.nonempty).val < Q := (i2.denoms.max' i2.nonempty).isLt.trans_le hs
  have ha_eq : (i1.denoms.min' i1.nonempty).val = (i2.denoms.min' i2.nonempty).val := by
    rcases Nat.eq_zero_or_pos Q with rfl | hQ
    · omega
    · have h1 : ((i1.denoms.min' i1.nonempty).val * Q + (i1.denoms.max' i1.nonempty).val) / Q = (i1.denoms.min' i1.nonempty).val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hb1, Nat.zero_add]
      have h2 : ((i2.denoms.min' i2.nonempty).val * Q + (i2.denoms.max' i2.nonempty).val) / Q = (i2.denoms.min' i2.nonempty).val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hb2, Nat.zero_add]
      exact h1.symm.trans (h2 ▸ congr_arg (· / Q) h_val)
  have hb_eq : (i1.denoms.max' i1.nonempty).val = (i2.denoms.max' i2.nonempty).val := by
    rcases Nat.eq_zero_or_pos Q with rfl | hQ
    · omega
    · have h1 : ((i1.denoms.min' i1.nonempty).val * Q + (i1.denoms.max' i1.nonempty).val) % Q = (i1.denoms.max' i1.nonempty).val := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb1]
      have h2 : ((i2.denoms.min' i2.nonempty).val * Q + (i2.denoms.max' i2.nonempty).val) % Q = (i2.denoms.max' i2.nonempty).val := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb2]
      exact h1.symm.trans (h2 ▸ congr_arg (· % Q) h_val)
  have ha : i1.denoms.min' i1.nonempty = i2.denoms.min' i2.nonempty := Fin.ext ha_eq
  have hb : i1.denoms.max' i1.nonempty = i2.denoms.max' i2.nonempty := Fin.ext hb_eq
  cases i1 with | mk d1 ne1 le1 =>
  cases i2 with | mk d2 ne2 le2 =>
  dsimp at ha hb
  congr
  rw [denoms_eq_of_min_max d1 ne1 le1, denoms_eq_of_min_max d2 ne2 le2, ha, hb]

private def embedTopology (Q : ℕ) (bt : BoundedTopology Q) : TargetType Q :=
  let hs : bt.denominatorCount ≤ Q := (le_max_left _ _).trans bt.score_le
  let ht : bt.termCount ≤ Q := (le_max_right _ _).trans bt.score_le
  let d_fin : Fin (Q + 1) := ⟨bt.denominatorCount, Nat.lt_succ_of_le hs⟩
  let t_fin : Fin (Q + 1) := ⟨bt.termCount, Nat.lt_succ_of_le ht⟩
  let inc_fn : Fin Q → Fin (Q ^ 2 + Q + 1) := fun i =>
    if h : i.val < bt.termCount then
      incCode Q bt.denominatorCount hs (bt.incidence ⟨i.val, h⟩)
    else
      ⟨0, Nat.zero_lt_succ _⟩
  ((d_fin, t_fin), inc_fn)

private theorem embedTopology_inj (Q : ℕ) : Function.Injective (embedTopology Q) := by
  intro bt1 bt2 h
  dsimp [embedTopology] at h
  have hd : bt1.denominatorCount = bt2.denominatorCount := by
    have h1 := (Prod.ext_iff.mp (Prod.ext_iff.mp h).1).1
    exact Fin.mk.inj h1
  have ht : bt1.termCount = bt2.termCount := by
    have h2 := (Prod.ext_iff.mp (Prod.ext_iff.mp h).1).2
    exact Fin.mk.inj h2
  have h_inc_fn := (Prod.ext_iff.mp h).2
  cases bt1 with | mk d1 t1 inc1 s1 =>
  cases bt2 with | mk d2 t2 inc2 s2 =>
  dsimp at hd ht
  subst hd ht
  congr
  ext ⟨i, hi⟩
  have h_eq := congr_fun h_inc_fn ⟨i, hi.trans_le ((le_max_right d1 t1).trans s1)⟩
  dsimp at h_eq
  rw [dif_pos hi, dif_pos hi] at h_eq
  exact incCode_inj Q d1 ((le_max_left d1 t1).trans s1) h_eq

/-- Cardinality of `BoundedTopology Q` is bounded by `topologyCountBound Q`. -/
theorem boundedTopology_card_le (Q : ℕ) :
    Fintype.card (BoundedTopology Q) ≤ topologyCountBound Q := by
  calc Fintype.card (BoundedTopology Q)
    _ ≤ Fintype.card (TargetType Q) := Fintype.card_le_of_injective (embedTopology Q) (embedTopology_inj Q)
    _ = topologyCountBound Q := by
      dsimp [topologyCountBound]
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
      ring

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
  haveI : DecidablePred (fun (f : BoolFn n) => ∃ C : Certificate n T, C.Represents f) :=
    Classical.decPred _
  let S := Finset.univ.filter (fun (f : BoolFn n) => ∃ C : Certificate n T, C.Represents f)
  use S
  refine ⟨by simp [S], ?_⟩
  let g : BoolFn n → (Fin (2 ^ n) → Bool) := fun f i => f (cubeIndexEquiv n i)
  have hg_inj : Function.Injective g := by
    intro f1 f2 h
    ext x
    have h1 := congr_fun h ((cubeIndexEquiv n).symm x)
    dsimp [g] at h1
    rwa [Equiv.apply_symm_apply] at h1
  have h_sub : (S.image g : Set (Fin (2 ^ n) → Bool)) ⊆
      HeadComplexity.signPatterns M.polynomial := by
    rintro s hs
    rw [Finset.mem_coe, Finset.mem_image] at hs
    rcases hs with ⟨f, hf, rfl⟩
    rw [Finset.mem_filter] at hf
    rcases hf.2 with ⟨C, hC⟩
    exact M.covers C f hC
  have h_card_eq : (S.image g).card = S.card := Finset.card_image_of_injective S hg_inj
  rw [← h_card_eq]
  rw [← Set.ncard_coe_finset (S.image g)]
  exact Set.ncard_le_ncard h_sub (Set.toFinite _)

/-- Real-to-Nat rounding bound for Warren sign pattern card bound. -/
theorem warren_pattern_card_nat_le (n : ℕ) (T : Topology) (M : FixedTopologyWarrenModel n T) :
    (HeadComplexity.signPatterns M.polynomial).ncard ≤
      Nat.floor ((8 * ((T.denominatorCount : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^
        (topologyParameterCount n T)) := by
  rw [Nat.le_floor_iff (by positivity)]
  exact HeadComplexity.warren_sign_patterns_weak M.polynomial M.degree_le

/-- Upper bound on denominatorCount and parameterCount when score is at most Q. -/
theorem topology_param_degree_le (n Q : ℕ) (T : Topology) (hT : T.score ≤ Q) :
    T.denominatorCount ≤ Q ∧ topologyParameterCount n T ≤ 2 * Q * (n + 1) := by
  have hden : T.denominatorCount ≤ Q := (le_max_left _ _).trans hT
  have hterm : T.termCount ≤ Q := (le_max_right _ _).trans hT
  constructor
  · exact hden
  · unfold topologyParameterCount
    have hsum : T.denominatorCount + T.termCount ≤ 2 * Q := by linarith
    nlinarith

/-- Cardinality of truth tables representable by one topology `T` with score at most `Q`. -/
theorem truthTables_per_topology_card_le (n Q : ℕ) (T : Topology) (hT : T.score ≤ Q) :
    haveI : DecidablePred (fun (f : BoolFn n) => ∃ C : Certificate n T, C.Represents f) :=
      Classical.decPred _
    (Finset.univ.filter (fun (f : BoolFn n) => ∃ C : Certificate n T, C.Represents f)).card ≤
      Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) := by
  letI : DecidablePred (fun (f : BoolFn n) => ∃ C : Certificate n T, C.Represents f) :=
    Classical.decPred _
  obtain ⟨M⟩ := fixedTopology_warren_model_helper n T
  obtain ⟨S, hS_iff, hS_card⟩ := represented_truthTables_embedding n T M
  have hS_eq : Finset.filter (fun (f : BoolFn n) => ∃ C : Certificate n T, C.Represents f)
      Finset.univ = S := by
    ext f
    simp [hS_iff]
  rw [hS_eq]
  have h1 := warren_pattern_card_nat_le n T M
  have ⟨hden, hparam⟩ := topology_param_degree_le n Q T hT
  have h3 : S.card ≤ Nat.floor ((8 * ((T.denominatorCount : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^
      (topologyParameterCount n T)) :=
    hS_card.trans h1
  apply h3.trans
  apply Nat.floor_le_floor
  have hbase_le : 8 * ((T.denominatorCount : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1) ≤
      8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1) := by
    gcongr
  have hbase_pos : 1 ≤ 8 * ((T.denominatorCount : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1) := by
    have : 0 ≤ (T.denominatorCount : ℝ) * ((2 ^ n : ℕ) : ℝ) := by positivity
    linarith
  have hstep1 : (8 * ((T.denominatorCount : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^
      (topologyParameterCount n T) ≤
      (8 * ((T.denominatorCount : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1)) := by
    gcongr
  have hstep2 : (8 * ((T.denominatorCount : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^
      (2 * Q * (n + 1)) ≤
      (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1)) := by
    gcongr
  exact hstep1.trans hstep2

private def BoundedTopology.toTopology (Q : ℕ) (bt : BoundedTopology Q) : Topology :=
  ⟨bt.denominatorCount, bt.termCount, bt.incidence⟩

/-- The union bound estimate for non-constant certificates with score at most Q. -/
theorem nonconstant_sublevel_card_le (n Q : ℕ) (hn : 2 ≤ n) (hQ0 : 1 ≤ Q) (hQN : Q ≤ 2 ^ n) :
    haveI : DecidablePred (fun (f : BoolFn n) =>
      ∃ (T : Topology) (C : Certificate n T), T.score ≤ Q ∧ C.Represents f) :=
      Classical.decPred _
    (Finset.univ.filter (fun (f : BoolFn n) =>
      ∃ (T : Topology) (C : Certificate n T), T.score ≤ Q ∧ C.Represents f)).card ≤
        topologyCountBound Q *
          Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) := by
  classical
  let W (bt : BoundedTopology Q) : Finset (BoolFn n) :=
    Finset.univ.filter (fun (f : BoolFn n) =>
      ∃ C : Certificate n (bt.toTopology Q), C.Represents f)
  have hsub : (Finset.univ.filter (fun (f : BoolFn n) =>
      ∃ (T : Topology) (C : Certificate n T), T.score ≤ Q ∧ C.Represents f)) ⊆
        Finset.univ.biUnion W := by
    intro f hf
    rw [mem_filter] at hf
    rcases hf.2 with ⟨T, C, hT, hC⟩
    let bt : BoundedTopology Q := ⟨T.denominatorCount, T.termCount, T.incidence, hT⟩
    rw [mem_biUnion]
    refine ⟨bt, mem_univ _, ?_⟩
    rw [mem_filter]
    exact ⟨mem_univ _, ⟨C, hC⟩⟩
  have hcard_le := Finset.card_le_card hsub
  have hbiUnion_le :=
    Finset.card_biUnion_le (s := (Finset.univ : Finset (BoundedTopology Q))) (t := W)
  have hsum_le : (∑ bt : BoundedTopology Q, (W bt).card) ≤
      (Fintype.card (BoundedTopology Q)) *
        Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) := by
    have hbound : ∀ bt : BoundedTopology Q, (W bt).card ≤
        Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) := by
      intro bt
      change (Finset.univ.filter
        (fun (f : BoolFn n) => ∃ C : Certificate n (bt.toTopology Q), C.Represents f)).card ≤ _
      exact truthTables_per_topology_card_le n Q (bt.toTopology Q) bt.score_le
    have hsum := Finset.sum_le_card_nsmul (Finset.univ : Finset (BoundedTopology Q))
      (fun bt => (W bt).card)
      (Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))))
      (fun bt _ => hbound bt)
    simpa using hsum
  have htop_le := boundedTopology_card_le Q
  have hprod_le : (Fintype.card (BoundedTopology Q)) *
        Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) ≤
      topologyCountBound Q *
        Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) :=
    Nat.mul_le_mul_right _ htop_le
  exact hcard_le.trans (hbiUnion_le.trans (hsum_le.trans hprod_le))

/-- Constant truth tables sublevel cardinality bound. -/
theorem constant_sublevel_card_le (n : ℕ) :
    haveI : DecidablePred (fun (f : BoolFn n) => IsConstant f) := Classical.decPred _
    (Finset.univ.filter (fun (f : BoolFn n) => IsConstant f)).card ≤ 2 := by
  classical
  let cFn : Bool → BoolFn n := fun b _ => b
  have h_sub : (Finset.univ.filter (fun (f : BoolFn n) => IsConstant f)) ⊆
      Finset.univ.image cFn := by
    intro f hf
    rw [mem_filter] at hf
    rcases hf.2 with ⟨b, hb⟩
    rw [mem_image]
    refine ⟨b, mem_univ _, ?_⟩
    ext x
    exact (hb x).symm
  have h_card_bool : (Finset.univ : Finset Bool).card = 2 := rfl
  have h1 : (Finset.univ.filter (fun (f : BoolFn n) => IsConstant f)).card ≤
      (Finset.univ.image cFn).card := card_le_card h_sub
  have h2 : (Finset.univ.image cFn).card ≤ (Finset.univ : Finset Bool).card := card_image_le
  rw [h_card_bool] at h2
  exact h1.trans h2

private theorem topologyCountBound_nat_le (n Q : ℕ) (hn : 2 ≤ n) (hQ0 : 1 ≤ Q)
    (hQN : Q ≤ 2 ^ n) :
    topologyCountBound Q ≤ 2 ^ (16 * n ^ 2 * Q) := by
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hQ1 : Q + 1 ≤ 2 ^ (n + 1) := by
    calc
      Q + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right hQN 1
      _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left (by nlinarith) _
      _ = 2 ^ (n + 1) := by ring
  have hQ1_sq : (Q + 1) ^ 2 ≤ 2 ^ (2 * n + 2) := by
    calc
      (Q + 1) ^ 2 ≤ (2 ^ (n + 1)) ^ 2 := Nat.pow_le_pow_left hQ1 2
      _ = 2 ^ (2 * n + 2) := by ring_nf
  have hpow_le : 2 ^ (n + 1) ≤ 2 ^ (2 * n) := by
    apply Nat.pow_le_pow_right (by decide)
    linarith
  have hpoly : Q ^ 2 + Q + 1 ≤ 2 ^ (2 * n + 1) := by
    have hQ2 : Q ^ 2 ≤ 2 ^ (2 * n) := by
      calc
        Q ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hQN 2
        _ = 2 ^ (2 * n) := by ring_nf
    have hQ_add1 : Q + 1 ≤ 2 ^ (2 * n) := hQ1.trans hpow_le
    calc
      Q ^ 2 + Q + 1 = Q ^ 2 + (Q + 1) := by ring
      _ ≤ 2 ^ (2 * n) + 2 ^ (2 * n) := Nat.add_le_add hQ2 hQ_add1
      _ = 2 ^ (2 * n + 1) := by ring
  have hpoly_pow : (Q ^ 2 + Q + 1) ^ Q ≤ 2 ^ ((2 * n + 1) * Q) := by
    calc
      (Q ^ 2 + Q + 1) ^ Q ≤ (2 ^ (2 * n + 1)) ^ Q := Nat.pow_le_pow_left hpoly Q
      _ = 2 ^ ((2 * n + 1) * Q) := by ring_nf
  have hprod : topologyCountBound Q ≤ 2 ^ (2 * n + 2 + (2 * n + 1) * Q) := by
    dsimp [topologyCountBound]
    calc
      (Q + 1) ^ 2 * (Q ^ 2 + Q + 1) ^ Q ≤ 2 ^ (2 * n + 2) * 2 ^ ((2 * n + 1) * Q) :=
        Nat.mul_le_mul hQ1_sq hpoly_pow
      _ = 2 ^ (2 * n + 2 + (2 * n + 1) * Q) := by rw [← Nat.pow_add]
  have hexp1 : 2 * n + 2 ≤ (2 * n + 2) * Q := by
    conv_lhs => rw [← mul_one (2 * n + 2)]
    exact Nat.mul_le_mul_left (2 * n + 2) hQ0
  have hexp2 : 2 * n + 2 + (2 * n + 1) * Q ≤ (16 * n ^ 2) * Q := by
    calc
      2 * n + 2 + (2 * n + 1) * Q ≤ (2 * n + 2) * Q + (2 * n + 1) * Q :=
        Nat.add_le_add_right hexp1 _
      _ = (4 * n + 3) * Q := by ring
      _ ≤ (16 * n ^ 2) * Q := by
        apply Nat.mul_le_mul_right Q
        nlinarith
  calc
    topologyCountBound Q ≤ 2 ^ (2 * n + 2 + (2 * n + 1) * Q) := hprod
    _ ≤ 2 ^ (16 * n ^ 2 * Q) := by
      apply Nat.pow_le_pow_right (by decide)
      nlinarith

/-- Elementary exponential inequality 1: topology count in the scale needed by the
final sublevel estimate. -/
theorem exp_ineq_topologyCountBound (n Q : ℕ) (hn : 2 ≤ n) (hQ0 : 1 ≤ Q)
    (hQN : Q ≤ 2 ^ n) :
    (topologyCountBound Q : ℝ) ≤ 2 ^ (16 * n ^ 2 * Q) := by
  exact_mod_cast topologyCountBound_nat_le n Q hn hQ0 hQN

/-- Elementary exponential inequality 2: bound on Warren term per topology. -/
theorem exp_ineq_warrenTerm (n Q : ℕ) (hn : 2 ≤ n) (hQ0 : 1 ≤ Q) (hQN : Q ≤ 2 ^ n) :
    (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1)) ≤
      2 ^ (32 * n ^ 2 * Q) := by
  have h2n : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by norm_cast
  have h_inner : (Q : ℝ) * (2 : ℝ) ^ n + 1 ≤ (2 : ℝ) ^ (2 * n + 1) := by
    calc (Q : ℝ) * (2 : ℝ) ^ n + 1
      _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n + 1 := by nlinarith [show (Q : ℝ) ≤ (2 : ℝ) ^ n by exact_mod_cast hQN]
      _ = (2 : ℝ) ^ (2 * n) + 1 := by rw [← pow_add, ← two_mul]
      _ ≤ (2 : ℝ) ^ (2 * n) + (2 : ℝ) ^ (2 * n) := by
        have h2n2 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * n) := by
          have : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
          exact_mod_cast this
        linarith
      _ = 2 * (2 : ℝ) ^ (2 * n) := by ring
      _ = (2 : ℝ) ^ (2 * n + 1) := by rw [pow_succ']
  have h_base_le : 8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1) ≤ (2 : ℝ) ^ (2 * n + 4) := by
    rw [h2n]
    calc 8 * ((Q : ℝ) * (2 : ℝ) ^ n + 1)
      _ ≤ 8 * (2 : ℝ) ^ (2 * n + 1) := by nlinarith
      _ = (2 : ℝ) ^ 3 * (2 : ℝ) ^ (2 * n + 1) := by norm_num
      _ = (2 : ℝ) ^ (2 * n + 4) := by rw [← pow_add]; congr 1; ring
  have h_exp_le : (2 * n + 4) * (2 * Q * (n + 1)) ≤ 32 * n ^ 2 * Q := by
    have h1 : 2 * n + 4 ≤ 4 * n := by omega
    have h2 : n + 1 ≤ 2 * n := by omega
    calc (2 * n + 4) * (2 * Q * (n + 1))
      _ = (2 * n + 4) * (n + 1) * 2 * Q := by ring
      _ ≤ (4 * n) * (2 * n) * 2 * Q := by gcongr
      _ = 16 * n ^ 2 * Q := by ring
      _ ≤ 32 * n ^ 2 * Q := by nlinarith
  have h_base_pos : 0 ≤ 8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1) := by positivity
  have h_pow1 : (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1)) ≤
      ((2 : ℝ) ^ (2 * n + 4)) ^ (2 * Q * (n + 1)) := by
    gcongr
  have h_pow2 : ((2 : ℝ) ^ (2 * n + 4)) ^ (2 * Q * (n + 1)) = (2 : ℝ) ^ ((2 * n + 4) * (2 * Q * (n + 1))) := by
    rw [← pow_mul]
  have h_pow3 : (2 : ℝ) ^ ((2 * n + 4) * (2 * Q * (n + 1))) ≤ (2 : ℝ) ^ (32 * n ^ 2 * Q) := by
    apply pow_le_pow_right₀
    · norm_num
    · exact h_exp_le
  exact h_pow1.trans (h_pow2.le.trans h_pow3)

/-- Combination of exponential bounds into the padded 2^(64 * n^2 * Q) bound. -/
theorem sublevel_exp_bound_combination (n Q : ℕ) (hn : 2 ≤ n) (hQ0 : 1 ≤ Q) (hQN : Q ≤ 2 ^ n)
    (N : ℕ) (hN : (N : ℝ) ≤ 2 + (topologyCountBound Q : ℝ) *
      (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) :
    N ≤ 2 ^ (64 * n ^ 2 * Q) := by
  have htop := exp_ineq_topologyCountBound n Q hn hQ0 hQN
  have hwar := exp_ineq_warrenTerm n Q hn hQ0 hQN
  have htop_pos : 0 ≤ (topologyCountBound Q : ℝ) := by positivity
  have hwar_pos : 0 ≤ (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1)) := by positivity
  have hprod : (topologyCountBound Q : ℝ) *
        (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1)) ≤
      (2 : ℝ) ^ (16 * n ^ 2 * Q) * (2 : ℝ) ^ (32 * n ^ 2 * Q) := by
    exact mul_le_mul htop hwar hwar_pos (by positivity)
  have hpow_add : (2 : ℝ) ^ (16 * n ^ 2 * Q) * (2 : ℝ) ^ (32 * n ^ 2 * Q) =
      (2 : ℝ) ^ (48 * n ^ 2 * Q) := by
    rw [← pow_add]
    congr 1
    ring
  rw [hpow_add] at hprod
  have h1_le_48 : 1 ≤ 48 * n ^ 2 * Q := by
    calc 1 ≤ 48 * 2 ^ 2 * 1 := by norm_num
    _ ≤ 48 * n ^ 2 * Q := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left
        · nlinarith
        · norm_num
      · exact hQ0
      · positivity
      · positivity
  have h2_le : (2 : ℝ) ≤ (2 : ℝ) ^ (48 * n ^ 2 * Q) := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
    _ ≤ (2 : ℝ) ^ (48 * n ^ 2 * Q) := pow_le_pow_right₀ (by norm_num) h1_le_48
  have h_double : (2 : ℝ) ^ (48 * n ^ 2 * Q) + (2 : ℝ) ^ (48 * n ^ 2 * Q) =
      (2 : ℝ) ^ (48 * n ^ 2 * Q + 1) := by
    calc (2 : ℝ) ^ (48 * n ^ 2 * Q) + (2 : ℝ) ^ (48 * n ^ 2 * Q) =
        2 * (2 : ℝ) ^ (48 * n ^ 2 * Q) := by ring
    _ = (2 : ℝ) ^ 1 * (2 : ℝ) ^ (48 * n ^ 2 * Q) := by norm_num
    _ = (2 : ℝ) ^ (1 + 48 * n ^ 2 * Q) := by rw [← pow_add]
    _ = (2 : ℝ) ^ (48 * n ^ 2 * Q + 1) := by
      congr 1
      ring
  have h1_le_16 : 1 ≤ 16 * n ^ 2 * Q := by
    calc 1 ≤ 16 * 2 ^ 2 * 1 := by norm_num
    _ ≤ 16 * n ^ 2 * Q := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left
        · nlinarith
        · norm_num
      · exact hQ0
      · positivity
      · positivity
  have h_exp_le : 48 * n ^ 2 * Q + 1 ≤ 64 * n ^ 2 * Q := by linarith
  have h_pow_le : (2 : ℝ) ^ (48 * n ^ 2 * Q + 1) ≤ (2 : ℝ) ^ (64 * n ^ 2 * Q) :=
    pow_le_pow_right₀ (by norm_num) h_exp_le
  have hN_real : (N : ℝ) ≤ (2 : ℝ) ^ (64 * n ^ 2 * Q) := by
    calc (N : ℝ) ≤ 2 + (topologyCountBound Q : ℝ) *
          (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1)) := hN
    _ ≤ 2 + (2 : ℝ) ^ (48 * n ^ 2 * Q) := by linarith
    _ ≤ (2 : ℝ) ^ (48 * n ^ 2 * Q) + (2 : ℝ) ^ (48 * n ^ 2 * Q) := by linarith
    _ = (2 : ℝ) ^ (48 * n ^ 2 * Q + 1) := h_double
    _ ≤ (2 : ℝ) ^ (64 * n ^ 2 * Q) := h_pow_le
  have hN_nat_cast : (2 : ℝ) ^ (64 * n ^ 2 * Q) = ((2 ^ (64 * n ^ 2 * Q) : ℕ) : ℝ) := by
    push_cast
    rfl
  rw [hN_nat_cast] at hN_real
  exact_mod_cast hN_real

/-- Final sublevel packaging helper. -/
theorem relaxed_poic2_sublevel_card_le_helper (n Q : ℕ) (hn : 2 ≤ n)
    (hQ0 : 1 ≤ Q) (hQN : Q ≤ 2 ^ n) :
    (sublevel (RelaxedPOIC2 n) Q).card ≤ 2 ^ (64 * n ^ 2 * Q) := by
  classical
  let S_const := Finset.univ.filter (fun (f : BoolFn n) => IsConstant f)
  let S_nonconst := Finset.univ.filter (fun (f : BoolFn n) =>
    ∃ (T : Topology) (C : Certificate n T), T.score ≤ Q ∧ C.Represents f)
  have hsub : sublevel (RelaxedPOIC2 n) Q ⊆ S_const ∪ S_nonconst := by
    intro f hf
    rw [mem_sublevel] at hf
    have hex : ∃ R, HasCertificate n R f := exists_hasCertificate f
    have hcert : HasCertificate n Q f := hasCertificate_of_relaxedPOIC2_le hex hf
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hcert with hc | ⟨T, C, hT, hC⟩
    · left; exact ⟨Finset.mem_univ f, hc⟩
    · right; exact ⟨Finset.mem_univ f, ⟨T, C, hT, hC⟩⟩
  have hcard_union : (sublevel (RelaxedPOIC2 n) Q).card ≤ S_const.card + S_nonconst.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le S_const S_nonconst)
  have hconst_le : S_const.card ≤ 2 := constant_sublevel_card_le n
  have hnonconst_le : S_nonconst.card ≤ topologyCountBound Q *
      Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) :=
    nonconstant_sublevel_card_le n Q hn hQ0 hQN
  have hbound : (sublevel (RelaxedPOIC2 n) Q).card ≤ 2 + topologyCountBound Q *
      Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) := by
    omega
  have hcast : ((sublevel (RelaxedPOIC2 n) Q).card : ℝ) ≤ 2 + (topologyCountBound Q : ℝ) *
      (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1)) := by
    have hfloor_le : (Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) : ℝ) ≤
        (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1)) := by
      apply Nat.floor_le
      positivity
    have htop_nonneg : 0 ≤ (topologyCountBound Q : ℝ) := by positivity
    have h1 : ((sublevel (RelaxedPOIC2 n) Q).card : ℝ) ≤
        (2 + topologyCountBound Q *
          Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) : ℕ) := by
      exact_mod_cast hbound
    have h2 : ((2 + topologyCountBound Q *
          Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) : ℕ) : ℝ) =
        2 + (topologyCountBound Q : ℝ) *
          (Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) : ℝ) := by
      push_cast
      rfl
    have h3 : 2 + (topologyCountBound Q : ℝ) *
          (Nat.floor ((8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1))) : ℝ) ≤
        2 + (topologyCountBound Q : ℝ) *
          (8 * ((Q : ℝ) * ((2 ^ n : ℕ) : ℝ) + 1)) ^ (2 * Q * (n + 1)) := by
      gcongr
    linarith
  exact sublevel_exp_bound_combination n Q hn hQ0 hQN (sublevel (RelaxedPOIC2 n) Q).card hcast

end HeadComplexity.TypicalLogCloseness
