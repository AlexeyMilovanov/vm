import HeadComplexity.TypicalLogCloseness.PowerBlockEquiv

set_option linter.style.header false

/-!
# Affine forms and evaluation identities for power-block localization

This module defines the affine forms (suffix penalty forms and Lagrange delta basis)
on each power-block and proves their evaluation properties.
-/

namespace HeadComplexity.TypicalLogCloseness

/-- Affine form detecting whether coordinate `k` differs from bit `b`. -/
def coordMismatchForm (n : ℕ) (k : Fin n) (b : Bool) : AffineForm n where
  constant := if b = true then 1 else 0
  linear j := if j = k then (if b = true then -1 else 1) else 0

/-- Evaluation identity for `coordMismatchForm`. -/
@[simp] theorem coordMismatchForm_eval (n : ℕ) (k : Fin n) (b : Bool)
    (x : Cube n) :
    (coordMismatchForm n k b).eval x = if x k = b then 0 else 1 := by
  dsimp [coordMismatchForm, AffineForm.eval]
  rw [Finset.sum_eq_single k]
  · cases b <;> cases x k <;> simp [bitReal]
  · intro j _ hj
    simp [hj]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

open Finset
open scoped BigOperators

private noncomputable def affineSum {ι : Type*} [Fintype ι]
    (L : ι → AffineForm n) : AffineForm n where
  constant := ∑ i, (L i).constant
  linear j := ∑ i, (L i).linear j

@[simp] private theorem affineSum_eval {ι : Type*} [Fintype ι]
    (L : ι → AffineForm n) (x : Cube n) :
    (affineSum L).eval x = ∑ i, (L i).eval x := by
  simp only [affineSum, AffineForm.eval]
  rw [Finset.sum_add_distrib]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

private def affineConst (n : ℕ) (a : ℝ) : AffineForm n where
  constant := a
  linear _ := 0

@[simp] private theorem affineConst_eval (n : ℕ) (a : ℝ) (x : Cube n) :
    (affineConst n a).eval x = a := by
  simp [affineConst, AffineForm.eval]

/-- The suffix penalty affine form `ell g` for a group index `g`. -/
noncomputable def powerBlockEll (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n)) : AffineForm n :=
  let m := Nat.log 2 n
  let p := powerBlockSize n
  let hp : p ≤ n := powerBlockSize_le_self n hn
  let cs := powerBlockGroupEquiv n hn g
  let pref := affineSum (fun k : Fin p =>
    coordMismatchForm n ⟨k.1, lt_of_lt_of_le k.2 hp⟩
      (cs.1.1 (starCoordEquiv m k)))
  let suffix := affineSum (fun j : Fin (n - p) =>
    coordMismatchForm n ⟨p + j.1, by omega⟩ (cs.2 j))
  (pref.add (suffix.smul 2)).add (affineConst n (-1))

private theorem cast_fin_val_alt {a b : ℕ} (h : a = b) (x : Fin a) :
    (cast (congrArg Fin h) x).val = x.val := by
  subst h
  rfl

private theorem cubeSplitEquiv_symm_apply_alt (n p : ℕ) (hp : p ≤ n)
    (x1 : Cube p) (x2 : Cube (n - p)) (i : Fin n) :
    (cubeSplitEquiv n p hp).symm (x1, x2) i =
      if hi : i.1 < p then
        x1 ⟨i.1, hi⟩
      else
        have hj : i.1 - p < n - p := by omega
        x2 ⟨i.1 - p, hj⟩ := by
  dsimp [cubeSplitEquiv]
  split_ifs with hi
  · change Sum.elim x1 x2
      (finSumFinEquiv.symm (cast (congrArg Fin (Nat.add_sub_of_le hp).symm) i)) =
        x1 ⟨i.1, hi⟩
    have h_cast : cast (congrArg Fin (Nat.add_sub_of_le hp).symm) i =
        Fin.castAdd (n - p) ⟨i.1, hi⟩ := by
      apply Fin.ext
      change (cast (congrArg Fin (Nat.add_sub_of_le hp).symm) i).val = i.val
      exact cast_fin_val_alt (Nat.add_sub_of_le hp).symm i
    rw [h_cast]
    change Sum.elim x1 x2
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl ⟨i.1, hi⟩))) = x1 ⟨i.1, hi⟩
    rw [Equiv.symm_apply_apply]
    rfl
  · have hj : i.1 - p < n - p := by omega
    change Sum.elim x1 x2
      (finSumFinEquiv.symm (cast (congrArg Fin (Nat.add_sub_of_le hp).symm) i)) =
        x2 ⟨i.1 - p, hj⟩
    have h_cast : cast (congrArg Fin (Nat.add_sub_of_le hp).symm) i =
        Fin.natAdd p ⟨i.1 - p, hj⟩ := by
      apply Fin.ext
      change (cast (congrArg Fin (Nat.add_sub_of_le hp).symm) i).val = p + (i.val - p)
      rw [cast_fin_val_alt (Nat.add_sub_of_le hp).symm i]
      omega
    rw [h_cast]
    change Sum.elim x1 x2
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr ⟨i.1 - p, hj⟩))) =
        x2 ⟨i.1 - p, hj⟩
    rw [Equiv.symm_apply_apply]
    rfl

private theorem powerBlockPartition_vertex_prefix_apply_alt (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n))
    (k i : Fin (powerBlockSize n)) :
    (powerBlockPartition n hn).vertex (g, k)
        ⟨i.1, lt_of_lt_of_le i.2 (powerBlockSize_le_self n hn)⟩ =
      toggle (powerBlockGroupEquiv n hn g).1.1 (starCoordEquiv (Nat.log 2 n) k)
        (starCoordEquiv (Nat.log 2 n) i) := by
  change (cubeSplitEquiv n (powerBlockSize n) (powerBlockSize_le_self n hn)).symm
    ((fun j => toggle (powerBlockGroupEquiv n hn g).1.1
        (starCoordEquiv (Nat.log 2 n) k) (starCoordEquiv (Nat.log 2 n) j)),
      (powerBlockGroupEquiv n hn g).2)
        ⟨i.1, lt_of_lt_of_le i.2 (powerBlockSize_le_self n hn)⟩ = _
  rw [cubeSplitEquiv_symm_apply_alt]
  simp

private theorem powerBlockPartition_vertex_suffix_apply (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n))
    (k : Fin (powerBlockSize n)) (j : Fin (n - powerBlockSize n)) :
    (powerBlockPartition n hn).vertex (g, k)
        ⟨powerBlockSize n + j.1, by
          have := j.2
          omega⟩ =
      (powerBlockGroupEquiv n hn g).2 j := by
  change (cubeSplitEquiv n (powerBlockSize n) (powerBlockSize_le_self n hn)).symm
    ((fun i => toggle (powerBlockGroupEquiv n hn g).1.1
        (starCoordEquiv (Nat.log 2 n) k) (starCoordEquiv (Nat.log 2 n) i)),
      (powerBlockGroupEquiv n hn g).2)
      ⟨powerBlockSize n + j.1, by omega⟩ = _
  rw [cubeSplitEquiv_symm_apply_alt]
  simp

private theorem mismatchSum_eq_hammingDist {ι : Type*} [Fintype ι]
    (a b : ι → Bool) :
    (∑ i, if b i = a i then (0 : ℝ) else 1) = (hammingDist a b : ℝ) := by
  unfold hammingDist
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : b i = a i
  · simp [h]
  · have h' : a i ≠ b i := fun hab => h hab.symm
    simp [h, h']

private theorem hammingDist_toggle_eq_one {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ι → Bool) (i : ι) :
    hammingDist a (toggle a i) = 1 := by
  unfold hammingDist
  rw [show (Finset.univ.filter fun j => a j ≠ toggle a i j) = {i} by
    ext j
    by_cases h : j = i
    · subst j
      cases a i <;> simp
    · simp [toggle, h]]
  simp

private theorem exists_toggle_of_hammingDist_eq_one {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a b : ι → Bool) (h : hammingDist a b = 1) :
    ∃ i, b = toggle a i := by
  unfold hammingDist at h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  refine ⟨i, funext fun j => ?_⟩
  by_cases hji : j = i
  · subst j
    have hmem : i ∈ Finset.univ.filter (fun k => a k ≠ b k) := by
      rw [hi]
      simp
    have hne := (Finset.mem_filter.mp hmem).2
    cases ha : a i <;> cases hb : b i <;> simp_all [toggle]
  · have hnot : j ∉ Finset.univ.filter (fun k => a k ≠ b k) := by
      rw [hi]
      simp [hji]
    have heq : a j = b j := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩)
    simp [toggle, hji, heq]

private theorem pullback_injective {ι κ : Type*} (e : κ ≃ ι) :
    Function.Injective (fun x : ι → Bool => fun j => x (e j)) := by
  intro x y h
  funext i
  have hi := congrFun h (e.symm i)
  simpa using hi

private theorem toggle_pullback {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : κ ≃ ι) (x : ι → Bool) (i : κ) :
    toggle (fun j => x (e j)) i = fun j => toggle x (e i) (e j) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [toggle]
  · have hne : e j ≠ e i := fun h => hji (e.injective h)
    simp [toggle, hji, hne]

/-- The suffix penalty `ell g` vanishes on vertex `z` if and only if `g = z.1`. -/
theorem powerBlockEll_zero_iff (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n))
    (z : Fin (2 ^ n / powerBlockSize n) × Fin (powerBlockSize n)) :
    (powerBlockEll n hn g).eval ((powerBlockPartition n hn).vertex z) = 0 ↔
      g = z.1 := by
  let m := Nat.log 2 n
  let cg := (powerBlockGroupEquiv n hn g).1
  let sg := (powerBlockGroupEquiv n hn g).2
  let cz := (powerBlockGroupEquiv n hn z.1).1
  let sz := (powerBlockGroupEquiv n hn z.1).2
  let kz := starCoordEquiv m z.2
  let pcg : Cube (2 ^ m) := fun i => cg.1 (starCoordEquiv m i)
  let pcz : Cube (2 ^ m) :=
    fun i => toggle cz.1 kz (starCoordEquiv m i)
  have heval :
      (powerBlockEll n hn g).eval ((powerBlockPartition n hn).vertex z) =
        (hammingDist pcg pcz : ℝ) +
          2 * (hammingDist sg sz : ℝ) - 1 := by
    change (powerBlockEll n hn g).eval
      ((powerBlockPartition n hn).vertex (z.1, z.2)) = _
    simp only [powerBlockEll, AffineForm.eval_add, affineSum_eval,
      AffineForm.eval_smul, affineConst_eval, coordMismatchForm_eval]
    simp_rw [powerBlockPartition_vertex_prefix_apply_alt]
    simp_rw [powerBlockPartition_vertex_suffix_apply]
    rw [mismatchSum_eq_hammingDist, mismatchSum_eq_hammingDist]
    rfl
  rw [heval]
  constructor
  · intro hzero
    have hreal :
        (hammingDist pcg pcz : ℝ) +
            2 * (hammingDist sg sz : ℝ) = 1 := by
      linarith
    have hnat : hammingDist pcg pcz +
        2 * hammingDist sg sz = 1 := by
      exact_mod_cast hreal
    have hpref : hammingDist pcg pcz = 1 := by omega
    have hsuff : hammingDist sg sz = 0 := by omega
    obtain ⟨i, hi⟩ := exists_toggle_of_hammingDist_eq_one pcg pcz hpref
    have hfull : toggle cz.1 kz = toggle cg.1 (starCoordEquiv m i) := by
      apply pullback_injective (starCoordEquiv m)
      calc
        (fun j => toggle cz.1 kz (starCoordEquiv m j)) = pcz := by rfl
        _ = toggle pcg i := hi
        _ = (fun j => toggle cg.1 (starCoordEquiv m i)
            (starCoordEquiv m j)) := by
          simpa [pcg] using toggle_pullback (starCoordEquiv m) cg.1 i
    have hpair : (cg, starCoordEquiv m i) = (cz, kz) := by
      apply (centerDirectionEquiv m (log_pos_of_two_le n hn)).injective
      simpa [centerDirectionEquiv_apply] using hfull.symm
    have hc : cg = cz :=
      congrArg (fun q : StarCenter m × StarCoord m => q.1) hpair
    have hs : sg = sz := hammingDist_eq_zero.mp hsuff
    apply (powerBlockGroupEquiv n hn).injective
    exact Prod.ext hc hs
  · intro hg
    subst g
    have hpc : pcz = toggle pcg z.2 := by
      simpa [pcg, pcz, cg, cz, kz] using
        (toggle_pullback (starCoordEquiv m) cz.1 z.2).symm
    rw [hpc, hammingDist_toggle_eq_one, hammingDist_self]
    norm_num

/-- The Lagrange delta affine form on block `g` for index `i`. -/
noncomputable def powerBlockLagrange (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n))
    (i : Fin (powerBlockSize n)) : AffineForm n :=
  let m := Nat.log 2 n
  let c := (powerBlockGroupEquiv n hn g).1
  let b := c.1 (starCoordEquiv m i)
  let k : Fin n := ⟨i.1, lt_of_lt_of_le i.2 (powerBlockSize_le_self n hn)⟩
  coordMismatchForm n k b

private theorem cast_fin_val {a b : ℕ} (h : a = b) (x : Fin a) :
    (cast (congrArg Fin h) x).val = x.val := by
  subst h
  rfl

private theorem cubeSplitEquiv_symm_apply_left (n p : ℕ) (hp : p ≤ n)
    (x1 : Cube p) (x2 : Cube (n - p)) (i : Fin p) :
    (cubeSplitEquiv n p hp).symm (x1, x2) ⟨i.1, lt_of_lt_of_le i.2 hp⟩ = x1 i := by
  dsimp [cubeSplitEquiv, finSumFinEquiv]
  have h_cast : (⟨i.1, lt_of_lt_of_le i.2 hp⟩ : Fin n) =
      (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hp).symm)).symm (Fin.castAdd (n - p) i) := by
    apply Fin.ext
    change i.val = (cast (congrArg Fin (Nat.add_sub_of_le hp).symm.symm) (Fin.castAdd (n - p) i)).val
    rw [cast_fin_val (Nat.add_sub_of_le hp)]
    rfl
  rw [h_cast]
  simp [Fin.addCases_left]

private theorem powerBlockPartition_vertex_apply (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n))
    (k i : Fin (powerBlockSize n)) :
    (powerBlockPartition n hn).vertex (g, k)
        ⟨i.1, lt_of_lt_of_le i.2 (powerBlockSize_le_self n hn)⟩ =
      toggle (powerBlockGroupEquiv n hn g).1.1 (starCoordEquiv (Nat.log 2 n) k)
        (starCoordEquiv (Nat.log 2 n) i) := by
  change (cubeSplitEquiv n (powerBlockSize n) (powerBlockSize_le_self n hn)).symm
    ((fun j => toggle (powerBlockGroupEquiv n hn g).1.1 (starCoordEquiv (Nat.log 2 n) k) (starCoordEquiv (Nat.log 2 n) j)),
     (powerBlockGroupEquiv n hn g).2) ⟨i.1, lt_of_lt_of_le i.2 (powerBlockSize_le_self n hn)⟩ = _
  rw [cubeSplitEquiv_symm_apply_left]

/-- Evaluation identity for `powerBlockLagrange` matching delta basis. -/
theorem powerBlockLagrange_delta (n : ℕ) (hn : 2 ≤ n)
    (g : Fin (2 ^ n / powerBlockSize n))
    (i k : Fin (powerBlockSize n)) :
    (powerBlockLagrange n hn g i).eval
        ((powerBlockPartition n hn).vertex (g, k)) =
      if i = k then 1 else 0 := by
  dsimp [powerBlockLagrange]
  rw [coordMismatchForm_eval]
  rw [powerBlockPartition_vertex_apply]
  by_cases h_ik : i = k
  · subst h_ik
    simp [toggle_same]
  · have h_ne : starCoordEquiv (Nat.log 2 n) i ≠ starCoordEquiv (Nat.log 2 n) k :=
      fun h_eq => h_ik ((starCoordEquiv (Nat.log 2 n)).injective h_eq)
    rw [toggle_ne _ h_ne]
    simp [h_ik]

end HeadComplexity.TypicalLogCloseness
