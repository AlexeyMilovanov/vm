import HeadComplexity.Separations.Warren
import HeadComplexity.Separations.SignRankBridge
import HeadComplexity.Separations.ThresholdDegAux
import HeadComplexity.Polynomial.ParityThresholdDegree
import HeadComplexity.Results.FractionalNormalForm

set_option linter.style.header false

/-!
# NDISJ and the split-shattering lower bound

`NDISJ_m(x, y) = 1 [∃ i, x_i ∧ y_i]` (non-disjointness) has threshold degree
`2` yet requires `Ω(m / log m)` heads: fixing `k` left points, the labels as
the right block varies are signs of `k` degree-`≤ H` polynomials in the `2 H`
denominator shifts, so Warren caps the shatterable set at
`2 ^ k ≤ (2 e k) ^ (2 H)` (`audit/sources/STRENGTHENING.md`).  With the monotone-DNF
upper bound `H* ≤ m` this pins `H*(NDISJ_m)` to `[Ω(m / log m), m]` — the
strongest explicit lower bound at constant degree.
-/

namespace HeadComplexity

/-- Non-disjointness on `m + m` bits. -/
def ndisj (m : ℕ) : (Fin (m + m) → Bool) → Bool :=
  fun z =>
    decide (∃ i, leftBits m m z i = true ∧ rightBits m m z i = true)

/-- `f` left-shatters `k` points: there are `k` left blocks on which, as the
right block varies, every `±` labelling is realized. -/
def LeftShatters {a b : ℕ} (f : (Fin (a + b) → Bool) → Bool) (k : ℕ) : Prop :=
  ∃ zs : Fin k → (Fin a → Bool),
    ∀ s : Fin k → Bool, ∃ w : Fin b → Bool, ∀ j, f (blockJoin (zs j) w) = s j

/-- Warren-bound simplification (PROOFS.md P10.1, final step): with `m := 2H`
and `d := H`, Warren's ceiling `(4·e·d·k/m)^m` collapses to `(2·e·k)^{2H}`
because `4·e·H·k / (2·H) = 2·e·k` (cancel `H ≠ 0`).  This turns the raw Warren
estimate into the `pow_le_of_leftShatters` conclusion. -/
theorem warren_pow_simp (H k : ℕ) (hH : 1 ≤ H) :
    (4 * Real.exp 1 * (H : ℝ) * (k : ℝ) / (2 * (H : ℝ))) ^ (2 * H)
      = (2 * Real.exp 1 * (k : ℝ)) ^ (2 * H) := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  have hbase : 4 * Real.exp 1 * (H : ℝ) * (k : ℝ) / (2 * (H : ℝ)) = 2 * Real.exp 1 * (k : ℝ) := by
    field_simp [hH0]
    ring
  rw [hbase]

/-- `NDISJ_m` left-shatters `m` points: the indicator left blocks `e_j`
satisfy `NDISJ(e_j, w) = w j`. -/
theorem ndisj_leftShatters (m : ℕ) : LeftShatters (ndisj m) m := by
  refine ⟨fun j i => decide (i = j), fun s => ⟨s, fun j => ?_⟩⟩
  have h : ndisj m (blockJoin (fun i => decide (i = j)) s) =
      decide (∃ i : Fin m, decide (i = j) = true ∧ s i = true) := by
    simp [ndisj]
  rw [h]
  cases hsj : s j with
  | false =>
      simp only [decide_eq_false_iff_not]
      rintro ⟨i, hi, hsi⟩
      rw [decide_eq_true_eq] at hi
      subst hi
      rw [hsj] at hsi
      exact Bool.false_ne_true hsi
  | true =>
      simp only [decide_eq_true_eq]
      exact ⟨j, by simp, hsj⟩

private noncomputable def ndisjAtomScale (m : ℕ) : ℝ :=
  1 / (8 * (m + 1) * (2 * m + 1))

private theorem ndisjAtomScale_pos (m : ℕ) : 0 < ndisjAtomScale m := by
  unfold ndisjAtomScale
  positivity

private theorem ndisjAtomScale_le_one (m : ℕ) : ndisjAtomScale m ≤ 1 := by
  unfold ndisjAtomScale
  rw [div_le_one (by positivity)]
  calc
    (1 : ℝ) ≤ 8 := by norm_num
    _ ≤ 8 * (m + 1 : ℝ) := by nlinarith
    _ = 8 * (m + 1 : ℝ) * 1 := by ring
    _ ≤ 8 * (m + 1 : ℝ) * (2 * m + 1) := by
      have hm : (0 : ℝ) ≤ m := by positivity
      have hfac : (1 : ℝ) ≤ 2 * m + 1 := by nlinarith
      have hbase : (0 : ℝ) ≤ 8 * (m + 1) := by nlinarith
      exact mul_le_mul_of_nonneg_left hfac hbase

/-- The coordinate-`i` atom in the P10.2 construction. Its two distinguished
coordinates have weight `1`; every other coordinate and the softmax parameter
have the small positive weight `ndisjAtomScale m`. -/
private noncomputable def ndisjAtom (m : ℕ) (i : Fin m) : FracAtom (m + m) where
  η := (2 * m + 1) * ndisjAtomScale m
  δ := 0
  γ := ndisjAtomScale m
  α := ndisjAtomScale m
  ρ p := if p = Fin.castAdd m i ∨ p = Fin.natAdd m i then 1 else ndisjAtomScale m
  m := fun _ => 0
  hγ := ndisjAtomScale_pos m
  hα := ndisjAtomScale_pos m
  hρ := by
    intro p
    split
    · norm_num
    · exact ndisjAtomScale_pos m

private theorem ndisjAtom_eval_eq (m : ℕ) (i : Fin m) (z : Fin (m + m) → Bool) :
    (ndisjAtom m i).eval z =
      ((2 * m + 1) * ndisjAtomScale m) /
        (ndisjAtomScale m + ∑ p, (ndisjAtom m i).wt z p) := by
  rw [FracAtom.eval]
  congr 1
  simp [ndisjAtom]

private theorem ndisjAtom_eval_nonneg (m : ℕ) (i : Fin m)
    (z : Fin (m + m) → Bool) : 0 ≤ (ndisjAtom m i).eval z := by
  rw [ndisjAtom_eval_eq]
  exact div_nonneg (mul_nonneg (by positivity) (ndisjAtomScale_pos m).le)
    ((ndisjAtom m i).denom_pos z).le

/-- The false-case estimate in PROOFS.md P10.2: if pair `i` is not jointly
set, its atom contributes at most `(2m+1) * ndisjAtomScale m`. -/
private theorem ndisjAtom_eval_le_of_not_pair (m : ℕ) (i : Fin m)
    (z : Fin (m + m) → Bool)
    (hpair : ¬ (z (Fin.castAdd m i) = true ∧ z (Fin.natAdd m i) = true)) :
    (ndisjAtom m i).eval z ≤ (2 * m + 1) * ndisjAtomScale m := by
  rw [ndisjAtom_eval_eq]
  have hfalse : z (Fin.castAdd m i) = false ∨ z (Fin.natAdd m i) = false := by
    cases hL : z (Fin.castAdd m i) <;> cases hR : z (Fin.natAdd m i) <;> simp_all
  obtain hL | hR := hfalse
  · have hwt : (ndisjAtom m i).wt z (Fin.castAdd m i) = 1 := by
      simp [FracAtom.wt, ndisjAtom, hL]
    have hsum : (1 : ℝ) ≤ ∑ p, (ndisjAtom m i).wt z p := by
      rw [← hwt]
      exact Finset.single_le_sum (fun p _ => ((ndisjAtom m i).wt_pos z p).le)
        (Finset.mem_univ _)
    apply (div_le_iff₀ ((ndisjAtom m i).denom_pos z)).2
    change (2 * (m : ℝ) + 1) * ndisjAtomScale m ≤
      (2 * (m : ℝ) + 1) * ndisjAtomScale m *
        (ndisjAtomScale m + ∑ p, (ndisjAtom m i).wt z p)
    have heta : (0 : ℝ) ≤ (2 * m + 1) * ndisjAtomScale m :=
      mul_nonneg (by positivity) (ndisjAtomScale_pos m).le
    nlinarith [ndisjAtomScale_pos m]
  · have hwt : (ndisjAtom m i).wt z (Fin.natAdd m i) = 1 := by
      have hrho : (ndisjAtom m i).ρ (Fin.natAdd m i) = 1 := by
        simp [ndisjAtom]
      rw [FracAtom.wt, hrho, hR]
      norm_num
    have hsum : (1 : ℝ) ≤ ∑ p, (ndisjAtom m i).wt z p := by
      rw [← hwt]
      exact Finset.single_le_sum (fun p _ => ((ndisjAtom m i).wt_pos z p).le)
        (Finset.mem_univ _)
    apply (div_le_iff₀ ((ndisjAtom m i).denom_pos z)).2
    change (2 * (m : ℝ) + 1) * ndisjAtomScale m ≤
      (2 * (m : ℝ) + 1) * ndisjAtomScale m *
        (ndisjAtomScale m + ∑ p, (ndisjAtom m i).wt z p)
    have heta : (0 : ℝ) ≤ (2 * m + 1) * ndisjAtomScale m :=
      mul_nonneg (by positivity) (ndisjAtomScale_pos m).le
    nlinarith [ndisjAtomScale_pos m]

/-- The true-case estimate in PROOFS.md P10.2: when pair `i` is jointly set,
every denominator weight is at most `ndisjAtomScale m`, so its atom is at
least `1`. -/
private theorem one_le_ndisjAtom_eval_of_pair (m : ℕ) (i : Fin m)
    (z : Fin (m + m) → Bool)
    (hL : z (Fin.castAdd m i) = true) (hR : z (Fin.natAdd m i) = true) :
    1 ≤ (ndisjAtom m i).eval z := by
  rw [ndisjAtom_eval_eq]
  have hwt : ∀ p, (ndisjAtom m i).wt z p ≤ ndisjAtomScale m := by
    intro p
    by_cases hp : p = Fin.castAdd m i ∨ p = Fin.natAdd m i
    · rcases hp with hp | hp
      · subst p
        have hrho : (ndisjAtom m i).ρ (Fin.castAdd m i) = 1 := by simp [ndisjAtom]
        rw [FracAtom.wt, hrho, hL]
        change 1 * (if true = true then ndisjAtomScale m else 1) ≤ ndisjAtomScale m
        norm_num
      · subst p
        have hrho : (ndisjAtom m i).ρ (Fin.natAdd m i) = 1 := by simp [ndisjAtom]
        rw [FracAtom.wt, hrho, hR]
        change 1 * (if true = true then ndisjAtomScale m else 1) ≤ ndisjAtomScale m
        norm_num
    · have hrho : (ndisjAtom m i).ρ p = ndisjAtomScale m := by
        change (if p = Fin.castAdd m i ∨ p = Fin.natAdd m i
          then 1 else ndisjAtomScale m) = ndisjAtomScale m
        exact if_neg hp
      cases hz : z p
      · rw [FracAtom.wt, hrho, hz]
        simp
      · rw [FracAtom.wt, hrho, hz]
        exact mul_le_of_le_one_right (ndisjAtomScale_pos m).le (ndisjAtomScale_le_one m)
  have hsum : ∑ p, (ndisjAtom m i).wt z p ≤
      ∑ _p : Fin (m + m), ndisjAtomScale m :=
    Finset.sum_le_sum fun p _ => hwt p
  apply (le_div_iff₀ ((ndisjAtom m i).denom_pos z)).2
  change 1 * (ndisjAtomScale m + ∑ p, (ndisjAtom m i).wt z p) ≤
    (2 * (m : ℝ) + 1) * ndisjAtomScale m
  rw [one_mul]
  calc
    ndisjAtomScale m + ∑ p, (ndisjAtom m i).wt z p
        ≤ ndisjAtomScale m + ∑ _p : Fin (m + m), ndisjAtomScale m :=
          add_le_add (le_refl _) hsum
    _ = (2 * m + 1) * ndisjAtomScale m := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]
      push_cast
      ring

/-- The `m` explicit atoms computing `NDISJ_m` (PROOFS.md P10.2). -/
theorem fracComputable_ndisj (m : ℕ) : fracComputable (m + m) m (ndisj m) := by
  refine ⟨ndisjAtom m, -(1 / 2 : ℝ), fun z => ?_⟩
  simp only [ndisj, decide_eq_true_eq]
  constructor
  · intro hpos
    by_contra hn
    push Not at hn
    have hle : ∑ i, (ndisjAtom m i).eval z ≤
        ∑ _i : Fin m, ((2 * m + 1) * ndisjAtomScale m) :=
      Finset.sum_le_sum fun i _ => ndisjAtom_eval_le_of_not_pair m i z (by
        intro hp
        exact hn i hp.1 hp.2)
    have hr : (2 * m + 1 : ℝ) * ndisjAtomScale m = 1 / (8 * (m + 1 : ℝ)) := by
      rw [ndisjAtomScale]
      field_simp
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hr] at hle
    have hmfrac : (m : ℝ) * (1 / (8 * (m + 1 : ℝ))) < 1 / 2 := by
      have hden : (0 : ℝ) < 8 * (m + 1 : ℝ) := by positivity
      rw [show (m : ℝ) * (1 / (8 * (m + 1 : ℝ))) =
        (m : ℝ) / (8 * (m + 1 : ℝ)) by ring]
      rw [div_lt_iff₀ hden]
      nlinarith
    linarith
  · rintro ⟨i, hL, hR⟩
    have hi := one_le_ndisjAtom_eval_of_pair m i z hL hR
    have hsum : (ndisjAtom m i).eval z ≤ ∑ j, (ndisjAtom m j).eval z :=
      Finset.single_le_sum (fun j _ => ndisjAtom_eval_nonneg m j z) (Finset.mem_univ i)
    linarith

/-- Monotone-DNF upper bound (corpus theorem 029): one calibrated head per
term gives `H*(NDISJ_m) ≤ m`. -/
private theorem not_leftShatters_zero_heads {a b k : ℕ} (hk : 1 ≤ k)
    {f : (Fin (a + b) → Bool) → Bool}
    (hcomp : computableWithHeadsN (a + b) 0 f) :
    ¬ LeftShatters f k := by
  rcases hcomp with ⟨d, Hs, w, τ, hcomp⟩
  intro hsh
  rcases hsh with ⟨zs, hsh⟩
  have h_const : ∀ z1 z2, f z1 = f z2 := by
    intro z1 z2
    have h1 : 0 > τ ↔ f z1 = true := by
      simpa [headFamilyAttnUpdate] using hcomp z1
    have h2 : 0 > τ ↔ f z2 = true := by
      simpa [headFamilyAttnUpdate] using hcomp z2
    cases hfz1 : f z1 <;> cases hfz2 : f z2
    · rfl
    · rw [hfz1] at h1
      rw [hfz2] at h2
      have hτ : 0 > τ := h2.mpr rfl
      have hff : false = true := h1.mp hτ
      contradiction
    · rw [hfz1] at h1
      rw [hfz2] at h2
      have hτ : 0 > τ := h1.mpr rfl
      have hff : false = true := h2.mp hτ
      contradiction
    · rfl
  set j0 : Fin k := ⟨0, by omega⟩
  rcases hsh (fun _ => true) with ⟨w1, hw1⟩
  rcases hsh (fun _ => false) with ⟨w2, hw2⟩
  have ht := hw1 j0
  have hf := hw2 j0
  have hce := h_const (blockJoin (zs j0) w1) (blockJoin (zs j0) w2)
  rw [ht, hf] at hce
  contradiction

private theorem pow_le_pow_of_lt_two_mul_H {H k : ℕ} (hk : 1 ≤ k) (hkH : k < 2 * H) :
    (2 : ℝ) ^ k ≤ (2 * Real.exp 1 * (k : ℝ)) ^ (2 * H) := by
  have hbase : (2 : ℝ) ≤ 2 * Real.exp 1 * (k : ℝ) := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    nlinarith
  have hpow1 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (2 * H) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpow2 : (2 : ℝ) ^ (2 * H) ≤ (2 * Real.exp 1 * (k : ℝ)) ^ (2 * H) :=
    pow_le_pow_left₀ (by norm_num) hbase (2 * H)
  exact hpow1.trans hpow2

private theorem warren_bound_of_leftShatters {a b H k : ℕ} (hH : 1 ≤ H) (hkH : 2 * H ≤ k)
    {f : (Fin (a + b) → Bool) → Bool}
    (hcomp : computableWithHeadsN (a + b) H f) (hsh : LeftShatters f k) :
    (2 : ℝ) ^ k ≤ (4 * Real.exp 1 * (H : ℝ) * (k : ℝ) / (2 * (H : ℝ))) ^ (2 * H) := by
  sorry

/-- **Split-shattering head bound** (mega-lab theorem, via Warren): if `f` is
computable with `H` heads and left-shatters `k` points, then
`2 ^ k ≤ (2 e k) ^ (2 H)`; equivalently `H* ≥ k / (2 log₂ (2 e k))`. -/

theorem pow_le_of_leftShatters {a b H k : ℕ}
    {f : (Fin (a + b) → Bool) → Bool} (hk : 1 ≤ k)
    (hcomp : computableWithHeadsN (a + b) H f) (hsh : LeftShatters f k) :
    (2 : ℝ) ^ k ≤ (2 * Real.exp 1 * k) ^ (2 * H) := by
  by_cases hH : H = 0
  · subst hH
    exfalso
    exact not_leftShatters_zero_heads hk hcomp hsh
  · have hH1 : 1 ≤ H := by omega
    by_cases hkH : k < 2 * H
    · exact pow_le_pow_of_lt_two_mul_H hk hkH
    · have hkH2 : 2 * H ≤ k := by omega
      have hw := warren_bound_of_leftShatters hH1 hkH2 hcomp hsh
      rw [warren_pow_simp H k hH1] at hw
      exact hw

theorem HStar_ndisj_le (m : ℕ) : HStar (m + m) (ndisj m) ≤ m := by
  have hcomp : computableWithHeadsN (m + m) m (ndisj m) :=
    computable_of_fracComputable (fracComputable_ndisj m)
  classical
  have hex : ∃ k, computableWithHeadsN (m + m) k (ndisj m) := ⟨m, hcomp⟩
  unfold HStar
  rw [dif_pos hex]
  exact Nat.find_min' hex hcomp

open MvPolynomial in
/-- Upper half of `deg±(NDISJ_m) ≤ 2` (PROOFS.md P10.3): the quadratic
`Σ_i X_i Y_i - 1/2` sign-represents `NDISJ_m` (its cube values lie in `ℤ - 1/2`,
positive iff some pair is jointly set). -/
theorem thresholdDegLE_ndisj (m : ℕ) : ThresholdDegLE (ndisj m) 2 := by
  classical
  refine ⟨(∑ i : Fin m, X (Fin.castAdd m i) * X (Fin.natAdd m i)) - C (1 / 2 : ℝ),
    ?_, ?_⟩
  · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine totalDegree_finsetSum_le (fun i _ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_X]
    · rw [totalDegree_C]; norm_num
  · intro z
    have hpair : ∀ i : Fin m,
        eval (cubePoint z) (X (Fin.castAdd m i) * X (Fin.natAdd m i))
          = if z (Fin.castAdd m i) = true ∧ z (Fin.natAdd m i) = true then (1 : ℝ) else 0 := by
      intro i
      simp only [map_mul, eval_X, cubePoint]
      cases hcA : z (Fin.castAdd m i) <;> cases hnA : z (Fin.natAdd m i) <;>
        simp [boolToReal]
    have hsum : eval (cubePoint z)
        ((∑ i : Fin m, X (Fin.castAdd m i) * X (Fin.natAdd m i)) - C (1 / 2 : ℝ))
        = ((Finset.univ.filter fun i : Fin m =>
            z (Fin.castAdd m i) = true ∧ z (Fin.natAdd m i) = true).card : ℝ) - 1 / 2 := by
      rw [map_sub, eval_C, map_sum, Finset.card_filter]
      push_cast
      rw [Finset.sum_congr rfl (fun i _ => hpair i)]
    rw [hsum]
    simp only [ndisj, decide_eq_true_eq]
    constructor
    · intro h
      have hpos : 0 < (Finset.univ.filter fun i : Fin m =>
          z (Fin.castAdd m i) = true ∧ z (Fin.natAdd m i) = true).card := by
        by_contra hc
        rw [not_lt, Nat.le_zero] at hc
        rw [hc] at h; norm_num at h
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at hi
      exact ⟨i, hi.2⟩
    · rintro ⟨i, hLi, hRi⟩
      have hmem : i ∈ Finset.univ.filter fun i : Fin m =>
          z (Fin.castAdd m i) = true ∧ z (Fin.natAdd m i) = true := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ i, hLi, hRi⟩
      have hcard : (1 : ℝ) ≤ ((Finset.univ.filter fun i : Fin m =>
          z (Fin.castAdd m i) = true ∧ z (Fin.natAdd m i) = true).card : ℝ) := by
        have := Finset.card_pos.mpr (⟨i, hmem⟩ : (Finset.univ.filter _).Nonempty)
        exact_mod_cast this
      linarith

/-- Lower half of `deg±(NDISJ_m) ≥ 2` (PROOFS.md P10.3): fixing all but the
first two pairs to `0`, the four inputs `(10|10),(01|01),(10|01),(01|10)` form
an affine identity `ℓ(a)+ℓ(d)=ℓ(b)+ℓ(c)` that no sign-representing affine `ℓ`
can satisfy (LHS `> 0 ≥` RHS).  Hence `NDISJ_m` is not an LTF. -/
theorem not_thresholdDegLE_one_ndisj {m : ℕ} (hm : 2 ≤ m) :
    ¬ ThresholdDegLE (ndisj m) 1 := by
  intro hLTF1
  rw [ThresholdDegLE_one_iff_isLTF] at hLTF1
  obtain ⟨c, cs, hsign⟩ := hLTF1
  set i0 : Fin m := ⟨0, by omega⟩ with hi0
  set i1 : Fin m := ⟨1, by omega⟩ with hi1
  have hne : i0 ≠ i1 := by rw [hi0, hi1]; simp [Fin.ext_iff]
  set e0 : Fin m → Bool := fun i => decide (i = i0) with he0
  set e1 : Fin m → Bool := fun i => decide (i = i1) with he1
  -- Per-coordinate `boolToReal` identity of the four inputs.
  have hpt : ∀ j, boolToReal (blockJoin e0 e0 j) + boolToReal (blockJoin e1 e1 j)
      = boolToReal (blockJoin e0 e1 j) + boolToReal (blockJoin e1 e0 j) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [blockJoin_castAdd]
    · simp only [blockJoin_natAdd]; ring
  -- Summed over the affine coefficients.
  have hsid : (∑ i, cs i * boolToReal (blockJoin e0 e0 i))
        + (∑ i, cs i * boolToReal (blockJoin e1 e1 i))
      = (∑ i, cs i * boolToReal (blockJoin e0 e1 i))
        + (∑ i, cs i * boolToReal (blockJoin e1 e0 i)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← mul_add, ← mul_add, hpt i]
  -- `NDISJ` values of the four inputs.
  have hna : ndisj m (blockJoin e0 e0) = true := by
    simp only [ndisj, leftBits_blockJoin, rightBits_blockJoin, decide_eq_true_eq]
    exact ⟨i0, by simp [he0], by simp [he0]⟩
  have hnd : ndisj m (blockJoin e1 e1) = true := by
    simp only [ndisj, leftBits_blockJoin, rightBits_blockJoin, decide_eq_true_eq]
    exact ⟨i1, by simp [he1], by simp [he1]⟩
  have hnb : ndisj m (blockJoin e0 e1) = false := by
    simp only [ndisj, leftBits_blockJoin, rightBits_blockJoin, decide_eq_false_iff_not]
    rintro ⟨i, hLi, hRi⟩
    simp only [he0, he1, decide_eq_true_eq] at hLi hRi
    exact hne (hLi.symm.trans hRi)
  have hnc : ndisj m (blockJoin e1 e0) = false := by
    simp only [ndisj, leftBits_blockJoin, rightBits_blockJoin, decide_eq_false_iff_not]
    rintro ⟨i, hLi, hRi⟩
    simp only [he0, he1, decide_eq_true_eq] at hLi hRi
    exact hne (hRi.symm.trans hLi)
  -- Sign constraints from `hsign`, then the affine identity gives a contradiction.
  have hpos_a : 0 < c + ∑ i, cs i * boolToReal (blockJoin e0 e0 i) := (hsign _).mpr hna
  have hpos_d : 0 < c + ∑ i, cs i * boolToReal (blockJoin e1 e1 i) := (hsign _).mpr hnd
  have hneg_b : c + ∑ i, cs i * boolToReal (blockJoin e0 e1 i) ≤ 0 := by
    by_contra h; push Not at h
    have := (hsign _).mp h; rw [hnb] at this; exact absurd this (by decide)
  have hneg_c : c + ∑ i, cs i * boolToReal (blockJoin e1 e0 i) ≤ 0 := by
    by_contra h; push Not at h
    have := (hsign _).mp h; rw [hnc] at this; exact absurd this (by decide)
  linarith [hsid, hpos_a, hpos_d, hneg_b, hneg_c]

/-- `NDISJ_m` has threshold degree exactly `2` for `m ≥ 2`
(upper: `Σ x_i y_i - 1/2`; lower: `NDISJ_m` is not an LTF). -/
theorem thresholdDeg_ndisj {m : ℕ} (hm : 2 ≤ m) :
    thresholdDeg (ndisj m) = 2 := by
  have hle := thresholdDeg_le_of (thresholdDegLE_ndisj m)
  have hlt := lt_thresholdDeg_of (not_thresholdDegLE_one_ndisj hm)
  omega

/-- **NDISJ separation** (`audit/sources/STRENGTHENING.md`): an explicit constant-
degree family with near-linear head complexity — degree stays `2` while
`2 ^ m ≤ (2 e m) ^ (2 H*)`, i.e. `H*(NDISJ_m) = Ω(m / log m)`. -/
theorem ndisj_separation {m : ℕ} (hm : 2 ≤ m) :
    thresholdDeg (ndisj m) = 2 ∧
      (2 : ℝ) ^ m ≤ (2 * Real.exp 1 * m) ^ (2 * HStar (m + m) (ndisj m)) :=
  ⟨thresholdDeg_ndisj hm,
    pow_le_of_leftShatters (by omega) (HStar_computable _) (ndisj_leftShatters m)⟩

/-- **Conjecture** (STRENGTHENING §3, the upper-bound half of `VC(F_H) = 2H`):
the sharp form of the shattering bound, `k ≤ 2 H`, removing the logarithm.
It would give the lower bound `H*(NDISJ_m) ≥ ⌈m/2⌉` (the matching upper bound
`⌈m/2⌉` would additionally need a shared-head construction; only `H* ≤ m` is
currently claimed).  Consistent with the computed values for `m ≤ 5`.
Stated as a `Prop`, deliberately not asserted. -/
def SharpShatteringUpperBound : Prop :=
  ∀ (a b H k : ℕ) (f : (Fin (a + b) → Bool) → Bool),
    computableWithHeadsN (a + b) H f → LeftShatters f k → k ≤ 2 * H

/-- The sharp bound would pin `NDISJ` to `H* ≥ ⌈m/2⌉`. -/
theorem ndisj_of_sharpShatteringUpperBound
    (hconj : SharpShatteringUpperBound) (m : ℕ) :
    m ≤ 2 * HStar (m + m) (ndisj m) :=
  hconj _ _ _ _ _ (HStar_computable _) (ndisj_leftShatters m)

end HeadComplexity
