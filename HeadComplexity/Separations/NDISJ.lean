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
`2 ^ k ≤ (8 k) ^ (4 H)` (`audit/sources/STRENGTHENING.md`).  With the monotone-DNF
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

/-- Arithmetic bridge from the diagonal weak-Warren bound to the clean
consumer endpoint.  The hypotheses give `H ≤ k`, hence the quadratic base
can be absorbed by doubling the exponent. -/
private theorem weak_warren_pow_le (H k : ℕ) (hH : 1 ≤ H) (hkH : 2 * H ≤ k) :
    (8 * ((H : ℝ) * k + 1)) ^ (2 * H) ≤
      (8 * (k : ℝ)) ^ (4 * H) := by
  have hHk : (H : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : H ≤ k)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  -- the RHS base squared dominates the LHS base (`H ≤ k`, `1 ≤ k`)
  have hbase : 8 * ((H : ℝ) * k + 1) ≤ (8 * (k : ℝ)) ^ 2 := by
    have h1 : (H : ℝ) * k ≤ (k : ℝ) * k :=
      mul_le_mul_of_nonneg_right hHk (by linarith)
    have h2 : (1 : ℝ) ≤ (k : ℝ) * k := by nlinarith
    nlinarith [h1, h2]
  -- `(8k)^(4H) = ((8k)^2)^(2H)`, then compare bases at the common exponent `2H`
  have hexp : (8 * (k : ℝ)) ^ (4 * H) = ((8 * (k : ℝ)) ^ 2) ^ (2 * H) := by
    rw [← pow_mul]; congr 1; ring
  rw [hexp]
  exact pow_le_pow_left₀ (by positivity) hbase (2 * H)

/-- The `k < 2H` branch does not need Warren: the deliberately loose consumer
base dominates `2`, and the exponent dominates `k`. -/
private theorem pow_le_weak_of_lt_two_mul_H {H k : ℕ} (hk : 1 ≤ k)
    (hkH : k < 2 * H) :
    (2 : ℝ) ^ k ≤ (8 * (k : ℝ)) ^ (4 * H) := by
  have hbase : (2 : ℝ) ≤ 8 * (k : ℝ) := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hpow1 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (4 * H) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpow2 : (2 : ℝ) ^ (4 * H) ≤ (8 * (k : ℝ)) ^ (4 * H) :=
    pow_le_pow_left₀ (by norm_num) hbase (4 * H)
  exact hpow1.trans hpow2

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

private theorem totalDegree_C_add_X_le {n : ℕ} (c : ℝ) (i : Fin n) :
    (MvPolynomial.C c + MvPolynomial.X i).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]; exact zero_le_one
  · rw [MvPolynomial.totalDegree_X]

private theorem totalDegree_finsetProd_le_card {ι : Type*} {n : ℕ} (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) ℝ) (hf : ∀ i ∈ s, (f i).totalDegree ≤ 1) :
    (∏ i ∈ s, f i).totalDegree ≤ s.card := by
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  have h1 : ∑ i ∈ s, (f i).totalDegree ≤ ∑ i ∈ s, 1 := Finset.sum_le_sum hf
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
  exact h1

private noncomputable def shatterPoly {H : ℕ} (a_j b_j : Fin H → ℝ) (τ : ℝ) :
    MvPolynomial (Fin (2 * H)) ℝ :=
  open MvPolynomial in
  ∑ h : Fin H,
    (C (a_j h) + X ⟨h.val, by omega⟩) *
    ∏ h' ∈ Finset.univ.erase h, (C (b_j h') + X ⟨H + h'.val, by omega⟩) -
  C τ * ∏ h : Fin H, (C (b_j h) + X ⟨H + h.val, by omega⟩)

private theorem totalDegree_shatterPoly {H : ℕ} (a_j b_j : Fin H → ℝ) (τ : ℝ) :
    (shatterPoly a_j b_j τ).totalDegree ≤ H := by
  open MvPolynomial in
  unfold shatterPoly
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine totalDegree_finsetSum_le (fun h _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have hlt1 : h.1 < 2 * H := by omega
    have h1 := totalDegree_C_add_X_le (a_j h) ⟨h.1, hlt1⟩
    have h2 := totalDegree_finsetProd_le_card (Finset.univ.erase h)
      (fun h' => C (b_j h') + X (⟨H + h'.1, by omega⟩ : Fin (2 * H)))
      (fun h' _ => totalDegree_C_add_X_le (b_j h') ⟨H + h'.1, by omega⟩)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h2
    by_cases hH : H = 0
    · subst hH; exact h.elim0
    · have : 1 + (H - 1) ≤ H := by omega
      exact (add_le_add h1 h2).trans this
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    have h2 := totalDegree_finsetProd_le_card (Finset.univ)
      (fun h' => C (b_j h') + X (⟨H + h'.1, by omega⟩ : Fin (2 * H)))
      (fun h' _ => totalDegree_C_add_X_le (b_j h') ⟨H + h'.1, by omega⟩)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    exact h2

private theorem eval_shatterPoly {H : ℕ} (a_j b_j : Fin H → ℝ) (τ : ℝ) (p q : Fin H → ℝ) :
    MvPolynomial.eval (fun i : Fin (2 * H) => if hlt : i.1 < H then p ⟨i.1, hlt⟩ else q ⟨i.1 - H, by omega⟩)
      (shatterPoly a_j b_j τ)
      = (∑ h : Fin H, (a_j h + p h) * ∏ h' ∈ Finset.univ.erase h, (b_j h' + q h')) -
        τ * ∏ h : Fin H, (b_j h + q h) := by
  open MvPolynomial in
  unfold shatterPoly
  simp only [map_sub, map_sum, map_mul, map_add, map_prod, eval_C, eval_X]
  have hp : ∀ h : Fin H, (if hlt : h.1 < H then p ⟨h.1, hlt⟩ else q ⟨h.1 - H, by omega⟩) = p h := by
    intro h
    have hlt : h.1 < H := h.2
    simp [hlt]
  have hq : ∀ h' : Fin H, (if hlt : H + h'.1 < H then p ⟨H + h'.1, hlt⟩ else q ⟨H + h'.1 - H, by omega⟩) = q h' := by
    intro h'
    have hnlt : ¬ (H + h'.1 < H) := by omega
    have hsub : H + h'.1 - H = h'.1 := by omega
    simp [hnlt, hsub]
  simp_rw [hp, hq]

private theorem cleared_score_iff' {H : ℕ} (τ : ℝ) (u D : Fin H → ℝ)
    (hD : ∀ h, 0 < D h) :
    (τ < ∑ h, u h / D h) ↔
      0 < (∑ h, u h * ∏ h' ∈ Finset.univ.erase h, D h') - τ * ∏ h, D h := by
  have hdpos : 0 < ∏ g, D g := Finset.prod_pos (fun g _ => hD g)
  have hU : (∑ h, u h / D h) = (∑ h, u h * ∏ h' ∈ Finset.univ.erase h, D h') / (∏ g, D g) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    have hne : ∏ h' ∈ Finset.univ.erase h, D h' ≠ 0 :=
      (Finset.prod_pos (fun g _ => hD g)).ne'
    have hd_eq : ∏ g, D g = D h * ∏ h' ∈ Finset.univ.erase h, D h' :=
      (Finset.mul_prod_erase Finset.univ D (Finset.mem_univ h)).symm
    rw [hd_eq]
    rw [mul_div_mul_right _ _ hne]
  rw [hU]
  rw [lt_div_iff₀ hdpos]
  exact sub_pos.symm

open scoped InnerProductSpace

/-- P10.1 (frozen-left-points normal form): with the left points fixed, the
label of `f` at `(z_j, w)` is the strict sign of a degree-`≤ H` polynomial
`Q_j` in the `2H` right-block head statistics `ξ(w) = (p_h(w), q_h(w))`.
Construction: `Q_j(p, q) = ∑_h (a_{hj} + p_h) ∏_{h'≠h} (b_{h'j} + q_{h'})
− τ ∏_h (b_{hj} + q_h)` with the frozen reals `a_{hj} = A'_h(z_j)`,
`b_{hj} = A_h(z_j)` (see `headA`, `exists_numerator_readout_two_block_split`
in SignRankBridge). -/
private theorem exists_shatter_polynomials {a b H : ℕ}
    {f : (Fin (a + b) → Bool) → Bool}
    (hcomp : computableWithHeadsN (a + b) H f) {k : ℕ}
    (zs : Fin k → (Fin a → Bool)) :
    ∃ (Q : Fin k → MvPolynomial (Fin (2 * H)) ℝ)
      (ξ : (Fin b → Bool) → (Fin (2 * H) → ℝ)),
      (∀ j, (Q j).totalDegree ≤ H) ∧
      ∀ j w, (f (blockJoin (zs j) w) = true ↔
        0 < MvPolynomial.eval (ξ w) (Q j)) := by
  obtain ⟨d, Hs, w, τ, hsep⟩ := hcomp
  have h1 := Classical.axiomOfChoice (fun h : Fin H => exists_numerator_readout_two_block_split (Hs h) w)
  obtain ⟨A', hA'⟩ := h1
  have h2 := Classical.axiomOfChoice hA'
  obtain ⟨B', hA'B'_eq⟩ := h2
  let a_j : Fin k → Fin H → ℝ := fun j h => A' h (zs j)
  let b_j : Fin k → Fin H → ℝ := fun j h => headA rfl (Hs h) (zs j)
  let p_w : (Fin b → Bool) → Fin H → ℝ := fun w_in h => B' h w_in
  let q_w : (Fin b → Bool) → Fin H → ℝ := fun w_in h => headB rfl (Hs h) w_in
  let Q : Fin k → MvPolynomial (Fin (2 * H)) ℝ := fun j => shatterPoly (a_j j) (b_j j) τ
  let ξ : (Fin b → Bool) → (Fin (2 * H) → ℝ) := fun w_in =>
    fun i => if hlt : i.1 < H then p_w w_in ⟨i.1, hlt⟩ else q_w w_in ⟨i.1 - H, by omega⟩
  refine ⟨Q, ξ, fun j => totalDegree_shatterPoly (a_j j) (b_j j) τ, fun j w_in => ?_⟩
  rw [eval_shatterPoly]
  have hDpos : ∀ h : Fin H, 0 < headA rfl (Hs h) (zs j) + headB rfl (Hs h) w_in := by
    intro h
    have hA := headA_pos rfl (Hs h) (zs j)
    have hB := headB_nonneg rfl (Hs h) w_in
    linarith
  have hU_split : (∑ h : Fin H, (a_j j h + p_w w_in h) / (b_j j h + q_w w_in h)) =
      ⟪w, headFamilyAttnUpdate Hs (blockJoin (zs j) w_in)⟫_ℝ := by
    change (∑ h : Fin H, (a_j j h + p_w w_in h) / (b_j j h + q_w w_in h)) =
      ⟪w, ∑ h : Fin H, (Hs h).attnUpdate (blockJoin (zs j) w_in)⟫_ℝ
    rw [inner_sum]
    refine Finset.sum_congr rfl ?_
    intro h _
    change (a_j j h + p_w w_in h) / (b_j j h + q_w w_in h) =
      ⟪w, ((Hs h).denominator (blockJoin (zs j) w_in))⁻¹ • (Hs h).numerator (blockJoin (zs j) w_in)⟫_ℝ
    rw [inner_smul_right, hA'B'_eq h (zs j) w_in, denominator_eq_headA_add_headB rfl (Hs h) (zs j) w_in]
    rw [div_eq_inv_mul]
  have hcleared := cleared_score_iff' τ (fun h => a_j j h + p_w w_in h) (fun h => b_j j h + q_w w_in h) hDpos
  rw [← hcleared, hU_split]
  exact (hsep (blockJoin (zs j) w_in)).symm


/-- A single positive shift below every "true"-slot value of a finite family
`g : (Fin k → Bool) → Fin k → ℝ`: if `g s j > 0` whenever `s j = true`, there
is `η > 0` strictly below all such values simultaneously (finite min over the
`(s, j)` pairs, halved).  This is the η-shift ingredient of P10.1, isolated so
the sign-pattern injection proof stays within budget. -/
private theorem exists_uniform_pos_shift {k : ℕ}
    (g : (Fin k → Bool) → Fin k → ℝ)
    (hg : ∀ (s : Fin k → Bool) (j : Fin k), s j = true → 0 < g s j) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (s : Fin k → Bool) (j : Fin k), s j = true → η < g s j := by
  classical
  set T : Finset ((Fin k → Bool) × Fin k) :=
    Finset.univ.filter (fun p => p.1 p.2 = true) with hT
  by_cases hTne : T.Nonempty
  · refine ⟨T.inf' hTne (fun p => g p.1 p.2) / 2, half_pos ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro p hp
      rw [hT, Finset.mem_filter] at hp
      exact hg p.1 p.2 hp.2
    · intro s j hsj
      have hmem : (s, j) ∈ T := by
        rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsj⟩
      have hle : T.inf' hTne (fun p => g p.1 p.2) ≤ g s j :=
        Finset.inf'_le (fun p => g p.1 p.2) hmem
      have hpos : (0 : ℝ) < T.inf' hTne (fun p => g p.1 p.2) := by
        rw [Finset.lt_inf'_iff]; intro q hq
        rw [hT, Finset.mem_filter] at hq; exact hg q.1 q.2 hq.2
      linarith
  · exact ⟨1, one_pos, fun s j hsj =>
      absurd (⟨(s, j), by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsj⟩⟩ :
        T.Nonempty) hTne⟩

/-- P10.1 (Warren application with the η-shift): if every labelling
`s : Fin k → Bool` is realized as the strict-positive pattern of `k`
degree-`≤ H` polynomials in `2H` real variables at a witness point, then the
`2^k` labellings inject into the strict sign patterns of the η-shifted family
`Q_j − η`, and `warren_sign_patterns_diag` bounds
their number. -/
private theorem pow_le_ncard_signPatterns {H k : ℕ}
    (Q : Fin k → MvPolynomial (Fin (2 * H)) ℝ)
    (hdeg : ∀ j, (Q j).totalDegree ≤ H)
    (ξ : (Fin k → Bool) → (Fin (2 * H) → ℝ))
    (hpat : ∀ s j, (s j = true ↔ 0 < MvPolynomial.eval (ξ s) (Q j))) :
    (2 : ℝ) ^ k ≤
      (8 * ((H : ℝ) * k + 1)) ^ (2 * H) := by
  classical
  -- a positive shift `η` strictly below every positive "true"-entry value
  obtain ⟨η, hηpos, hηlt⟩ := exists_uniform_pos_shift
    (fun s j => MvPolynomial.eval (ξ s) (Q j)) (fun s j h => (hpat s j).mp h)
  replace hηlt : ∀ (s : Fin k → Bool) (j : Fin k),
      s j = true → η < MvPolynomial.eval (ξ s) (Q j) := hηlt
  -- the η-shifted family; same degree bound, strictly signed on both sides
  set Q' : Fin k → MvPolynomial (Fin (2 * H)) ℝ := fun j => Q j - MvPolynomial.C η with hQ'
  have hdeg' : ∀ j, (Q' j).totalDegree ≤ H := by
    intro j
    have hj : Q' j = Q j - MvPolynomial.C η := rfl
    rw [hj]
    exact (MvPolynomial.totalDegree_sub_C_le (Q j) η).trans (hdeg j)
  have heval : ∀ (s : Fin k → Bool) (j : Fin k),
      MvPolynomial.eval (ξ s) (Q' j) = MvPolynomial.eval (ξ s) (Q j) - η := by
    intro s j
    have hj : Q' j = Q j - MvPolynomial.C η := rfl
    rw [hj]; simp only [map_sub, MvPolynomial.eval_C]
  have hstrict : ∀ (s : Fin k → Bool) (i : Fin k),
      (s i = true → 0 < MvPolynomial.eval (ξ s) (Q' i)) ∧
      (s i = false → MvPolynomial.eval (ξ s) (Q' i) < 0) := by
    intro s i
    refine ⟨fun hsi => ?_, fun hsi => ?_⟩
    · rw [heval]; linarith [hηlt s i hsi]
    · rw [heval]
      have hle : MvPolynomial.eval (ξ s) (Q i) ≤ 0 := by
        by_contra hc
        have hcon := (hpat s i).mpr (not_le.mp hc)
        rw [hsi] at hcon
        exact absurd hcon (by decide)
      linarith
  -- every labelling is a strict sign pattern of `Q'`, realized at `ξ s`
  have hall : ∀ s : Fin k → Bool, s ∈ signPatterns Q' := by
    intro s
    refine ⟨ξ s, ?_, ?_⟩
    · intro i
      cases hsi : s i with
      | false => exact ne_of_lt ((hstrict s i).2 hsi)
      | true => exact ne_of_gt ((hstrict s i).1 hsi)
    · intro i
      cases hsi : s i with
      | false =>
        exact (decide_eq_false_iff_not.mpr
          (not_lt.mpr (le_of_lt ((hstrict s i).2 hsi)))).symm
      | true =>
        exact (decide_eq_true_iff.mpr ((hstrict s i).1 hsi)).symm
  have huniv : signPatterns Q' = Set.univ := Set.eq_univ_of_forall hall
  have hcard : (signPatterns Q').ncard = 2 ^ k := by
    rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  -- Diagonal instance of the weak Warren-type bound.
  have hwarren := warren_sign_patterns_diag Q' hdeg'
  rw [hcard] at hwarren
  have hcast : (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
  rw [hcast]
  exact hwarren

private theorem warren_bound_of_leftShatters {a b H k : ℕ}
    {f : (Fin (a + b) → Bool) → Bool}
    (hcomp : computableWithHeadsN (a + b) H f) (hsh : LeftShatters f k) :
    (2 : ℝ) ^ k ≤ (8 * ((H : ℝ) * k + 1)) ^ (2 * H) := by
  rcases hsh with ⟨zs, hw⟩
  choose w hw using hw
  obtain ⟨Q, ξ, hdeg, h_iff⟩ := exists_shatter_polynomials hcomp zs
  have hpat : ∀ (s : Fin k → Bool) (j : Fin k),
      s j = true ↔ 0 < MvPolynomial.eval (ξ (w s)) (Q j) := by
    intro s j
    rw [← hw s j]
    exact h_iff j (w s)
  exact pow_le_ncard_signPatterns Q hdeg (fun s => ξ (w s)) hpat

/-- **Split-shattering head bound** (mega-lab theorem, via Warren): if `f` is
computable with `H` heads and left-shatters `k` points, then
`2 ^ k ≤ (8 k) ^ (4 H)`, which still gives `H* = Ω(k / log k)`. -/
theorem pow_le_of_leftShatters {a b H k : ℕ}
    {f : (Fin (a + b) → Bool) → Bool} (hk : 1 ≤ k)
    (hcomp : computableWithHeadsN (a + b) H f) (hsh : LeftShatters f k) :
    (2 : ℝ) ^ k ≤ (8 * (k : ℝ)) ^ (4 * H) := by
  by_cases hH : H = 0
  · subst hH
    exfalso
    exact not_leftShatters_zero_heads hk hcomp hsh
  · have hH1 : 1 ≤ H := by omega
    by_cases hkH : k < 2 * H
    · exact pow_le_weak_of_lt_two_mul_H hk hkH
    · have hkH2 : 2 * H ≤ k := by omega
      have hw := warren_bound_of_leftShatters hcomp hsh
      exact hw.trans (weak_warren_pow_le H k hH1 hkH2)

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
`2 ^ m ≤ (8 m) ^ (4 H*)`, i.e. `H*(NDISJ_m) = Ω(m / log m)`. -/
theorem ndisj_separation {m : ℕ} (hm : 2 ≤ m) :
    thresholdDeg (ndisj m) = 2 ∧
      (2 : ℝ) ^ m ≤
        (8 * (m : ℝ)) ^ (4 * HStar (m + m) (ndisj m)) :=
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
