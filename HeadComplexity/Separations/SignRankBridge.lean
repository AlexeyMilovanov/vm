import HeadComplexity.Separations.SignRank
import HeadComplexity.Results.LowComplexity
import HeadComplexity.Polynomial.ThresholdDegree

set_option linter.style.header false

/-!
# The sign-rank bridge (theorem 028) and the Theorem C ceilings

`H` heads force sign-rank at most `2 ^ (H + 1) - 2` under every two-block
partition: clearing the softmax denominators and grouping the cleared
polynomial by subsets of heads yields `2 + 2 (2 ^ H - 2)` rank-one pieces.
Conversely (Theorem C of `audit/sources/EXPLICIT_GAP.md`) a degree-`d` sign
polynomial caps sign-rank at `(a + 1) ^ d`, and the dimensions cap it at
`2 ^ min a b`; together these bound what any sign-rank argument can ever
certify (ratio `≲ log n`, additive gap `≲ n / 2`).
-/

namespace HeadComplexity

/-- Helper lemma: two-block decomposition of head attention denominator.
`D_h(x, y) = A_h(x) + B_h(y)`. -/
noncomputable def headA {n d : ℕ} {a b : ℕ} (hab : n = a + b)
    (H : Head n d) (x : Fin a → Bool) : ℝ :=
  H.sigma (hab ▸ blockJoin x (fun _ => false)) none +
  ∑ i : Fin a, H.sigma (hab ▸ blockJoin x (fun _ => false)) (some (hab ▸ Fin.castAdd b i))

noncomputable def headB {n d : ℕ} {a b : ℕ} (hab : n = a + b)
    (H : Head n d) (y : Fin b → Bool) : ℝ :=
  ∑ j : Fin b, H.sigma (hab ▸ blockJoin (fun _ => false) y) (some (hab ▸ Fin.natAdd a j))


/-- Helper lemma for PROOFS.md P2.1: two-block decomposition of a head's
attention denominator, `D_h(x, y) = A_h(x) + B_h(y)`. -/
theorem denominator_eq_headA_add_headB {n d : ℕ} {a b : ℕ} (hab : n = a + b)
    (H : Head n d) (x : Fin a → Bool) (y : Fin b → Bool) :
    H.denominator (hab ▸ blockJoin x y) = headA hab H x + headB hab H y := by
  subst n
  simp only [Head.denominator, Fintype.sum_option, headA, headB]
  rw [Fin.sum_univ_add]
  simp [Head.sigma, Head.x, Head.seqTok]
  ring

/-- Positivity of the left denominator block (PROOFS.md P2.1): `A_h(x) > 0`, since
its query term `σ_none` is a positive exponential (`Head.sigma_pos`) and every
remaining left term is nonnegative (`Finset.sum_nonneg`). -/
theorem headA_pos {n d a b : ℕ} (hab : n = a + b) (H : Head n d) (x : Fin a → Bool) :
    0 < headA hab H x := by
  unfold headA
  have h1 : 0 < H.sigma (hab ▸ blockJoin x (fun _ => false)) none := H.sigma_pos _ _
  have h2 : 0 ≤ ∑ i : Fin a,
      H.sigma (hab ▸ blockJoin x (fun _ => false)) (some (hab ▸ Fin.castAdd b i)) :=
    Finset.sum_nonneg (fun _ _ => (H.sigma_pos _ _).le)
  exact add_pos_of_pos_of_nonneg h1 h2

/-- Nonnegativity of the right denominator block (PROOFS.md P2.1): `B_h(y) ≥ 0`,
a finite sum of positive exponentials (`Head.sigma_pos`, `Finset.sum_nonneg`). -/
theorem headB_nonneg {n d a b : ℕ} (hab : n = a + b) (H : Head n d) (y : Fin b → Bool) :
    0 ≤ headB hab H y := by
  unfold headB
  exact Finset.sum_nonneg (fun j _ => (H.sigma_pos _ _).le)

/-- Positivity of the cleared multiplier (PROOFS.md P2.2): the product of the `H`
head denominators is positive (`Head.denominator_pos`, `Finset.prod_pos`), so
multiplying the softmax score by it preserves signs entrywise. -/
theorem denominator_prod_pos {n d H : ℕ} (Hs : HeadFamily n d H) (z : Fin n → Bool) :
    0 < ∏ h : Fin H, (Hs h).denominator z := by
  exact Finset.prod_pos (fun h _ => (Hs h).denominator_pos z)

/-- Rank-count arithmetic of the bridge (PROOFS.md P2.3): the two boundary head
subsets (`∅` and the full set) contribute one rank-one piece each, and each of the
`2^H − 2` interior subsets contributes two, for a total
`2·(2^H − 2) + 2 = 2^(H+1) − 2` (using `2 ≤ 2^H` from `H ≥ 1` and
`2^(H+1) = 2·2^H`). -/
theorem two_mul_two_pow_sub (H : ℕ) (hH : 1 ≤ H) :
    2 * (2 ^ H - 2) + 2 = 2 ^ (H + 1) - 2 := by
  have h2 : 2 ≤ 2 ^ H := by
    calc 2 = 2 ^ 1 := by rfl
    _ ≤ 2 ^ H := Nat.pow_le_pow_right (by decide) hH
  rw [pow_succ]
  omega

open scoped InnerProductSpace in
/-- Two-block split of a head's numerator readout (PROOFS.md P2.1): the readout
`u_h(x, y) = ⟪w, numerator_h (blockJoin x y)⟫` splits additively as `A'(x) + B'(y)`,
because each position's contribution `σ_p · ⟪w, value_p⟫` depends only on the
single input bit at position `p` (`Head_scoreTerm_single`, `Head_scoreTerm_none_const`
in `ModelToPolynomial`).  Peel the query term with `Fintype.sum_option`, then split
the `some` positions into the left (`Fin.castAdd`) and right (`Fin.natAdd`) blocks
with `Fin.sum_univ_add`; `real_inner_sum`/`inner_smul_right` distribute the readout
over the position sum.  The proved companion is `denominator_eq_headA_add_headB`. -/
theorem exists_numerator_readout_two_block_split {a b d : ℕ}
    (H : Head (a + b) d) (w : Vec d) :
    ∃ (A' : (Fin a → Bool) → ℝ) (B' : (Fin b → Bool) → ℝ),
      ∀ (x : Fin a → Bool) (y : Fin b → Bool),
        ⟪w, H.numerator (blockJoin x y)⟫_ℝ = A' x + B' y := by
  use fun x =>
    H.sigma (blockJoin x (fun _ => false)) none * ⟪w, H.value (blockJoin x (fun _ => false)) none⟫_ℝ +
    ∑ i : Fin a, H.sigma (blockJoin x (fun _ => false)) (some (Fin.castAdd b i)) *
      ⟪w, H.value (blockJoin x (fun _ => false)) (some (Fin.castAdd b i))⟫_ℝ
  use fun y =>
    ∑ j : Fin b, H.sigma (blockJoin (fun _ => false) y) (some (Fin.natAdd a j)) *
      ⟪w, H.value (blockJoin (fun _ => false) y) (some (Fin.natAdd a j))⟫_ℝ
  intro x y
  unfold Head.numerator
  rw [Fintype.sum_option, Fin.sum_univ_add]
  rw [inner_add_right, inner_add_right, inner_sum, inner_sum]
  simp only [inner_smul_right]
  simp [Head.sigma, Head.value, Head.x, Head.seqTok]
  ring

/-- **Sign-rank bridge** (theorem 028 of the corpus): `H ≥ 1` heads give
sign-rank at most `2 ^ (H + 1) - 2` under the left/right block partition.
(`H = 0` is genuinely excluded: a constant function has sign-rank `1 > 0`.) -/
theorem signRank_le_of_computableWithHeadsN {a b H : ℕ}
    {f : (Fin (a + b) → Bool) → Bool} (hH : 1 ≤ H)
    (h : computableWithHeadsN (a + b) H f) :
    signRank (signMatrix a b f) ≤ 2 ^ (H + 1) - 2 := by
  sorry

/-- The bridge instantiated at the optimum: sign-rank bounds `H*` from below
for any nonconstant function (`1 ≤ H*`). -/
theorem signRank_le_pow_HStar (a b : ℕ) (f : (Fin (a + b) → Bool) → Bool)
    (hH : 1 ≤ HStar (a + b) f) :
    signRank (signMatrix a b f) ≤ 2 ^ (HStar (a + b) f + 1) - 2 :=
  signRank_le_of_computableWithHeadsN hH (HStar_computable f)

private lemma choose_succ_le_mul (a d : ℕ) : a.choose (d + 1) ≤ a * a.choose d := by
  have h1 : a.choose (d + 1) ≤ a.choose (d + 1) * (d + 1) := by
    conv_lhs => rw [← Nat.mul_one (a.choose (d + 1))]
    apply Nat.mul_le_mul_left
    omega
  have h2 : a.choose (d + 1) * (d + 1) = a.choose d * (a - d) := Nat.choose_succ_right_eq a d
  have h3 : a.choose d * (a - d) ≤ a.choose d * a := by
    apply Nat.mul_le_mul_left
    omega
  calc a.choose (d + 1)
    _ ≤ a.choose (d + 1) * (d + 1) := h1
    _ = a.choose d * (a - d) := h2
    _ ≤ a.choose d * a := h3
    _ = a * a.choose d := Nat.mul_comm _ _

/-- Counting bound for `signRank_le_of_thresholdDegLE` (PROOFS.md P3.3): the
number of left sub-monomials of degree `≤ d` in `a` variables, `∑_{i ≤ d}
C(a, i)`, is at most `(a + 1) ^ d`.  Induction on `d`: the step uses
`C(a, d+1) ≤ a · C(a, d)` (from `Nat.succ_mul_choose_eq` / `Nat.choose_succ_right_eq`)
together with `C(a, d) ≤ ∑_{i ≤ d} C(a, i) ≤ (a + 1) ^ d` (a term is `≤` the sum,
which is `≤` the inductive bound). -/
theorem sum_choose_le_pow (a d : ℕ) :
    ∑ i ∈ Finset.range (d + 1), a.choose i ≤ (a + 1) ^ d := by
  induction d with
  | zero =>
    simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have h_term_le_sum : a.choose d ≤ ∑ i ∈ Finset.range (d + 1), a.choose i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self d))
    have h_choose_le : a.choose (d + 1) ≤ a * (a + 1) ^ d := calc
      a.choose (d + 1) ≤ a * a.choose d := choose_succ_le_mul a d
      _ ≤ a * (a + 1) ^ d := Nat.mul_le_mul_left a (h_term_le_sum.trans ih)
    calc ∑ i ∈ Finset.range (d + 1), a.choose i + a.choose (d + 1)
      _ ≤ (a + 1) ^ d + a * (a + 1) ^ d := Nat.add_le_add ih h_choose_le
      _ = (1 + a) * (a + 1) ^ d := by ring
      _ = (a + 1) ^ (d + 1) := by ring

/-- Count of left sub-monomials of degree `≤ d` (PROOFS.md P3.2/P3.3): the number
of subsets of `Fin a` of size at most `d` is `∑_{i ≤ d} C(a, i)`.  Partition the
size-`≤ d` subsets by their cardinality: `Finset.powersetCard i univ` has exactly
`C(a, i)` elements (`Finset.card_powersetCard` with `Finset.card_fin`), and the
size-`≤ d` subsets are the disjoint union of these over `i ∈ range (d+1)`
(`Finset.card_biUnion` on the pairwise-disjoint `powersetCard` layers). -/
theorem card_subsets_card_le (a d : ℕ) :
    ((Finset.univ : Finset (Fin a)).powerset.filter (fun μ => μ.card ≤ d)).card
      = ∑ i ∈ Finset.range (d + 1), a.choose i := by
  have h_eq : ((Finset.univ : Finset (Fin a)).powerset.filter (fun μ => μ.card ≤ d)) =
      (Finset.range (d + 1)).biUnion (fun i => Finset.powersetCard i (Finset.univ : Finset (Fin a))) := by
    ext μ
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · intro h
      refine ⟨μ.card, Nat.lt_succ_iff.mpr h.2, h.1, rfl⟩
    · rintro ⟨i, hi, hμ1, hμ2⟩
      exact ⟨hμ1, hμ2 ▸ Nat.le_of_lt_succ hi⟩
  rw [h_eq]
  rw [Finset.card_biUnion]
  · congr 1
    ext i
    rw [Finset.card_powersetCard, Finset.card_fin]
  · intro i _ j _ hij
    simp only [Set.PairwiseDisjoint, Function.onFun, Finset.disjoint_left, Finset.mem_powersetCard]
    intro μ hμi hμj
    exact hij (hμi.2.symm.trans hμj.2)

/-- P3.1: a degree-`d` sign representation may be taken multilinear
(substitute `x_i^e ↦ x_i`; cube evaluations are unchanged and the total
degree does not increase). -/
theorem exists_multilinear_signRepr {n d : ℕ} {f : (Fin n → Bool) → Bool}
    (h : ThresholdDegLE f d) :
    ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ d ∧
      (∀ i, P.degreeOf i ≤ 1) ∧ SignRepresents P f := by
  sorry

/-- P3.2 + η-shift: a multilinear degree-`d` sign representation exhibits the
sign matrix as a sum of one outer product per left sub-monomial of degree
`≤ d` (grouping `P = ∑_μ x^μ c_μ(y)`), plus the strictifying constant folded
into the `μ = ∅` term; hence the rank bound by the monomial count. -/
theorem signRank_le_of_multilinear_signRepr {a b d : ℕ}
    {f : (Fin (a + b) → Bool) → Bool} (P : MvPolynomial (Fin (a + b)) ℝ)
    (hdeg : P.totalDegree ≤ d) (hml : ∀ i, P.degreeOf i ≤ 1)
    (hsr : SignRepresents P f) :
    signRank (signMatrix a b f) ≤ ∑ i ∈ Finset.range (d + 1), a.choose i := by
  sorry

/-- Multilinearization & left-monomial factorization core of the degree half
(PROOFS.md P3.1–P3.2): a degree-`d` sign representation `P` multilinearizes on
the cube to `P̃` of the same total degree, which groups by its left sub-monomial
`x^μ` (`|μ| ≤ d`) as `M = ∑_{|μ| ≤ d} (x^μ)·c_μ(y)`, a sum of
`#{μ : |μ| ≤ d} = ∑_{i ≤ d} C(a, i)` rank-one outer products; the η-shift
(P2.4/P3.3) strictifies the sign match, so `signRank ≤ ∑_{i ≤ d} C(a, i)`.  The
arithmetic tail `∑_{i ≤ d} C(a, i) ≤ (a + 1) ^ d` is `sum_choose_le_pow`. -/
private theorem signRank_le_sum_choose {a b d : ℕ}
    {f : (Fin (a + b) → Bool) → Bool} (h : ThresholdDegLE f d) :
    signRank (signMatrix a b f) ≤ ∑ i ∈ Finset.range (d + 1), a.choose i := by
  rcases exists_multilinear_signRepr h with ⟨P, hdeg, hml, hsr⟩
  exact signRank_le_of_multilinear_signRepr P hdeg hml hsr

/-- **Theorem C, degree half** (ceiling of the sign-rank route): a degree-`d`
sign representation factors the sign matrix through its monomials in the
left-block variables, so sign-rank is at most `(a + 1) ^ d`.  Hence sign-rank
can never certify more than `H* ≳ d · log₂ a` for a degree-`d` function.
(PROOFS.md P3: the linear-algebra core is `signRank_le_sum_choose`, the count
`sum_choose_le_pow`.) -/
theorem signRank_le_of_thresholdDegLE {a b d : ℕ}
    {f : (Fin (a + b) → Bool) → Bool} (h : ThresholdDegLE f d) :
    signRank (signMatrix a b f) ≤ (a + 1) ^ d :=
  (signRank_le_sum_choose h).trans (sum_choose_le_pow a d)

/-- **Theorem C, dimension half**: sign-rank is capped by the matrix
dimensions, `signRank ≤ 2 ^ min a b`.  Together with the degree half this
bounds the additive gap any sign-rank argument can certify by `≈ n / 2`. -/
theorem signRank_le_two_pow_min {a b : ℕ} (f : (Fin (a + b) → Bool) → Bool) :
    signRank (signMatrix a b f) ≤ 2 ^ min a b := by
  have h1 : signRank (signMatrix a b f) ≤ (signMatrix a b f).rank :=
    signRank_le_rank _
  have hw : (signMatrix a b f).rank ≤ Fintype.card (Fin b → Bool) :=
    Matrix.rank_le_card_width _
  have hh : (signMatrix a b f).rank ≤ Fintype.card (Fin a → Bool) :=
    Matrix.rank_le_card_height _
  have ca : Fintype.card (Fin a → Bool) = 2 ^ a := by
    simp
  have cb : Fintype.card (Fin b → Bool) = 2 ^ b := by
    simp
  rcases Nat.le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact h1.trans (by rw [ca] at hh; exact hh)
  · rw [min_eq_right hba]
    exact h1.trans (by rw [cb] at hw; exact hw)


/-! ### Manual decomposition round (PROOFS.md P2/P3), 2026-08-24.
New sub-leaves for the two bridge sorries; the parents above should be
reassembled from these (move declarations up as needed). -/

/-- P2.2 (clearing, pure real algebra): with positive denominators the
threshold test on the softmax score is equivalent to positivity of the
cleared combination. -/
theorem cleared_score_iff {H : ℕ} (τ : ℝ) (u D : Fin H → ℝ)
    (hD : ∀ h, 0 < D h) :
    (τ < ∑ h, u h / D h) ↔
      0 < (∑ h, u h * ∏ h' ∈ Finset.univ.erase h, D h') - τ * ∏ h, D h := by
  have hP : 0 < ∏ h, D h := Finset.prod_pos (fun h _ => hD h)
  have h_eq : (∑ h, u h / D h) * (∏ h, D h) = ∑ h, (u h * ∏ h' ∈ Finset.univ.erase h, D h') := by
    rw [Finset.sum_mul]
    congr 1
    ext h
    have h_erase : (∏ h', D h') = D h * ∏ h' ∈ Finset.univ.erase h, D h' :=
      (Finset.mul_prod_erase Finset.univ D (Finset.mem_univ h)).symm
    rw [h_erase, ← mul_assoc, div_mul_cancel₀ (u h) (ne_of_gt (hD h))]
  constructor
  · intro hlt
    have h1 : τ * ∏ h, D h < (∑ h, u h / D h) * ∏ h, D h :=
      mul_lt_mul_of_pos_right hlt hP
    rw [h_eq] at h1
    linarith
  · intro hgt
    have h1 : τ * ∏ h, D h < (∑ h, u h / D h) * ∏ h, D h := by
      rw [h_eq]
      linarith
    exact lt_of_mul_lt_mul_right h1 (le_of_lt hP)

/-- P2.3+P2.4 (linear-algebra core of the bridge): any function whose strict
sign is realized by a two-block head-form score has sign-rank at most
`2^(H+1) - 2`.  Proof plan: clear denominators (`cleared_score_iff`), group
the cleared matrix by the subset `T ⊆ [H]` of factors contributing their
left part (`2(2^H - 2) + 2` outer products, boundary subsets merging), and
strictify the false side by the η-shift absorbed into the `T = ∅` piece. -/
theorem signRank_le_of_headForm {a b H : ℕ} (hH : 1 ≤ H) (τ : ℝ)
    {f : (Fin (a + b) → Bool) → Bool}
    (A : Fin H → (Fin a → Bool) → ℝ) (B : Fin H → (Fin b → Bool) → ℝ)
    (A' : Fin H → (Fin a → Bool) → ℝ) (B' : Fin H → (Fin b → Bool) → ℝ)
    (hpos : ∀ h x y, 0 < A h x + B h y)
    (hf : ∀ x y, f (blockJoin x y) = true ↔
      τ < ∑ h, (A' h x + B' h y) / (A h x + B h y)) :
    signRank (signMatrix a b f) ≤ 2 ^ (H + 1) - 2 := by
  sorry

end HeadComplexity
