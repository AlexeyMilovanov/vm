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

/-- **Theorem C, degree half** (ceiling of the sign-rank route): a degree-`d`
sign representation factors the sign matrix through its monomials in the
left-block variables, so sign-rank is at most `(a + 1) ^ d`.  Hence sign-rank
can never certify more than `H* ≳ d · log₂ a` for a degree-`d` function. -/
theorem signRank_le_of_thresholdDegLE {a b d : ℕ}
    {f : (Fin (a + b) → Bool) → Bool} (h : ThresholdDegLE f d) :
    signRank (signMatrix a b f) ≤ (a + 1) ^ d := by
  sorry

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

end HeadComplexity
