import HeadComplexity.Polynomial.SymmetricLowerBound
import HeadComplexity.Polynomial.UnivariateReduction
import HeadComplexity.Separations.ThresholdDegAux
import HeadComplexity.TypicalLogCloseness.ThresholdDegreeBridge
import HeadComplexity.TypicalLogCloseness.FracAtomBridge

set_option linter.style.header false

/-!
# One marked bit plus a symmetric block: exact equality (P04)

For `f(z, y) = F(z, |y|)` with one marked Boolean bit `z` and an arbitrary
table `F : Bool → ℕ → Bool` on a fully symmetric `m`-bit block `y`,

    thresholdDeg f = RelaxedPOIC2 f = POIC2 f = HStar f.

Companion source: `notes/ONE_MARKED_BIT_EXACT_2026-08-24.md` (P04) in the
research archive; the compiler is corpus theorem 138 (positive-statistic
raw-bit degree span) with denominators `B_h(z, k) = k + h + 2 d z`.

Proof shape.  The sandwich `thresholdDeg ≤ RelaxedPOIC2 ≤ POIC2 ≤ HStar` is
already proved (`thresholdDeg_le_relaxedPOIC2_le_POIC2_le_HStar`), so the
whole content is the converse `HStar f ≤ thresholdDeg f`:

1. slice a minimal strict sign polynomial at `z = 0, 1`; the slice
   difference automatically has total degree `≤ d - 1` because every
   monomial surviving the difference contains `z`;
2. symmetrize each slice over the `y`-block and reduce to univariate
   polynomials in the Hamming weight (`symmetrize`,
   `exists_univariate_of_symmetric`);
3. run the theorem-138 interpolation: the products
   `Q_h^{(t)} = ∏_{j ≠ h} (X + C (j + 1 + 2 d t))` form a basis of the
   degree-`< d` polynomials, the two slices share the leading coefficient,
   and affine numerators `a_h + μ_h k + c_h z` over the legal denominators
   `k + (h + 1) + 2 d z` reproduce the table;
4. each ratio is one `FracAtom` (`exists_fracAtom_eval_eq`), giving
   `fracComputable (m+1) d` and `HStar ≤ d`.

Every `sorry` below is one Jules target; doc comments fix the local
contract.  Statements are frozen: repair requests go through BLOCKER files,
never silent edits.
-/

namespace HeadComplexity

open MvPolynomial Finset
open scoped BigOperators

variable {m : ℕ}

/-! ## The marked-bit model -/

/-- Prepend the marked bit to the symmetric block. -/
def consBit (z : Bool) (y : Fin m → Bool) : Fin (m + 1) → Bool :=
  Fin.cases z y

/-- The symmetric block of an input. -/
def tailBits (x : Fin (m + 1) → Bool) : Fin m → Bool := fun i => x i.succ

/-- One marked bit plus a fully symmetric block: `f(z, y) = F(z, |y|)`. -/
def markedFn (F : Bool → ℕ → Bool) : (Fin (m + 1) → Bool) → Bool :=
  fun x => F (x 0) (hammingWeight (tailBits x))

@[simp] theorem consBit_zero (z : Bool) (y : Fin m → Bool) : consBit z y 0 = z := rfl

@[simp] theorem consBit_succ (z : Bool) (y : Fin m → Bool) (i : Fin m) :
    consBit z y i.succ = y i := rfl

@[simp] theorem tailBits_consBit (z : Bool) (y : Fin m → Bool) :
    tailBits (consBit z y) = y := rfl

@[simp] theorem markedFn_consBit (F : Bool → ℕ → Bool) (z : Bool) (y : Fin m → Bool) :
    markedFn F (consBit z y) = F z (hammingWeight y) := rfl

/-- Substitute the marked variable by the constant `t` and renumber the block:
the slice of a polynomial at `z = t`. -/
noncomputable def sliceAt (t : ℝ) (P : MvPolynomial (Fin (m + 1)) ℝ) :
    MvPolynomial (Fin m) ℝ :=
  aeval (Fin.cases (C t) X) P

/-- [MB01] Slice evaluation: evaluating the slice on the block equals
evaluating the original polynomial on the extended input.  Route: `aeval`
composition — push `eval (cubePoint y)` through `aeval (Fin.cases (C t) X)`
via `eval_aeval`/`aeval_def` and case-split the variable index with
`Fin.cases`; note `cubePoint (consBit z y) 0 = boolToReal z` and
`… i.succ = cubePoint y i`. -/
theorem sliceAt_cube_eval (z : Bool) (y : Fin m → Bool)
    (P : MvPolynomial (Fin (m + 1)) ℝ) :
    eval (cubePoint y) (sliceAt (boolToReal z) P) =
      eval (cubePoint (consBit z y)) P := by
  unfold sliceAt
  rw [aeval_def, eval_eval₂]
  have h1 : (eval (cubePoint y)).comp (algebraMap ℝ (MvPolynomial (Fin m) ℝ)) = RingHom.id ℝ := by
    ext r
    simp [eval_C]
  have h2 : (fun s : Fin (m + 1) => eval (cubePoint y) (Fin.cases (C (boolToReal z)) X s)) =
      cubePoint (consBit z y) := by
    ext s
    induction s using Fin.cases with
    | zero =>
      simp [cubePoint, boolToReal]
    | succ i =>
      simp [cubePoint]
  rw [h1, h2, eval₂_id]

/-- [MB02] Slicing never raises the total degree.  Route: `sliceAt` is
`aeval` sending `X 0 ↦ C t` (degree `0`) and `X i.succ ↦ X i` (degree `1`);
bound via `aeval_def`/`eval₂` as a sum over the support, using
`totalDegree_finsetSum_le`, `totalDegree_mul`, `totalDegree_prod`, and
`totalDegree_C/X`. -/
theorem sliceAt_totalDegree_le (t : ℝ) (P : MvPolynomial (Fin (m + 1)) ℝ) :
    (sliceAt t P).totalDegree ≤ P.totalDegree := by
  dsimp [sliceAt]
  conv_lhs => rw [as_sum P, map_sum]
  refine (totalDegree_finsetSum_le (d := P.totalDegree) (fun d hd => ?_))
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  have h_bound :
      ∑ i ∈ d.support, (Fin.cases (C t) X i ^ d i : MvPolynomial (Fin m) ℝ).totalDegree ≤
        ∑ i ∈ d.support, d i := by
    refine sum_le_sum (fun i _ => ?_)
    refine (totalDegree_pow _ _).trans ?_
    have h_deg : (Fin.cases (C t) X i : MvPolynomial (Fin m) ℝ).totalDegree ≤ 1 := by
      refine Fin.cases ?_ (fun _ => ?_) i
      · rw [Fin.cases_zero, totalDegree_C]
        exact zero_le_one
      · rw [Fin.cases_succ, totalDegree_X]
    calc d i * (Fin.cases (C t) X i : MvPolynomial (Fin m) ℝ).totalDegree
      _ ≤ d i * 1 := Nat.mul_le_mul_left (d i) h_deg
      _ = d i := mul_one (d i)
  refine h_bound.trans ?_
  have h_sum : ∑ i ∈ d.support, d i = d.sum (fun _ e => e) := rfl
  rw [h_sum]
  exact le_totalDegree hd

private lemma sliceAt_monomial (t : ℝ) (s : Fin (m + 1) →₀ ℕ) (c : ℝ) :
    sliceAt t ((monomial s) c) =
      (C (c * t ^ (s 0))) * ∏ i : Fin m, (X i) ^ (s i.succ) := by
  dsimp [sliceAt]
  rw [aeval_monomial]
  dsimp
  rw [Finsupp.prod_fintype s _ (fun _ => pow_zero _)]
  rw [Fin.prod_univ_succ]
  simp [Fin.cases]
  ring

private lemma sliceDiff_monomial (s : Fin (m + 1) →₀ ℕ) (c : ℝ) :
    sliceAt 1 ((monomial s) c) - sliceAt 0 ((monomial s) c) =
      C (c * (1 ^ (s 0) - 0 ^ (s 0))) * ∏ i : Fin m, (X i) ^ (s i.succ) := by
  rw [sliceAt_monomial, sliceAt_monomial]
  rw [← sub_mul, ← C_sub]
  congr 2
  ring

private lemma sliceDiff_monomial_totalDegree_le (s : Fin (m + 1) →₀ ℕ) (c : ℝ) :
    (sliceAt 1 ((monomial s) c) - sliceAt 0 ((monomial s) c)).totalDegree ≤
      ∑ i : Fin m, s i.succ := by
  rw [sliceDiff_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  rw [totalDegree_X]
  simp

private lemma sum_succ_le_sum_sub_one {d : ℕ} (hd : 1 ≤ d) (s : Fin (m + 1) →₀ ℕ)
    (hs_deg : s.sum (fun _ e => e) ≤ d) (hs0 : s 0 ≠ 0) :
    ∑ i : Fin m, s i.succ ≤ d - 1 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hs_deg
  rw [Fin.sum_univ_succ] at hs_deg
  have h1 : 1 ≤ s 0 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs0)
  omega

private lemma sliceDiff_monomial_eq_zero_of_s0_zero (s : Fin (m + 1) →₀ ℕ) (c : ℝ) (hs0 : s 0 = 0) :
    sliceAt 1 ((monomial s) c) - sliceAt 0 ((monomial s) c) = 0 := by
  rw [sliceDiff_monomial, hs0]
  norm_num

private lemma sliceAt_sum (t : ℝ) (s : Finset (Fin (m + 1) →₀ ℕ)) (f : (Fin (m + 1) →₀ ℕ) → MvPolynomial (Fin (m + 1)) ℝ) :
    sliceAt t (∑ x ∈ s, f x) = ∑ x ∈ s, sliceAt t (f x) :=
  aeval_sum _ _ _

/-- [MB03] The slice difference loses one degree: every monomial that
survives `sliceAt 1 P - sliceAt 0 P` comes from a monomial of `P`
containing the marked variable, whose block part therefore has degree
`≤ d - 1`.  Route: write both slices as support sums; monomials with
marked exponent `0` contribute equally and cancel; a monomial with marked
exponent `e ≥ 1` and block degree `b` has `e + b ≤ d`, so `b ≤ d - 1`;
bound the difference's total degree by the maximum surviving block degree. -/
theorem sliceDiff_totalDegree_le {d : ℕ} (hd : 1 ≤ d)
    (P : MvPolynomial (Fin (m + 1)) ℝ) (hP : P.totalDegree ≤ d) :
    (sliceAt 1 P - sliceAt 0 P).totalDegree ≤ d - 1 := by
  have h1 : sliceAt 1 P = ∑ s ∈ P.support, sliceAt 1 (monomial s (coeff s P)) := by
    conv_lhs => rw [as_sum P]
    exact sliceAt_sum 1 P.support _
  have h0 : sliceAt 0 P = ∑ s ∈ P.support, sliceAt 0 (monomial s (coeff s P)) := by
    conv_lhs => rw [as_sum P]
    exact sliceAt_sum 0 P.support _
  rw [h1, h0, ← sum_sub_distrib]
  refine totalDegree_finsetSum_le (fun s hs => ?_)
  by_cases hs0 : s 0 = 0
  · rw [sliceDiff_monomial_eq_zero_of_s0_zero s _ hs0]
    rw [totalDegree_zero]
    exact Nat.zero_le _
  · refine (sliceDiff_monomial_totalDegree_le s _).trans ?_
    exact sum_succ_le_sum_sub_one hd s (le_totalDegree hs |>.trans hP) hs0

/-- [MB04] The grid pair.  From a minimal strict witness for `markedFn F`,
symmetrizing each slice and reducing to the Hamming weight produces a pair
of univariate polynomials of degrees `≤ d` and `≤ d - 1` reproducing the
strict signs of the table on the whole grid `{0,1} × {0,…,m}`.  Route:
apply `symmetrize` and `exists_univariate_of_symmetric` to `sliceAt 0 P`
and to the difference `sliceAt 1 P - sliceAt 0 P` (degrees by MB02/MB03);
`symmetrize` is a sum of renames, so it is additive and commutes with
evaluation averages; strictness of each slice target
(`fun y => F z (hammingWeight y)` is `symmetricFn (F z)`) transports by
`symmetrize_strictSignRep`; finally evaluate with MB01 and
`exists_hammingWeight_eq`. -/
theorem exists_grid_pair {d : ℕ} (hd : 1 ≤ d) (F : Bool → ℕ → Bool)
    (P : MvPolynomial (Fin (m + 1)) ℝ) (hdeg : P.totalDegree ≤ d)
    (hrep : StrictSignRep P (markedFn F)) :
    ∃ p₀ p₁ : Polynomial ℝ, p₀.natDegree ≤ d ∧ p₁.natDegree ≤ d - 1 ∧
      ∀ (z : Bool) (y : Fin m → Bool),
        (F z (hammingWeight y) = true →
          0 < p₀.eval (hammingWeight y : ℝ) +
            boolToReal z * p₁.eval (hammingWeight y : ℝ)) ∧
        (F z (hammingWeight y) = false →
          p₀.eval (hammingWeight y : ℝ) +
            boolToReal z * p₁.eval (hammingWeight y : ℝ) < 0) := by
  sorry

/-! ## The theorem-138 compiler (univariate layer) -/

section Compiler

variable (d : ℕ)

/-- The denominator of head `h` on the `z = t` slice, as a univariate
polynomial in the Hamming weight: `X + (h + 1 + 2 d t)`. -/
noncomputable def denPoly (h : Fin d) (t : ℝ) : Polynomial ℝ :=
  Polynomial.X + Polynomial.C ((h : ℝ) + 1 + 2 * d * t)

/-- The product of all denominators except head `h` on the `z = t` slice. -/
noncomputable def coprod (h : Fin d) (t : ℝ) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.erase h, denPoly d j t

/-- [MB05] Structure of the coproducts: degree `d - 1`, leading coefficient
`1`, and diagonalizing evaluations at the nodes `u_j = -(j + 1 + 2 d t)`:
`coprod h t` is nonzero at `u_h` and vanishes at `u_j` for `j ≠ h`.
Route: `denPoly` is monic of degree one (`Polynomial.monic_X_add_C`);
products of monics are monic (`Polynomial.monic_prod`), degrees add
(`Polynomial.natDegree_prod`); the evaluation facts are
`Polynomial.eval_prod` plus the linear-factor root arithmetic — the nodes
are pairwise distinct because `j ↦ j + 1 + 2 d t` is injective for fixed
`t`. -/
theorem coprod_structure (h : Fin d) (t : ℝ) :
    (coprod d h t).natDegree = d - 1 ∧ (coprod d h t).Monic ∧
      (coprod d h t).eval (-((h : ℝ) + 1 + 2 * d * t)) ≠ 0 ∧
      ∀ j : Fin d, j ≠ h →
        (coprod d j t).eval (-((h : ℝ) + 1 + 2 * d * t)) = 0 := by
  sorry

/-- [MB06] Interpolation basis: every polynomial of degree `< d` is a linear
combination of the `d` coproducts of a fixed slice.  Route: the map
`c ↦ ∑ h, c h • coprod h t` into polynomials of degree `≤ d - 1` is
injective by evaluating at the `d` diagonalizing nodes (MB05), and the two
spaces have the same finite dimension; alternatively interpolate directly:
match values at the `d` nodes by solving the diagonal system, then the
difference has `d` roots and degree `≤ d - 1`, hence vanishes
(`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'` or root
counting via `Polynomial.card_roots'`). -/
theorem exists_coprod_interpolation (hd : 1 ≤ d) (t : ℝ) (R : Polynomial ℝ)
    (hR : R.natDegree ≤ d - 1) :
    ∃ cvec : Fin d → ℝ, R = ∑ h, Polynomial.C (cvec h) * coprod d h t := by
  sorry

/-- [MB07] The theorem-138 numerator construction.  Given the grid pair
`(p₀, p₁)` with `deg p₀ ≤ d`, `deg p₁ ≤ d - 1`, there are affine numerator
data `a, μ, c : Fin d → ℝ` with the two exact slice identities below.
Route (mirrors the corpus proof): both slices `p₀` and `p₀ + p₁` share the
`u^d` coefficient `ℓ := p₀.coeff d`; put `μ` with `∑ μ_h = ℓ` (e.g. all in
head `0`); then `p₀ - ∑ μ_h • X * coprod h 0` has degree `≤ d - 1` because
each `X * coprod h 0` is monic of degree `d` — expand it by MB06 at `t = 0`
to get `a`; transport to the `t = 1` slice: `∑ (a_h + μ_h X) coprod h 1`
again has `u^d`-coefficient `ℓ`, so the difference from `p₀ + p₁` has
degree `≤ d - 1` — expand by MB06 at `t = 1` to get `c`. -/
theorem exists_numerators (hd : 1 ≤ d) (p₀ p₁ : Polynomial ℝ)
    (h₀ : p₀.natDegree ≤ d) (h₁ : p₁.natDegree ≤ d - 1) :
    ∃ a μ c : Fin d → ℝ,
      p₀ = ∑ h, (Polynomial.C (a h) + Polynomial.C (μ h) * Polynomial.X) *
        coprod d h 0 ∧
      p₀ + p₁ = ∑ h, (Polynomial.C (a h + c h) + Polynomial.C (μ h) *
        Polynomial.X) * coprod d h 1 := by
  sorry

/-- [MB08] Pointwise sign transfer.  On the Boolean slice `z ∈ {0, 1}` and
any grid point `u = k ≥ 0`, the head sum with numerators
`a_h + μ_h u + c_h z` over the positive denominators `u + h + 1 + 2 d z`
has the sign of `p₀ + z p₁` at `u`.  Route: multiply by the positive product
of all `d` denominators (each is `≥ 1` for `u ≥ 0`, `z ∈ {0,1}`); the
cleared sum telescopes into the slice identity of MB07 evaluated at `u`
(`div_add_div`, `Finset.sum_div`, positivity of the product;
`Polynomial.eval_prod` connects `coprod` values with the denominator
product with one factor removed). -/
theorem head_sum_sign (hd : 1 ≤ d) (p₀ p₁ : Polynomial ℝ)
    (a μ c : Fin d → ℝ)
    (hid₀ : p₀ = ∑ h, (Polynomial.C (a h) + Polynomial.C (μ h) *
      Polynomial.X) * coprod d h 0)
    (hid₁ : p₀ + p₁ = ∑ h, (Polynomial.C (a h + c h) + Polynomial.C (μ h) *
      Polynomial.X) * coprod d h 1)
    (z : Bool) (k : ℕ) :
    (0 < ∑ h : Fin d, (a h + μ h * k + c h * boolToReal z) /
        ((k : ℝ) + (h : ℝ) + 1 + 2 * d * boolToReal z) ↔
      0 < p₀.eval (k : ℝ) + boolToReal z * p₁.eval (k : ℝ)) := by
  sorry

end Compiler

/-- [MB09] Atom realization: the compiled score is `d` fractional atoms.
Route: head `h` has numerator affine form `constant = a h`, marked slope
`c h`, block slopes all `μ h`, and denominator affine form
`constant = h + 1`, marked slope `2 d`, block slopes all `1` — the
denominator has strictly positive coefficients (`d ≥ 1`), so
`TypicalLogCloseness.exists_fracAtom_eval_eq` provides an atom whose value
at `x` is exactly the displayed ratio at `u = hammingWeight (tailBits x)`,
`z = x 0`; note `∑ i, boolToReal (x i.succ) = hammingWeight (tailBits x)`.
Conclude `fracComputable (m + 1) d (markedFn F)` with constant `0` from
MB04 + MB07 + MB08. -/
theorem markedFn_fracComputable {d : ℕ} (hd : 1 ≤ d) (F : Bool → ℕ → Bool)
    (hTD : ThresholdDegLE (markedFn (m := m) F) d) :
    fracComputable (m + 1) d (markedFn (m := m) F) := by
  sorry

/-- [MB10] Degree-zero case: a function of threshold degree zero is
constant, and a constant function has `HStar = 0`.  Route: a strict sign
witness of total degree `0` is a constant polynomial `C c` whose sign is
fixed, so `markedFn F` is constant; `computableWithHeadsN_zero_iff` (or the
explicit zero-head model) gives `HStar = 0` via `Nat.find`/`HStar`
unfolding as in `HStar_f8`-style arguments. -/
theorem HStar_eq_zero_of_thresholdDeg_zero (F : Bool → ℕ → Bool)
    (h0 : thresholdDeg (markedFn (m := m) F) = 0) :
    HStar (m + 1) (markedFn (m := m) F) = 0 := by
  sorry

/-! ## Assembly -/

/-- The compiled upper bound: `HStar ≤ thresholdDeg` for the marked-bit
class. -/
theorem HStar_markedFn_le (F : Bool → ℕ → Bool) :
    HStar (m + 1) (markedFn (m := m) F) ≤ thresholdDeg (markedFn (m := m) F) := by
  classical
  set f := markedFn (m := m) F with hf
  set d := thresholdDeg f with hdd
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [h0]
    exact Nat.le_of_eq (HStar_eq_zero_of_thresholdDeg_zero F (hdd ▸ h0))
  · have hTD : ThresholdDegLE f d := by
      have hex : ∃ k, ThresholdDegLE f k := exists_thresholdDegLE f
      rw [hdd, thresholdDeg, dif_pos hex]
      exact Nat.find_spec hex
    have hfrac := markedFn_fracComputable (m := m) hpos F hTD
    exact TypicalLogCloseness.HStar_le_of_fracComputable hfrac

/-- **P04 (one marked bit plus a symmetric block).**  For
`f(z, y) = F(z, |y|)` all four measures coincide:
`thresholdDeg = RelaxedPOIC2 = POIC2 = HStar`. -/
theorem markedBit_exact (F : Bool → ℕ → Bool) :
    thresholdDeg (markedFn (m := m) F) =
        TypicalLogCloseness.RelaxedPOIC2 (m + 1) (markedFn (m := m) F) ∧
      thresholdDeg (markedFn (m := m) F) =
        TypicalLogCloseness.POIC2 (m + 1) (markedFn (m := m) F) ∧
      thresholdDeg (markedFn (m := m) F) =
        HStar (m + 1) (markedFn (m := m) F) := by
  obtain ⟨h1, h2, h3⟩ :=
    TypicalLogCloseness.thresholdDeg_le_relaxedPOIC2_le_POIC2_le_HStar
      (markedFn (m := m) F)
  have hup := HStar_markedFn_le (m := m) F
  refine ⟨?_, ?_, ?_⟩ <;> omega

end HeadComplexity
