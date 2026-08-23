import HeadComplexity.Separations.Warren
import HeadComplexity.Separations.SignRankBridge
import HeadComplexity.Polynomial.ParityThresholdDegree

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

/-- **Split-shattering head bound** (mega-lab theorem, via Warren): if `f` is
computable with `H` heads and left-shatters `k` points, then
`2 ^ k ≤ (2 e k) ^ (2 H)`; equivalently `H* ≥ k / (2 log₂ (2 e k))`. -/
theorem pow_le_of_leftShatters {a b H k : ℕ}
    {f : (Fin (a + b) → Bool) → Bool} (hk : 1 ≤ k)
    (hcomp : computableWithHeadsN (a + b) H f) (hsh : LeftShatters f k) :
    (2 : ℝ) ^ k ≤ (2 * Real.exp 1 * k) ^ (2 * H) := by
  sorry

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

/-- Monotone-DNF upper bound (corpus theorem 029): one calibrated head per
term gives `H*(NDISJ_m) ≤ m`. -/
theorem HStar_ndisj_le (m : ℕ) : HStar (m + m) (ndisj m) ≤ m := by
  sorry

/-- `NDISJ_m` has threshold degree exactly `2` for `m ≥ 2`
(upper: `Σ x_i y_i - 1/2`; lower: `NDISJ_m` is not an LTF). -/
theorem thresholdDeg_ndisj {m : ℕ} (hm : 2 ≤ m) :
    thresholdDeg (ndisj m) = 2 := by
  sorry

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
