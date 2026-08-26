import HeadComplexity.TypicalLogCloseness.AffineForm
import Mathlib

set_option linter.style.header false

/-!
# The finite counting core of typical logarithmic closeness

This module is deliberately independent of H*, POIC₂, and Warren.  It records
the exact finite sets and isolates the elementary arithmetic obligations used
by the final theorem.
-/

namespace HeadComplexity.TypicalLogCloseness

open Finset

variable {F : Type*} [Fintype F] [DecidableEq F]

/-- The sublevel set of an integer-valued complexity measure. -/
def sublevel (q : F → ℕ) (Q : ℕ) : Finset F :=
  Finset.univ.filter fun f => q f ≤ Q

/-- Truth tables violating a logarithmic comparison. -/
def badLog (q h : F → ℕ) (C : ℕ) : Finset F :=
  Finset.univ.filter fun f => C * q f * (Nat.log 2 (q f) + 1) < h f

@[simp] theorem mem_sublevel {q : F → ℕ} {Q : ℕ} {f : F} :
    f ∈ sublevel q Q ↔ q f ≤ Q := by
  simp [sublevel]

@[simp] theorem mem_badLog {q h : F → ℕ} {C : ℕ} {f : F} :
    f ∈ badLog q h C ↔ C * q f * (Nat.log 2 (q f) + 1) < h f := by
  simp [badLog]

theorem badLog_subset_sublevel {q h : F → ℕ} {C Q : ℕ}
    (hgood : ∀ f, Q < q f → h f ≤ C * q f * (Nat.log 2 (q f) + 1)) :
    badLog q h C ⊆ sublevel q Q := by
  intro f hf
  rw [mem_badLog] at hf
  rw [mem_sublevel]
  by_contra hnle
  exact (Nat.not_lt_of_ge (hgood f (Nat.lt_of_not_ge hnle))) hf

theorem badLog_card_le_of_outside_bound {q h : F → ℕ} {C Q E : ℕ}
    (hgood : ∀ f, Q < q f → h f ≤ C * q f * (Nat.log 2 (q f) + 1))
    (hsmall : (sublevel q Q).card ≤ E) :
    (badLog q h C).card ≤ E :=
  (Finset.card_le_card (badLog_subset_sublevel hgood)).trans hsmall

/-- The threshold `⌊2ⁿ/(2An²)⌋` used to define the exceptional set. -/
def countingThreshold (n A : ℕ) : ℕ :=
  2 ^ n / (2 * A * n ^ 2)

/-- Exact contract for the exceptional-cardinality part of the abstract proof. -/
theorem exception_card
    (n A : ℕ) (hn : 2 ≤ n) (hA : 1 ≤ A)
    (q : F → ℕ)
    (hcount : ∀ Q, 1 ≤ Q → Q ≤ 2 ^ n →
      (sublevel q Q).card ≤ 2 ^ (A * n ^ 2 * Q))
    (hgrowth : 2 * A * n ^ 2 ≤ 2 ^ (n / 2)) :
    (sublevel q (countingThreshold n A)).card ≤ 2 ^ ((2 ^ n) / 2) := by
  have hDpos : 0 < 2 * A * n ^ 2 := by positivity
  have hhalf : 2 ^ (n / 2) ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self n 2)
  have hDle : 2 * A * n ^ 2 ≤ 2 ^ n := hgrowth.trans hhalf
  have hQpos : 1 ≤ countingThreshold n A := by
    have hpos : 0 < (2 ^ n) / (2 * A * n ^ 2) := Nat.div_pos hDle hDpos
    unfold countingThreshold
    omega
  have hQle : countingThreshold n A ≤ 2 ^ n := by
    exact (Nat.div_le_self _ _)
  have hraw := hcount (countingThreshold n A) hQpos hQle
  have hmul : (2 * A * n ^ 2) * countingThreshold n A ≤ 2 ^ n := by
    simpa [countingThreshold] using Nat.mul_div_le (2 ^ n) (2 * A * n ^ 2)
  have hexp : A * n ^ 2 * countingThreshold n A ≤ (2 ^ n) / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    calc
      (A * n ^ 2 * countingThreshold n A) * 2 =
          (2 * A * n ^ 2) * countingThreshold n A := by ring
      _ ≤ 2 ^ n := hmul
  exact hraw.trans (Nat.pow_le_pow_right (by norm_num) hexp)

/-- Outside the exceptional sublevel set, the bank estimate gives a linear
comparison. -/
theorem good_linear_bound
    (n A : ℕ) (hn : 2 ≤ n) (hA : 1 ≤ A)
    (q h : F → ℕ)
    (hbank : ∀ f, (n + 1) * h f ≤ 2 * (2 ^ n))
    (f : F) (hf : countingThreshold n A < q f) :
    h f ≤ 4 * A * n * q f := by
  have hDpos : 0 < 2 * A * n ^ 2 := by positivity
  have hNlt : 2 ^ n < q f * (2 * A * n ^ 2) := by
    apply (Nat.div_lt_iff_lt_mul hDpos).mp
    simpa [countingThreshold] using hf
  have hnh : n * h f < n * (4 * A * n * q f) := by
    calc
      n * h f ≤ (n + 1) * h f := by gcongr <;> omega
      _ ≤ 2 * (2 ^ n) := hbank f
      _ < 2 * (q f * (2 * A * n ^ 2)) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hNlt
      _ = n * (4 * A * n * q f) := by ring
  exact (Nat.mul_lt_mul_left (by omega : 0 < n)).mp hnh |>.le

/-- The growth condition converts the ambient dimension into a binary
logarithm of the complexity outside the exceptional sublevel set. -/
theorem good_log_lower_bound
    (n A : ℕ) (hn : 2 ≤ n) (hA : 1 ≤ A)
    (q : F → ℕ)
    (hgrowth : 2 * A * n ^ 2 ≤ 2 ^ (n / 2))
    (f : F) (hf : countingThreshold n A < q f) :
    n ≤ 2 * (Nat.log 2 (q f) + 1) := by
  have hDpos : 0 < 2 * A * n ^ 2 := by positivity
  have hNlt : 2 ^ n < q f * (2 * A * n ^ 2) := by
    apply (Nat.div_lt_iff_lt_mul hDpos).mp
    simpa [countingThreshold] using hf
  have hprod :
      2 ^ (n / 2) * 2 ^ (n - n / 2) < 2 ^ (n / 2) * q f := by
    calc
      2 ^ (n / 2) * 2 ^ (n - n / 2) = 2 ^ n := by
        rw [← pow_add]
        congr 1
        omega
      _ < q f * (2 * A * n ^ 2) := hNlt
      _ ≤ q f * 2 ^ (n / 2) := Nat.mul_le_mul_left _ hgrowth
      _ = 2 ^ (n / 2) * q f := by ring
  have hpow : 2 ^ (n - n / 2) ≤ q f := by
    exact ((Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ (n / 2))).mp hprod).le
  have hlog : n - n / 2 ≤ Nat.log 2 (q f) :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  omega

/-- Abstract typical-closeness theorem.  Notice that no assumption `q ≤ h`
is needed by the finite counting argument. -/
theorem typical_from_bank_and_warren
    (n A : ℕ) (hn : 2 ≤ n) (hA : 1 ≤ A)
    (q h : F → ℕ)
    (hbank : ∀ f, (n + 1) * h f ≤ 2 * (2 ^ n))
    (hcount : ∀ Q, 1 ≤ Q → Q ≤ 2 ^ n →
      (sublevel q Q).card ≤ 2 ^ (A * n ^ 2 * Q))
    (hgrowth : 2 * A * n ^ 2 ≤ 2 ^ (n / 2)) :
    (badLog q h (8 * A)).card ≤ 2 ^ ((2 ^ n) / 2) := by
  apply badLog_card_le_of_outside_bound (Q := countingThreshold n A)
  · intro f hf
    have hlin := good_linear_bound n A hn hA q h hbank f hf
    have hlog := good_log_lower_bound n A hn hA q hgrowth f hf
    calc
      h f ≤ 4 * A * n * q f := hlin
      _ ≤ 4 * A * (2 * (Nat.log 2 (q f) + 1)) * q f := by
        gcongr
      _ = (8 * A) * q f * (Nat.log 2 (q f) + 1) := by ring
  · exact exception_card n A hn hA q hcount hgrowth

end HeadComplexity.TypicalLogCloseness
