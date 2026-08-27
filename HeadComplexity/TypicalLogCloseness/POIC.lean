import HeadComplexity.TypicalLogCloseness.AffineForm

set_option linter.style.header false

/-!
# Relaxed POIC₂ certificates

The representation is a sum of affine numerators divided by products of one
or two members of a shared strictly-positive affine denominator pool.  There
is deliberately no free global bias.
-/

namespace HeadComplexity.TypicalLogCloseness

open Finset
open scoped BigOperators

/-- A nonempty singleton or doubleton incidence set in a denominator pool. -/
structure Incidence (s : ℕ) where
  denoms : Finset (Fin s)
  nonempty : denoms.Nonempty
  card_le_two : denoms.card ≤ 2

/-- The discrete data of a labeled POIC₂ certificate. -/
structure Topology where
  denominatorCount : ℕ
  termCount : ℕ
  incidence : Fin termCount → Incidence denominatorCount

namespace Topology

/-- Canonical certificate cost: the maximum of pool size and term count. -/
def score (T : Topology) : ℕ := max T.denominatorCount T.termCount

end Topology

/-- Continuous coefficient data attached to a fixed topology. -/
structure Certificate (n : ℕ) (T : Topology) where
  denominators : Fin T.denominatorCount → AffineForm n
  numerators : Fin T.termCount → AffineForm n
  legal : ∀ j, (denominators j).StrictLegal

namespace Certificate

variable {T : Topology}

/-- The denominator product used by one term. -/
noncomputable def termDenominator (C : Certificate n T) (t : Fin T.termCount)
    (x : Cube n) : ℝ :=
  ∏ j ∈ (T.incidence t).denoms, (C.denominators j).eval x

theorem termDenominator_pos (C : Certificate n T) (t : Fin T.termCount)
    (x : Cube n) : 0 < C.termDenominator t x := by
  unfold termDenominator
  exact Finset.prod_pos fun j _ => (C.denominators j).eval_pos (C.legal j) x

/-- Evaluation of a no-bias POIC₂ certificate. -/
noncomputable def eval (C : Certificate n T) (x : Cube n) : ℝ :=
  ∑ t, (C.numerators t).eval x / C.termDenominator t x

/-- Strict sign representation of a Boolean truth table. -/
def Represents (C : Certificate n T) (f : BoolFn n) : Prop :=
  ∀ x, (f x = true → 0 < C.eval x) ∧ (f x = false → C.eval x < 0)

theorem eval_ne_zero_of_represents {C : Certificate n T} {f : BoolFn n}
    (h : C.Represents f) (x : Cube n) : C.eval x ≠ 0 := by
  cases hx : f x
  · exact (h x).2 hx |>.ne
  · exact (h x).1 hx |>.ne'

end Certificate

/-- A truth table is constant.  Constants have relaxed POIC₂ cost zero. -/
def IsConstant (f : BoolFn n) : Prop := ∃ b, ∀ x, f x = b

/-- Existence of a certificate of cost at most `Q`, including the constant layer. -/
def HasCertificate (n Q : ℕ) (f : BoolFn n) : Prop :=
  IsConstant f ∨
    ∃ (T : Topology) (C : Certificate n T), T.score ≤ Q ∧ C.Represents f

theorem HasCertificate.mono {Q R : ℕ} (hQR : Q ≤ R) {f : BoolFn n}
    (h : HasCertificate n Q f) : HasCertificate n R f := by
  rcases h with hc | ⟨T, C, hT, hC⟩
  · exact Or.inl hc
  · exact Or.inr ⟨T, C, hT.trans hQR, hC⟩

/-- Relaxed no-bias POIC₂ complexity.  The fallback branch disappears once
the bridge from the already-total H* normal form has been established. -/
noncomputable def RelaxedPOIC2 (n : ℕ) (f : BoolFn n) : ℕ := by
  classical
  exact if h : ∃ Q, HasCertificate n Q f then Nat.find h else 0

theorem hasCertificate_at_relaxedPOIC2 {f : BoolFn n}
    (hex : ∃ Q, HasCertificate n Q f) : HasCertificate n (RelaxedPOIC2 n f) f := by
  classical
  simp only [RelaxedPOIC2, dif_pos hex]
  exact Nat.find_spec hex

theorem relaxedPOIC2_le_of_hasCertificate {Q : ℕ} {f : BoolFn n}
    (h : HasCertificate n Q f) : RelaxedPOIC2 n f ≤ Q := by
  classical
  unfold RelaxedPOIC2
  split_ifs with hex
  · exact Nat.find_min' hex h
  · exact Nat.zero_le _

theorem hasCertificate_of_relaxedPOIC2_le {Q : ℕ} {f : BoolFn n}
    (hex : ∃ R, HasCertificate n R f) (hQ : RelaxedPOIC2 n f ≤ Q) :
    HasCertificate n Q f :=
  (hasCertificate_at_relaxedPOIC2 hex).mono hQ

theorem relaxedPOIC2_eq_zero_of_constant {f : BoolFn n} (hf : IsConstant f) :
    RelaxedPOIC2 n f = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact relaxedPOIC2_le_of_hasCertificate (Q := 0) (Or.inl hf)

end HeadComplexity.TypicalLogCloseness
