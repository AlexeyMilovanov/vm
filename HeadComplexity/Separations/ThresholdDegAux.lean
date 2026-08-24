import HeadComplexity.Polynomial.ParityThresholdDegree
import HeadComplexity.Results.ThresholdDegree
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Threshold-degree wiring lemmas (PROOFS.md P1.4)

Small `Nat.find`-level lemmas connecting `ThresholdDegLE` (existence of a
degree-`≤ d` sign representation) to `thresholdDeg` (the least such `d`), plus
the corpus chain `thresholdDeg f ≤ H*(f)`.  These are used to pin exact
threshold degrees (`thresholdDeg_ndisj`, `thresholdDeg_distThreshold`) and in
the Theorem B additive gap (`theoremB_gap`).
-/

namespace HeadComplexity

variable {n : ℕ}

/-- P1.4(iii): monotonicity of `ThresholdDegLE` in the degree (same polynomial). -/
theorem ThresholdDegLE.mono {f : (Fin n → Bool) → Bool} {d d' : ℕ}
    (h : ThresholdDegLE f d) (hdd : d ≤ d') : ThresholdDegLE f d' := by
  obtain ⟨P, hP, hs⟩ := h
  exact ⟨P, hP.trans hdd, hs⟩

/-- Every Boolean function has some sign representation (of degree `≤ H*(f)`),
so the `∃ d, ThresholdDegLE f d` premise of `thresholdDeg` is always met. -/
theorem exists_thresholdDegLE (f : (Fin n → Bool) → Bool) :
    ∃ d, ThresholdDegLE f d :=
  ⟨HStar n f, degree_le_of_computableWithHeadsN (HStar_computable f)⟩

/-- P1.4(i): `ThresholdDegLE f d` gives `thresholdDeg f ≤ d`. -/
theorem thresholdDeg_le_of {f : (Fin n → Bool) → Bool} {d : ℕ}
    (h : ThresholdDegLE f d) : thresholdDeg f ≤ d := by
  classical
  have hex : ∃ d, ThresholdDegLE f d := ⟨d, h⟩
  rw [thresholdDeg, dif_pos hex]
  exact Nat.find_min' hex h

/-- The threshold degree is itself achieved by a sign representation. -/
theorem thresholdDegLE_thresholdDeg (f : (Fin n → Bool) → Bool) :
    ThresholdDegLE f (thresholdDeg f) := by
  classical
  have hex := exists_thresholdDegLE f
  rw [thresholdDeg, dif_pos hex]
  exact Nat.find_spec hex

/-- P1.4(ii): if `f` has no degree-`≤ d` sign representation, then
`d < thresholdDeg f`. -/
theorem lt_thresholdDeg_of {f : (Fin n → Bool) → Bool} {d : ℕ}
    (h : ¬ ThresholdDegLE f d) : d < thresholdDeg f := by
  by_contra hle
  rw [not_lt] at hle
  exact h ((thresholdDegLE_thresholdDeg f).mono hle)

/-- Corpus chain (P1.4 note): `thresholdDeg f ≤ H*(f)`, since `H*` heads give a
degree-`≤ H*` sign representation. -/
theorem thresholdDeg_le_HStar (f : (Fin n → Bool) → Bool) :
    thresholdDeg f ≤ HStar n f :=
  thresholdDeg_le_of (degree_le_of_computableWithHeadsN (HStar_computable f))

end HeadComplexity
