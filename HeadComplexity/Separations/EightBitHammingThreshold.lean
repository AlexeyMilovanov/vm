import HeadComplexity.Separations.EightBitHammingThreshold.Obstruction
import HeadComplexity.Separations.EightBitHammingThreshold.Certificate

set_option linter.style.header false

/-!
# Theorem 189: the eight-bit Hamming-threshold separation
-/

namespace HeadComplexity

open Finset
open scoped BigOperators
open TypicalLogCloseness
open MvPolynomial
open EightBitInternal

private theorem HStar_f8_ge_three : 3 ≤ HStar 8 f8 := by
  by_contra hlt
  have hcomp := HStar_computable f8
  rcases (by omega : HStar 8 f8 = 0 ∨ HStar 8 f8 = 1 ∨ HStar 8 f8 = 2) with h0 | h1 | h2
  · have hconst : ∀ x y, f8 x = f8 y := (computableWithHeadsN_zero_iff f8).mp (h0 ▸ hcomp)
    have hF : f8 (fun _ => false) = false := rfl
    have hT : f8 ![true, true, false, false, false, false, false, false] = true := rfl
    have hEQ := hconst (fun _ => false) ![true, true, false, false, false, false, false, false]
    rw [hF, hT] at hEQ
    contradiction
  · have hdeg : ThresholdDegLE f8 1 := signReprDegLe_of_computableWithHeadsN (h1 ▸ hcomp)
    exact f8_not_thresholdDegLE_one hdeg
  · exact f8_not_computableWithHeadsN_two (h2 ▸ hcomp)

theorem HStar_f8 : HStar 8 f8 = 3 := by
  classical
  have h3 : computableWithHeadsN 8 3 f8 := f8_computableWithHeadsN_three
  have hex : ∃ k, computableWithHeadsN 8 k f8 := ⟨3, h3⟩
  have hle : HStar 8 f8 ≤ 3 := by
    unfold HStar
    rw [dif_pos hex]
    exact Nat.find_min' hex h3
  have hge : 3 ≤ HStar 8 f8 := HStar_f8_ge_three
  omega

/-- The complete theorem 189. -/
theorem theorem189_eight_bit_hamming_threshold :
    thresholdDeg f8 = 2 ∧ HStar 8 f8 = 3 ∧
      thresholdDeg f8 < HStar 8 f8 := by
  rw [thresholdDeg_f8, HStar_f8]
  norm_num

end HeadComplexity
