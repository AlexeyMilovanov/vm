import HeadComplexity.Separations.DistanceThreshold
import HeadComplexity.Separations.Tensor
import HeadComplexity.Separations.NDISJ

set_option linter.style.header false

/-!
# Explicit paper-facing separation wrappers

This module packages the already proved core inequalities in the exact forms
used by Theorems A and B and by the explicit logarithmic NDISJ corollary.
-/

namespace HeadComplexity

/-- The central-binomial estimate also covers the only odd case below `3`. -/
theorem sqrt_le_forsterRatio_odd {m : ℕ} (hm : Odd m) :
    Real.sqrt ((m : ℝ) - 1) ≤ forsterRatio m := by
  by_cases h3 : 3 ≤ m
  · exact sqrt_le_forsterRatio hm h3
  · have hm1 : 1 ≤ m := by
      have := Nat.odd_iff.mp hm
      omega
    have hm_eq : m = 1 := by
      have hm_le : m ≤ 2 := by omega
      have := Nat.odd_iff.mp hm
      omega
    subst m
    norm_num [forsterRatio, Nat.choose]

/-- Full finite Theorem A package: exact degree, explicit central-binomial
lower bound, and the head-complexity upper envelope for the Forster ratio. -/
theorem theoremA_full {m : ℕ} (hm : Odd m) :
    thresholdDeg (distThreshold m) = 2 ∧
      Real.sqrt ((m : ℝ) - 1) ≤ forsterRatio m ∧
      forsterRatio m ≤ (2 : ℝ) ^ (HStar (m + m) (distThreshold m) + 1) - 2 :=
  ⟨(theoremA hm).1, sqrt_le_forsterRatio_odd hm, (theoremA hm).2⟩

/-- Closed form of the odd-parameter Forster ratio. -/
theorem forsterRatio_odd_eq (t : ℕ) :
    forsterRatio (2 * t + 1) = (4 : ℝ) ^ t / (Nat.centralBinom t : ℝ) := by
  rw [forsterRatio]
  congr 1
  · rw [show 2 * t + 1 - 1 = 2 * t by omega, pow_mul]
    norm_num
  · rw [show 2 * t + 1 - 1 = 2 * t by omega, show 2 * t / 2 = t by omega,
      Nat.centralBinom_eq_two_mul_choose]

/-- The odd-parameter Forster ratio strictly increases at every step. -/
theorem forsterRatio_odd_lt_succ (t : ℕ) :
    forsterRatio (2 * t + 1) < forsterRatio (2 * (t + 1) + 1) := by
  rw [forsterRatio_odd_eq t, forsterRatio_odd_eq (t + 1)]
  have hcb_pos : 0 < (Nat.centralBinom t : ℝ) := Nat.cast_pos.mpr (Nat.centralBinom_pos t)
  have hcb_succ_pos : 0 < (Nat.centralBinom (t + 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.centralBinom_pos (t + 1))
  have h_rel : ((t : ℝ) + 1) * (Nat.centralBinom (t + 1) : ℝ) =
      2 * (2 * (t : ℝ) + 1) * (Nat.centralBinom t : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ t
  have ht1_pos : 0 < (t : ℝ) + 1 := by positivity
  have h4_pos : 0 < (4 : ℝ) ^ t := by positivity
  rw [div_lt_div_iff₀ hcb_pos hcb_succ_pos]
  have h_lhs : ((t : ℝ) + 1) * ((4 : ℝ) ^ t * (Nat.centralBinom (t + 1) : ℝ)) =
      (4 : ℝ) ^ t * (((t : ℝ) + 1) * (Nat.centralBinom (t + 1) : ℝ)) := by ring
  have h_rhs : ((t : ℝ) + 1) * ((4 : ℝ) ^ (t + 1) * (Nat.centralBinom t : ℝ)) =
      (4 : ℝ) ^ t * (4 * ((t : ℝ) + 1) * (Nat.centralBinom t : ℝ)) := by
    calc ((t : ℝ) + 1) * ((4 : ℝ) ^ (t + 1) * (Nat.centralBinom t : ℝ))
      _ = ((t : ℝ) + 1) * ((4 : ℝ) ^ t * 4 * (Nat.centralBinom t : ℝ)) := by rw [pow_succ]
      _ = (4 : ℝ) ^ t * (4 * ((t : ℝ) + 1) * (Nat.centralBinom t : ℝ)) := by ring
  nlinarith

theorem forsterRatio_odd_strictMono :
    StrictMono (fun t => forsterRatio (2 * t + 1)) :=
  strictMono_nat_of_lt_succ forsterRatio_odd_lt_succ

/-- The coefficient in Theorem B is already positive at every odd `m ≥ 13`. -/
theorem four_lt_forsterRatio_of_odd_ge_thirteen {m : ℕ}
    (hm : Odd m) (hm13 : 13 ≤ m) : 4 < forsterRatio m := by
  obtain ⟨t, rfl⟩ := hm
  have ht : 6 ≤ t := by omega
  calc
    (4 : ℝ) < forsterRatio (2 * 6 + 1) := by
      norm_num [forsterRatio, Nat.choose]
    _ ≤ forsterRatio (2 * t + 1) := forsterRatio_odd_strictMono.monotone ht

theorem theoremB_coefficient_pos {m : ℕ} (hm : Odd m) (hm13 : 13 ≤ m) :
    0 < Real.logb 2 (forsterRatio m) - 2 := by
  have hlog := Real.logb_lt_logb (b := (2 : ℝ)) (by norm_num) (by norm_num)
    (four_lt_forsterRatio_of_odd_ge_thirteen hm hm13)
  have hlog4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [hlog4] at hlog
  linarith

/-- Full Theorem B inequality together with positivity of its linear
coefficient at the advertised cutoff. -/
theorem theoremB_full {m : ℕ} (hm : Odd m) (hm13 : 13 ≤ m) (k : ℕ) :
    0 < Real.logb 2 (forsterRatio m) - 2 ∧
      (k : ℝ) * (Real.logb 2 (forsterRatio m) - 2) - 1 ≤
        (HStar (k * (m + m)) (tensorDistThreshold m k) : ℝ) -
          (thresholdDeg (tensorDistThreshold m k) : ℝ) :=
  ⟨theoremB_coefficient_pos hm hm13, theoremB_gap hm k⟩

/-- A convenient strict-gap consequence once `k` makes the explicit lower
bound positive. -/
theorem theoremB_strict_gap {m k : ℕ} (hm : Odd m) (hm13 : 13 ≤ m)
    (hk : 1 < (k : ℝ) * (Real.logb 2 (forsterRatio m) - 2)) :
    thresholdDeg (tensorDistThreshold m k) <
      HStar (k * (m + m)) (tensorDistThreshold m k) := by
  have hgap := (theoremB_full hm hm13 k).2
  have hpos : 0 < (HStar (k * (m + m)) (tensorDistThreshold m k) : ℝ) -
      (thresholdDeg (tensorDistThreshold m k) : ℝ) := by
    linarith
  exact_mod_cast (sub_pos.mp hpos)

/-- Explicit real-valued form of the `Ω(m / log m)` NDISJ lower bound. -/
theorem HStar_ndisj_log_lower_bound {m : ℕ} (hm : 2 ≤ m) :
    (m : ℝ) / (4 * Real.logb 2 (8 * (m : ℝ))) ≤
      (HStar (m + m) (ndisj m) : ℝ) := by
  have hpow := (ndisj_separation hm).2
  have hbase : (1 : ℝ) < 2 := by norm_num
  have hleft : 0 < (2 : ℝ) ^ m := by positivity
  have hlog := Real.logb_le_logb_of_le hbase hleft hpow
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
    Real.logb_pow] at hlog
  push_cast at hlog
  have harg : (1 : ℝ) < 8 * (m : ℝ) := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hlogpos : 0 < Real.logb 2 (8 * (m : ℝ)) :=
    Real.logb_pos hbase harg
  have hden : 0 < 4 * Real.logb 2 (8 * (m : ℝ)) := by positivity
  rw [div_le_iff₀ hden]
  calc
    (m : ℝ) ≤
        (4 * (HStar (m + m) (ndisj m) : ℝ)) *
          Real.logb 2 (8 * (m : ℝ)) := hlog
    _ = (HStar (m + m) (ndisj m) : ℝ) *
        (4 * Real.logb 2 (8 * (m : ℝ))) := by ring

/-- Full NDISJ package: exact degree, explicit logarithmic lower bound, and
the elementary `m`-head upper bound. -/
theorem ndisj_separation_full {m : ℕ} (hm : 2 ≤ m) :
    thresholdDeg (ndisj m) = 2 ∧
      (m : ℝ) / (4 * Real.logb 2 (8 * (m : ℝ))) ≤
        (HStar (m + m) (ndisj m) : ℝ) ∧
      HStar (m + m) (ndisj m) ≤ m :=
  ⟨thresholdDeg_ndisj hm, HStar_ndisj_log_lower_bound hm, HStar_ndisj_le m⟩

end HeadComplexity
