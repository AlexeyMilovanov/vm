import HeadComplexity.Separations.All

set_option linter.style.header false

/-!
# Statement lock for the Separations layer

Every theorem below re-states, verbatim, a frozen endpoint of
`HeadComplexity/Separations/` and proves it by direct application of the
original. If any frozen statement is renamed, weakened, strengthened, or
re-hypothesized, this module stops elaborating.  Its theorem declarations are
included in the release-wide `collectAxioms` audit.
-/

namespace HeadComplexity

open scoped Kronecker

-- SignRank.lean
theorem frozen_signRank_reindex {α β α' β' : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (eα : α ≃ α') (eβ : β ≃ β') (M : Matrix α β ℝ) :
    signRank (Matrix.reindex eα eβ M) = signRank M :=
  signRank_reindex eα eβ M

theorem frozen_signRank_le_rank {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ) : signRank M ≤ M.rank :=
  signRank_le_rank M

-- SignRankBridge.lean
theorem frozen_signRank_le_of_computableWithHeadsN {a b H : ℕ}
    {f : (Fin (a + b) → Bool) → Bool} (hH : 1 ≤ H)
    (h : computableWithHeadsN (a + b) H f) :
    signRank (signMatrix a b f) ≤ 2 ^ (H + 1) - 2 :=
  signRank_le_of_computableWithHeadsN hH h

theorem frozen_signRank_le_pow_HStar (a b : ℕ)
    (f : (Fin (a + b) → Bool) → Bool) (hH : 1 ≤ HStar (a + b) f) :
    signRank (signMatrix a b f) ≤ 2 ^ (HStar (a + b) f + 1) - 2 :=
  signRank_le_pow_HStar a b f hH

theorem frozen_signRank_le_of_thresholdDegLE {a b d : ℕ}
    {f : (Fin (a + b) → Bool) → Bool} (h : ThresholdDegLE f d) :
    signRank (signMatrix a b f) ≤ (a + 1) ^ d :=
  signRank_le_of_thresholdDegLE h

theorem frozen_signRank_le_two_pow_min {a b : ℕ}
    (f : (Fin (a + b) → Bool) → Bool) :
    signRank (signMatrix a b f) ≤ 2 ^ min a b :=
  signRank_le_two_pow_min f

-- Warren.lean
theorem frozen_warren_sign_patterns_weak {m k d : ℕ}
    (P : Fin k → MvPolynomial (Fin m) ℝ)
    (hdeg : ∀ i, (P i).totalDegree ≤ d) :
    ((signPatterns P).ncard : ℝ) ≤ (8 * ((d : ℝ) * k + 1)) ^ m :=
  warren_sign_patterns_weak P hdeg

theorem frozen_warren_sign_patterns_diag {H k : ℕ}
    (P : Fin k → MvPolynomial (Fin (2 * H)) ℝ)
    (hdeg : ∀ i, (P i).totalDegree ≤ H) :
    ((signPatterns P).ncard : ℝ) ≤ (8 * ((H : ℝ) * k + 1)) ^ (2 * H) :=
  warren_sign_patterns_diag P hdeg

-- Forster.lean
theorem frozen_forster {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1) :
    (Fintype.card ι : ℝ) ≤ (signRank M : ℝ) * specNorm M :=
  forster M hM

theorem frozen_specNorm_kronecker {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    specNorm (A ⊗ₖ B) = specNorm A * specNorm B :=
  specNorm_kronecker A B

theorem frozen_specNorm_reindex {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (M : Matrix ι ι ℝ) :
    specNorm (Matrix.reindex e e M) = specNorm M :=
  specNorm_reindex e M

-- DistanceThreshold.lean
theorem frozen_thresholdDegLE_distThreshold {m : ℕ} (hm : Odd m) :
    ThresholdDegLE (distThreshold m) 2 :=
  thresholdDegLE_distThreshold hm

theorem frozen_thresholdDeg_distThreshold {m : ℕ} (hm : Odd m) :
    thresholdDeg (distThreshold m) = 2 :=
  thresholdDeg_distThreshold hm

theorem frozen_specNorm_signMatrix_distThreshold {m : ℕ} (hm : Odd m) :
    specNorm (signMatrix m m (distThreshold m)) =
      2 * ((m - 1).choose ((m - 1) / 2)) :=
  specNorm_signMatrix_distThreshold hm

theorem frozen_forsterRatio_le_signRank {m : ℕ} (hm : Odd m) :
    forsterRatio m ≤ (signRank (signMatrix m m (distThreshold m)) : ℝ) :=
  forsterRatio_le_signRank hm

theorem frozen_theoremA {m : ℕ} (hm : Odd m) :
    thresholdDeg (distThreshold m) = 2 ∧
      forsterRatio m ≤ (2 : ℝ) ^ (HStar (m + m) (distThreshold m) + 1) - 2 :=
  theoremA hm

theorem frozen_sqrt_le_forsterRatio {m : ℕ} (hm : Odd m) (h3 : 3 ≤ m) :
    Real.sqrt ((m : ℝ) - 1) ≤ forsterRatio m :=
  sqrt_le_forsterRatio hm h3

theorem frozen_four_le_HStar_distThreshold_127 :
    4 ≤ HStar (127 + 127) (distThreshold 127) :=
  four_le_HStar_distThreshold_127

-- Tensor.lean
theorem frozen_thresholdDegLE_tensorDistThreshold {m : ℕ} (hm : Odd m)
    (k : ℕ) : ThresholdDegLE (tensorDistThreshold m k) (2 * k) :=
  thresholdDegLE_tensorDistThreshold hm k

theorem frozen_theoremB_HStar {m : ℕ} (hm : Odd m) {k : ℕ} (hk : 1 ≤ k) :
    forsterRatio m ^ k ≤
      (2 : ℝ) ^ (HStar (k * (m + m)) (tensorDistThreshold m k) + 1) - 2 :=
  theoremB_HStar hm hk

theorem frozen_theoremB_gap {m : ℕ} (hm : Odd m) (k : ℕ) :
    (k : ℝ) * (Real.logb 2 (forsterRatio m) - 2) - 1 ≤
      (HStar (k * (m + m)) (tensorDistThreshold m k) : ℝ) -
        (thresholdDeg (tensorDistThreshold m k) : ℝ) :=
  theoremB_gap hm k

-- NDISJ.lean
theorem frozen_pow_le_of_leftShatters {a b H k : ℕ}
    {f : (Fin (a + b) → Bool) → Bool} (hk : 1 ≤ k)
    (hcomp : computableWithHeadsN (a + b) H f) (hsh : LeftShatters f k) :
    (2 : ℝ) ^ k ≤ (8 * (k : ℝ)) ^ (4 * H) :=
  pow_le_of_leftShatters hk hcomp hsh

theorem frozen_ndisj_leftShatters (m : ℕ) : LeftShatters (ndisj m) m :=
  ndisj_leftShatters m

theorem frozen_HStar_ndisj_le (m : ℕ) : HStar (m + m) (ndisj m) ≤ m :=
  HStar_ndisj_le m

theorem frozen_thresholdDeg_ndisj {m : ℕ} (hm : 2 ≤ m) :
    thresholdDeg (ndisj m) = 2 :=
  thresholdDeg_ndisj hm

theorem frozen_ndisj_separation {m : ℕ} (hm : 2 ≤ m) :
    thresholdDeg (ndisj m) = 2 ∧
      (2 : ℝ) ^ m ≤
        (8 * (m : ℝ)) ^ (4 * HStar (m + m) (ndisj m)) :=
  ndisj_separation hm

theorem frozen_ndisj_of_sharpShatteringUpperBound
    (hconj : SharpShatteringUpperBound) (m : ℕ) :
    m ≤ 2 * HStar (m + m) (ndisj m) :=
  ndisj_of_sharpShatteringUpperBound hconj m

end HeadComplexity
