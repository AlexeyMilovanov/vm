import HeadComplexity.TypicalLogCloseness.PowerBlockForms

set_option linter.style.header false

/-!
# Power-block partition and its affine localization data

The equivalence field is the canonical row reindexing used later by the
localization determinant.
-/

namespace HeadComplexity.TypicalLogCloseness

/-- Construction of localization data for power blocks. -/
noncomputable def powerBlockLocalizationData (n : ℕ) (hn : 2 ≤ n) :
    LocalizationData n where
  toUniformCubePartition := powerBlockPartition n hn
  ell := powerBlockEll n hn
  lagrange := powerBlockLagrange n hn
  ell_zero_iff := powerBlockEll_zero_iff n hn
  lagrange_delta := powerBlockLagrange_delta n hn

/-- Hamming stars, extended by frozen suffixes, give localization data with the
two exact dimensions required downstream.  Keeping construction and dimensions
in one existential prevents incoherent choices. -/
theorem exists_powerBlockLocalization (n : ℕ) (hn : 2 ≤ n) :
    ∃ L : LocalizationData n,
      L.blockSize = powerBlockSize n ∧
      L.groupCount = 2 ^ n / powerBlockSize n :=
  ⟨powerBlockLocalizationData n hn, rfl, rfl⟩

noncomputable def powerBlockLocalization (n : ℕ) (hn : 2 ≤ n) :
    LocalizationData n :=
  (exists_powerBlockLocalization n hn).choose

theorem powerBlockLocalization_blockSize (n : ℕ) (hn : 2 ≤ n) :
    (powerBlockLocalization n hn).blockSize = powerBlockSize n :=
  (exists_powerBlockLocalization n hn).choose_spec.1

theorem powerBlockLocalization_groupCount (n : ℕ) (hn : 2 ≤ n) :
    (powerBlockLocalization n hn).groupCount = 2 ^ n / powerBlockSize n :=
  (exists_powerBlockLocalization n hn).choose_spec.2

theorem powerBlockSize_lower_bound (n : ℕ) (_hn : 2 ≤ n) :
    n + 1 ≤ 2 * powerBlockSize n := by
  rw [Nat.succ_le_iff]
  simpa [powerBlockSize, pow_succ, Nat.mul_comm] using
    (Nat.lt_pow_succ_log_self Nat.one_lt_two n)

end HeadComplexity.TypicalLogCloseness
