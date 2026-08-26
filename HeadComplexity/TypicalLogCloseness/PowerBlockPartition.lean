import HeadComplexity.TypicalLogCloseness.HammingCode

set_option linter.style.header false

/-!
# Power-block partition and its affine localization data

The equivalence field is the canonical row reindexing used later by the
localization determinant.
-/

namespace HeadComplexity.TypicalLogCloseness

/-- A uniform partition of the Boolean cube, presented as an equivalence. -/
structure UniformCubePartition (n : ℕ) where
  groupCount : ℕ
  blockSize : ℕ
  vertex : Fin groupCount × Fin blockSize ≃ Cube n

/-- A partition together with affine equations and a delta basis on each block. -/
structure LocalizationData (n : ℕ) extends UniformCubePartition n where
  ell : Fin groupCount → AffineForm n
  lagrange : Fin groupCount → Fin blockSize → AffineForm n
  ell_zero_iff :
    ∀ g z, (ell g).eval (vertex z) = 0 ↔ g = z.1
  lagrange_delta :
    ∀ g i k, (lagrange g i).eval (vertex (g, k)) = if i = k then 1 else 0

/-- The largest power of two not exceeding n. -/
def powerBlockSize (n : ℕ) : ℕ := 2 ^ Nat.log 2 n

/-- Hamming stars, extended by frozen suffixes, give localization data with the
two exact dimensions required downstream.  Keeping construction and dimensions
in one existential prevents incoherent choices. -/
theorem exists_powerBlockLocalization (n : ℕ) (hn : 2 ≤ n) :
    ∃ L : LocalizationData n,
      L.blockSize = powerBlockSize n ∧
      L.groupCount = 2 ^ n / powerBlockSize n := by
  sorry

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
