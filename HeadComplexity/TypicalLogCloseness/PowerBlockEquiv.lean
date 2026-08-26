import HeadComplexity.TypicalLogCloseness.HammingCode

set_option linter.style.header false

/-!
# Equivalence and cardinality helpers for power-block localization

This module provides the cardinal arithmetic and equivalences used to partition
`Cube n` into blocks of size `powerBlockSize n`.
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

/-- Lower bound on `Nat.log 2 n` when `2 ≤ n`. -/
theorem log_pos_of_two_le (n : ℕ) (hn : 2 ≤ n) : 1 ≤ Nat.log 2 n := by
  sorry

/-- The power-of-two block size `2^(Nat.log 2 n)` is at most `n`. -/
theorem powerBlockSize_le_self (n : ℕ) (hn : 2 ≤ n) : powerBlockSize n ≤ n := by
  sorry

/-- The cardinality of `StarCoord m` is `2^m`. -/
theorem starCoord_card (m : ℕ) : Fintype.card (StarCoord m) = 2 ^ m := by
  sorry

/-- Reindexing equivalence between `Fin (2^m)` and `StarCoord m`. -/
noncomputable def starCoordEquiv (m : ℕ) : Fin (2 ^ m) ≃ StarCoord m := by
  sorry

/-- Splits a Boolean cube of dimension `n` into a prefix of size `p` and a suffix of size `n - p`. -/
noncomputable def cubeSplitEquiv (n p : ℕ) (hp : p ≤ n) :
    Cube n ≃ Cube p × Cube (n - p) := by
  sorry

/-- The cardinality of `StarCenter m` is `2^(2^m) / 2^m`. -/
theorem starCenter_card (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (StarCenter m) = 2 ^ (2 ^ m) / 2 ^ m := by
  sorry

/-- Equivalence between group indices and pair of star-center and frozen suffix. -/
noncomputable def powerBlockGroupEquiv (n : ℕ) (hn : 2 ≤ n) :
    Fin (2 ^ n / powerBlockSize n) ≃
      StarCenter (Nat.log 2 n) × Cube (n - powerBlockSize n) := by
  sorry

/-- Uniform partition of `Cube n` into blocks of size `powerBlockSize n`. -/
noncomputable def powerBlockPartition (n : ℕ) (hn : 2 ≤ n) :
    UniformCubePartition n where
  groupCount := 2 ^ n / powerBlockSize n
  blockSize := powerBlockSize n
  vertex := sorry

end HeadComplexity.TypicalLogCloseness
