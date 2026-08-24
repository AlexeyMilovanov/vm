import Mathlib.LinearAlgebra.Matrix.Rank
import HeadComplexity.Separations.TwoBlock

set_option linter.style.header false

/-!
# Sign-rank of a two-block sign matrix

`signRank M` is the least rank of a real matrix agreeing in sign with `M`
entrywise, and `signMatrix a b f` is the `±1` matrix of a Boolean function on
`a + b` bits under the left/right block partition.  This is the invariant of
`theorems/028` (the sign-rank bridge) and of Forster's theorem; neither had a
Lean statement before this module.
-/

namespace HeadComplexity

/-- `A` agrees with `M` in sign at every entry (all entries of `M` implicitly
nonzero: a zero entry of `M` makes the condition unsatisfiable). -/
def SignMatches {α β : Type*} (M A : Matrix α β ℝ) : Prop :=
  ∀ i j, 0 < M i j * A i j

/-- The sign-rank of `M`: the least rank of a real matrix matching `M` in sign.
For a matrix with a zero entry the defining set is empty and `sInf` returns `0`;
all uses are for `±1` matrices, where the set is nonempty (witness `M` itself). -/
noncomputable def signRank {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ) : ℕ :=
  sInf {r | ∃ A : Matrix α β ℝ, SignMatches M A ∧ A.rank = r}

/-- The `±1` sign matrix of `f` under the two-block partition: rows are left
blocks, columns are right blocks. -/
def signMatrix (a b : ℕ) (f : (Fin (a + b) → Bool) → Bool) :
    Matrix (Fin a → Bool) (Fin b → Bool) ℝ :=
  fun x y => if f (blockJoin x y) then 1 else -1

theorem signMatrix_apply (a b : ℕ) (f : (Fin (a + b) → Bool) → Bool)
    (x : Fin a → Bool) (y : Fin b → Bool) :
    signMatrix a b f x y = if f (blockJoin x y) then 1 else -1 := rfl

theorem signMatrix_ne_zero (a b : ℕ) (f : (Fin (a + b) → Bool) → Bool)
    (x : Fin a → Bool) (y : Fin b → Bool) : signMatrix a b f x y ≠ 0 := by
  unfold signMatrix
  split <;> norm_num

/-- Sign-rank is at most rank: a matrix with nonzero entries matches its own
sign, and a matrix with a zero entry has sign-rank `0` by the `sInf ∅`
convention. -/
theorem signRank_le_rank {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ) : signRank M ≤ M.rank := by
  by_cases hM : ∀ i j, M i j ≠ 0
  · exact Nat.sInf_le ⟨M, fun i j => mul_self_pos.mpr (hM i j), rfl⟩
  · push Not at hM
    obtain ⟨i, j, hij⟩ := hM
    have hempty :
        {r | ∃ A : Matrix α β ℝ, SignMatches M A ∧ A.rank = r} = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨A, hA, -⟩
      have h0 := hA i j
      rw [hij, zero_mul] at h0
      exact lt_irrefl 0 h0
    unfold signRank
    rw [hempty, Nat.sInf_empty]
    exact Nat.zero_le _

/-- Sign-rank is invariant under reindexing rows and columns.  The map
`A ↦ reindex eα eβ A` is a rank-preserving bijection between matrices matching
`M` in sign and matrices matching `reindex eα eβ M` in sign, so the two
defining `sInf` index sets coincide. -/
theorem signRank_reindex {α β α' β' : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (eα : α ≃ α') (eβ : β ≃ β') (M : Matrix α β ℝ) :
    signRank (Matrix.reindex eα eβ M) = signRank M := by
  unfold signRank
  congr 1
  ext r
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨Matrix.reindex eα.symm eβ.symm A, ?_, ?_⟩
    · intro i j
      have hij := hA (eα i) (eβ j)
      simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using hij
    · rw [Matrix.rank_reindex]
  · rintro ⟨A, hA, rfl⟩
    refine ⟨Matrix.reindex eα eβ A, ?_, ?_⟩
    · intro i j
      simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using
        hA (eα.symm i) (eβ.symm j)
    · rw [Matrix.rank_reindex]

/-- Rank is invariant under negation: `(-A).mulVecLin = -(A.mulVecLin)` has the
same range as `A.mulVecLin`. -/
theorem rank_neg {α β : Type*} [Fintype β] (A : Matrix α β ℝ) :
    (-A).rank = A.rank := by
  have h : (-A).mulVecLin = -(A.mulVecLin) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.mulVecLin_apply, LinearMap.neg_apply, Matrix.mulVecLin_apply,
      Matrix.neg_mulVec]
  unfold Matrix.rank
  rw [h, LinearMap.range_neg]

/-- **Matrix rank subadditivity** (PROOFS.md P2.3; §11 inventory item 4).
`(A + B).rank ≤ A.rank + B.rank`.  Not a named lemma in mathlib at v4.31, but
`Matrix.rank M = finrank ℝ (range M.mulVecLin)`, `(A + B).mulVecLin =
A.mulVecLin + B.mulVecLin`, and `range (f + g) ≤ range f ⊔ range g`, so this
follows from `LinearMap.rank_add_le`/`Submodule.finrank_add_le_finrank_add_finrank`
(the range submodules are finite-dimensional since `β` is a `Fintype`).  Used to
count the `2 ^ (H + 1) - 2` rank-one pieces of the cleared bridge polynomial. -/
theorem rank_add_le {α β : Type*} [Fintype β] (A B : Matrix α β ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  have h_range := LinearMap.range_add_le A.mulVecLin B.mulVecLin
  have h_mono := Submodule.finrank_mono h_range
  have h_sup := Submodule.finrank_add_le_finrank_add_finrank A.mulVecLin.range B.mulVecLin.range
  exact h_mono.trans h_sup

/-- Sign-rank is invariant under negation (PROOFS.md P1.2): `A ↦ -A` is a
rank-preserving bijection carrying sign-matches of `M` onto sign-matches of
`-M`.  Needed for the global `(-1)^(k+1)` factor in Theorem B. -/
theorem signRank_neg {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ) : signRank (-M) = signRank M := by
  unfold signRank
  congr 1
  ext r
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨-A, ?_, ?_⟩
    · intro i j
      have hij := hA i j
      simpa [Matrix.neg_apply] using hij
    · rw [rank_neg]
  · rintro ⟨A, hA, rfl⟩
    refine ⟨-A, ?_, ?_⟩
    · intro i j
      have hij := hA i j
      simpa [Matrix.neg_apply] using hij
    · rw [rank_neg]

end HeadComplexity
