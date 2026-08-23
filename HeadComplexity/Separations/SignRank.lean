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
  · push_neg at hM
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

/-- Sign-rank is invariant under reindexing rows and columns. -/
theorem signRank_reindex {α β α' β' : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (eα : α ≃ α') (eβ : β ≃ β') (M : Matrix α β ℝ) :
    signRank (Matrix.reindex eα eβ M) = signRank M := by
  sorry

end HeadComplexity
