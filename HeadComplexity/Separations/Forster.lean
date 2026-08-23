import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import HeadComplexity.Separations.SignRank

set_option linter.style.header false

/-!
# Forster's sign-rank lower bound

`specNorm M` is the spectral (`ℓ² → ℓ²` operator) norm of a square real matrix,
and Forster's theorem bounds the sign-rank of a `±1` matrix from below by
`N / specNorm`.  The Kronecker multiplicativity of the spectral norm is what
makes the bound tensor (Theorem B of `audit/sources/EXPLICIT_GAP.md`).
-/

namespace HeadComplexity

open scoped Kronecker

/-- Spectral norm of a square real matrix: the operator norm of the induced map
on Euclidean space. -/
noncomputable def specNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

/-- **Forster's theorem** (Forster 2002): a `±1` matrix of size `N × N` has
sign-rank at least `N / ‖M‖₂`. -/
theorem forster {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1) :
    (Fintype.card ι : ℝ) ≤ (signRank M : ℝ) * specNorm M := by
  sorry

/-- The spectral norm is multiplicative under Kronecker products.  Together
with `Fintype.card (ι × κ) = card ι * card κ` this makes the Forster ratio
`N / ‖M‖₂` multiplicative, which is the engine of the tensored separation. -/
theorem specNorm_kronecker {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    specNorm (A ⊗ₖ B) = specNorm A * specNorm B := by
  sorry

/-- The spectral norm is invariant under simultaneous reindexing. -/
theorem specNorm_reindex {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (M : Matrix ι ι ℝ) :
    specNorm (Matrix.reindex e e M) = specNorm M := by
  sorry

end HeadComplexity
