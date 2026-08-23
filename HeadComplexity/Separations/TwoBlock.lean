import HeadComplexity.Model.Head
import Mathlib.InformationTheory.Hamming

set_option linter.style.header false

/-!
# Two-block conventions

Inputs on `n = a + b` bits viewed as a pair (left block `x : Fin a → Bool`,
right block `y : Fin b → Bool`), following the convention of
`Results/StrictSeparation.lean` (`f10Join`).  These are the shared plumbing
definitions for the sign-rank and shattering lower bounds
(`audit/sources/EXPLICIT_GAP.md`, `audit/sources/STRENGTHENING.md`).
-/

namespace HeadComplexity

/-- Join a left block and a right block into one input on `a + b` bits. -/
def blockJoin {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    Fin (a + b) → Bool :=
  fun i => Fin.addCases x y i

/-- Left block of an `(a + b)`-bit input. -/
def leftBits (a b : ℕ) (z : Fin (a + b) → Bool) : Fin a → Bool :=
  fun i => z (Fin.castAdd b i)

/-- Right block of an `(a + b)`-bit input. -/
def rightBits (a b : ℕ) (z : Fin (a + b) → Bool) : Fin b → Bool :=
  fun i => z (Fin.natAdd a i)

@[simp] theorem blockJoin_castAdd {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool)
    (i : Fin a) : blockJoin x y (Fin.castAdd b i) = x i := by
  simp [blockJoin]

@[simp] theorem blockJoin_natAdd {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool)
    (i : Fin b) : blockJoin x y (Fin.natAdd a i) = y i := by
  simp [blockJoin]

@[simp] theorem leftBits_blockJoin {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    leftBits a b (blockJoin x y) = x := by
  funext i; simp [leftBits]

@[simp] theorem rightBits_blockJoin {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    rightBits a b (blockJoin x y) = y := by
  funext i; simp [rightBits]

theorem blockJoin_leftBits_rightBits {a b : ℕ} (z : Fin (a + b) → Bool) :
    blockJoin (leftBits a b z) (rightBits a b z) = z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [blockJoin, leftBits, rightBits]

end HeadComplexity
