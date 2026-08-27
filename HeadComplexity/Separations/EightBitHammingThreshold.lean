import HeadComplexity.Separations.DistanceThreshold
import HeadComplexity.TypicalLogCloseness.AffineForm

set_option linter.style.header false

/-!
# Theorem 189: the eight-bit Hamming-threshold separation

This file freezes the complete theorem statement and the proof interfaces used
by the paper proof: quadratic mixed curvature, the normalized two-head system,
the four-dimensional column-max spectral obstruction, and the explicit integer
three-head certificate.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators
open TypicalLogCloseness

/-- The radius-one Hamming-ball threshold on two four-bit strings. -/
def f8 : (Fin 8 → Bool) → Bool :=
  distThreshold 4

theorem f8_apply (z : Fin 8 → Bool) :
    f8 z = decide
      (2 ≤ hammingDist (leftBits 4 4 z) (rightBits 4 4 z)) := by
  rfl

/-- The quadratic distance polynomial gives the upper threshold-degree bound. -/
theorem f8_thresholdDegLE_two : ThresholdDegLE f8 2 := by
  sorry

/-- A two-coordinate checkerboard restriction excludes affine threshold
representations. -/
theorem f8_not_thresholdDegLE_one : ¬ ThresholdDegLE f8 1 := by
  sorry

theorem thresholdDeg_f8 : thresholdDeg f8 = 2 := by
  sorry

/-- Mixed coefficient matrix between the left and right four-bit blocks. -/
noncomputable def mixedMatrix4
    (P : MvPolynomial (Fin 8) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    MvPolynomial.coeff
      (Finsupp.single (Fin.castAdd 4 i) 1 +
        Finsupp.single (Fin.natAdd 4 j) 1) P

/-- Symmetric part of a square matrix. -/
noncomputable def symmetricPart4 (K : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (K i j + K j i) / 2

/-- Quadratic form convention used by the spectral lower bound. -/
noncomputable def quadraticForm4 (M : Matrix (Fin 4) (Fin 4) ℝ)
    (z : Fin 4 → ℝ) : ℝ :=
  dotProduct z (M.mulVec z)

/-- Elementary negative-definiteness predicate, avoiding any dependence on a
particular eigenvalue API. -/
def NegativeDefinite4 (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ z, z ≠ 0 → quadraticForm4 M z < 0

/-- Elementary positive-definiteness predicate. -/
def PositiveDefinite4 (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ z, z ≠ 0 → 0 < quadraticForm4 M z

/-- The form is positive on a two-dimensional subspace, encoded by two
generators and all their nontrivial linear combinations. -/
def PositiveIndexAtLeastTwo4 (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃ u v : Fin 4 → ℝ, ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
    0 < quadraticForm4 M (fun i => a * u i + b * v i)

/-- Inertia `(2,2)` in dimension four. -/
def InertiaTwoTwo4 (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  M.IsSymm ∧ PositiveIndexAtLeastTwo4 M ∧ PositiveIndexAtLeastTwo4 (-M)

/-- Paper Lemma 2: every quadratic sign representation of `f8` has strictly
negative symmetric mixed curvature. -/
theorem f8_quadratic_mixed_negative
    (P : MvPolynomial (Fin 8) ℝ)
    (hdeg : P.totalDegree ≤ 2)
    (hrep : SignRepresents P f8) :
    NegativeDefinite4 (symmetricPart4 (mixedMatrix4 P)) := by
  sorry

/-- The normalized pointwise system forced by a hypothetical two-head score. -/
structure F8NormalizedSystem where
  U : Matrix (Fin 4) (Fin 4) ℝ
  V : Matrix (Fin 4) (Fin 4) ℝ
  w : Fin 4 → ℝ
  μ : Fin 4 → ℝ
  U_pos : PositiveDefinite4 (U + U.transpose)
  V_inertia : InertiaTwoTwo4 V
  diagonal_pos : ∀ j, 0 < U j j
  contraction : ∀ i j, i ≠ j →
    |w j| + |U j i - V j i| +
      ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
        |U j k + V j k| < U j j
  leftSlope_pos : ∀ i, 0 < (U.transpose.mulVec μ) i
  rightSlope_pos : ∀ i, 0 < (V.mulVec μ) i
  null : quadraticForm4 V μ = 0
  intercept :
    (∑ i, (U.transpose.mulVec μ) i) +
      (∑ i, (V.mulVec μ) i) < dotProduct μ w

/-- The spectral hypothesis used in the paper: a positive diagonal left
multiplier symmetrizes `M`, and the resulting symmetric form has positive
index at least two. Encoding the index on the symmetrized matrix avoids any
choice of a nonsymmetric eigenvalue API. -/
def DiagonallySymmetrizableWithPositiveIndexTwo4
    (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃ d : Fin 4 → ℝ, (∀ i, 0 < d i) ∧
    ((Matrix.diagonal d) * M).IsSymm ∧
    PositiveIndexAtLeastTwo4 ((Matrix.diagonal d) * M)

/-- Paper Lemma 5, in a max-free but equivalent form: one can choose an
off-diagonal maximizer in each column so that the trace-plus-column-max
expression is positive. -/
theorem columnMax_spectral_inequality
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hspectral : DiagonallySymmetrizableWithPositiveIndexTwo4 M)
    (hrow : ∀ i, 0 < (M.mulVec (fun _ => 1)) i) :
    ∃ pick : Fin 4 → Fin 4,
      (∀ j, pick j ≠ j) ∧
      0 < Matrix.trace M + 2 * ∑ j, M (pick j) j := by
  sorry

/-- Paper Lemmas 3 and 4: a two-head realization supplies the normalized
system. -/
theorem two_heads_yield_f8NormalizedSystem
    (h : computableWithHeadsN 8 2 f8) :
    Nonempty F8NormalizedSystem := by
  sorry

/-- Paper Lemma 6: the normalized system is impossible. -/
theorem not_nonempty_f8NormalizedSystem :
    ¬ Nonempty F8NormalizedSystem := by
  sorry

theorem f8_not_computableWithHeadsN_two :
    ¬ computableWithHeadsN 8 2 f8 := by
  intro h
  exact not_nonempty_f8NormalizedSystem
    (two_heads_yield_f8NormalizedSystem h)

/-- Build an eight-variable affine form from integer certificate data. -/
def integerAffine8 (constant : ℤ) (linear : Fin 8 → ℤ) :
    AffineForm 8 where
  constant := constant
  linear i := linear i

def f8D1 : AffineForm 8 :=
  integerAffine8 34 ![-1, -6, -1, -8, -1, -1, -1, -1]

def f8D2 : AffineForm 8 :=
  integerAffine8 31 ![-4, -1, -3, -7, -5, -6, -3, -1]

def f8D3 : AffineForm 8 :=
  integerAffine8 32 ![-1, -1, -6, -1, -1, -6, -6, -4]

def f8A1 : AffineForm 8 :=
  integerAffine8 (-476)
    ![1794, 2403, 2934, 132, 1890, -4130, 2868, -661]

def f8A2 : AffineForm 8 :=
  integerAffine8 622
    ![-2333, -1471, 188, 3074, -2633, 2202, 208, -1392]

def f8A3 : AffineForm 8 :=
  integerAffine8 (-1006)
    ![1501, -577, -1950, -4044, 1799, 1406, -1914, 2472]

/-- Denominator-cleared value of the published three-head score with bias one. -/
noncomputable def f8ClearedScore (z : Fin 8 → Bool) : ℝ :=
  f8D1.eval z * f8D2.eval z * f8D3.eval z +
  f8A1.eval z * f8D2.eval z * f8D3.eval z +
  f8A2.eval z * f8D1.eval z * f8D3.eval z +
  f8A3.eval z * f8D1.eval z * f8D2.eval z

def boolSign (b : Bool) : ℝ := if b then 1 else -1

/-- All three published denominators are exact native denominators. -/
theorem f8_denominators_admissible :
    f8D1.StrictAdmissible ∧
      f8D2.StrictAdmissible ∧ f8D3.StrictAdmissible := by
  sorry

/-- Exact audit target for the integer certificate: the minimum signed cleared
margin over all 256 vertices is at least 58. -/
theorem f8_integer_certificate_margin (z : Fin 8 → Bool) :
    58 ≤ boolSign (f8 z) * f8ClearedScore z := by
  sorry

/-- Paper Lemma 7: the explicit certificate realizes `f8` with three heads. -/
theorem f8_computableWithHeadsN_three :
    computableWithHeadsN 8 3 f8 := by
  sorry

theorem HStar_f8 : HStar 8 f8 = 3 := by
  sorry

/-- The complete theorem 189. -/
theorem theorem189_eight_bit_hamming_threshold :
    thresholdDeg f8 = 2 ∧ HStar 8 f8 = 3 ∧
      thresholdDeg f8 < HStar 8 f8 := by
  rw [thresholdDeg_f8, HStar_f8]
  norm_num

end HeadComplexity
