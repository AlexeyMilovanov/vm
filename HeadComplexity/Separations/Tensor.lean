import HeadComplexity.Separations.DistanceThreshold

set_option linter.style.header false

/-!
# Theorem B: an explicit linear additive gap `H* - deg±  = Ω(n)`

XOR-composition of `k` disjoint copies of `F_m`.  Under the all-left/all-right
partition the sign matrix is, up to reindexing and a global sign `(-1)^(k+1)`
(from `σ(XOR) = (-1)^(k+1) ∏ σ` in the `true ↦ +1` convention — affecting
neither spectral norm nor sign-rank), the Kronecker power of the base sign
matrix, and the Forster ratio is multiplicative (`specNorm_kronecker`), so the
sign-rank lower bound raises to `γ_m ^ k` while the threshold degree only
grows to `2 k`.  At `m = 29` this gives `H* - deg± ≥ n / 78.1 - 1`; at `m = 127` the
ratio `H* / deg± ≥ 1.908` (`audit/sources/EXPLICIT_GAP.md`, Theorem B).
-/

namespace HeadComplexity

/-- Block `j` of an input on `k * N` bits. -/
def blockOf {N k : ℕ} (z : Fin (k * N) → Bool) (j : Fin k) : Fin N → Bool :=
  fun i => z (finProdFinEquiv (j, i))

/-- XOR of `k` independent copies of `f` on disjoint blocks. -/
def xorPower (k : ℕ) {N : ℕ} (f : (Fin N → Bool) → Bool) :
    (Fin (k * N) → Bool) → Bool :=
  fun z => decide (Odd (Finset.univ.filter fun j : Fin k => f (blockOf z j)).card)

/-- The tensored distance-majority family `G_{m,k}` on `k * (m + m)` bits. -/
def tensorDistThreshold (m k : ℕ) : (Fin (k * (m + m)) → Bool) → Bool :=
  xorPower k (distThreshold m)

/-- Degree upper bound: the product of the `k` quadratic block sign
polynomials (with the appropriate global sign) sign-represents `G_{m,k}`,
so `deg±(G_{m,k}) ≤ 2 k`. -/
theorem thresholdDegLE_tensorDistThreshold {m : ℕ} (hm : Odd m) (k : ℕ) :
    ThresholdDegLE (tensorDistThreshold m k) (2 * k) := by
  sorry

/-- **Theorem B, lower half**: the Forster ratio tensors, so
`γ_m ^ k ≤ 2 ^ (H* + 1) - 2` for the `k`-fold XOR power.  (Route: the sign
matrix under the all-left/all-right partition is a reindexed Kronecker power
up to the global sign `(-1)^(k+1)`, which preserves spectral norm and
sign-rank; apply `specNorm_kronecker`, `signRank_reindex`, `forster`, and the
sign-rank bridge.) -/
theorem theoremB_HStar {m : ℕ} (hm : Odd m) {k : ℕ} (hk : 1 ≤ k) :
    forsterRatio m ^ k ≤
      (2 : ℝ) ^ (HStar (k * (m + m)) (tensorDistThreshold m k) + 1) - 2 := by
  sorry

/-- **XOR sign encoding** (PROOFS.md P8.2): with the `signMatrix` encoding
`e(true) = 1`, `e(false) = -1`, the sign of an XOR of `k` bits is
`(-1)^(k+1) · ∏ⱼ e(bⱼ)`.  This is the global-sign bookkeeping that lets the
product of the `k` block sign polynomials sign-represent the tensored family
(`thresholdDegLE_tensorDistThreshold`).  Induction on `k`: `k = 0` gives `-1 =
-1`; the step is `e(b ⊕ c) = -e(b)·e(c)`.  Equivalently `∏ⱼ e(gⱼ) =
(-1) ^ (#false)`, and `#true + #false = k`. -/
theorem sign_xor_prod {k : ℕ} (g : Fin k → Bool) :
    (if (decide (Odd (Finset.univ.filter fun j : Fin k => g j).card)) then (1 : ℝ) else -1)
      = (-1 : ℝ) ^ (k + 1) * ∏ j : Fin k, (if g j then (1 : ℝ) else -1) := by
  sorry

open MvPolynomial in
/-- **Per-block strict sign representation** (PROOFS.md P8.4): the block-`j` copy
of the P7.1 quadratic `Δ - m/2`, its variables renamed to block `j` along
`i ↦ finProdFinEquiv (j, i)`, sign-represents `z ↦ distThreshold m (blockOf z j)`
with **nonzero** cube values (half-integers for odd `m`) and total degree `≤ 2`.
Route: take the explicit polynomial of `thresholdDegLE_distThreshold` and apply
`MvPolynomial.rename (fun i => finProdFinEquiv (j, i))`; `eval_rename` rewrites
the cube value as the block's `hammingDist - m/2`, an element of `ℤ + 1/2`. -/
theorem blockSignRep_distThreshold {m : ℕ} (hm : Odd m) {k : ℕ} (j : Fin k) :
    ∃ P : MvPolynomial (Fin (k * (m + m))) ℝ, P.totalDegree ≤ 2 ∧
      (∀ z : Fin (k * (m + m)) → Bool, eval (cubePoint z) P ≠ 0) ∧
      (∀ z : Fin (k * (m + m)) → Bool,
        (0 < eval (cubePoint z) P ↔ distThreshold m (blockOf z j) = true)) := by
  sorry

/-- **Theorem B** (`audit/sources/EXPLICIT_GAP.md`): explicit additive gap linear in
the input length: `H*(G_{m,k}) - deg±(G_{m,k}) ≥ k (log₂ γ_m - 2) - 1`,
positive for every odd `m ≥ 13`. -/
theorem theoremB_gap {m : ℕ} (hm : Odd m) (k : ℕ) :
    (k : ℝ) * (Real.logb 2 (forsterRatio m) - 2) - 1 ≤
      (HStar (k * (m + m)) (tensorDistThreshold m k) : ℝ) -
        (thresholdDeg (tensorDistThreshold m k) : ℝ) := by
  -- Degree stays `≤ 2k`, and `thresholdDeg ≤ H*` always.
  have hdeg : thresholdDeg (tensorDistThreshold m k) ≤ 2 * k :=
    thresholdDeg_le_of (thresholdDegLE_tensorDistThreshold hm k)
  have hdegR : (thresholdDeg (tensorDistThreshold m k) : ℝ) ≤ 2 * (k : ℝ) := by
    exact_mod_cast hdeg
  have hDH : thresholdDeg (tensorDistThreshold m k)
      ≤ HStar (k * (m + m)) (tensorDistThreshold m k) := thresholdDeg_le_HStar _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: LHS `= -1 ≤ 0 ≤` RHS, since `thresholdDeg ≤ H*`.
    simp only [Nat.cast_zero, zero_mul, zero_sub]
    have hDHR : (thresholdDeg (tensorDistThreshold m 0) : ℝ)
        ≤ (HStar (0 * (m + m)) (tensorDistThreshold m 0) : ℝ) := by exact_mod_cast hDH
    linarith
  · -- `k ≥ 1`: `γ^k ≤ 2^(H+1) - 2 < 2^(H+1)`, take `logb 2`.
    have hB := theoremB_HStar hm hk
    set H := HStar (k * (m + m)) (tensorDistThreshold m k) with hHdef
    have hγ : 0 < forsterRatio m := forsterRatio_pos m
    have hγk : 0 < forsterRatio m ^ k := pow_pos hγ k
    have hlt : forsterRatio m ^ k < (2 : ℝ) ^ (H + 1) := by linarith [hB]
    have hlog : (k : ℝ) * Real.logb 2 (forsterRatio m) < (H : ℝ) + 1 := by
      have h1 : Real.logb 2 (forsterRatio m ^ k) < Real.logb 2 ((2 : ℝ) ^ (H + 1)) :=
        Real.logb_lt_logb (by norm_num) hγk hlt
      rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h1
      push_cast at h1
      linarith [h1]
    have hexpand : (k : ℝ) * (Real.logb 2 (forsterRatio m) - 2) - 1
        = (k : ℝ) * Real.logb 2 (forsterRatio m) - 2 * (k : ℝ) - 1 := by ring
    rw [hexpand]
    linarith [hlog, hdegR]

end HeadComplexity
