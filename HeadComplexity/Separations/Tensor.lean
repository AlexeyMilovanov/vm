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

/-- **Theorem B** (`audit/sources/EXPLICIT_GAP.md`): explicit additive gap linear in
the input length: `H*(G_{m,k}) - deg±(G_{m,k}) ≥ k (log₂ γ_m - 2) - 1`,
positive for every odd `m ≥ 13`. -/
theorem theoremB_gap {m : ℕ} (hm : Odd m) (k : ℕ) :
    (k : ℝ) * (Real.logb 2 (forsterRatio m) - 2) - 1 ≤
      (HStar (k * (m + m)) (tensorDistThreshold m k) : ℝ) -
        (thresholdDeg (tensorDistThreshold m k) : ℝ) := by
  sorry

end HeadComplexity
