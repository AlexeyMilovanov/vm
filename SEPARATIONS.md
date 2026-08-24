# Separations layer: `H*` vs `deg±` (asymptotic)

Formalization target: the explicit asymptotic separations of
`audit/sources/EXPLICIT_GAP.md` (Theorems A, B, C) and `audit/sources/STRENGTHENING.md`
(NDISJ / split-shattering), on top of the corpus `HeadComplexity` base
(`HStar`, `ThresholdDegLE`, `degree_le_of_computableWithHeadsN`).

**Statement freeze.** The statements in `HeadComplexity/Separations/*.lean`
are the deliverable; proof work must not weaken, rename, or re-quantify them.
Any genuinely false statement is a blocker to report, not to repair silently.

## Status table

| Lean statement | File | Content | Status |
|---|---|---|---|
| `blockJoin` / `leftBits` / `rightBits` + simp API | TwoBlock.lean | two-block plumbing | **proved** |
| `signRank`, `signMatrix`, `signRank_le_rank` | SignRank.lean | sign-rank definition | **proved** (defs + basic lemma) |
| `signRank_reindex` | SignRank.lean | reindex invariance | **proved** (P1.1; also `signRank_neg`, `rank_neg`) |
| `signRank_le_of_computableWithHeadsN` | SignRankBridge.lean | **028 bridge**: `H` heads ⇒ srank ≤ 2^(H+1)−2 | **proved** (iter_002; main own result — group-cleared polynomial by head subsets, 2+2(2^H−2) rank-one pieces) |
| `signRank_le_pow_HStar` | SignRankBridge.lean | bridge at the optimum | **proved** modulo bridge |
| `signRank_le_of_thresholdDegLE` | SignRankBridge.lean | **Theorem C, degree half**: ceiling `(a+1)^d` | **proved** (iter_002; factor through monomials) |
| `signRank_le_two_pow_min` | SignRankBridge.lean | **Theorem C, dimension half**: ceiling `2^min(a,b)` | **proved** (via signRank_le_rank + rank_le_card) |
| `warren_sign_patterns_weak` | Warren.lean | **Warren 1968** (weak constant `(8(dk+1))^m`) | **sorry — EXTERNAL** (SOLE remaining sorry; real algebraic geometry: Milnor/Warren component bounds; parallel `warren-lean-28` pipeline; never attempt/queue) |
| `forster` | Forster.lean | **Forster 2002** `N ≤ srank·‖M‖₂` | **proved** (iter_002 s1; isotropic-position / eigendecomposition argument, P5.3) |
| `specNorm_reindex` | Forster.lean | spectral norm reindex invariance | **proved** (P6.1; piLpCongrLeft conjugation) |
| `specNorm_kronecker` | Forster.lean | spectral norm Kronecker multiplicativity | **proved** (P6.2; both halves `specNorm_kronecker_le` / `le_specNorm_kronecker` closed) |
| `thresholdDegLE_distThreshold` | DistanceThreshold.lean | `deg±(F_m) ≤ 2` | **proved** (P7.1; `Δ − m/2` quadratic, m odd) |
| `thresholdDeg_distThreshold` | DistanceThreshold.lean | `deg±(F_m) = 2` | **proved** (P7.2; lower half, cf. `not_thresholdDegLE_one_ndisj`) |
| `specNorm_signMatrix_distThreshold` | DistanceThreshold.lean | `‖M‖₂ = 2·C(m−1,(m−1)/2)` | **proved** (characters diagonalize; Fourier max at level 1) |
| `forsterRatio_le_signRank` | DistanceThreshold.lean | `γ_m ≤ srank(F_m)` | **proved** (P7.3, modulo forster + P4 deps) |
| `theoremA` | DistanceThreshold.lean | **Theorem A** | **proved** (P7.4, modulo P7.2 + srank deps) |
| `sqrt_le_forsterRatio` | DistanceThreshold.lean | `γ_m ≥ √(m−1)` | **proved** (P7.5; `two_mul_centralBinom_sq_le`) |
| `four_le_HStar_distThreshold_127` | DistanceThreshold.lean | `H*(F_127) ≥ 4` | **proved** (P7.6; kernel-checked `Nat.choose` arithmetic) |
| `thresholdDegLE_tensorDistThreshold` | Tensor.lean | `deg±(G_{m,k}) ≤ 2k` | **proved** (product of block quadratics) |
| `theoremB_HStar` | Tensor.lean | **Theorem B** lower `γ^k` | **proved** (Kronecker route) |
| `theoremB_gap` | Tensor.lean | **Theorem B** additive gap | **proved** (P8.5, modulo theoremB_HStar + P8.4) |
| `pow_le_of_leftShatters` | NDISJ.lean | shattering bound via Warren | **proved** modulo external `warren_sign_patterns` (P10.1 `pow_le_ncard_signPatterns` closed: η-shift + strict-sign-pattern injection) |
| `ndisj_leftShatters` | NDISJ.lean | `NDISJ` shatters `m` points | **proved** |
| `HStar_ndisj_le` | NDISJ.lean | `H*(NDISJ_m) ≤ m` | **proved** (P10.2; explicit smoothed `FracAtom` family) |
| `thresholdDeg_ndisj` | NDISJ.lean | `deg±(NDISJ_m) = 2` | **proved** (P10.3; `thresholdDegLE_ndisj` + `not_thresholdDegLE_one_ndisj`) |
| `ndisj_separation` | NDISJ.lean | **NDISJ separation** | **proved** modulo the two sorries it cites |
| `SharpShatteringUpperBound` | NDISJ.lean | upper half of the `VC = 2H` conjecture (`k ≤ 2H`) | `Prop` only, deliberately unasserted |
| `ndisj_of_sharpShatteringUpperBound` | NDISJ.lean | conjecture ⇒ `H* ≥ m/2` | **proved** |

## Suggested attack order

1. Easy own lemmas: `thresholdDegLE_distThreshold`, `signRank_reindex`,
   `thresholdDeg_ndisj` (upper half), `HStar_ndisj_le`.
2. The 028 bridge (`signRank_le_of_computableWithHeadsN`) — the central own
   result; the clearing machinery of `Polynomial/ModelToPolynomial.lean` is
   the starting point.
3. Theorem C, spectral layer (`specNorm_signMatrix_distThreshold`,
   `specNorm_kronecker`), then the compositions (`theoremA`, `theoremB_*`).
4. External monuments: `forster`, then `warren_sign_patterns` (hardest;
   `pow_le_of_leftShatters` depends on Warren).
5. Numeric endpoint `four_le_HStar_distThreshold_127` (big-binomial
   arithmetic; certified rational arithmetic, no `native_decide`).

Informal proofs: `audit/sources/EXPLICIT_GAP.md`, `audit/sources/STRENGTHENING.md` in the
rs-takehome archive. Model conventions: `model.md` of the corpus; the sign
matrix uses the canonical left/right split (`Fin.castAdd` / `Fin.natAdd`).
