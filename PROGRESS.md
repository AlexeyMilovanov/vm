# Pipeline progress log

Append-only. Each pipeline stage and each Jules phase adds a dated entry:
what was proved, decomposed, fixed, or found (including negative findings).

## Seed (2026-08-24)
- Layer state: 20 sorried declarations (1 external: warren_sign_patterns).
- Initial queue seeded from SEPARATIONS.md + PROOFS.md; 8 jules_ready.

## s1_opus_audit (2026-08-24)

**Audit.** Checked all 20 sorried declarations against their PROOFS.md items
(hypotheses, types, provability as stated). No frozen statement is wrong; no
helper statement needed repair. `lake env lean scripts/smoke/FrozenStatements.lean`
still elaborates (exit 0). No BLOCKER files needed.

**Proved (8 frozen leaves + supporting helpers), all compiling, no
axiom/admit/native_decide/maxHeartbeats:**
- `signRank_reindex` (P1.1) — sInf set equality via `Matrix.rank_reindex`.
- `signRank_neg` (P1.2, NEW helper) + `rank_neg` (NEW) — for Theorem B's global sign.
- `forsterRatio_le_signRank` (P7.3) — compose `forster` + `specNorm_signMatrix_distThreshold` value + `2^m` card, divide by binomial.
- `theoremA` (P7.4) — non-constancy of `F_m` (all-agree/all-disagree) ⇒ `1 ≤ H*`; chain bridge + P7.3, ℕ→ℝ cast of `2^(H+1)-2`.
- `thresholdDegLE_distThreshold` (P7.1) — quadratic `Σ(X_i+Y_i-2X_iY_i) - m/2`; per-pair XOR indicator; `hammingDist = Σ ite`; odd-`m` half-integer sign.
- `sqrt_le_forsterRatio` (P7.5) + `two_mul_centralBinom_sq_le` (NEW) — Nat invariant `(3t+1)·C(2t,t)² ≤ 16^t` (decreasing, `=` at t=0) ⇒ `2t·C² ≤ 16^t`; `Real.sqrt_le_sqrt`+`sqrt_sq`.
- `theoremB_gap` (P8.5) + `forsterRatio_pos` (NEW) — k=0 via `thresholdDeg ≤ H*`; k≥1 via `logb 2` of `γ^k < 2^(H+1)`.
- `thresholdDeg_ndisj` (P10.3) + `thresholdDegLE_ndisj`, `not_thresholdDegLE_one_ndisj` (NEW) — upper `ΣX_iY_i - 1/2`; lower via 4-point affine identity `(10|10),(01|01),(10|01),(01|10)` on indicator blocks.
- `specNorm_reindex` (P6.1) — `toEuclideanCLM(reindex e e M)` = `toEuclideanCLM M` conjugated by `LinearIsometryEquiv.piLpCongrLeft`; `submatrix_mulVec_equiv` for the identity, pre/post-comp isometry opNorm invariance.

**Added wiring (P1.4, new file `ThresholdDegAux.lean`):** `ThresholdDegLE.mono`,
`thresholdDeg_le_of`, `lt_thresholdDeg_of`, `thresholdDegLE_thresholdDeg`,
`exists_thresholdDegLE`, `thresholdDeg_le_HStar`. Imported by DistanceThreshold
and NDISJ (hence Tensor).

**Decomposed:** `specNorm_kronecker` (P6.2) now `le_antisymm` of two new
jules_ready halves `specNorm_kronecker_le` / `le_specNorm_kronecker` (parent
compiles from them).

**Queue now:** 13 sorried declarations — 1 external (warren), 3 jules_ready
(`specNorm_kronecker_le`, `le_specNorm_kronecker`, `thresholdDeg_distThreshold`),
9 hard. `lake build` green; FrozenStatements green.

## s2_gemini_do (2026-08-24)

**Proved:**
- `thresholdDeg_distThreshold` (P7.2) — added a helper `not_thresholdDegLE_one_distThreshold` proving `¬ ThresholdDegLE (distThreshold m) 1` using a 4-point affine identity on a subcube (pairs agreeing vs disagreeing), then combined with `thresholdDegLE_distThreshold` to get exactly degree 2.

**Queue now:** Removed `thresholdDeg_distThreshold` from `sorry_queue.json`.

## s3_gemini_check (2026-08-24)

**Findings:**
- Checked the `thresholdDeg_distThreshold` proof added by the previous agent. The proof is honest, does not weaken conclusions, and fully captures the `P7.2` requirement without vacuous statements. `sorry_queue.json` matches the codebase state.
- Removed 22 unused scratch files left behind by the previous agent.
- Cleaned up deprecation warnings (`push_neg` -> `push Not`, `mul_le_mul_right'` -> `mul_le_mul_left`) and unused `simp` arguments in `DistanceThreshold.lean`, `SignRankBridge.lean`, `Forster.lean`, and `NDISJ.lean`.

Build is fully green and `scripts/smoke/FrozenStatements.lean` compiles successfully.

## s4_codex_audit (2026-08-24)

**Audit.** Checked all 12 declarations that contained `sorry` at the start of
this stage against their PROOFS.md items and the frozen smoke statements.  The
hypotheses, types, edge cases, and claimed bounds are consistent; no frozen or
non-frozen statement needed repair, and no `BLOCKER_*.md` was needed.  Warren
remains the sole `external` leaf.  The two Kronecker halves remain the only
`jules_ready` leaves; the other seven open own leaves remain `hard`.

**Proved:**
- `four_le_HStar_distThreshold_127` (P7.6) — `norm_num [Nat.choose]`
  kernel-checks the exact central-binomial inequality (without
  `native_decide`); Theorem A then contradicts the three-head ceiling `14`.
- `HStar_ndisj_le` (P10.2) — added the honest helper
  `fracComputable_ndisj` and an explicit family of `m` smoothed `FracAtom`s.
  Distinguished pair coordinates have weight `1`, all other required-positive
  weights use `r = 1/(8(m+1)(2m+1))`; a true pair contributes at least `1`,
  while in the disjoint case the whole sum is below `1/2`.  The construction
  also handles `m = 0` directly.  Updated P10.2 in PROOFS.md to the exact Lean
  construction.

**Queue now:** 10 sorried declarations — 1 external, 2 jules_ready, 7 hard.
`lake build` is green; `lake env lean scripts/smoke/FrozenStatements.lean` is
green; the forbidden-declaration scan is clean.

## s5_gemini_do (2026-08-24)

**Proved (2 jules_ready leaves + supporting helpers):**
- `specNorm_kronecker_le` (P6.2) — proved via `A ⊗ₖ B = (A ⊗ₖ 1) * (1 ⊗ₖ B)` and the operator norm multiplicativity, bounding the Kronecker product with identity by identifying its action with a reshaped pointwise application of the base matrix, leveraging `EuclideanSpace.real_norm_sq_eq`.
- `le_specNorm_kronecker` (P6.2) — proved via compactness of the unit sphere yielding an operator norm maximizing vector (`attains_opNorm_aux`), then applying the action of `A ⊗ₖ B` to the Kronecker product vector of the respective maximizers for `A` and `B` and bounding the resulting norm.

**Queue now:** 8 sorried declarations left — 1 external (warren), 0 jules_ready, 7 hard. `lake build` is green; `lake env lean scripts/smoke/FrozenStatements.lean` is green.

## s6_gemini_check (2026-08-24)

**Verification:**
- Verified that the proofs for `specNorm_kronecker_le` and `le_specNorm_kronecker` in `Forster.lean` are honest, handle empty cases properly, and correctly formalize the bounds described in `PROOFS.md` (P6.2).
- Confirmed that new helper lemmas are all used and mathematically sound (e.g. `attains_opNorm_aux` using compactness, pointwise matrix products).
- `sorry_queue.json` correctly reflects 8 remaining sorried leaves, with 0 marked `jules_ready`.

**Fixes:**
- Removed several scratch/log files (`Forster_helpers.lean`, `fix.py`, `patch.lean`, `scratch.lean`, etc.) that were mistakenly added to the tree in the previous run.

## s7_opus_final (2026-08-24)

**Audit (gatekeeper).** `lake build` green (2504 jobs), `lake env lean
scripts/smoke/FrozenStatements.lean` exit 0, forbidden-construct scan
(`axiom`/`admit`/`native_decide`/`unsafe`/`maxHeartbeats`/`maxRecDepth`) clean.
Entry state: 8 sorried decls (1 external `warren_sign_patterns`, 7 hard,
**0 `jules_ready`**).  No frozen statement is wrong; no `BLOCKER_*` needed.

**Decomposition — grew the queue from 0 to 10 `jules_ready` leaves** by carving
self-contained, ≤2h sub-statements out of the "close" hard leaves (each proved
inside the referenced PROOFS.md item; statements verified to elaborate, all
TRUE):
- `rank_add_le` (P2.3, SignRank.lean) — matrix rank subadditivity (§11 item 4;
  confirmed absent in mathlib v4.31).
- `sum_choose_le_pow` (P3.3, SignRankBridge.lean) — `∑_{i≤d} C(a,i) ≤ (a+1)^d`.
- `card_le_specNorm_sq` (P5.1, Forster.lean) — `card ≤ (specNorm M)^2` for `±1` `M`.
- `sign_xor_prod` (P8.2) + `blockSignRep_distThreshold` (P8.4) (Tensor.lean) —
  the XOR sign identity and the per-block strict degree-2 sign rep; together they
  isolate the assembly of `thresholdDegLE_tensorDistThreshold`.
- Character framework for §4 (DistanceThreshold.lean): new defs `charFn`,
  `distSign` + **proved** `charFn_xor` (P4.1 multiplicativity, `cases`/`simp`),
  and four leaves `signMatrix_distThreshold_apply` (P4.1), `signMatrix_mulVec_charFn`
  (P4.1 eigen-action), `charFn_orthogonal` (P4.3), `distSign_sum_eq_zero` (P4.2).
- `warren_pow_simp` (P10.1, NDISJ.lean) — `(4 e H k/(2H))^{2H} = (2 e k)^{2H}`.

No parent was rewired (each hard parent still owns its monolithic `sorry`); the
new leaves are honest on-critical-path components, and every hard entry's queue
`note` now points to the leaves that decompose it.  PROOFS.md §11 updated with
the inventory of new leaves.

**Left `hard` (genuinely deep, not ≤2h-decomposable in this pass):** the 028
bridge P2 and shattering P10.1 (Model/Head internals), `forster` P5 (isotropic
position kernel P5.3), `specNorm_signMatrix_distThreshold` P4 (level-1 eigenvalue
bound P4.2 + Parseval assembly P4.3), `theoremB_HStar` P8.3 (needs new
`HStar_comp_equiv` P1.3 + forster), `signRank_le_of_thresholdDegLE` P3
(multilinearization/monomial factorization).

**Queue now:** 18 sorried decls — 1 external, 7 hard, **10 `jules_ready`**.
`lake build` green; FrozenStatements green.
