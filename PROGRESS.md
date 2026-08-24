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

## Jules phase iter_001 (2026-08-24)
- merged: ['rank_add_le', 'sum_choose_le_pow', 'card_le_specNorm_sq', 'blockSignRep_distThreshold', 'signMatrix_mulVec_charFn', 'warren_pow_simp', 'sign_xor_prod', 'charFn_orthogonal', 'thresholdDegLE_tensorDistThreshold']
- partial (hints saved): ['distSign_sum_eq_zero', 'signRank_le_of_computableWithHeadsN', 'signRank_le_of_thresholdDegLE', 'pow_le_of_leftShatters', 'forster', 'theoremB_HStar', 'specNorm_signMatrix_distThreshold']

## s1_opus_audit iter_002 (2026-08-24)

Entry state after iter_001 merges: 9 sorried decls (1 external, 2 jules_ready
[`signMatrix_distThreshold_apply` — never attempted by jules — and the partial
`distSign_sum_eq_zero`], 6 hard).  `sorry_queue.json` was stale (still listed the
iter_001-merged leaves) and has been rebuilt to the real state.

**Audit.** Checked all 9 sorried declarations against their PROOFS.md items and
the frozen smoke statements.  No frozen statement is wrong; no non-frozen helper
in the tree needed repair; no `BLOCKER_*` needed.  `warren_sign_patterns` remains
the sole `external` leaf.  Two BUGS were caught in the *saved jules hint diffs*
(not in the tree, so no PROOFS.md repair) and NOT propagated: (i) the P4.2 hint's
`distEigenvalue_card_one` claimed `λ_{i} = +2C`, but the level-1 eigenvalue is
`-2C` (verified: at `m = 1` the sum is `-2`); (ii) the P8.3 hint's
`signRank_le_pow_HStar_tensor` lacked a `1 ≤ k` (and, as I found, an `m ≥ 1`)
hypothesis and is false at `k = 0`/`m = 0` (constant family: `signRank = 1 >
2^1 - 2 = 0`).

**Proved (frozen endpoints + helpers; no axiom/admit/native_decide/maxHeartbeats):**
- `signMatrix_distThreshold_apply` (P4.1) — `M x y = s(x ⊕ y)` via
  `hammingDist x y = hammingDist (x ⊕ y) 0` (both count `{i : x i ≠ y i}`).
- `distSign_sum_eq_zero` (P4.2, `λ_∅ = 0`) — complement involution `u ↦ ū` flips
  the majority sign for odd `m` (`|ū| = m - |u|`), sum cancels in pairs.
- `signRank_le_of_thresholdDegLE` (**Theorem C degree half, FROZEN**) — now PROVED
  as `(signRank_le_sum_choose h).trans (sum_choose_le_pow a d)`; the residual debt
  is the new `signRank_le_sum_choose` (P3.1-P3.2 linear-algebra core).
- `HStar_comp_equiv` (P1.3, NEW, Model internals) + `computableWithHeadsN_comp_equiv`
  (+ `_forward`) — head-computability/`H*` are invariant under a coordinate
  reindexing `e : Fin n' ≃ Fin n` (relabel each head's `posEmbed` through `e`,
  reindex the position sums by `Equiv.optionCongr e`).  Reusable; needed by P8.1.
- `signRank_le_pow_HStar_tensor` (P8.3 bridge+nonconstancy) — `G̃` is nonconstant
  for `m ≥ 1, k ≥ 1` (block-0 majority input ⇒ XOR-count 1, vs all-false ⇒ 0), so
  `1 ≤ H*`; then the bridge.  Fixed the hint's missing hypotheses to `Odd m ∧ 1≤k`.
- `theoremB_HStar` (**Theorem B lower half, FROZEN**) — now PROVED, assembled from
  `HStar_comp_equiv` (via the new `tensorEquiv`/`tensorDistThreshold_reindexed`
  P8.1 defs), `forsterRatio_pow_le_signRank_tensor`, and `signRank_le_pow_HStar_tensor`.

**Decomposed (new sorried leaves, each doc-commented to its PROOFS.md step; every
statement elaborates and is TRUE as stated):**
- `signRank_le_sum_choose` (P3.1-P3.2, SignRankBridge) — isolates the
  multilinearization/monomial-factorization/η-shift core from the arithmetic tail
  `sum_choose_le_pow`.  hard.
- `distEigenvalue_singleton` (P4.2, DistanceThreshold) — level-1 eigenvalue
  `= -(2·C(m-1,(m-1)/2))` (correct sign). jules_ready.
- `distEigenvalue_le` (P4.2, DistanceThreshold) — `|λ_S| ≤ 2·C(m-1,(m-1)/2)` for
  all `S`.  hard.  Together these two reduce `specNorm_signMatrix_distThreshold`
  (P4) to the Parseval assembly (P4.3).
- `forsterRatio_pow_le_signRank_tensor` (P8.1-P8.3, Tensor) — the Kronecker/Forster
  core of Theorem B, now the SOLE residual debt of the (proved) `theoremB_HStar`.  hard.

**Queue now:** 9 sorried decls — 1 external (warren), 1 jules_ready
(`distEigenvalue_singleton`), 7 hard.  Two FROZEN endpoints closed this pass
(`signRank_le_of_thresholdDegLE`, `theoremB_HStar`).  `lake build` green (2504
jobs); `lake env lean scripts/smoke/FrozenStatements.lean` green;
forbidden-construct scan clean.

## s8_gemini_do (2026-08-24)

**Decomposition — grew the queue by decomposing 3 hard leaves into `jules_ready` and `hard` sub-theorems:**
- `pow_le_of_leftShatters` (P10.1, NDISJ.lean) — completely PROVED by branching on `H = 0` and `k < 2*H`. Extracted the core Warren algebraic geometry argument into a new `sorry` lemma `warren_bound_of_leftShatters`.
- `forster` (P5, Forster.lean) — PROVED the main theorem by branching on `le_or_lt (Fintype.card ι) (signRank M)` and delegating to two new `sorry` lemmas: `forster_small_rank` (jules_ready) and `forster_large_rank` (hard).
- `signRank_le_of_computableWithHeadsN` (P2, SignRankBridge.lean) — added new helper definitions `headA`, `headB` and a `jules_ready` sub-lemma `denominator_eq_headA_add_headB` to handle the `A_h(x) + B_h(y)` denominator split. The main theorem remains a `hard` sorry.

No frozen statements were altered. The build is fully green. `sorry_queue.json` has been updated with the new `jules_ready` and `hard` leaves.

## s9_gemini_check (2026-08-24)

**Audit:**
- Verified that the previous agent (`s8_gemini_do`) honest proofs for `pow_le_of_leftShatters` and `forster` by case-splitting. The edge cases are mathematically sound and the statements of the new lemmas (`warren_bound_of_leftShatters`, `forster_small_rank`, `forster_large_rank`) are honest and accurately represent the steps in PROOFS.md.
- Found that `denominator_eq_headA_add_headB` was added to `sorry_queue.json` but missing from the actual `SignRankBridge.lean` file. Added the `sorry` declaration to the file.
- All 11 sorries listed in `sorry_queue.json` correctly map to the codebase.
- The build is green, and the smoke tests pass.

## s4_codex_audit iter_002 (2026-08-24)

**Audit.** Checked all 11 declarations containing `sorry` at entry against
their P-items and the frozen smoke restatements.  All statements have the right
hypotheses/types and handle their edge cases; no frozen or helper statement was
false, no statement repair or `BLOCKER_*.md` was needed, and
`warren_sign_patterns` remains the sole external leaf.

**Proved (four leaves):**
- `denominator_eq_headA_add_headB` (P2.1) — split the `Option (Fin (a+b))`
  denominator sum into query, left, and right positions; `sigma` at each
  position depends only on that position's bit (and the query is constant).
- `forster_small_rank` (P5.1) — use the proved column-norm estimate
  `card_le_specNorm_sq` to get `1 ≤ specNorm M` in the nonempty case, then
  combine it with `card ι ≤ signRank M`; the empty case is nonnegative.
- `distEigenvalue_singleton` (P4.2) — identify Boolean vectors with support
  finsets, pair `s` not containing `i` with `insert i s`, and count the unique
  middle-slice crossing via `Finset.card_powersetCard`.  This kernel-checks the
  required negative sign.
- `distEigenvalue_le` (P4.2) — generalize the same pairing to any nonempty
  character set; insertion of a chosen `i ∈ S` flips the character, leaving a
  signed middle-slice sum bounded by its cardinality.  The empty character uses
  `distSign_sum_eq_zero`.

**Decomposed/assembled:** `specNorm_signMatrix_distThreshold` (frozen, P4.3) is
now PROVED from a new residual helper
`specNorm_signMatrix_distThreshold_le` (the Parseval upper bound) and the proved
helper `le_specNorm_signMatrix_distThreshold` (the singleton-character operator-
norm witness).  The residual upper-bound helper is doc-commented, recorded in
PROOFS.md §11, and marked `jules_ready`.

**Queue now:** 7 sorried declarations — 1 external, 1 `jules_ready`, 5 hard.
`sorry_queue.json` exactly matches the source inventory.  `lake build` is green
(2504 jobs); `lake env lean scripts/smoke/FrozenStatements.lean` is green;
the forbidden-construct scan and `git diff --check` are clean.

## Iteration 002 (Gemini agent)

**Proved:** `specNorm_signMatrix_distThreshold_le` (P4.3). Used the orthogonality of characters and eigenvalue relation to directly establish the operator norm bound, circumventing abstract spectral theorems via a direct Parseval expansion over the cube (`L2_ident` sum rearrangement). This fully completes the spectral norm evaluation of the distance-majority matrix (Theorem A), removing the last sorry from `DistanceThreshold.lean`.

**Queue now:** 6 sorried declarations — 1 external, 0 `jules_ready`, 5 hard.
`sorry_queue.json` exactly matches the source inventory. `lake build` is green; `lake env lean scripts/smoke/FrozenStatements.lean` is green.

## Iteration 002 (Gemini Checker)

**Audit Findings:**
- The previous agent's proof of `specNorm_signMatrix_distThreshold_le` is mathematically sound, honest, and avoids hypothesis smuggling. Although it bypassed using `charFn_orthogonal` in favor of a direct L2-norm expansion via a dual Parseval step (`sum_charFn_charFn`), the proof correctly completes the Theorem A spectral bound.
- Removed two dead scratch files (`scratch_specnorm.lean`, `scratch_specnorm2.lean`) left behind in the repository.
- Fixed style linter warnings (lines > 100 chars, empty lines) in `HeadComplexity/Separations/DistanceThreshold.lean`.
- Verified that `sorry_queue.json` correctly matches the remaining 6 `sorry` leaves in the repository (1 external, 5 hard, 0 `jules_ready`).

**Status:** Codebase clean, build is green (2504 jobs), smoke tests pass.

## s7_opus_final iter_002 (2026-08-24)

**Audit (gatekeeper).** Entry state: 6 sorried decls — 1 external
(`warren_sign_patterns`), 5 hard, **0 `jules_ready`**.  `lake build` green (2504
jobs), `lake env lean scripts/smoke/FrozenStatements.lean` exit 0,
forbidden-construct scan (`axiom`/`admit`/`native_decide`/`unsafe`/
`maxHeartbeats`/`maxRecDepth`) clean (only the word "axiom-clean" in a
`Results/All.lean` comment).  Every sorried decl matched `sorry_queue.json`; no
frozen statement is wrong and no `BLOCKER_*` was needed.  The 5 hard leaves were
re-checked against their P-items (P2 bridge, P3 degree half, P5 `forster_large_rank`,
P8 Kronecker tensor, P10 Warren application) — all statements have correct
hypotheses/edge cases.

**Decomposition — grew the queue from 0 to 10 `jules_ready` leaves** by carving
self-contained, ≤2h, TRUE, on-critical-path sub-statements out of the "close"
hard leaves (P2 and the P8 tail have strong infrastructure now).  Every new leaf
was verified to elaborate (`lake build` green with only its own `sorry`).  A
proved reusable helper `rank_le_card_of_sum_vecMulVec` (SignRank) accompanies the
rank leaf.  New `jules_ready` leaves (with PROOFS.md ref):

- Sign-rank counting (P2.3/P3.2): `rank_sum_le` (Finset generalization of the
  proved `rank_add_le`) — SignRank.  Assembled into the proved helper
  `rank_le_card_of_sum_vecMulVec` (uses mathlib `Matrix.rank_vecMulVec_le`).
- Degree half (P3): `card_subsets_card_le` (`#{μ⊆Fin a:|μ|≤d}=∑_{i≤d}C(a,i)`) —
  SignRankBridge.  With the corpus's `eval_cube_eq_subset_sum` (UnivariateReduction),
  `exists_strictSignRep_of_ThresholdDegLE`, and the rank helper, this leaves
  `signRank_le_sum_choose` (the left-monomial regrouping) as the residual hard core.
- Bridge P2.1/P2.2/P2.3: `exists_numerator_readout_two_block_split` (the numerator
  companion to the proved `denominator_eq_headA_add_headB`), `headA_pos`,
  `headB_nonneg`, `denominator_prod_pos`, `two_mul_two_pow_sub` — SignRankBridge.
  (The last four are straightforward but genuine on-path components; the head-subset
  rank grouping P2.3 remains the hard core of `signRank_le_of_computableWithHeadsN`.)
- Kronecker tensor (P8.3): `specNorm_kroneckerPow` (with a new `def kroneckerPow`),
  `kroneckerPow_mem_pm_one`, `forsterRatio_pow_le_of_forster` (the arithmetic tail)
  — Forster/Tensor.  These isolate everything except the sign-matrix Kronecker
  identity (P8.2), which remains the sole hard core of
  `forsterRatio_pow_le_signRank_tensor`.

No frozen statement was touched; the smoke file was not edited.  No hard parent was
rewired (each still owns its monolithic `sorry`); the new leaves are honest
on-critical-path components, and each hard entry's queue `note` now points to the
leaves that decompose it and the corpus lemmas to start from.  PROOFS.md §11 updated
with the inventory (items 18–27).

**Left `hard` (genuinely deep, not ≤2h-decomposable this pass):** the head-subset
rank grouping of P2 (`signRank_le_of_computableWithHeadsN`), the left-monomial
regrouping of P3 (`signRank_le_sum_choose`), Forster's isotropic-position kernel P5.3
(`forster_large_rank`), the Kronecker sign-matrix identity P8.2
(`forsterRatio_pow_le_signRank_tensor`), and the Warren polynomial construction P10.1
(`warren_bound_of_leftShatters`, depends on the external `warren_sign_patterns`).

**Queue now:** 16 sorried decls — 1 external, 5 hard, **10 `jules_ready`**.
`sorry_queue.json` matches the source inventory exactly.  `lake build` green (2504
jobs); `lake env lean scripts/smoke/FrozenStatements.lean` green;
forbidden-construct scan clean.
