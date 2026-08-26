# rs-takehome: map of 197 corpus theorems and post-corpus results

Repo at commit `9117f29`. Full corpus read by three parallel surveyors (folders 01–02 / 03–04 / 05–06),
each file read in full; key algebraic identities spot-checked; the 8-bit separation verifiers (Thm 189)
and the 9-bit verifier (185) re-run and passing.

Setup: H*(f) = min heads to compute Boolean f in a 1-layer attention-only transformer with linear
readout. Organizing sandwich: `deg_±(f) ≤ H*(f) = L_frac(f) ≤ C_+(f) ≤ M_+(f)−1`, parallel sparse
route `deg_± ≤ H* ≤ afs_± ≤ ptfsp`, and the optimized invariant chain `H* ≤ actc ≤ min{ctc, afs_±}`.

Legend per row: `NNN | title | statement | Sig (S/A/B/C) | novelty | proof confidence | role | deps`.

---

## Post-corpus results through 2026-08-25

The original numbered corpus ends at theorem 197. The following results were
obtained later and are kept as theorem-grade notes rather than silently
renumbering the immutable source snapshot.

The global hierarchy is

$$ \deg_{\pm}(f)\leq\operatorname{POIC}_2(f)\leq H^{\ast}(f). $$

It must not be replaced by an equality. The post-corpus project has explicit
families on which the left and right quantities differ asymptotically.

| ID | result | status and source |
|---|---|---|
| P01 | **Explicit asymptotic gaps.** The XOR-tensor family has $H^{\ast}-\deg_{\pm}=\Omega(n)$; `NDISJ_m` has $\deg_{\pm}=2$ and $H^{\ast}=\Omega(n/\log n)$. | Proved, using respectively the Forster/sign-rank bridge and split shattering. See [EXPLICIT_GAP.md](EXPLICIT_GAP.md) and Sections 1-2 of [STRENGTHENING.md](STRENGTHENING.md). The proposed linear `NDISJ` strengthening remains conjectural. |
| P02 | **Canonical POIC2 hierarchy.** With no free bias, $\deg_{\pm}\leq\operatorname{POIC}_2\leq H^{\ast}\leq2^{\operatorname{POIC}_2}-1$. | Proved with finite-cube strictification and polarization. See [POLY_CLOSENESS_MODEL_AUDIT.md](POLY_CLOSENESS_MODEL_AUDIT.md). General polynomial closeness remains open. |
| P03 | **Fixed-block polynomial converse.** If $f$ is symmetric within each of $b$ fixed blocks and $d=\deg_{\pm}(f)$, then $H^{\ast}(f)\leq(d-1)\binom{d+b-2}{b-1}+1$. Hence $H^{\ast}=O_b(\operatorname{POIC}_2^b)$. | Proved. See [TWO_BLOCK_ATTACK_2026-08-24.md](TWO_BLOCK_ATTACK_2026-08-24.md). This is a special-class bound, not a general equality. |
| P04 | **One marked bit exactness.** If $f(z,y)=F(z,\lvert y\rvert)$, then $\deg_{\pm}(f)=\operatorname{POIC}_2(f)=H^{\ast}(f)$. | Proved for this explicitly scoped class. See [ONE_MARKED_BIT_EXACT_2026-08-24.md](ONE_MARKED_BIT_EXACT_2026-08-24.md). |
| P05 | **Two-block low-degree and cycle closure.** For two independently symmetric blocks and $\deg_{\pm}\leq2$, $\operatorname{POIC}_2=H^{\ast}\leq3$. The two-block pure-cycle budget-three topology also recollapses to three heads. | Proved. The common value may be three when $\deg_{\pm}=2$. The residual budget-three topologies are `B`, `D`, and `F'`. See [TWO_BLOCK_ATTACK_2026-08-24.md](TWO_BLOCK_ATTACK_2026-08-24.md) and [TWO_BLOCK_Q3_ATTACK.md](TWO_BLOCK_Q3_ATTACK.md). |
| P06 | **Transverse-cut parity family.** For $m\geq1$, $\deg_{\pm}(g_m)=2m-1$; at $m=2$, $\deg_{\pm}=\operatorname{POIC}_2=H^{\ast}=3$. | Proved by a finite-difference dual witness, interpolation, and an exact strict certificate. See [TWO_BLOCK_ONE_CUT_EXACT.md](TWO_BLOCK_ONE_CUT_EXACT.md) and its verifier. |
| P07 | **cpr2 mechanism exclusions (2026-08-25 gap hunt).** Top-face LTF necessity for hierarchical pinching cascades (Lemma 1); for the deterministic orbit-C instance `cpr2` (n=12) all monotone faces of codimension $\leq3$ are certified non-LTF and exactly 8 codim-4 LTF faces exist, all with exact rational Farkas/LTF certificates — cascades with top codimension $\leq4$ are confined to those 8 tops. New active-set search engine independently re-derives $H^{\ast}(\mathrm{cpr1})=3$ (83 s, exact margin 1) and resolves 8/8 designed $n=10$ C-instances (incl. orientation-incompatible pools) to equality via exact signature certificates. **Finale: `cpr2` RESOLVED — an exact interior 3-head certificate was found (dedicated active-set run, 31 min) and verified in rational arithmetic (min margin 1), so $H^{\ast}(\mathrm{cpr2})\leq3$ and $\operatorname{POIC}_2(\mathrm{cpr2})=H^{\ast}(\mathrm{cpr2})$ unconditionally. Seed 7 of PUSH3_FINAL closed; still ZERO known instances with $\operatorname{POIC}_2<H^{\ast}$.** | Exact parts CERTIFICATE-grade; search parts NUMERICAL with per-vertex calibration. See [POIC2_GAP_HUNT_2026-08-25_PLAN.md](POIC2_GAP_HUNT_2026-08-25_PLAN.md), [POIC2_GAP_HUNT_2026-08-25_RESULTS.md](POIC2_GAP_HUNT_2026-08-25_RESULTS.md), verifier [verify_gap25_session.py](verify_gap25_session.py). |

| P08 | **Positive-multiplier recollapse, corrected.** Exact pole-cancellation identities close aligned D/F'/B subclasses; for constant singleton numerator in D, multiplication by $B_2$ actually gives two heads, sharper than the earlier $B_2+B_3$ formula. | Proved identities. The earlier formal-degree claim of completeness is retracted because pole cancellation and Boolean aliasing evade it. See [POIC2_MULTIPLIER_RECOLLAPSE_2026-08-25.md](POIC2_MULTIPLIER_RECOLLAPSE_2026-08-25.md) and the corrected audit in [POIC2_GLOBAL_EQUALITY_2H_SPRINT_2026-08-25_RESULTS.md](POIC2_GLOBAL_EQUALITY_2H_SPRINT_2026-08-25_RESULTS.md). |
| P09 | **Five-variable quadratic equality.** Every quadratic threshold function on $n\le5$ satisfies $H^*\le3$ and $\operatorname{POIC}_2=H^*$. Hence every pure-C budget-three source on $n\le5$ recollapses without rank/orientation restrictions. | Proved by Boolean diagonal completion to inertia at most $(2,2)$ plus the legal signature compiler. The matrix threshold is sharp at $n=6$ via a constant nonprincipal minor, but that is not a Boolean lower bound. See [POIC2_GLOBAL_EQUALITY_2H_SPRINT_2026-08-25_RESULTS.md](POIC2_GLOBAL_EQUALITY_2H_SPRINT_2026-08-25_RESULTS.md). |
| P10 | **All-budget multiplier compilers.** PV1/PV2 at one pool vertex imply $H^*\le s$; a genuine aligned vertex-cover-two class gives the strict reduction $H^*\le s-1$; an affine common multiplier gives the corresponding merged-pole compiler. Optimal PV/common-multiplier certificates yield $\operatorname{POIC}_2=H^*$; the VC2 identity instead proves its displayed budget-$s$ certificate nonoptimal, and equality at the reduced level needs a separate lower bound. | Proved by exact identities, with rational verifier [verify_pool_vertex_multiplier.py](verify_pool_vertex_multiplier.py). See the sprint [results](POIC2_GLOBAL_EQUALITY_2H_SPRINT_2026-08-25_RESULTS.md) and live journal. |
| P11 | **Hollow--Koszul compiler.** The space $\mathrm{Aff}+\mathrm{Aff}\,u+\mathrm{Aff}\,v+\langle uv(u-v)\rangle$ is a three-head boundary class. It strictly exceeds quadratic signature (exact parity example). On $n=4$ every nonzero cubic coefficient stratum has a hollow-injective representative, yielding a new structural proof for all degree-$\le3$ targets. | Proved with exact rational/symbolic checks. Equality for all $n\le4$ functions was already implicit in original theorem 183 and is not claimed new. See [POIC2_GLOBAL_EQUALITY_2H_SPRINT_2026-08-25_RESULTS.md](POIC2_GLOBAL_EQUALITY_2H_SPRINT_2026-08-25_RESULTS.md). |

| P12 | **n<=5 reduction.** $\operatorname{POIC}_2=H^{\ast}$ for every $f$ on $n\le5$ with $\deg_{\pm}\ne3$ (assembled from 183/186/187, Q5, parity). At $n=5$, A/C-certified functions have $H^{\ast}\le2$ (187 upgrades the general $\le3$), so full $n\le5$ equality is EXACTLY: degree-3 D/F'/B-certified functions have $H^{\ast}\le3$, plus the budget-4 clause. Saturation note: at $n=5$ the 3-head family has 34 parameters vs 32 vertices; the proposed finishing move is a 186-style exhaustive NPN census of the $\deg_{\pm}=3$ stratum (also advancing the open $n_{sep}$ question). | Theorems proved by assembly; sweep NUMERICAL. See [POIC2_N5_REDUCTION_2026-08-25.md](POIC2_N5_REDUCTION_2026-08-25.md), verifier [verify_n5_reduction.py](verify_n5_reduction.py). |

| P13 | **n=5 census feasibility.** The legal symmetry group for $H^{\ast}$ is $S_5\times\{\pm\}$ (NPN is invalid: input complementation breaks denominator orientation), giving exactly **18,666,624** classes by Burnside — 30x the NPN count. Measured: 66% of 5-bit functions have $\deg_{\pm}=3$; degree filtering costs ~4.3 ms/function; a naive 3-head search costs ~0.46 s/class; a fixed dictionary of 60 denominator triples covers **95%** of degree-three classes with median second-entry hit, cutting the whole census to roughly 7 CPU-days. One pass would settle n<=5 equality, the corpus's open $n_{sep}\in\{5,6,7,8\}$, and $H^{\ast}$ flip-invariance. | Class count PROVED (Burnside); costs and coverage EXPERIMENTAL; plan not yet run. See [POIC2_N5_CENSUS_FEASIBILITY_2026-08-25.md](POIC2_N5_CENSUS_FEASIBILITY_2026-08-25.md). |

| P18 | **Unconditional two-block joint-event equality.** For a uniformly random table on `{0..a}x{0..b}`, `a,b>=1`, `Pr[POIC_2<=3 AND POIC_2!=H*] <= (1+a^2+b^2+4ab+a^2b^2)/2^(2a+2b-1)`, the exact all-four-edges-quiet probability. This is ambient joint-event control, not a conditional exact-budget estimate. | Proved by budget-<=2 exactness, Reynolds clearing, SFO-3, and exact boundary counting. See [POIC2_TYPICALITY_3H_SPRINT_2026-08-26_RESULTS.md](POIC2_TYPICALITY_3H_SPRINT_2026-08-26_RESULTS.md). |
| P19 | **Universal power-block bank and exact Q6 ACI tiling.** With `p=2^floor(log2 n)`, every real table has a fixed legal `N/p`-head bank, so `H*<=Bank(n)<=N/p<=2N/(n+1)`; shared constants give `Bank(n)>=ceil((N-1)/n)`. Equality holds for power-of-two arities and, by independently reproduced modular banks, for `1<=n<=12`. An explicit exact ACI partition gives `P_ACI(6)=11` (nine 6-blocks and two 5-blocks). `Bank` is fixed-pole span complexity, not archive calibration rho. | Proved; exact Fraction/modular verifiers. See [POIC2_TYPICALITY_3H_SPRINT_2026-08-26_RESULTS.md](POIC2_TYPICALITY_3H_SPRINT_2026-08-26_RESULTS.md), `agents/typicality-sprint-2026-08-26/verify_power_block_partition.py`, `agents/typicality-sprint-2026-08-26/verify_q6_optimal_partition.py`, and the independent `agents/typicality-sprint-2026-08-26/verify_aci_partition_n6_exact.py`. |
| P20 | **Exact conditional 6x5 profile theorem.** Uniformly over distinct two-block functions of block sizes `5+4`, `Pr[H*>3 | POIC_2=3] <= 40/168277 < 2.38e-4`. | Certificate-grade sandwich from 168237 disjoint easy exact-q3 tables and at most 40 E candidates. See [POIC2_TYPICALITY_3H_SPRINT_2026-08-26_RESULTS.md](POIC2_TYPICALITY_3H_SPRINT_2026-08-26_RESULTS.md). |
| P23 | **Exact-layer entropy atypicality.** With `S_ex(f)=log2 #{g:POIC_2(g)=POIC_2(f)}` and `m_ex=N/max(1,S_ex)`, large `m_ex` has an exponential raw-function tail and every nonconstant `f` satisfies `H*<=C m_ex POIC_2 log(2+m_ex POIC_2)`. | Proved by exact-layer counting, Warren, and P19; information-theoretic rather than geometric. See [POIC2_TYPICALITY_3H_SPRINT_2026-08-26_RESULTS.md](POIC2_TYPICALITY_3H_SPRINT_2026-08-26_RESULTS.md). |
| P24 | **Anchored QMOD-rank compilers.** A strict legal-anchor PENCIL cubic of quotient rank `r` has `H*<=3+r`; `R` shared-anchor pencils plus residual rank `r` have `H*<=1+2R+r`. | Proved algebraically with affine numerators; compiler only, no rarity tail. See [POIC2_TYPICALITY_3H_SPRINT_2026-08-26_RESULTS.md](POIC2_TYPICALITY_3H_SPRINT_2026-08-26_RESULTS.md) and `agents/typicality-sprint-2026-08-26/verify_qmod_rank_compiler.py` (saved output `verify_qmod_rank_compiler.out`: `ALL PASS`). |

Status discipline: solver successes become upper bounds only after independent
sign verification; solver failures are not lower bounds. Conditional lemmas in
`TWO_BLOCK_Q3_ATTACK.md` and the conjecture
$H^{\ast}\leq\operatorname{poly}(\operatorname{POIC}_2)$ remain open.

## S-tier (the results a human would headline)

| # | result | why it matters |
|---|--------|----------------|
| 010 | **Normal form H\* = L_frac** | Converts the architecture question into a clean algebraic invariant (min # of linear-fractional "atoms" whose sum sign-represents f). Everything in the corpus routes through it. |
| 006 | **deg_±(f) ≤ H\*(f)** | The general lower bound; powers all exactness through n=4 and every separation's degree side. |
| 011 | **H\*=1 ⇔ nonconstant LTF** (H\*=0 ⇔ const) | Pins levels 0/1 exactly; one head = one halfspace. |
| 012 | **Symmetric f: H\* = # sign changes of the profile** | Complete exact answer for the symmetric class; partial-fraction reciprocal-atom construction is the corpus's prettiest upper bound. |
| 008 | **H\*(XOR_n) = n** | The motivating question answered exactly. |
| 016 / 183 | **Exact H\* = deg_± for all n ≤ 3 / n ≤ 4** | 183 is exhaustive with exact-integer certificate archives (SHA-256-pinned); establishes n_sep ≥ 5. |
| 026 | **Counting LB: #{f : H\*≤H} ≤ 2^{O(n²H)}** | Worst case Ω(2^n/n²); almost all f need exponentially many heads; proves no poly-size classical invariant can equal H*. The only superlinear lower bound. |
| 02_sep/013 | **10-bit strict separation deg_±=2 < 3 ≤ H\*** | First proof the left sandwich inequality is strict; debuts the mixed-antipodal-rank technique (rank ≤4 for 2 heads vs forced rank 5). |
| 060 | **H\*(EQ_m) = 2 exactly, all m** | Elegant complete answer for a named family (1−(X−Y)² two-atom trick on binary encodings). |
| 087 | **H\*(G(z,T)) ≤ H\*(T)+1 for every non-XOR gate G** | The only true head-level Shannon recursion; isolates XOR/XNOR as the sole open recursive case. (Leans on an uncited strengthening of 028's dummy-extension — re-audit first.) |
| 091/092 | **Calibration obstruction: an LTF computable by 1 head cannot be 0/1-approximated by 1 head below error exactly 1/4** | Genuinely novel concept: *computing* ≠ *calibrating*; foundation of the ρ theory. |
| 105 | **∃ LTFs T,U: H\*(T∧U) ≥ cn** | The hardness benchmark (Sherstov 2009 import through 006); with 106/107 kills vote-size and decision-list-length as upper bounds. |
| 180 | **First strict separation (n=56)** | Tope-cycle ⇒ sign-rank ≥ 7 vs 2-head ≤ 6, by hand. Source of the whole folder-06 arc. |
| 182 | **Natural function separation: Δ(x,y) ≥ 3 on 12 bits** | Home of the reusable lemma: 2 heads ⇒ partition sign-rank ≤ 6 under *every* split. |
| 185 | **9-bit separation, enumeration-free** | Antipodal slices force cross-block rank 5 vs ≤ 4 for two heads; pure hand linear algebra. Most reusable LB idea besides 189's. |
| 186 / 187 | **5-bit classifications: deg_±=4 ⇒ H\*=4; deg_±=2 ⇒ H\*=2** | Pincer: any 5-bit separation must sit at deg_± = 3. (187's Lemma 1 cites an *external* GitHub lead file — load-bearing provenance gap.) |
| 189 | **HEADLINE: f_8 = 1[Δ(x,y)≥2] on 4+4 bits has deg_± = 2 < H\* = 3 exactly** | Smallest-dimension separation, most natural function, and the only one with a matching upper bound (explicit integer 3-head certificate, min margin 58). Lower bound is a new hand-written spectral technique (mixed curvature ≺ 0 → dual-null factor → column-max spectral inequality). Both verifiers re-run: pass. |

Separation dimension trajectory: 56 (180) → 43 (181) → 12 (182) → 11 (184) → 9 (185) → 8 (189).
181 and 184 are strictly superseded as results (survive only as method steps).
Open: n_sep ∈ {5,6,7,8}; any 5-bit separation forced to deg_± = 3 by 186+187.

## A-tier highlights (important machinery / tight family results)

- 004 (thresholds = 1 head), 009 (M_+−1 bound, universal 2^n−1), 013-found. (C_+ upper half of sandwich), 021/025 (determinant-span schema, universal ⌈(2^n−1)/n⌉ certificates for n ≤ 12 — independently reproduced exact modular ranks, including 4096/4096 at n=12), 027 (deg_±=n only for parity), 028 (restriction/junta invariances + tangent sign-rank cap 2^{H+1}−2), 029 (monotone DNF ≤ s heads), 032 (denominator orientation: single-head denominators = one-signed affine forms), 041 (H\* ≤ ptfsp), 045 (Fourier support cost), 048 (afs_± engine), 046 (affine-parity restriction witness π⊕), 050 (intersection profiles), 061/062 (affine level sets & slabs ≤ 2 heads — most reused exactness engine), 076 (LTF cofactor slope distance), 081 (fresh-XOR: deg_±(z⊕f) = deg_±(f)+1), 085/086 (calibrated votes), 088 (literal decision lists), 093/095 (ρ calibration invariant + LB), 103/104/110 (actc invariant and hierarchy), 106/107 (vote/DL/ρ negative results), 126 (H\*(z⊕OR)=H\*(z⊕AND)=2 exact), 135/136/138 (positive-statistic degree spans — engine of folder 05), 137/141 (exact gate tables), 139 (fresh-XOR ≤ C+1), 158 (shared-statistic sandwich), 165/170 (positive grids / lex multigrid), 176 (multigrid cost exponentially loose on parity — honest negative), 190–192 (slice-rank-2 obstruction + its ceiling + multiway limits), 195 (κ_atom sparsification via approximate Carathéodory).

## Reliability notes

1. **Solid & verified here:** 189 and 185 verifiers re-run (pass); 135/136 determinants recomputed (−9, −480); 060's identity, 091/092's 1/4, 081's slice argument hand-checked by surveyor.
2. **Plausible only:** 017–025 universal bounds rest entirely on asserted determinant residues mod 1000003, no reproduction script cited. 054/058/059 rest on Python enumerations + hardcoded certificates. 186/187 archives exact-integer-verified but heavy verifiers not re-run.
3. **Single points of failure:** every upper bound routes through 010/011/015/032 (atom calculus) — these are also the Lean-formalized core, which mitigates. 105 is only as good as Sherstov 2009 (safe).
4. **Provenance gaps:** 187 Lemma 1 cites an external repo lead file; 087 leans on an uncited strengthening of 028; 183's degree census imports the known 4-var LTF count.
5. **Editorial:** two theorems numbered 013 (no mathematical conflict; cross-refs point to the foundations one); 188 missing (no dangling references — presumably retracted); theorems.md duplicates 190–197 entries; main README still advertises the 10-bit separation as the frontier, superseded by 189.

## Dead ends (know they exist, don't spend writeup space)

- Classical restatements: 007, 027 (folklore), 031, 034, 047's degree half, 071, 081/083 (standard composition), 102, 197.
- Superseded: 130, 131(C≥2), 134 (by 137/139); 146/150 (worst-case shadows); 181, 184 (as separations).
- Machinery that never pays off: lgactc/xactc (122–125) — the one real fresh-XOR exactness (126) bypasses it; the invariant-naming layer osc₊/eps₊/pgc₊/mgc₊/mhc (149, 163, 169, 173, 174) — nothing downstream instantiates it, and 176 proves it exponentially loose; scafs± (078, superseded by 114); ctc satellites 100/101/102, and routine invariance files 097/108/125.
- At the original corpus commit, the folder 05 to folder 06 feed is formally **zero**: no separation cites folder 05. Theorems 177–179 prove two-head bounds only for a singleton profile-grid point, one affine profile-grid line, and one affine profile-grid strip. They do **not** cover all functions of $(|x_A|,|x_B|)$. The successful corpus candidates 182 and 189 are Hamming-distance thresholds and do not factor through those two independent block weights.

## Recommended Part One narrative (single coherent line)

1. Normal form **H\* = L_frac** (010) with levels 0/1 (011) — the model-native invariant.
2. General lower bound **deg_± ≤ H\*** (006) + symmetric exactness (012) + parity (008).
3. Exactness holds through n ≤ 4 (016, 183) — degree almost *is* the answer…
4. …but strictly fails: separation arc 180 → 182 → 185 → **189** (exact 8-bit deg_±=2 < H\*=3), with 186/187 pinning any smaller example to deg_±=3 at n=5.
5. Why no classical measure can ever fully work: counting bound 026 (Ω(2^n/n²) worst case) + slice-rank/sign-rank caps (028, 190–192) + calibration obstruction (091, 107).

## Historical Part Two candidate directions at the corpus commit

Direction 1 below was superseded by post-corpus result P01. The list is kept to
record what was open at commit `9117f29`; use the post-corpus table above for
the current frontier.

1. **Asymptotic separation.** 189 gives one point (n=8, gap 3 vs 2). Does the family f_{2m}(x,y)=1[Δ(x,y)≥2] (or ≥m/2) on m+m bits have H\* = ω(1) while deg_± = O(1)? Even H\* ≥ 4 for some constant-degree family would be new — the corpus has NO lower bound beyond 3 heads except via degree. The 189 spectral technique and 185 rank technique are the starting points.
2. **Close the counting-vs-construction gap.** 026 gives W(n) = Ω(2^n/n²); 025 gives W(n) ≤ ⌈(2^n−1)/n⌉. A factor n apart — tighten either side (e.g. improve Warren-bound bookkeeping to Ω(2^n/n), or beat the determinant-span construction).
3. **n_sep ∈ {5,6,7,8}.** Search 5-bit deg_±=3 functions (only class left open by 186/187) for a 4-head lower bound, or prove 5-bit collapse.
4. **IP_m gap.** m ≤ H\*(IP_m) ≤ 2^m−1 is wide open; any ω(m) lower bound would be a scalable-family result (relates to direction 1).
5. **Formalize 189 in Lean** (the repo's own bonus criterion; formalization/ already has the atom calculus and the 10-bit separation L13 as scaffolding).
6. **Calibration theory ρ:** 091/107 open the question of characterizing ρ(LTF) (margin/weight complexity?) — a clean self-contained direction.

## Full per-theorem tables

### Folder 01 (001–027) + 02 (028–045, 190–197) + 02_sep (013)

```
001 | Checkerboard additive decomposition | 1-head numerator/denominator split additively on a 2-cube | B | low | solid | machinery | model
002 | Antipode identities | N(0,0)+N(1,1)=N(0,1)+N(1,0), same for D | C | low | solid | machinery | 001
003 | Checkerboard obstruction | XOR-pattern restriction ⇒ H*≥2 | B | med | solid | machinery (superseded by 011) | 001,002
004 | Symmetric thresholds | H*(T_{n,t})=1 incl. AND/OR/MAJ | A | med | solid | core construction | model
005 | Family consequences | digest: thresholds 1, parity n, EXACT 2 | B | — | solid | corollary digest | 003,004,012
006 | deg_± ≤ H* | H heads clear to degree-H sign polynomial | S | high | solid | core-pillar LB | model
007 | deg_±(XOR_n)=n | classical | B | low | solid | machinery | —
008 | H*(XOR_n)=n | LB via 006+007; UB explicit n heads (partial-fraction basis) | S | high | solid | core-pillar | 006,007
009 | Weighted-sum bound | f=F(pos. weighted sum), M values ⇒ H*≤M−1; universal 2^n−1 | A | high | solid | core construction | 008
010 | Linear-fractional normal form | H* = L_frac exactly, both directions constructive | S | high | solid | core-pillar | model
011 | One-head characterization | H*≤1 ⇔ const/LTF | S | high | solid | core-pillar | 010
012 | Symmetric sign changes | H*(sym f) = C(F) exactly | S | high | solid | core-pillar | 006,010
013 | Positive-projection sign changes | H* ≤ C_t(F) ≤ C_+ ≤ M_+−1 | A | high | solid | core (upper sandwich) | 010,012
014 | Three-bit projection cases | H*(00011000)=2; 2≤H*(00101001)≤3 | B | low | solid | case work | 011,013
015 | Three-bit quadratic UB | deg-2 sign poly (n=3) ⇒ H*≤2 (7×7 det basis) | A | med | solid | machinery | 010,014
016 | Three-bit exact classification | n=3: H*=deg_± | S | high | solid | core-pillar | 006,011,015
017–020,022–024 | Universal UBs n=4..10 | H* ≤ 4/7/11/19/32/57/103 via determinant certificates | B | med | SOLID (independently reproduced exact mod-p ranks; see P19) | corollaries of 021 | 021
021 | Determinant-span schema | span criterion; method floor H ≥ ⌈(2^n−1)/n⌉ | A | high | solid | machinery | 010,015
025 | Compact certificates | n=3..12: H* ≤ ⌈(2^n−1)/n⌉, one pseudorandom recipe | A | med | PLAUSIBLE | machinery | 021
026 | Counting lower bound | #{H*≤H} ≤ 2^{O(n²H)}; W(n)=Ω(2^n/n²) | S | high | solid | core-pillar | 010
027 | Top degree only parity | deg_±=n ⇔ (anti)parity | A | low | solid | machinery | 007
028 | Restrictions/juntas/sign-rank | H* restriction-monotone; junta-exact; srank ≤ 2^{H+1}−2 (needs n≥2H+2) | A | high | solid | core machinery | 010,008
029 | Monotone DNF/CNF | H* ≤ #terms | A | high | solid | core construction | 010,032
030 | Threshold-degree span schema | program toward H* vs deg_± via degree-restricted spans | A | med | solid | machinery | 021,015
031 | Fourier tail criterion | tail < 1 ⇒ deg_± ≤ d | B | low | solid | machinery | —
032 | Denominator orientation | 1-head denominators = one-signed affine forms | A | high | solid | machinery | 010
033 | Shared projection closure | Boolean combos through one t: H* ≤ Σ C_t | B | med | solid | corollary | 013
034 | Width ⇒ deg_± | width-w DNF/CNF ⇒ deg_± ≤ w | C | low | solid | feed for 030 | —
035 | Monotone antichain | H* ≤ min{#minterms,#maxterms} ≤ C(n,n/2) | A | med | solid | corollary | 029
036 | Monotone counting LB | W_mon(n)=Ω(C(n,n/2)/n²) — 035 near-tight | A | high | solid | corollary | 026,035
037 | Sparse support | H* ≤ 2·min support | B | med | solid | machinery | 013,011
038 | DNF/CNF volume | H* ≤ 2Σ2^{n−w_a} | B | low | solid | corollary | 037
039 | Junta UBs | H*=H*(f_ess); tables | B | low | solid | corollary | 028,025,009
040 | Certificate cover | H* ≤ 2·certvol | B | low | solid | packaging | 037
041 | PTF sparsity | H* ≤ ptfsp | A | high | solid | core machinery | 010,032
042 | Literal expansion | mixed DNF: H* ≤ min{Σ2^{|P_a|},Σ2^{|N_a|}} | B | med | solid | corollary | 041,028
043 | Decision tree | H* ≤ 2^{2d−1} for depth d | B | med | solid | corollary | 042
044 | Oriented certificate expansion | H* ≤ Σ min{2^{|P|},2^{|N|}} | B | med | solid | corollary | 041,042
045 | Fourier support cost | H* ≤ a_1 + Σ_{|S|≥2}|S| | A | high | solid | core machinery | 008,010,028
190 | Slice-rank-2 obstruction | cleared score = L₁Q₁+L₂Q₂; no such sign-rep ⇒ H*>H; Grassmann atlas program | A | high | solid (program part open) | machinery | 010
191 | Cube ceiling | slice relaxation collapses to deg_± when H ≥ (n+1)/2 | A | high | solid | limit theorem | 190
192 | Multiway tensor rank | k-block cap k(k^H−(k−1)^H); can't beat matrix screen | A | high | solid | limit theorem | 028,010
193 | Positive-secant blow-up | exact feasibility reformulation, tangent charts | B | med | solid | infrastructure | 010,032
194 | Signed-secant blow-up | 2^n signed ineqs, ≤4(n+1)+2 chart types | B | med | solid | preferred comp. target | 193
195 | Atomic-margin sparsification | H* ≤ C(n+1)(Λ/γ)² via approx. Carathéodory; κ_atom | A | high | solid | machinery | 010
196 | Fourier-tail knapsack | optimal 045-certificate by DP, verified | B | low | solid | algorithmic | 045
197 | Box-sum greedy | fractional-knapsack exact intervals for 194 | C | low | solid | helper | 194
02_sep/013 | Strict separation n=10 | deg_±(f₁₀)=2 < 3 ≤ H*; mixed antipodal rank 4 vs dominance rank 5 | S | high | solid | core-pillar | 006,010
```

### Folder 03 (046–073) + 04 (074–126)

```
046 | Affine parity exact | H*(parity on S)=|S|; π⊕ restriction witness | A | med | solid | core LB witness | 008,028
047 | Inner product | m ≤ H*(IP_m) ≤ 2^m−1 — WIDE OPEN | A | low | solid | benchmark | 046,006,041
048 | afs_± UB | H* ≤ afs_± (affine part 1 head + 1/monomial) | A | high | solid | core UB engine | 015,041,010
049 | Equality bounds | deg_±(EQ)=2; see 060 | B | low | solid | corollary | 007,048,060
050 | Intersection profiles | C(F) ≤ H*(F(Σx_iy_i)) ≤ Σ_{r≤C}C(m,r) | A | med | solid | machinery | 012,028,041
051 | Hamming-distance profiles | analogous for F(Δ) | B | med | solid | machinery | 012,048,050
052 | Directed-defect profiles | analogous for F(#{x_i>y_i}) | B | med | solid | machinery | 012,048,050
053 | Local-pattern schema | unified F(Σp(x_i,y_i)) | B | med | solid | machinery | 012,048
054 | 3-bit vote match | s_LTF=H*=deg_± on 3 bits (enumeration) | B | med | plausible (Python) | curiosity | 016,027
055 | EQ vote size | s_LTF(EQ_m)=2 | B | low | solid | machinery | 054
056 | EQ2 exact | H*(EQ_2)=2 (certificate) | C | med | plausible | subsumed by 060 | 015,011
057 | SUB2 exact | H*(SUB_2)=H*(NCON_2)=2 | B | med | plausible | corollary | 015,052
058 | Two-pair local counts | all 1-sign-change two-pair families exact ≤2 | B | med | plausible (enumeration) | corollary | 015,011
059 | Three-pair endpoints | INT_3,DISJ_3,SUB_3,NCON_3,EQ_3,NEQ_3 all =2 | B | med | plausible (certificates) | corollary | 015,050,052
060 | EQ exact | H*(EQ_m)=H*(NEQ_m)=2 all m; 1−(X−Y)² trick | S | high | solid | core-pillar | 015,011,028,055
061 | Affine level set | H*(1[L=0]) ≤ 2, exact split | A | high | solid | core UB engine | 015,011
062 | Affine slab | H*(1[α≤L≤β]) ≤ 2, exact split | A | high | solid | core UB engine | 015,011,061
063 | Affine statistic sign changes | f=G(L(x)) bounds via C | B | med | solid | machinery | 062,048
064 | Two-point support | s(f)≤2 ⇒ H*≤2 exact | B | med | solid | corollary | 061,011,028
065 | Affine-hull-clean supports | label class = cube ∩ own hull ⇒ ≤2 | B | med | solid | machinery | 061,011
066 | Positive run count | H* ≤ 2R₊ | B | med | solid | machinery | 013,037
067 | Sign-rank method limits | degree-based srank can't show H*≥3 for n≤13 | B | med | solid | negative/meta | 028
068 | Positive one-run | one block ⇒ slab ⇒ exact ≤2 | B | med | solid | corollary | 062,066
069 | Degree-tight squeeze | deg_±=C_t ⇒ exact | B | med | solid | proof template | 006,013
070 | Low afs exact | afs_±≤2 ⇒ exact | B | med | solid | corollary | 048,011
071 | Depth-2 trees | D(f)≤2 ⇒ H*≤2 exact | B | low | solid | corollary | 039,015
072 | Decision-tree hybrid | H* ≤ min{...} = O(v^d) | B | med | solid | machinery | 044,039,048
073 | DNF/CNF hybrid | combined min bound | B | med | solid | machinery | 037,044,048
074 | Cofactor sparse recursion | H* ≤ 2ptfsp(f_0)+ptfsp(f_1)+1 | B | med | solid | machinery | 041,048
075 | Affine-free cofactor recursion | pay only nonlinear+changed slopes | B | med | solid | machinery | 048,070
076 | LTF cofactor slope distance | LTF cofactors, t slope diffs ⇒ H*≤1+t | A | high | solid | machinery | 048,070,011
077 | σ_split invariant | H* ≤ 1+σ_split | B | med | solid | packaging | 076,028
078 | scafs_± | split afs invariant (superseded by 114) | B | med | solid | machinery | 048,028
079 | One-bit LTF branching | H*(G(z,T)) ≤ 1+|supp| | B | med | solid | corollary | 076
080 | One-bit sparse branching | refined | B | med | solid | machinery | 078
081 | Fresh-XOR degree | deg_±(z⊕f)=deg_±(f)+1 exactly | A | low-med | solid | core LB amplifier | 006,080
082 | One-bit gate trichotomy | deg_± under all 2-bit gates | B | med | solid | machinery | 081
083 | Parity-block amplifier | deg_±(π_k⊕T)=deg_±(T)+k | B | low-med | solid | machinery | 081
084 | Parity-block restriction LB | H* ≥ k+deg_±(T) certificate | B | med | solid | corollary | 083,006
085 | Calibrated threshold vote | margin/ε condition ⇒ H* ≤ s | A | high | solid | core concept | 010
086 | Endpoint vote UB | unconditional for endpoint features | A | high | solid | machinery | 085,032
087 | Non-XOR Shannon recursion | H*(G(z,T)) ≤ H*(T)+1, G ∉ {XOR,XNOR} | S | high | plausible (uncited strengthening of 028) | core-pillar | 010,028,032
088 | Literal decision lists | H* ≤ list length | A | high | solid | machinery | 087
089 | Endpoint decision lists | affine-threshold tests | B | med | solid | machinery | 085,086
090 | Calibrated decision lists | lists = strict votes | B | high | solid | machinery | 085
091 | LTF indicator obstruction | 1-atom error ≥ 1/4 vs indicator of x1∧(x2∨x3) | S | high | solid | core-pillar | 032
092 | Infimum = 1/4 | matching construction | B | high | solid | sharpness | 091
093 | ρ calibration invariant | H* ≤ Σρ(T_j) for strict votes; ρ ≤ eafs | A | high | solid | core-pillar | 085,048,041
094 | ρ decision lists | H* ≤ Σρ | B | med | solid | corollary | 090,093
095 | ρ ≥ deg_±/votes | Σρ ≥ deg_±(f) | B | high | solid | enables 107 | 093,006
096 | Subcube ρ | ρ(cylinder) ≤ min{2^|P|,2^|N|} | B | med | solid | machinery | 044
097 | ρ invariances | routine | B | low | solid | hygiene | 010,028
098 | Subcube votes | H* ≤ Σκ | B | med | solid | machinery | 093,096
099 | ctc | cylinder-threshold cost; H* ≤ ctc | B | med | solid | stepping stone | 098
100–102 | ctc satellites | invariances/subsumptions | C | low | solid | bookkeeping | 099
103 | actc | affine block + signed cylinder vote; H* ≤ actc ≤ ctc | A | high | solid | central UB invariant | 048,096,093
104 | actc hierarchy | actc ≤ afs_± ≤ ptfsp | B | med | solid | machinery | 103,048
105 | Halfspace-intersection LB | H*(T_n∧U_n) ≥ cn (Sherstov import) | S | low | solid | hard benchmark | 006
106 | Vote/DL separation | s_LTF≤2, DL≤2, yet H*≥cn | A | high | solid | core negative | 105
107 | ρ linear worst case | H*=1 LTFs with ρ ≥ cn | A | high | solid | core negative | 105,093,095
108 | actc invariances | routine | C | low | solid | hygiene | 103
109 | Low actc exact | actc≤2 ⇒ exact | B | med | solid | corollary | 103,011
110 | actc sandwich | organizing statement | B | med | solid | corollary | 006,103,105
111 | actc cofactor interpolation | pay only changed coefficients | B | med | solid | machinery | 103
112 | sactc | best split cost | B | med | solid | machinery | 111
113–116 | sactc satellites | subsumptions, first levels | C–B | low | solid | routine | 112
117 | Pure-cylinder perturbation | A+c·C_{P,N} ⇒ actc≤2 exact | B | med | solid | corollary | 103,109
118 | One-bit ac branching | gate bounds via sactc | B | med | solid | machinery | 112
119 | Fresh-XOR ac bound | bracket for z⊕T | B | med | solid | machinery | 118,081
120 | actc Shannon fallback | coarse recursion | B | med | solid | loose | 111,112
121–125 | lgactc/xactc layer | lifted literal gating costs — GOES NOWHERE (126 bypasses it) | C–B | low-med | solid | dead-end | 118
126 | Endpoint fresh-XOR exact | H*(z⊕OR_S)=H*(z⊕AND_S)=2 via slabs | A | high | solid | exactness anchor | 081,062,028
```

### Folder 05 (127–179) + 06 (180–189)

```
127–129 | Fresh-XOR/gate classification for endpoints & LTFs | H*(G(z,T)) ∈ {0,1,2} table | B | low | solid | corollaries | 062,081,011
130–131 | Old fresh-XOR sign-change bounds | superseded by 139 | B–C | low | solid | dead-end | 063,013
132 | Positive-projection gate bound | slice sign changes | B | low | solid | machinery | 013,011
133–134 | Internal slab gates (partial) | superseded by 137 | B–C | low | solid | dead-end | 062,132
135 | Quadratic span (t,z) | deg-2 sign poly ⇒ H*≤2 (det −9, re-verified) | A | med | solid | machinery | 015
136 | Cubic span (t,z) | ⇒ H*≤3 (det −480, re-verified) | A | med | solid | machinery | 015
137 | Internal slab exact gate table | complete: 0/1/3(XOR)/2 | A | med | solid | tight result | 135,136,081,062
138 | Degree span (t,z) | deg-d ⇒ H*≤d uniformly in m — folder-05 engine | A | med | solid | core machinery | 015
139 | Fresh-XOR ≤ C+1 | kills 130/131; exact when deg-tight | A | med | solid | machinery | 138,081
140–144 | Gate sandwiches | d ≤ H*(G(z,T)) ≤ C tables; C₊ fallback | B–C | low | solid | corollaries | 138,082
141 | Degree-tight gate classification | exact 0/1/C+1/C when deg_±=C | A | med | solid | tight result | 139,140
142 | Symmetric-feature gates | exact table | B | low | solid | corollary | 141,012
145–164 | Multi-slice/boundary chain | shared-statistic sandwiches; payoffs only in single-active-slice cases (155,156,158,160) | B–C | low-med | solid | mostly bookkeeping | 013,147,151,158
158 | Shared-statistic sandwich | workhorse two-sided bound | A | med | solid | machinery | 147,151,028
165 | Positive grid sandwich | pay per raw level | A | med | solid | machinery | 013
166–169 | Grid satellites | degree versions, pgc₊ | C–B | low | solid | corollaries/dead-end | 165
170 | Lex multigrid | H* ≤ L_lex over product grids | A | med | solid | machinery | 013,165
171–175 | Multigrid satellites | Hamming profiles, runs, mgc₊/mhc, projection collapse | B–C | low | solid | corollaries/dead-end | 170,012
176 | Multigrid separation on parity | mgc₊(XOR_n) ~ 2^{n+1}/3 vs H*=n: exponentially loose | A | med | solid | honest negative | 012,170
177 | Two-block grid points | H* ≤ 2 | B | med | solid | machinery | 061
178 | Two-block grid lines | H* = δ ∈ {0,1,2} | B | med | solid | machinery | 061,177
179 | Two-block grid strips | all affine strips ≤ 2 heads — delimits where separations can live | B | med | solid | machinery | 062,178
180 | Separation n=56 | tope-cycle srank ≥7 vs 2-head ≤6, by hand | S | high | solid | core-pillar (first) | 010,028
181 | Compact n=43 | 35-row compression, script-certified | A | med | solid | superseded | 180
182 | Natural separation n=12 | Δ≥3 on 6+6; partition-srank ≤6 lemma | S | high | solid | core-pillar | 010,180
183 | Exact classification n≤4 | H*=deg_± exhaustively; n_sep ≥ 5 | S | high | solid | core-pillar | 006,011,032
184 | n=11 quadratic | reuses 181's matrix + 182's lemma | A | med | solid | superseded | 181,182
185 | n=9 antipodal slices | cross-block rank 5 vs ≤4; hand LA, verifier passes | S | high | solid | core-pillar | 010,006
186 | 5-bit deg-4 exactness | deg_±=4 ⇒ H*=4 (4.5M tables, exact-integer archive) | S | high | solid | core-pillar | 006,032
187 | 5-bit deg-2 exactness | deg_±=2 ⇒ H*=2 (Lemma 1 cites EXTERNAL repo) | S | high | plausible-to-solid | core-pillar | 006,010,032
189 | n=8 EXACT separation | Δ≥2 on 4+4: deg_±=2 < H*=3 exactly; new spectral LB + integer 3-head certificate; verifiers re-run, pass | S | high | solid | HEADLINE | 010,032,183
```
