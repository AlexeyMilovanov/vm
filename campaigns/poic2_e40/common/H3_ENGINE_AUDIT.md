# Engineering audit: unrestricted interior H=3 search for `g19`

Date: 2026-08-26

Scope: inspect the existing all-vertex H3 locators and the `cpr2` cutting-plane
engine, then specify the exact adaptation needed for the 19-bit pure-C
restriction.  No experiment longer than three minutes was run.  The main
search algorithm was not changed; the requested validated warm-resume entry
point was added after the audit.

## Verdict

`notes/agents/purec19-h3-search-2026-08-26/purec19_h3_search.py` has the right
high-level model:

* it reconstructs the exact `g19` labels from `purec_shatter7_exact.json`;
* it searches all 57 within-coordinate pole slopes, rather than a block/profile
  ansatz;
* its four cells `ppp`, `ppm`, `pmm`, `mmm` cover the eight ordered pole
  orientations modulo permutation of the three heads;
* for fixed poles it eliminates the 61 linear numerator/readout parameters by
  a hinge LP;
* it evaluates every candidate selected for a full check on all `2^19`
  vertices in chunks.

That is the correct architecture for a serious *positive* H3 search.  The
current file is a useful scout, but it is not yet a restartable production
engine.  The most important repairs before a multi-hour run are:

1. implement a genuine, atomic resume checkpoint containing the whole
   population, RNG state, current active set and generation (the present
   `checkpoint_*.npz` is only a best-candidate snapshot and collides across
   seeds);
2. use max-margin as a secondary population objective once active hinge is
   zero, otherwise DE cannot replace zero-loss individuals and can stagnate;
3. select the worst **non-active** full-cube rows and retain deterministic
   historical/support rows when pruning; the current top-576 filter can return
   only already-active rows and the pruning step rebuilds new random anchors;
4. add the separate rational exactifier/standard-library verifier before any
   hit is called a certificate;
5. remove or repair the selector warm start: the referenced signrank-8 file
   has 128 `B` rows plus **eight** `Q` rows, so line 197 constructs a `(3,20)`
   array and the `(3,19)` test at line 198 always rejects it.

The finite log-slope box remains a search heuristic, not a completeness
claim.  A no-hit has no theorem status.

## 1. Files and APIs actually present

### 1.1 `cpr2` active-set locator

The reusable baseline is:

* `code/gap25_h3.py`
* `code/gap25_common.py`
* `results/gap25_h3_cpr2.txt`
* `results/gap25_h3_cpr2_cert.npz`
* the H3 post-check in `notes/verify_gap25_session.py`

`gap25_common.hinge_heads(X, f, orients, W, idx=None, ret=False)` builds

```text
1,  1/D_h,  x_1/D_h, ..., x_n/D_h       (h=1,2,3)
```

and calls `_hinge_lp`.  With `ret=True` it returns `(hinge_sum, theta)`.
`gap25_h3.cell_search` searches `log W` by differential evolution, fits the
numerators on a working vertex set, occasionally solves the full LP, and adds
the worst rows.  It found the archived `cpr2` `+++` certificate after about
1838 seconds in the dedicated-cell run.

The saved `cpr2` NPZ contains only `orients` and `logW`.  The verifier
rationalizes `W`, refits `theta` on all 4096 vertices, rationalizes that refit,
and checks every sign with `Fraction`.  This post-refit detail is essential;
the NPZ itself is not an independently checkable exact certificate.

What transfers to `g19`: log-pole parametrization, head-orientation reduction,
fixed-pole numerator LP, DE/Nelder-Mead outer search, source-shaped starts and
cutting planes.

What does **not** transfer: `gap25_h3.full_margins` calls `hinge_heads` on the
entire cube at every audit.  At `2^19` this would create 524288 slack variables
and a dense-in-practice 524288-by-61 feature block.  `g19` must fit on the
active rows and merely *evaluate that fitted theta* in a chunked full scan.

### 1.2 The named `E284244` engine is absent

As of this audit, no file named
`search_e284244_h3_nonsym.py` exists anywhere under `/home/lesha`.  The file

```text
notes/agents/e40-single-case-2026-08-26/search_e283156_h3_nonsym.py
```

imports it at line 5, so that wrapper is currently not executable.  The
wrapper reveals the intended API (`ROWS`, `Y`, `W1`, `W2`,
`exactify(logslopes, ori)`, `main()`), but not the implementation.  The nearest
complete all-512 implementation is

```text
notes/agents/e40-single-case-2026-08-26/hinge_de_e283156_h3.py
```

It supplies the useful exactification pattern: absorb the free bias into head
0, rationalize poles/numerators, and verify all vertices exactly.  It is a
full-LP engine and therefore cannot simply be pointed at `g19`.

### 1.3 Current `g19` engine

The new implementation is:

```text
notes/agents/purec19-h3-search-2026-08-26/purec19_h3_search.py
```

Important callable boundaries are:

```text
load_instance(source)
initial_active(x, y, rng, gordan_file)
feature_matrix(xa, orients, w)
hinge_lp(cols, y)
max_margin_lp(cols, y)
fit_active(x, y, active, orients, logw, robust=False)
scan_full(x, y, orients, w, theta, chunk=32768, keep=768)
warm_population(...)
seed_from_checkpoint(...)
search_cell(...)
```

These are appropriate module seams for a repaired version; no dependency on
the `gap25` instance factory is needed.

## 2. Exact target and complete interior parametrization

The local variables are ordered as the twelve selector bits followed by the
seven `Y` bits:

```text
(0,3,8,18,24,25,26,30,42,48,71,84), y_0,...,y_6.
```

For each source term `k`, the loader computes

```text
a_k(x) = x . (ax[SELECTORS,k], ay[:,k])
b_k(x) = 1 + x . (bx[SELECTORS,k], by[:,k])
2P(x)  = 2 sum_k a_k(x)b_k(x) + b_0(x).
```

This agrees with both independent exact `g19` verifiers.  A direct diagnostic
of the current loader gave:

```text
vertices                 524288
positive labels          162369
target-label SHA-256     6e799ddf35c2a33ec8feba8c4454f05b337fe0b2d893a8a5adf7fdabf01e1c71
range a_k                [-667253, 505343]
range b_k                [1, 12156097]
range 2P                 [-9093946595841, 6513549962071]
minimum |2P|             1
```

Thus signed `int64` arithmetic is safe for this particular restriction.  The
loader should nevertheless record both the source-file SHA and the derived
label SHA in every run/certificate.

For one head, every finite legal one-signed positive affine denominator can be
scaled into exactly one of

```text
D_+(x) = 1 + sum_j w_j x_j,
D_-(x) = 1 + sum_j w_j (1-x_j),          w_j >= 0.
```

The search uses `w_j=exp(p_j)>0`.  Zero slopes do not create a logical gap for
a positive search: any strict finite-cube certificate with a zero slope
survives a sufficiently small positive perturbation.  The four orientation
multisets

```text
(+++), (++-), (+--), (---)
```

are exhaustive because heads may be permuted.  Within each cell, all 57
slopes are independent; there is no profile or block-symmetry restriction.

For fixed poles, define

```text
Phi_D(x) = [1; (1,x)/D_1(x); (1,x)/D_2(x); (1,x)/D_3(x)].
```

Then strict H3 feasibility is equivalent to the existence of `theta` with
`y(x) Phi_D(x).theta >= 1` on every vertex.  The leading constant is
absorbable: add `c D_1` to the first affine numerator.  It makes the numerical
feature count 61 although the span has a redundancy and a final certificate
still has exactly three heads.

## 3. Audit of the current `purec19_h3_search.py`

### Correct and worth keeping

* Lines 33-49 construct every label exactly and retain `X` as a compact
  `uint8` matrix.
* Lines 52-79 seed extremes, complete one-hot-Y fibres, both label classes and
  the four exceptional exact Gordan supports.
* Lines 86-140 implement the correct fixed-pole LP.  The L1-normalized
  max-margin refit is a good hit-stability check.
* Lines 143-183 scan the complete cube in 32768-row chunks; no sampled fit is
  mistaken for a full hit.
* Lines 416-424 expose the four canonical orientation names.
* A saved hit is explicitly called `NUMERICAL_HIT` and says that exactification
  is required.

### P0: repair before long runs

#### Checkpoint supports only a warm restart

Lines 227-241 save only the current best `logw`, `theta`, `active` and four
metrics.  They omit:

* the whole DE population and its current objective values;
* generation/phase and `last_scan`;
* NumPy bit-generator state;
* immutable anchors and cut history;
* configuration, code hash and source-file hash.

An audit patch added `--resume PATH`.  It validates the checkpoint orientation
and target SHA, prepends the saved pole triple plus Gaussian perturbations at
scales `.03,.1,.3,.7,1.3`, and unions the saved active rows with fresh anchors
up to `max_active`.  A short smoke test confirmed that path.

This remains a warm restart rather than an exact continuation: it does not
restore the population, objectives, generation, phase, cut ages or RNG state.
In addition, the checkpoint filename is `checkpoint_{cell}.npz`, without the
seed, so two seeds in the same output directory overwrite each other.
`np.savez_compressed` writes directly to the final filename and is not
crash-atomic.

#### Zero-hinge DE stagnation

At lines 337-339 a trial replaces its parent only when its active hinge is
strictly smaller.  Once several candidates have active hinge zero, they are
all tied and none can replace another even if it has a much larger active
margin or a much better full-cube scan.  The robust max-margin LP is used only
for the one selected individual at lines 343-347 and its margin is not fed
back into DE selection.

Use a lexicographic per-candidate objective:

```text
(active_hinge, -active_L1_margin)
```

and, after hinge reaches zero, optimize `-margin` directly.  Also full-scan at
least the best candidate from two or three diversity clusters, not always only
`argmin(values)`.

#### Cutting planes can stall or cycle

`scan_full` returns the globally worst rows, including active rows.  Lines
372-375 filter active IDs only after retaining 576 rows.  If those 576 are
already active, no new cut is added even when many non-active vertices violate
the unit margin.  The scan should receive an active bitmap and maintain a
separate top-K heap for **non-active** rows.

When `max_active` is exceeded, lines 378-381 call `initial_active` again with
the already-advanced RNG.  This creates a new random anchor set, discards old
anchors/history, and retains at most the currently returned 576 bad rows even
though the nominal cap is 6000.  This invites recurring cuts.

Build `anchors` once and keep it immutable.  A deterministic capped working
set should be the union of:

1. immutable anchors;
2. active rows with nonzero LP slack or significant HiGHS dual weight;
3. the most recent novel worst rows;
4. a bounded reservoir of older cuts, stratified by label and
   `(selector Hamming weight, Y Hamming weight)`.

Never discard a row merely because a fresh call generated different anchors.

#### No exact hit pipeline

The engine stops at a float NPZ.  Before reporting `H*(g19)<=3`, a separate
tool must rationalize/refit and check all 524288 vertices in exact arithmetic.
The expected API is specified in section 5 below.

#### Dead/mismatched selector warm start

Lines 192-201 load `purec_signrank8_h3_selector_exact.json`.  Its `B` array has
128 rows and its `Q` array has eight rows.  Consequently

```text
vstack([B[SELECTORS], Q]).T.shape == (3,20),
```

so the `(3,19)` guard always fails.  Moreover it is a signrank-8 selector
certificate, not automatically a certificate for this seven-Y restriction.
Delete this silent branch or introduce an explicit, audited seven-coordinate
map and log whether the warm start was accepted.

### P1: robustness and operations

* `np.clip` occurs inside `pole_weights` (line 83) as well as on trials.  Values
  outside the box lie on flat objective plateaus.  Keep population coordinates
  inside explicit bounds by reflection/projection and use several declared
  windows, for example `[-12,8]`, `[-18,16]`, and `[-25,25]`.  A no-hit in one
  window says nothing about poles outside it.
* The upper bound 16 is only barely above the largest unscaled source-pool
  slope (`log 4.56e6 ~= 15.33`); the `source*10` start is clipped and partially
  flattened.
* Lines 448-449 set BLAS thread variables after NumPy/SciPy have already been
  imported.  Set them in the launcher environment before Python starts, or use
  `threadpoolctl`.
* The wall clock is checked around, not inside, LP/full-scan calls.  A 12-second
  smoke run ended after 16 seconds.  This is harmless for hour runs but job
  launchers need grace time and signal-triggered checkpointing.
* Expected completed `NO_HIT` currently returns exit code 1.  For schedulers,
  return zero for a completed numerical miss and reserve nonzero codes for
  malformed state/runtime errors.
* Hard-coded absolute paths at lines 290-291 should be derived from the
  repository root or exposed as CLI arguments.
* Summary and hit writes should also use temporary files plus `os.replace`.

## 4. Recommended search loop

Use one independent process per `(cell,seed)`.  Do not share mutable state
between cells.

```text
instance = load exact labels; validate source SHA and target SHA
anchors  = deterministic_initial_active(seed)
state    = new population or validated --resume state

while budget remains:
    for each population member:
        hinge, theta, active_margin = solve active LP
        objective = (hinge, -active_margin if hinge~0 else 0)
    perform bounded DE mutation/crossover

    every K generations:
        choose 2-3 best/diverse pole triples
        refit theta on current active set
        chunk-scan all 524288 vertices
        collect worst NON-ACTIVE rows, balanced/stratified
        if full minimum margin is safely positive:
            save numerical hit and invoke exactifier
        update/prune active set deterministically
        recompute all population objectives
        atomically checkpoint complete state

    periodically polish the best member with bounded NM/Powell
```

Recommended initial active size is roughly 2500-5000.  The present smoke run
started with 2520 rows, which is reasonable.  At a cap near 6000-12000, a
hinge LP remains manageable; the full cube should never be passed to
`linprog`.  Request at least 4-8 times as many novel candidates from the full
scan as the number ultimately added, because active filtering and diversity
deduplication remove many rows.

When multiple active candidates have zero hinge, max-margin is not optional:
it supplies the gradient-free outer ranking needed to keep DE moving.

## 5. Checkpoint and exact-certificate contracts

### 5.1 Restartable checkpoint

Use a collision-free directory such as:

```text
runs/<target_sha[:12]>/<cell>/seed_<seed>/
```

Write `state.npz.tmp` and `meta.json.tmp`, `fsync` if practical, then
`os.replace`.  Suggested schema:

```text
state.npz
  population          float64 [pop,57]
  objectives          float64 [pop,2]
  active              int64   [m]
  immutable_anchors   int64   [a]
  cut_age             int32   [m]          # or equivalent history metadata
  best_logw            float64 [57]
  best_theta           float64 [61]
  best_full_metrics    numeric scalar fields

meta.json
  schema_version
  target_sha256
  source_file_sha256
  selectors_and_variable_order
  cell, seed, generation, phase, elapsed_seconds
  numpy_bit_generator_state
  complete CLI/config dictionary
  engine git/blob hash and scipy/numpy versions
```

On resume, reject mismatched target/source/cell/dimensions.  Recompute all
active objectives and one full scan rather than trusting saved floating-point
values across SciPy versions.  Install `SIGTERM`/`SIGINT` handlers that request
a checkpoint at the next safe boundary.

### 5.2 Numerical hit

The float hit NPZ should contain `orients`, normalized `w`, `theta`, exact
variable order, target/source hashes, full minimum margin and its vertex ID.
Absorb the readout bias before emitting three heads:

```text
A_1 <- A_1 + c D_1,     c <- 0.
```

For a negative head,

```text
D(x) = 1 + sum_j w_j(1-x_j)
     = (1+sum_j w_j) - sum_j w_j x_j.
```

### 5.3 Rational exactifier

Implement a separate command, for example:

```text
python3 exactify_purec19_h3.py NUMERICAL_HIT_....npz --out certificate.json
```

For increasing rational denominator limits:

1. rationalize `w` and preserve its legal orientation;
2. refit the numerators on the active/cutting set with those fixed rational
   poles (float HiGHS is acceptable only as a locator);
3. rationalize the three affine numerators after bias absorption;
4. verify exact denominator positivity and

   ```text
   y(x) [A_1 D_2 D_3 + A_2 D_1 D_3 + A_3 D_1 D_2] > 0
   ```

   for every one of the 524288 vertices using integers/Fractions;
5. record the exact minimum cleared margin and argmin vertex.

The final JSON should contain only rational strings and enough target metadata
for a standalone verifier.  The standalone verifier should use the standard
library, regenerate labels from `purec_shatter7_exact.json`, check all vertices
and reject zero margins.  A float `min_margin > 1e-9` is only a trigger for
this process, never the result.

## 6. Concrete launch plan after repairs

First run four equal screening shards, preferably with several independent
seeds and explicit pre-Python thread limits:

```text
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python3 purec19_h3_search.py --cell ppp --seed 0 ...
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python3 purec19_h3_search.py --cell ppm --seed 0 ...
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python3 purec19_h3_search.py --cell pmm --seed 0 ...
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python3 purec19_h3_search.py --cell mmm --seed 0 ...
```

Do not eliminate a cell because one short seed scores poorly.  Rank shards by
full wrong count, full minimum margin and full hinge, then continue the best
states with `--resume` while preserving at least one long run in every cell.
Use multiple log-slope windows/scales.  Any numerical hit goes immediately to
the independent exactifier; numerical misses remain evidence only.

## 7. Short diagnostics performed

Only read-only or short smoke diagnostics were run:

* exact loader range/balance/SHA check (under five seconds);
* one 12-second `ppp` smoke run with population 4, which performed complete
  cube scans and ended after 16 seconds because the final LP/scan is
  non-preemptive;
* a 0.1-second-budget warm-resume smoke on that temporary checkpoint.

The smoke run began with 2520 active rows and produced no hit (as expected for
such a run).  Its purpose was solely to validate the execution path and expose
the wall-budget/checkpoint behavior.  Resume restored the saved pole centre,
added all five requested perturbation scales, and merged to 4865 active rows.
None of these diagnostics is search evidence.
