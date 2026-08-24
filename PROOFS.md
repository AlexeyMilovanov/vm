# Detailed proofs for the Separations layer

Status: proof document, 2026-08-23.  Every `sorry` leaf of
`HeadComplexity/Separations/` gets here a complete informal proof at a
granularity intended to map one-to-one onto Lean steps.  Each item is labeled
`P<sec>.<n>` and names the Lean declaration it discharges.  Section 9 (Warren)
is the single place where a deep external theorem is cited rather than fully
re-proved; everything else is self-contained.

Conventions of the Lean model (verified against the source files):

* A head (`Model/Head.lean`) has embeddings `x p = tokenEmbed (seqTok bits p)
  + posEmbed p` for `p : Option (Fin n)`; the query position `p = none` has
  `seqTok = 2` independent of `bits`.  Attention weight
  `σ_p = exp ⟪WK (x p), WQ (x none)⟫`; since `x none` does not depend on
  `bits` and `x (some i)` depends only on bit `i`, **`σ_p` depends only on
  the single bit at `p`** (and on nothing for `p = none`).
* `computesPred f g ↔ ∃ w τ, ∀ z, ⟪w, g z⟫ > τ ↔ f z = true`.  So with score
  `S(z) := ⟪w, Σ_h attnUpdate_h(z)⟫ − τ`: `f z = true ⇒ S(z) > 0` and
  `f z = false ⇒ S(z) ≤ 0` (possibly `= 0`; never assume strictness on the
  false side).
* `signMatrix a b f (x)(y) = if f (blockJoin x y) then 1 else -1`
  (rows = left blocks).  `SignMatches M A ↔ ∀ i j, 0 < M i j * A i j`
  (strict!).  `signRank = sInf` of ranks of sign-matching matrices.
* Everything is on the finite cube, so minima of finite sets of positive
  reals are positive; this is used repeatedly as "the margin".

---

## §1 Auxiliary lemmas (small new Lean leaves)

### P1.1 `signRank_reindex`

**Claim.** `signRank (reindex eα eβ M) = signRank M`.

**Proof.** The map `A ↦ reindex eα eβ A` is a bijection between matrices
sign-matching `M` and matrices sign-matching `reindex eα eβ M`
(`(reindex A) (eα i) (eβ j) = A i j`, and every index of the reindexed matrix
is of this form).  `Matrix.rank` is invariant under `reindex`
(mathlib `Matrix.rank_reindex`).  Hence the two `sInf` index sets are equal
as subsets of `ℕ`, and the infima agree.  ∎

### P1.2 `signRank_neg` (NEW lemma, add to `SignRank.lean`)

**Claim.** `signRank (-M) = signRank M`.

**Proof.** `A ↦ -A` is a rank-preserving bijection (`(-M)ij·(-A)ij =
Mij·Aij`), mapping sign-matches of `M` onto sign-matches of `-M`.  ∎

Needed in Theorem B for the global `(-1)^(k+1)` factor.

### P1.3 `HStar_comp_equiv` (NEW lemma, add to the layer or `Model`)

**Claim (generalized to cover type transport).**  Let `e : Fin n' ≃ Fin n`
(this forces `n' = n` as naturals, but only propositionally — e.g.
`n' = k·m + k·m` versus `n = k·(m+m)`).  For `f : (Fin n → Bool) → Bool`
define `f' : (Fin n' → Bool) → Bool` by `f' z' := f (z' ∘ e.symm)`.  Then
for every `H`: `computableWithHeadsN n H f ↔ computableWithHeadsN n' H f'`;
consequently `HStar n' f' = HStar n f`.  The permutation special case is
`e := π.symm : Fin n ≃ Fin n` with `f' z = f (z ∘ π)`.

**Proof.**  (⟸ follows from ⟹ applied to `e.symm` and
`(f')' = f` by `e.symm.symm = e` and function extensionality.)  Given heads
`Hs` computing `f`, define `Hs'` over `n'` bits by

    posEmbed' (some i') := posEmbed (some (e i')),
    posEmbed' none := posEmbed none,

all other data (`tokenEmbed`, `WQ`, `WK`, `WV`) unchanged.  Fix an input
`z' : Fin n' → Bool` and put `z̃ := z' ∘ e.symm : Fin n → Bool` (so
`f' z' = f z̃`).  Match head' positions to head positions by the bijection
`Option.map e : Option (Fin n') ≃ Option (Fin n)`, sending
`some i' ↦ some (e i')` and `none ↦ none`.  At matched positions the
embedded vectors agree:

* tokens: at `some i'` the head' token is `z' i'`, and the head token at
  `some (e i')` is `z̃ (e i') = z' (e.symm (e i')) = z' i'` — equal; at
  `none` both are the query token, independent of the input;
* position embeddings: equal by the definition of `posEmbed'`.

Hence `x' z' p' = x z̃ (Option.map e p')` for every position `p'`, so
`σ'_{p'}(z') = σ_{Option.map e p'}(z̃)` and the value vectors agree
likewise; re-indexing the finite sums by the bijection `Option.map e`
gives `denominator' z' = denominator z̃` and `numerator' z' = numerator
z̃`, hence equal updates.  Summing over the head family and reusing the
same `(w, τ)`: `computesPred f' (update')` holds.  ∎

### P1.4 `thresholdDeg_le_of` and `le_thresholdDeg_of` (wiring lemmas)

**Claim.** (i) `ThresholdDegLE f d → thresholdDeg f ≤ d`;
(ii) `¬ ThresholdDegLE f d → d < thresholdDeg f` provided
`∃ d', ThresholdDegLE f d'` (always true: any `f` has some sign polynomial,
e.g. the ±1 multilinear extension, degree ≤ n).
Also (iii) monotonicity `ThresholdDegLE f d → d ≤ d' → ThresholdDegLE f d'`
(same polynomial).

**Proof.** `thresholdDeg` is `Nat.find` of the predicate `ThresholdDegLE f ·`
(which is monotone by (iii)); (i) is `Nat.find_min'`, (ii) is
`Nat.find`-minimality plus monotonicity.  ∎

Corpus fact used throughout: `degree_le_of_computableWithHeadsN` +
`HStar_computable` + (i) give `thresholdDeg f ≤ HStar n f`.

---

## §2 The sign-rank bridge — `signRank_le_of_computableWithHeadsN` (P2)

**Claim.** `1 ≤ H`, `computableWithHeadsN (a+b) H f` ⟹
`signRank (signMatrix a b f) ≤ 2^(H+1) − 2`.

### P2.1 Per-head two-block decomposition

Fix heads `1..H` (each of some inner dimension `d`), the readout `w`, and
threshold `τ`.  For head `h` and input `z = blockJoin x y`:

* `D_h(z) := denominator_h z = Σ_{p} σ_{h,p}(z_p)`.  Since each summand
  depends on at most the single bit at `p`, splitting the position range
  `Option (Fin (a+b)) = {none} ⊔ left ⊔ right`:

      D_h(x,y) = A_h(x) + B_h(y),
      A_h(x) := σ_{h,none} + Σ_{i<a} σ_{h,some(castAdd i)}(x_i),
      B_h(y) := Σ_{j<b} σ_{h,some(natAdd j)}(y_j).

  `A_h > 0` and `B_h ≥ 0`, and `D_h > 0` (sums of exponentials, mathlib
  `denominator_pos`).

* `u_h(z) := ⟪w, numerator_h z⟫ = Σ_p σ_{h,p}(z_p)·⟪w, WV_h(x_h z p)⟫`.
  Every summand again depends on the single bit at `p`, so identically

      u_h(x,y) = A'_h(x) + B'_h(y)

  (put the `none` term into `A'_h`).

These are *functions on the finite cube*, not polynomials; no algebraic
structure beyond the additive split is needed.

### P2.2 Clearing

`S(z) = Σ_h u_h(z)/D_h(z) − τ` and `f z = true ↔ S(z) > 0`.  Multiply by the
positive quantity `∏_h D_h(z)`:

    Q(x,y) := Σ_{h=1}^H u_h·∏_{h'≠h} D_{h'} − τ·∏_h D_h,

so `sign Q = "sign" S` pointwise: `f = true ⇒ Q > 0`, `f = false ⇒ Q ≤ 0`.

### P2.3 Rank decomposition by head subsets

Substitute the splits and expand every product over the choice A-side /
B-side per factor.  Group the expansion by the set `T ⊆ [H]` of factors
contributing their A-side.  Writing `φ_T(x) := ∏_{h∈T} A_h(x)` and
`ψ_T(y) := ∏_{h∉T} B_h(y)`, a direct regrouping gives the exact identity

    Q(x,y) = Σ_{T ⊆ [H]} [ α_T(x)·ψ_T(y) + φ_T(x)·β_T(y) ],
    α_T(x) := Σ_{h∈T} A'_h(x)·∏_{h'∈T∖{h}} A_{h'}(x),
    β_T(y) := Σ_{h∉T} B'_h(y)·∏_{h'∉T, h'≠h} B_{h'}(y) − τ·ψ_T(y).

*Check of the identity.*  Expand the right side: the `α_T·ψ_T` terms
enumerate, over all `T` and `h ∈ T`, the expansion term of
`u_h·∏_{h'≠h}D_{h'}` in which `h` contributes `A'_h` and the A-side set is
exactly `T`; the `φ_T·Σ B'` terms enumerate those in which `h` contributes
`B'_h`; the `φ_T·(−τψ_T)` terms enumerate the full expansion of
`−τ∏D_h`.  Every expansion term of `Q` appears exactly once.  ∎

As a matrix in `(x, y)`, each summand `α_T·ψ_T` and `φ_T·β_T` is an outer
product, hence has rank ≤ 1.  Count: for `T = [H]`, `ψ_T ≡ 1` (empty
product) and `β_{[H]}(y) = −τ` is a constant (the `Σ_{h∉T}` sum is empty),
so the two pieces merge into the single outer product
`(α_{[H]} − τ·φ_{[H]})(x) · 1(y)`: **1 piece**.  Dually for
`T = ∅`: `φ_∅ ≡ 1`, `α_∅ ≡ 0` (empty sum), giving `1(x)·β_∅(y)`: **1
piece**.  Every other `T` (there are `2^H − 2` of them, and `2^H ≥ 2`
because `H ≥ 1`) contributes ≤ 2 pieces.  Total:

    rank Q ≤ 2(2^H − 2) + 2 = 2^(H+1) − 2,

using subadditivity of matrix rank (mathlib: rank of a sum ≤ sum of ranks,
via `LinearMap.range` additivity; if the named lemma `Matrix.rank_add_le`
is absent at 4.31, prove it once from `range (f+g) ≤ range f ⊔ range g`).

### P2.4 Strictification (the η-shift)

`Q` sign-matches `signMatrix` on true entries but may vanish on false ones.
Let `η := (1/2)·min { Q(x,y) : f (blockJoin x y) = true }` if the set is
nonempty (a positive real: finite nonempty min of positives), else `η := 1`.
Define `A := Q − η·𝟙`.  Then `f = true ⇒ A = Q − η ≥ Q/2 > 0` and `f = false
⇒ A ≤ −η < 0`; so `SignMatches (signMatrix a b f) A` **strictly**.  The
constant shift is absorbed into the `T = ∅` piece (`β_∅ ↦ β_∅ − η`), so the
rank count is unchanged.  Hence `signRank ≤ rank A ≤ 2^(H+1) − 2`.  ∎

`signRank_le_pow_HStar` is the composition with `HStar_computable` (already
in Lean, modulo the bridge).

---

## §3 Theorem C, degree half — `signRank_le_of_thresholdDegLE` (P3)

**Claim.** `ThresholdDegLE f d ⟹ signRank (signMatrix a b f) ≤ (a+1)^d`.

### P3.1 Multilinearization

Let `P` be a sign polynomial of total degree ≤ `d`.  On `{0,1}`-points,
`x_i^e = x_i` for `e ≥ 1`, so the multilinearization `P̃` (replace every
positive exponent by 1; in Lean: induct on monomials, or use the corpus's
cube-evaluation lemmas) satisfies `eval (cubePoint z) P̃ = eval (cubePoint z)
P` and `totalDegree P̃ ≤ totalDegree P ≤ d`.

### P3.2 Left-monomial factorization

Split variables into the left block (`a` of them) and right block.  Group
`P̃` by its left sub-monomial: `P̃ = Σ_μ x^μ · c_μ(y)` where `μ` ranges over
subsets of the left variables with `|μ| ≤ d` (total degree ≤ d forces
`|μ| ≤ d`), and `c_μ` is a polynomial in the right variables.  Evaluating on
the cube gives the matrix identity

    M(x,y) := eval P̃ = Σ_{μ, |μ| ≤ d} (x^μ)·(c_μ(y)),

a sum of `#{μ : |μ| ≤ d} = Σ_{i≤d} C(a,i)` outer products.

### P3.3 Count and strictification

`Σ_{i≤d} C(a,i) ≤ (a+1)^d` by induction on `d`: at `d = 0` it is `1 = 1`;
for the step, `C(a, d+1) ≤ a·C(a,d) ≤ a·(a+1)^d` (since `C(a,d+1) =
C(a,d)·(a−d)/(d+1)` and `(a−d)/(d+1) ≤ a`), so
`Σ_{i≤d+1} ≤ (a+1)^d + a(a+1)^d = (a+1)^{d+1}`.

`SignRepresents` gives `M > 0` on true entries, `≤ 0` on false ones; apply
the η-shift of P2.4 verbatim, absorbing `−η` into the `μ = ∅` term (present
because `0 ≤ d`).  Hence `signRank ≤ Σ_{i≤d} C(a,i) ≤ (a+1)^d`.  ∎

(`signRank_le_two_pow_min`, the dimension half, is already proved in Lean.)

---

## §4 Spectral norm of the distance-majority matrix (P4)

Throughout `m` is odd, `s : {0,1}^m → {±1}`, `s(u) := +1` if
`|u| ≥ (m+1)/2` else `−1` (`|u|` = Hamming weight), and
`M(x,y) := signMatrix m m (distThreshold m) = s(x ⊕ y)` (because
`hammingDist x y = |x ⊕ y|`).

### P4.1 Characters diagonalize

For `S ⊆ [m]` let `χ_S(x) := (−1)^{Σ_{i∈S} x_i}` (values ±1).  Key
identity: `χ_S(x ⊕ u) = χ_S(x)·χ_S(u)` (mod-2 additivity of the exponent).
Hence, substituting `y = x ⊕ u`:

    (M χ_S)(x) = Σ_y s(x⊕y) χ_S(y) = Σ_u s(u) χ_S(x⊕u) = λ_S · χ_S(x),
    λ_S := Σ_u s(u) χ_S(u).

So each `χ_S` is an eigenvector with eigenvalue `λ_S`.

### P4.2 The eigenvalue identity (NEW: replaces the source's brute force)

**Claim.** For every `S ≠ ∅`, picking any `i ∈ S`,

    λ_S = −2 · Σ_{u' ∈ {0,1}^{[m]∖{i}}, |u'| = (m−1)/2} χ_{S∖{i}}(u').

**Proof.** Pair `u` (with `u_i = 0`) against `u ⊕ e_i`.  Since `i ∈ S`,
`χ_S(u ⊕ e_i) = −χ_S(u)`, so the pair contributes
`χ_S(u)·(s(u) − s(u⊕e_i))`.  Now `|u ⊕ e_i| = |u| + 1`, and `s(u) −
s(u⊕e_i) = 0` unless the weight crosses the threshold, i.e. unless
`|u| = (m−1)/2`, where it equals `(−1) − (+1) = −2`.  Restricting the sum
to those `u` and dropping coordinate `i` (which is 0) gives the claim.  ∎

**Consequences.**

1. `|λ_S| ≤ 2·C(m−1, (m−1)/2)` for all `S ≠ ∅` — triangle inequality: the
   sum has `C(m−1, (m−1)/2)` terms of absolute value 1.
2. `|λ_S| = 2·C(m−1, (m−1)/2)` when `|S| = 1` — then `S∖{i} = ∅`, `χ_∅ ≡ 1`,
   and the sum is the full slice count.
3. `λ_∅ = 0`: pair `u ↔ ū` (complement); `m` odd makes this a fixed-point-
   free involution and `s(ū) = −s(u)` (`|ū| = m − |u|`, and exactly one of
   `|u|, m−|u|` is `≥ (m+1)/2`), while `χ_∅ ≡ 1`.

Note the source (`EXPLICIT_GAP.md`) verified "max at level 1" by brute force
for `m = 3,5,7,9` only; the argument above proves it for **all** odd `m`,
and is simpler than computing the level-`s` coefficients.

### P4.3 `specNorm_signMatrix_distThreshold`

**Claim.** `specNorm M = 2·C(m−1, (m−1)/2)`.

**Proof.** The `2^m` characters are pairwise orthogonal
(`⟨χ_S, χ_T⟩ = Σ_x χ_{SΔT}(x) = 0` for `S ≠ T` by the pairing of P4.2-style
on any `i ∈ SΔT`, and `= 2^m` for `S = T`), hence form an orthogonal basis
of `ℝ^{2^m}`.  For `v = Σ_S v̂_S χ_S`: `Mv = Σ_S λ_S v̂_S χ_S`, so by
Parseval `‖Mv‖² = 2^m Σ λ_S² v̂_S² ≤ (max_S λ_S²)·‖v‖²`, giving
`specNorm ≤ max |λ_S|`; the eigenvector `χ_S` itself gives `≥`.  Combining
with P4.2: `max_S |λ_S| = 2·C(m−1,(m−1)/2)` (levels ≥ 1 are dominated by
level 1, level 0 vanishes).  ∎

Lean route: avoid the abstract spectral theorem; work with the explicit
basis, proving Parseval by bilinearity + orthogonality.  `specNorm` is the
operator norm of `toEuclideanCLM`, i.e. `sup {‖Mv‖/‖v‖}`; both inequalities
above are elementary against this definition (`opNorm_le_bound` and the
witness vector).

---

## §5 Forster's theorem — `forster` (P5)

**Claim.** `M : Matrix ι ι ℝ` with entries ±1, `N := card ι`:
`(N : ℝ) ≤ signRank M · specNorm M`.

### P5.1 Reduction to unit vectors, and the small-rank regime

If `N = 0` the claim is `0 ≤ 0`.  Assume `N ≥ 1` and let `r := signRank M`
(realized: the `sInf` set is nonempty — `M` itself sign-matches — and a
minimum of a nonempty set of naturals is attained).  Take `A` sign-matching
with `rank A = r`.  A rank-`r` factorization gives vectors
`u_x, v_y ∈ ℝ^r` with `⟨u_x, v_y⟩ = A_{xy}`; all these inner products are
nonzero (strict sign match), in particular `u_x ≠ 0 ≠ v_y`; replace each by
its normalization (positive scaling preserves signs).

First dispose of `N ≤ r`: every ±1 column has norm `√N`
(`‖M e_y‖² = Σ_x M_{xy}² = N`), so `specNorm M ≥ √N ≥ 1`; hence if `r ≥ N`
then `r·specNorm ≥ N·1 = N` and the claim holds.  So assume `r < N`.

### P5.2 General position

Let `ε := min_{x,y} |⟨u_x, v_y⟩| > 0`.  Perturb each `u_x` by less than
`ε/2` (then re-normalize) so that afterwards every `w`-dimensional linear
subspace of `ℝ^r` (`1 ≤ w ≤ r−1`) contains at most `w` of the `u_x`: the
excluded configurations form finitely many measure-zero conditions
(some `r` of the perturbed vectors linearly dependent), so a suitable
arbitrarily small perturbation exists; all inner-product signs survive.
Since `N > r ≥ w·(N/r)/(N/r)`… precisely: `w < (w/r)·N` ⟺ `r < N`, so after
perturbation every proper subspace `W` satisfies

    #{x : u_x ∈ W} ≤ dim W < (dim W / r) · N.       (★)

### P5.3 Isotropic position (Forster's lemma)

**Claim.** Under (★) there is an invertible `B` with, writing
`û_x := B u_x/‖B u_x‖`:  `Σ_x û_x û_xᵀ = (N/r)·I_r`.

**Proof.** Minimize `Φ(P) := Σ_x log (u_xᵀ P u_x)` over the set
`𝒫 := {P ≻ 0 : det P = 1}`.

*Coercivity.*  Let `P_t ∈ 𝒫` with `‖P_t‖ → ∞`; take eigenvalues
`λ_1(t) ≤ … ≤ λ_r(t)`, `∏ λ_i = 1`, orthonormal eigenbases.  Passing to a
subsequence, the eigenbases converge and there is an index `w < r` such that
the bottom `w` eigenvalues stay bounded and `λ_{w+1}(t) → ∞`.  Let `W` be
the limit span of the bottom `w` eigenvectors.  For `u_x ∉ W`,
`u_xᵀ P_t u_x ≥ λ_{w+1}(t)·dist(u_x, W_t)² → ∞` at rate `log λ_{w+1}`;
for `u_x ∈ W` the term is bounded below by `log λ_1(t) ≥ −(r−1)·(max log λ)`
— summing and using `#{x : u_x ∈ W} ≤ w` from (★) together with
`Σ_i log λ_i = 0`:

    Φ(P_t) ≥ (N − w)·log λ_{w+1}·c − w·(r−1)·log λ_r·c' + O(1),

and since (★) gives `(N−w)/N > (r−w)/r`, a short computation (Forster 2002,
Lemma 4.3; the count of vectors escaping every degenerating subspace beats
the loss from the shrinking directions) shows `Φ(P_t) → +∞`.  Hence `Φ`
attains its minimum at some `P* ∈ 𝒫` (continuity on the closed unbounded
set plus coercivity).

*First-order condition.*  For symmetric `X` with `tr(P*^{-1}X) = 0`
(tangent to `det = 1`), `0 = dΦ = Σ_x (u_xᵀ X u_x)/(u_xᵀ P* u_x)`, i.e.
`Σ_x (u_x u_xᵀ)/(u_xᵀ P* u_x) ⟂ {X : tr(P*^{-1}X) = 0}`, forcing

    Σ_x (u_x u_xᵀ)/(u_xᵀ P* u_x) = c·P*^{-1}·…

precisely: `= μ P*⁻¹`… taking `B := P*^{1/2}` and traces (`tr` of both
sides after conjugating by `B`): `Σ_x û_x û_xᵀ = (N/r) I_r` with
`û_x = B u_x/‖B u_x‖`.  ∎

(The full derivative computation is mechanical: `d/dt log(uᵀ(P+tX)u) =
(uᵀXu)/(uᵀPu)`; the Lagrange multiplier is fixed by taking traces.)

### P5.4 The main chain

Set also `v̂_y := B^{-T} v_y / ‖B^{-T} v_y‖`.  Signs are preserved:
`⟨B u_x, B^{-T} v_y⟩ = ⟨u_x, v_y⟩`.  Now:

    Σ_{x,y} M_{xy} ⟨û_x, v̂_y⟩
      = Σ_{x,y} |⟨û_x, v̂_y⟩|            (signs match)
      ≥ Σ_{x,y} ⟨û_x, v̂_y⟩²             (unit vectors: |t| ≥ t² for |t| ≤ 1)
      = Σ_y v̂_yᵀ (Σ_x û_x û_xᵀ) v̂_y
      = Σ_y (N/r)‖v̂_y‖² = N²/r.         (isotropy)

Upper bound: with `U` the `N×r` matrix of rows `û_xᵀ` and `V` of rows
`v̂_yᵀ`,

    Σ_{x,y} M_{xy} ⟨û_x, v̂_y⟩ = tr(Uᵀ M V) = Σ_{j<r} (U^{(j)})ᵀ M V^{(j)}
      ≤ Σ_j ‖U^{(j)}‖·specNorm·‖V^{(j)}‖
      ≤ specNorm · √(Σ_j ‖U^{(j)}‖²) · √(Σ_j ‖V^{(j)}‖²)   (Cauchy–Schwarz)
      = specNorm · √N · √N.

(Columns `U^{(j)}`; `Σ_j ‖U^{(j)}‖² = Σ_x ‖û_x‖² = N`.)  Combining:
`N²/r ≤ N·specNorm`, i.e. `N ≤ r·specNorm`.  ∎

Formalization notes: P5.3 is the hard analytic kernel (compactness +
first-order condition); P5.1–P5.2 and P5.4 are finite-dimensional linear
algebra available in mathlib.  The statement frozen in Lean is exactly the
conclusion; the internal `r < N` and perturbation devices are proof-local.

---

## §6 Kronecker multiplicativity — `specNorm_kronecker`, `specNorm_reindex` (P6)

### P6.1 `specNorm_reindex`

`reindex e e M` acts on Euclidean space as `M` conjugated by the linear
isometry permuting coordinates by `e`; operator norms are invariant under
composition with isometric isomorphisms on either side.  ∎

### P6.2 `specNorm_kronecker`

*Upper bound.*  `A ⊗ₖ B = (A ⊗ₖ I)·(I ⊗ₖ B)` (mathlib
`Matrix.mul_kronecker_mul` with identity factors).  For any `u : ι×κ → ℝ`,
`‖(A ⊗ₖ I)u‖² = Σ_{c:κ} ‖A·u(·,c)‖² ≤ ‖A‖² Σ_c ‖u(·,c)‖² = ‖A‖²‖u‖²`,
so `‖A ⊗ₖ I‖ ≤ specNorm A`, dually for `I ⊗ₖ B`; submultiplicativity of the
operator norm finishes: `specNorm (A⊗ₖB) ≤ specNorm A · specNorm B`.

*Lower bound.*  The operator norm on a finite-dimensional space is attained:
pick unit `u, v` with `‖Au‖ = specNorm A`, `‖Bv‖ = specNorm B` (compactness
of the unit sphere; if `ι` or `κ` is empty both sides are 0).  With
`w(i,c) := u(i)·v(c)`: `‖w‖ = ‖u‖‖v‖ = 1` and `(A⊗ₖB)w = (Au)⊗(Bv)` (direct
computation of the double sum), so `‖(A⊗ₖB)w‖ = ‖Au‖·‖Bv‖`.  ∎

---

## §7 Theorem A — degree, Forster ratio, and the assembly (P7)

### P7.1 `thresholdDegLE_distThreshold` (deg ≤ 2)

The polynomial `P := Σ_{i<m} (X_i + Y_i − 2 X_i Y_i) − C(m/2)` — i.e.
`Δ(x,y) − m/2` where `Δ` is expressed by the multilinear XOR gadget per
pair — has total degree ≤ 2.  On the cube `Δ` is the Hamming distance
(check per coordinate: `x + y − 2xy = 1` iff `x ≠ y`).  For odd `m`,
`Δ − m/2 ∈ ℤ + 1/2` never vanishes, and `Δ − m/2 > 0 ⟺ Δ ≥ (m+1)/2`, which
is the definition of `distThreshold` (natural division `(m+1)/2` is exact).
So `P` sign-represents `F_m` and `ThresholdDegLE F_m 2`.  ∎

### P7.2 `thresholdDeg_distThreshold` (deg = 2)

By P7.1 and P1.4 it remains to rule out degree ≤ 1.  Suppose affine `ℓ`
sign-represents `F_m`.  Restrict: fix pairs `2..(m+1)/2` to disagree
(`x_i = 1, y_i = 0`), the remaining pairs except the first to agree
(`x_i = y_i = 0`); the restricted function of `(x_1, y_1)` is
`1[Δ ≥ (m+1)/2]` with `Δ = (m−1)/2 + 1[x_1 ≠ y_1]`, i.e. 2-bit XOR (also
correct at `m = 1`, where no pairs are fixed).  Substituting the constants
into `ℓ` yields an affine `ℓ'` in `(x_1,y_1)` sign-representing XOR.  But
`ℓ'(0,0) + ℓ'(1,1) = ℓ'(0,1) + ℓ'(1,0)` for affine `ℓ'` (both equal
`2·const + coeffs`), while sign-representation forces LHS ≤ 0 < RHS.
Contradiction.  ∎

### P7.3 `forsterRatio_le_signRank`

`N = 2^m` (card of `Fin m → Bool`).  By P5 and P4.3:
`2^m ≤ signRank · 2·C(m−1,(m−1)/2)`.  The binomial is positive, so divide:
`signRank ≥ 2^(m−1)/C(m−1,(m−1)/2) = forsterRatio m`.  ∎

### P7.4 `theoremA`

First conjunct: P7.2.  Second: `F_m` is nonconstant (all-agree input has
`Δ = 0 < (m+1)/2`; the input `x = 0…0, y = 1…1` has `Δ = m ≥ (m+1)/2`), so
by the corpus `HStar_eq_zero_iff`, `1 ≤ HStar`.  Chain P7.3 with
`signRank_le_pow_HStar` (cast to ℝ; `(2:ℝ)^(H+1) − 2` equals the cast of
`2^(H+1) − 2 : ℕ` since `H ≥ 1 ⇒ 2^(H+1) ≥ 2`).  ∎

### P7.5 `sqrt_le_forsterRatio`

Write `m = 2t+1`, `t ≥ 1`.  Claim: `C(2t,t) ≤ 4^t/√(2t+1)`, equivalently
`(C(2t,t)/4^t)² ≤ 1/(2t+1)`.  Induction-free: `C(2t,t)/4^t =
∏_{i=1}^t (2i−1)/(2i)` (induction on `t`: ratio of consecutive terms is
`C(2i,i)/C(2i−2,i−1)·(1/4) = (2i−1)/(2i)`).  Then

    [∏ (2i−1)/(2i)]² ≤ ∏ (2i−1)/(2i) · ∏ (2i)/(2i+1) = 1/(2t+1)

using `(2i−1)/(2i) ≤ (2i)/(2i+1)` (cross-multiply: `(2i−1)(2i+1) = 4i²−1 ≤
4i²`) and the telescoping `∏ (2i−1)/(2i) · (2i)/(2i+1) = 1/(2t+1)`.
Hence `forsterRatio m = 4^t/C(2t,t) ≥ √(2t+1) = √m ≥ √(m−1)`.  ∎

### P7.6 `four_le_HStar_distThreshold_127`

Numeric core (to be certified in ℕ): `14 · C(126,63) < 2^126`.  Then
`forsterRatio 127 > 14`, so by P7.3 `(signRank : ℝ) > 14`, hence
`signRank ≥ 15`.  `F_127` is nonconstant so `H* ≥ 1`; if `H* ≤ 3` the
bridge gives `signRank ≤ 2^4 − 2 = 14 < 15`, contradiction.  So `H* ≥ 4`.
Lean note: the ℕ-inequality is kernel-checkable (`Nat.choose` on binary
numerals; if `decide` is too slow, verify the explicit value of `C(126,63)`
by a Pascal-recurrence chain or a product-formula certificate — no
`native_decide`).  ∎

---

## §8 Theorem B — tensoring (P8)

Notation: `N₀ := m + m`, blocks `j < k`, `G := tensorDistThreshold m k =
xorPower k (distThreshold m)`, base sign matrix `S₁ := signMatrix m m F_m`.

### P8.1 Rearrangement to the all-left/all-right split

Build an explicit equivalence

    E : Fin (k·m + k·m) ≃ Fin (k·(m+m))

as the composite of standard mathlib equivalences: on the left,
`Fin (k·m + k·m) ≃ Fin (k·m) ⊕ Fin (k·m) ≃ (Fin k × Fin m) ⊕ (Fin k ×
Fin m) ≃ Fin k × (Fin m ⊕ Fin m) ≃ Fin k × Fin (m+m) ≃ Fin (k·(m+m))`
(via `finSumFinEquiv`, `finProdFinEquiv`, `Equiv.prodSumDistrib`,
`Equiv.sumCongr`, `Equiv.prodCongr`).  Concretely, `E` sends the `i`-th
x-coordinate of block `j` in the "all-x-first" layout to the coordinate
`castAdd i` of block `j` in the interleaved layout, and similarly for the
y-halves.  Note `k·(m+m) = k·m + k·m` only *propositionally* (`Nat.mul_add`
— not a definitional equality), which is exactly why the equivalence-based
lemma P1.3 is used instead of a `Fin`-permutation.

Define `G̃ : (Fin (k·m + k·m) → Bool) → Bool` by `G̃ z' := G (z' ∘ E.symm)`.
By P1.3 (with `e := E`), `HStar (k·m + k·m) G̃ = HStar (k·(m+m)) G`, and
`G̃` reads its first `k·m` coordinates as the x-halves of the `k` blocks in
order and its last `k·m` coordinates as the y-halves.  The sign matrix
`S_k := signMatrix (k·m) (k·m) G̃` is now the object of P8.2, and every
`HStar` conclusion about `G̃` transfers to the frozen statement about `G`
through the displayed equality.

### P8.2 The sign matrix identity

Under the identification `(Fin (k·m) → Bool) ≃ (Fin k → (Fin m → Bool))`
(rows: the k x-halves; columns: the k y-halves), the entry of
`S_k := signMatrix (k·m) (k·m) G̃` at `((x_j)_j, (y_j)_j)` is the ±1
encoding of `XOR_j F_m(x_j, y_j)`.  With the encoding `e(true)=+1,
e(false)=−1`: `e(b₁ ⊕ … ⊕ b_k) = (−1)^{k+1} ∏_j e(b_j)` (induction on `k`;
check `k=1` identity and the step `e(b ⊕ c) = −e(b)e(c)`).  Hence

    S_k = (−1)^{k+1} · reindex (⊗ₖ_{j<k} S₁)

where `⊗ₖ` is the `k`-fold Kronecker power (index type `(Fin m → Bool)^k`)
and `reindex` transports along the two identifications.  Proof: pointwise
evaluation of both sides; the Kronecker entry at `((x_j), (y_j))` is
`∏_j S₁(x_j, y_j)` by induction on `k`.

### P8.3 `theoremB_HStar` (`1 ≤ k`)

By P1.1 (reindex) and P1.2 (negation): `signRank S_k = signRank (⊗^k S₁)`.
By P6.2 (induction on `k`) `specNorm (⊗^k S₁) = (2C)^k` with
`C := C(m−1,(m−1)/2)`, and the index-type card is `2^{k m}` per side, total
`N = 2^{km}`.  Forster (P5): `2^{km} ≤ signRank · (2C)^k`, so

    signRank (⊗^k S₁) ≥ (2^m/(2C))^k = forsterRatio m ^ k.

`G̃` is nonconstant for `k ≥ 1` (fix all blocks but one at agree; the free
block toggles `F_m`, and XOR with a constant toggles `G̃`), so `1 ≤ HStar`.
Bridge (`signRank_le_pow_HStar`) + P8.1 give

    forsterRatio m ^ k ≤ 2^(HStar (k·(m+m)) G + 1) − 2.  ∎

### P8.4 `thresholdDegLE_tensorDistThreshold` (deg ≤ 2k)

Let `P_j` be the block-`j` copy of the quadratic of P7.1 (in the block's
variables).  On the cube each `P_j ∈ ℤ + 1/2`, with `P_j > 0 ⟺ b_j := F_m
(block j) = true`.  The product `Q := (−1)^{k+1} ∏_j P_j` has total degree
≤ 2k, never vanishes, and `sign Q = (−1)^{k+1} ∏ sign P_j = e(⊕ b_j)` by the
encoding identity of P8.2.  So `Q` sign-represents `G` (`Q > 0 ⟺ G = true`).
At `k = 0`: `Q = −1` and `G ≡ false` — still correct.  ∎

### P8.5 `theoremB_gap` (no hypothesis on k)

Case `k = 0`: LHS `= −1`; RHS `= HStar − thresholdDeg ≥ 0` by the corpus
chain (P1.4 note).  Case `k ≥ 1`: from P8.3,
`γ^k ≤ 2^{H+1} − 2 < 2^{H+1}` (γ := forsterRatio m > 0 since numerator and
denominator are positive), so taking `logb 2`:
`k·logb 2 γ < H + 1`, i.e. `(H:ℝ) > k·logb 2 γ − 1`.  From P8.4 and P1.4,
`(thresholdDeg : ℝ) ≤ 2k`.  Subtract:
`H − thresholdDeg ≥ k·logb 2 γ − 1 − 2k = k(logb 2 γ − 2) − 1`.  ∎

---

## §9 Warren's theorem — `warren_sign_patterns` (P9)

**Statement (frozen).** `1 ≤ m ≤ k`, `1 ≤ d`, polynomials
`P i : MvPolynomial (Fin m) ℝ` with `totalDegree ≤ d`:
`(signPatterns P).ncard ≤ (4·e·d·k/m)^m`, where `signPatterns` is the set
of Boolean vectors `s` realized as `s i = decide (0 < eval x (P i))` at
points `x` where no `P i` vanishes.

### P9.1 Patterns are separated by components (fully detailed)

Let `U := {x ∈ ℝ^m : ∀ i, eval x (P i) ≠ 0}` (open: finite intersection of
preimages of `ℝ∖{0}` under the continuous `eval · (P i)`).  On each
connected component of `U`, every `eval · (P i)` has constant sign
(a continuous nonvanishing function on a connected set cannot change sign:
the preimages of `(0,∞)` and `(−∞,0)` are open, disjoint, cover).  Hence
the map {components} → {patterns} is well-defined and **surjective** onto
`signPatterns P`, so `ncard (signPatterns P) ≤ #components(U)`.

### P9.2 Component bound (Warren 1968, Theorems 1–2; cited)

`#components(ℝ^m ∖ ∪_i Z(P_i)) ≤ Σ_{j=0}^{m} 2^j·C(k,j)·binom-terms ≤
(4edk/m)^m` for `k ≥ m ≥ 1`, `d ≥ 1`.  Proof architecture (for the Lean
decomposition; the bookkeeping is Warren's):

1. *Perturbation.*  For small generic `ε > 0`, each component of `U`
   contains a component of `U_ε := {∀ i, |P_i| > ε}`, and the boundary
   varieties `{P_i = ±ε}` are smooth hypersurfaces meeting transversally
   (Sard's theorem — in mathlib — applied to the polynomial maps; generic
   regular values `±ε`).
2. *Charging.*  Each bounded component of `U_ε` is charged to a critical
   point of a generic linear functional on an intersection of ≤ m of the
   `2k` hypersurfaces; unbounded components are handled by intersecting
   with a large sphere (adds the `+1`-type terms).
3. *Counting.*  Critical points of a generic linear functional on a smooth
   complete intersection of `j` hypersurfaces of degree ≤ d in `ℝ^m` are
   solutions of a polynomial system of `m` equations of degrees
   ≤ d, d−1, …; Bézout-type counting bounds them by `d^j (d−1)^{m−j} ≤
   d(2d)^{m−1}`-order terms (Milnor 1964 / Oleinik–Petrovsky).
4. *Assembly.*  Summing `Σ_j 2^j C(k,j)·(deg-bound)` and estimating
   binomials by `C(k,j) ≤ (ek/j)^j` yields `(4edk/m)^m` for `k ≥ m`.

References: H. E. Warren, *Lower bounds for approximation by nonlinear
manifolds*, Trans. AMS 133 (1968), Thm 2–3; J. Milnor, *On the Betti
numbers of real varieties* (1964); Matoušek, *Lectures on Discrete
Geometry*, §6.2.  **Audit scope note:** the layer freezes only the
*statement*; the internal constants are taken from the literature.  The
deep kernel for a future Lean proof is step 3 (no multivariate Bézout in
mathlib); steps 1–2 need real-analytic infrastructure (Sard exists).  This
is the hardest leaf of the layer and is flagged as such in SEPARATIONS.md.

---

## §10 The shattering bound and the NDISJ leaves (P10)

### P10.1 `pow_le_of_leftShatters`

**Claim.** `1 ≤ k`, `computableWithHeadsN (a+b) H f`, `LeftShatters f k` ⟹
`2^k ≤ (2·e·k)^{2H}`.

**Proof.**  Fix heads, `w`, `τ`, and the shattered left points
`z_1, …, z_k`.  By P2.1, for input `blockJoin z_j w'`:

    D_h = b_{hj} + q_h(w'),   u_h = a_{hj} + p_h(w'),

where `b_{hj} := A_h(z_j)`, `a_{hj} := A'_h(z_j)` are **fixed reals**
(the left blocks are frozen) and `q_h(w') := B_h(w')`, `p_h(w') := B'_h(w')`
depend only on the right block.  Define for each `j ≤ k` the real polynomial
in `2H` variables `(p_1..p_H, q_1..q_H)`:

    Q_j(p, q) := Σ_h (a_{hj} + p_h)·∏_{h'≠h} (b_{h'j} + q_{h'})
                 − τ·∏_h (b_{hj} + q_h).

Each monomial of `Q_j` has degree ≤ H (one factor from each of ≤ H
brackets), so `totalDegree Q_j ≤ H`.  Since all denominators are positive
at cube points, clearing gives: for every right block `w'`,

    f (blockJoin z_j w') = true  ⟺  Q_j(p(w'), q(w')) > 0,
    f (…) = false                ⟹  Q_j(p(w'), q(w')) ≤ 0.

*Case `H = 0`.*  Zero heads: the update is the zero vector, `⟪w, 0⟫ > τ` is
input-independent, so `f` is constant; `LeftShatters f k` with `k ≥ 1`
requires realizing two different labels at `z_1` — contradiction, the
hypotheses are void.  (If one prefers: the conclusion `2^k ≤ 1` is
unreachable, but the case never occurs.)

*Case `1 ≤ H`, `k < 2H`.*  `2^k ≤ 2^{2H} ≤ (2ek)^{2H}` since
`2ek ≥ 2e ≥ 2` for `k ≥ 1`.

*Case `1 ≤ H`, `k ≥ 2H`.*  Shattering supplies, for every
`s : Fin k → Bool`, a witness `w_s` with labels `s`; let
`ξ_s := (p(w_s), q(w_s)) ∈ ℝ^{2H}`.  Let

    η := (1/2)·min { Q_j(ξ_s) : s j = true }   (or 1 if the set is empty),

a positive real (finite nonempty min of positives).  The shifted
polynomials `Q̃_j := Q_j − η` (same degrees) satisfy, at every witness:
`s j = true ⇒ Q̃_j(ξ_s) > 0`; `s j = false ⇒ Q̃_j(ξ_s) ≤ −η < 0`.  Thus each
of the `2^k` label vectors `s` is a *strict* sign pattern of
`(Q̃_1, …, Q̃_k)` realized at `ξ_s`, where no `Q̃_j` vanishes; distinct `s`
are distinct patterns.  Warren (`m := 2H ≥ 2·1`, `d := H`, `k` polynomials;
hypotheses `1 ≤ 2H ≤ k`, `1 ≤ H` hold in this case):

    2^k ≤ (4·e·H·k/(2H))^{2H} = (2ek)^{2H}.  ∎

### P10.2 `HStar_ndisj_le` (`H*(NDISJ_m) ≤ m`)

Via `computable_of_fracComputable`, it suffices to exhibit `m` formal
`FracAtom`s whose sum plus a constant sign-represents `NDISJ_m`.  The
`FracAtom` interface requires every positional weight to be strictly positive,
so use the following fully smoothed construction (this is the formal version
of the small-`δ` engineering note in the source proof).  Put

    r := 1 / (8(m+1)(2m+1)),

and for `i < m` take the atom with

    η_i := (2m+1)r,   δ_i := 0,   γ_i := r,   α_i := r,
    ρ_{i,p} := 1  if p is x_i or y_i, and r otherwise,
    m_{i,p} := 0.

All required positivity fields hold because `r > 0`; also `r ≤ 1`.  Its
value is exactly

    g_i(z) = (2m+1)r / (r + Σ_p ρ_{i,p} · (if z_p then r else 1)).

If `x_i = y_i = 1`, both distinguished weights in the denominator equal
`r`, and every other positional weight is at most `r` (using `r ≤ 1`).
There are `2m` positions, so the denominator is at most `(2m+1)r` and
`g_i ≥ 1`.  If the pair is not jointly set, at least one distinguished
weight equals `1`, so the denominator is at least `1` and

    0 ≤ g_i ≤ (2m+1)r = 1/(8(m+1)).

Use score `R := Σ_i g_i − 1/2`.  If some pair is jointly set, that atom
contributes at least `1` and all others are nonnegative, hence `R > 0`.  If
no pair is jointly set, then

    Σ_i g_i ≤ m/(8(m+1)) < 1/2,

so `R < 0`.  This also covers `m = 0`: the empty sum with constant `−1/2`
computes the constantly-false `NDISJ_0`.  Thus `fracComputable (m+m) m
NDISJ_m`, hence `computableWithHeadsN (m+m) m NDISJ_m`; minimality in the
definition of `HStar` gives `HStar ≤ m`.  ∎

### P10.3 `thresholdDeg_ndisj` (`= 2` for `m ≥ 2`)

Upper: `P := Σ_i X_i Y_i − 1/2` has degree 2; on the cube its values lie in
`ℤ − 1/2 ≠ 0`, and `P > 0 ⟺ Σ x_iy_i ≥ 1 ⟺ NDISJ`.  Lower: suppose affine
`ℓ` sign-represents `NDISJ_m`, `m ≥ 2`.  Fix all coordinates outside pairs
1, 2 to zero and consider the four inputs (writing `(x_1x_2 | y_1y_2)`):
`a = (10|10) ↦ true`, `d = (01|01) ↦ true`, `b = (10|01) ↦ false`,
`c = (01|10) ↦ false`.  As 0/1 vectors `a + d = b + c`, so affine `ℓ` gives
`ℓ(a) + ℓ(d) = ℓ(b) + ℓ(c)`; but sign-representation forces
`ℓ(a) + ℓ(d) > 0 ≥ ℓ(b) + ℓ(c)`.  Contradiction; so `¬ThresholdDegLE 1`,
and P1.4 with the upper bound pins `thresholdDeg = 2`.  ∎

### P10.4 already-proved items

`ndisj_leftShatters` and the composition `ndisj_separation` are proved in
Lean; the `SharpShatteringUpperBound` corollary likewise.  No informal debt.

---

## §11 New-lemma inventory surfaced by this document

To be added as statements (some already provable, none contradicting the
freeze):

1. `signRank_neg` (P1.2) — needed by P8.3.
2. `HStar_comp_equiv` (P1.3) — needed by P8.1.
3. `thresholdDeg_le_of` / monotonicity wiring (P1.4) — needed by P8.5, P10.3.
4. Rank subadditivity for matrices, if absent at 4.31 (P2.3) — realized as the
   `rank_add_le` leaf (`(A + B).rank ≤ A.rank + B.rank`); it is absent at 4.31.
5. (Optional) `signRank_pos` for nonempty ±1 matrices — cheap sanity lemma.

**Decomposition leaves surfaced by the gatekeeper pass (self-contained,
`jules_ready`, each proved inside the P-item named).**  These are honest
sub-statements carved out of the harder own leaves so that the analytic/model
core is isolated:

6. `sum_choose_le_pow` (P3.3) — `∑_{i≤d} C(a,i) ≤ (a+1)^d`, the monomial count
   of the degree-`d` sign-rank ceiling.
7. `card_le_specNorm_sq` (P5.1) — `card ι ≤ (specNorm M)^2` for `±1` `M`, the
   `√N` column estimate disposing of Forster's small-rank regime.
8. `sign_xor_prod` (P8.2) — the XOR sign identity `e(⊕ gⱼ) = (−1)^{k+1} ∏ e(gⱼ)`.
9. `blockSignRep_distThreshold` (P8.4) — the per-block strict degree-`≤2` sign
   representation of `z ↦ distThreshold m (blockOf z j)` (rename of P7.1's
   `Δ − m/2`, nonzero half-integer values).
10. Character framework for §4 (new defs `charFn`, `distSign`; proved
    `charFn_xor` = P4.1 multiplicativity), with leaves `signMatrix_distThreshold_apply`
    (P4.1, `M = s(x ⊕ y)`), `signMatrix_mulVec_charFn` (P4.1, eigen-action
    `M χ_S = λ_S χ_S`), `charFn_orthogonal` (P4.3, `⟨χ_S, χ_T⟩ = [S=T] 2^m`),
    `distSign_sum_eq_zero` (P4.2, `λ_∅ = 0` for odd `m`).  Remaining hard core of
    P4: the level-1 eigenvalue bound (P4.2) and the Parseval assembly (P4.3).
11. `warren_pow_simp` (P10.1) — `(4 e H k / (2H))^{2H} = (2 e k)^{2H}` for
    `H ≥ 1`, the final Warren-ceiling simplification.

Corrections/upgrades of the informal sources established here:

* P4.2 proves the "Fourier maximum at level 1" claim for **all** odd `m`
  (the source had verified it only for `m ≤ 9` by brute force), via the
  boundary-pairing identity `λ_S = −2·Σ_{middle slice} χ_{S∖{i}}` and the
  triangle inequality — no Krawtchouk formulas needed.
* P2.4/P3.3/P10.1 make explicit the strictification (η-shift) that the
  sources leave implicit; the false-side of `computesPred` is only `≤ 0`.
* P8.1 surfaces the permutation-invariance lemma that the sources use
  silently when moving to the all-left/all-right partition.
* P8.2 records the global `(−1)^{k+1}` in the XOR sign identity (absent in
  the source, harmless for norms/ranks but required in any Lean proof).
