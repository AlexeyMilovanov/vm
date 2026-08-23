# Explicit separations between H* and threshold degree (unrestricted model)

All statements are about the model exactly as specified in `model.md` — arbitrary reals,
exact computation on all 2^n inputs, no weight or margin restriction.

Notation. `H*(f)` = minimum heads. `deg_±(f)` = threshold degree. For a two-block
partition `I ⊔ J` of the variables, `Σ_f` is the ±1 sign matrix and `srank(f)` its sign-rank.

Two facts are imported from the corpus and one from the classical literature:

* **(028)** `H` heads ⟹ `srank_{I,J}(f) ≤ 2^{H+1} − 2`, hence
  `H*(f) ≥ ⌈log₂(srank+2)⌉ − 1`. (Verified: the proof groups the cleared polynomial by
  subsets `T ⊆ [H]`, giving `2 + 2(2^H − 2)` rank-one pieces. The constant is correct —
  a naive count of distinct x-side functions gives only `2^{H−1}(H+2)`, which is weaker.)
* **(006)** `deg_±(f) ≤ H*(f)`.
* **Forster.** For an `N × N` sign matrix, `srank(M) ≥ N / ‖M‖₂`.

---

## Base family

For odd `m`, on `n = 2m` bits:

    F_m(x, y) := 1[ Δ(x, y) ≥ (m+1)/2 ],     x, y ∈ {0,1}^m

**deg_±(F_m) = 2.** Upper: `Δ(x,y) − m/2` is quadratic and never zero (m odd), and is
positive exactly on `F_m = 1`. Lower: fix `(m−1)/2` of the remaining pairs to disagree;
the free pair reduces `F_m` to 2-bit XOR, so `deg_± ≥ 2`.

**Sign-rank.** Under the `x | y` partition the matrix is the XOR-pattern of majority,
`M[x,y] = MAJ_m(x ⊕ y)`. Its eigenvectors are the characters, so `‖M‖ = 2^m · max_S |ĝ(S)|`
with `g = MAJ_m`. The maximum sits at level 1 (checked by brute force for m = 3,5,7,9) and
equals `C(m−1,(m−1)/2) / 2^{m−1}`. Forster gives

    srank(F_m) ≥ γ_m := 2^{m−1} / C(m−1, (m−1)/2)  ~  sqrt(π m / 2).

### Theorem A (unbounded ratio, constant degree)

    deg_±(F_m) = 2  and  H*(F_m) ≥ ⌈log₂(γ_m + 2)⌉ − 1 = (1/2)·log₂ m − O(1).

Smallest explicit point beating the corpus's 3-head ceiling: `m = 127` (n = 254 bits),
where `γ = 14.0964`, so `srank ≥ 15 > 14 = 2^{3+1} − 2` and `H*(F_127) ≥ 4`.
`m = 125` gives only `13.98 → 14`, so 127 is minimal for this route.

---

## Tensoring: a linear additive gap

Forster's bound — unlike sign-rank itself — is **multiplicative under Kronecker products**,
because both `N` and `‖·‖₂` are. XOR-composition of independent blocks produces exactly a
Kronecker product of sign matrices. So put, for odd `m ≥ 13` and `k ≥ 1`, on `n = 2mk` bits:

    G_{m,k} := F_m^{(1)} ⊕ F_m^{(2)} ⊕ ... ⊕ F_m^{(k)}     (XOR of the outputs)

* `Σ_G = ⊗_i Σ_{F_m}` under the all-x | all-y partition, so
  `srank(G) ≥ (2^{mk}) / ‖Σ_{F_m}‖^k = γ_m^k`, hence `H*(G) ≥ k·log₂ γ_m − 1`.
* `deg_±(G) ≤ 2k`: the product `(−1)^{k+1} ∏_i (Δ(x^{(i)},y^{(i)}) − m/2)` sign-represents `G`
  and never vanishes. (Equality holds — restrict each block to a 2-bit XOR to get parity
  on 2k bits — but only the upper bound is needed.)

### Theorem B (explicit linear gap)

    H*(G_{m,k}) − deg_±(G_{m,k})  ≥  k(log₂ γ_m − 2) − 1.

The gap per input bit is `(log₂ γ_m − 2)/(2m)`, positive iff `γ_m > 4` iff `m ≥ 13`,
and maximised at `m = 29` (`γ = 6.6914`, `log₂ γ = 2.7423`):

    m = 29:   deg_±(G) = n/29,   H*(G) ≥ n/21.2 − 1,   gap ≥ n/78.1 − 1.

Choosing `m = 127` instead maximises the ratio at any scale: `H*(G) ≥ 1.908 · deg_±(G)`.

**Consequence.** `H*` is not asymptotically equal to `deg_±`: there is an explicit family
with `H* − deg_± = Ω(n)` and an explicit family with `H*/deg_± = Ω(log n)`. The corpus's
best was `H* − deg_± = 1` and `H*/deg_± = 3/2`, both at the single point `n = 8`
(theorem 189).

---

## Theorem C (ceiling of the whole sign-rank route)

If `deg_±(f) = d` then any degree-`d` sign-representing polynomial factors the matrix
through its monomials, so for every partition

    srank_{I,J}(f) ≤ Σ_{i ≤ d} C(|I|, i) ≤ (n+1)^d,   and also  srank ≤ 2^{n/2}.

Feeding this into the 028 bridge, the sign-rank route can never certify more than

    H* ≥ d · log₂(n+1)          — so ratio at most log₂(n+1),
    H* − deg_± ≥ (n/2)(1 − 1/log₂(n+1))   — so additive gap at most ≈ n/2.

Theorem A is therefore within a factor ≈ 4 of the ratio ceiling, and Theorem B within a
factor ≈ 39 of the additive ceiling. Both are "the right order" for this technique.
Beating `O(deg_± · log n)` for constant-degree functions provably requires a method that
does **not** factor through the rank of the cleared polynomial.

---

## What this does and does not settle

Settled: `H* ≠ Θ(deg_±)`, explicitly and asymptotically, in the unrestricted model.

Open (and unchanged): an explicit constant-degree family with `H* = ω(log n)`.
Counting (theorem 026) says almost every degree-2 function needs `Ω(n)` heads — combining
026 with the known count `2^{Θ(n³)}` of degree-2 PTFs (Baldi–Vershynin) — but no explicit
witness is known, and Theorem C says sign-rank will never produce one.

## Practical reformulation used for the finite search

With the denominators `D_1..D_H` **fixed**, deciding whether `f` is computable is a
**linear program** in `(c, N_1, ..., N_H)`, because

    S(x) = c + Σ_h N_h(x)/D_h(x)

is linear in those unknowns. So

    maximise t  s.t.  σ(x)·S(x) ≥ t  for all x,   |coefficients| ≤ 1

has optimum `> 0` exactly when that denominator tuple realises `f` (t = 0 is always
attainable by the zero solution, so only strict positivity counts). Only the denominators
need to be searched: `H` nonnegative weight vectors plus `H` orientation bits, since by
theorem 032 every admissible denominator is, after positive scaling, either
`1 + ⟨w, x⟩` or `1 + ⟨w, 1−x⟩` with `w ≥ 0` (automatically positive on the cube).

This replaces "degree-`H` polynomial feasibility" (theorem 194's system, and the SoS
proposals) by an exact LP inside a low-dimensional search. Validated end to end: fed the
three denominators of theorem 189's certificate
(`34 − x₁ − 6x₂ − x₃ − 8x₄ − x₅ − x₆ − x₇ − x₈`, and two others, all negatively oriented),
the LP returns margin `+1.7e−3` and independent evaluation confirms the sign pattern on
all 256 inputs.

### Exact dual criterion (what a lower-bound proof must exhibit)

Apply Gordan's theorem to the LP. For fixed denominators the achievable cleared scores are
exactly the subspace `V_D = Σ_h (∏_{k≠h} D_k)·Aff`, of dimension at most `H(n+1)`. So the
tuple fails iff there is a nonzero `μ ≥ 0` with `μσ ⊥ V_D`, i.e. for every `h`

    ν_h := μ · ∏_{k≠h} D_k  ≥ 0   satisfies   ν_h·σ ⊥ Aff.

Each `ν_h` is therefore a **witness that f is not a linear threshold function**, and the
`H` witnesses are coupled by `ν_1 D_1 = ν_2 D_2 = ... = ν_H D_H`. Writing
`K_f := { ν ≥ 0 : ν·σ ⊥ Aff }` for the (convex, polyhedral) cone of LTF-refuting witnesses:

    H*(f) ≤ H   ⟺   there are admissible D_1..D_H with   ∩_h  D_h · K_f  =  {0}.

For `H = 1` this reads `K_f = {0}`, i.e. `f` is an LTF — matching theorem 011. So head
complexity is exactly *the number of reweightings by admissible positive affine forms needed
to collapse the LTF-obstruction cone*. This is the object a scalable lower bound has to
control; it keeps positivity and the joint factorisation, and unlike slice-rank it is not a
relaxation. (Slice-rank alone is provably useless at `H = 3`: multiplying any degree-2 sign
polynomial by a positive affine form gives a cubic of slice rank one with the same signs.)

**Structural warning for distance thresholds.** Block-symmetric denominators
`D = 1 + a|x| + b|y|` can never work: their contribution to the cross-block coefficient
matrix has the form `C_ij = a_i + b_j`, whereas `Δ(x,y)` needs `C = I`. Any successful
denominator tuple must break the block symmetry — as theorem 189's does. This also explains
why the symmetric-SDP proposal (chain 17 of the barrier lab) was doomed.
