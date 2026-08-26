# Strict audit: polynomial closeness of `H*` and `POIC_2`

This note records only theorem-grade statements. Numerical solver failures are
listed separately and are not promoted to lower bounds.

## 1. Exact conventions and the closure issue

Let `X = {0,1}^n` and let `sigma_f : X -> {+1,-1}` be the desired strict sign
pattern.

An exact nonconstant one-head denominator has the form

```text
B(x) = b_0 + sum_i b_i x_i > 0 on X,
```

where every variable coefficient is nonzero and all variable coefficients
have the same sign. For such a denominator, every affine numerator `A(x)` is
realizable by one model-native head.

It is useful to distinguish:

- **strict admissibility:** all variable coefficients are nonzero and have one
  common sign;
- **weak admissibility:** all variable coefficients have one weak sign, so zero
  coefficients and a constant denominator are allowed.

Weak denominators are legitimate for sign complexity through the following
closure lemma.

### Strictification lemma

Suppose that, for a parameter `h -> 0`, a sum of `H` fractions with positive
weakly admissible affine denominators converges uniformly on `X` to a function
`Q` satisfying

```text
min_x |Q(x)| > 0.
```

Then the same sign pattern is realized by `H` exact heads.

Indeed, first fix a sufficiently small `h`. Then perturb every weak denominator
arbitrarily slightly to a positive strict denominator. Continuity on the finite
cube preserves the sign. If a numerator grows as `h^{-k}`, choose the denominator
perturbation to be `o(h^k)`. Thus no uniform perturbation rate in `h` is needed.

In particular, an arbitrary affine fraction `A/1` is not literally an exact
constant-denominator atom of the original model. It is, however, a valid
one-head sign-limit by strictification. This repairs every cleanup-head use in
the Order Lemma constructions.

For a nonconstant function, the free output bias of the original `H*` model may
be absorbed into one numerator, since `A_1 + c B_1` remains affine. Hence at the
sign level

```text
H*(f) = min H such that sign(sum_{h=1}^H A_h/B_h) = sigma_f,
```

with exact strict denominators, or equivalently with weak denominators followed
by strictification.

### Canonical definition of `POIC_2`

For nonconstant `f`, define `POIC_2(f)` as the minimum of `max{s,r}` over strict
sign representations

```text
R(x) = sum_{t=1}^r L_t(x) / prod_{j in J_t} B_j(x),
```

where:

- `B_1,...,B_s` form a common positive admissible affine pool;
- every `L_t` is affine;
- `J_t` is nonempty and `1 <= |J_t| <= 2`;
- repeated incidences may be merged and unused pool elements removed.

Positive constant denominators are allowed via the same closure convention.
Constants have complexity zero. There is **no free global bias `c` in this
canonical definition**.

Clearing the positive product of all pool denominators gives

```text
deg_pm(f) <= POIC_2(f) <= H*(f),
POIC_1(f) = H*(f).
```

The lower bridge holds because every cleared term has degree
`1+s-|J_t| <= s`. The upper bridge uses singleton incidences for an `H*`
certificate.

Adding a free `c` to the definition is a substantive change. It can be absorbed
when a singleton term is present, but not in a pure double-pole certificate such
as `c + L/(B_1 B_2)`.

## 2. Universal conditioning-free converse

### Theorem

For the canonical no-bias definition, if a certificate has pool size `s`, then

```text
H*(f) <= 2^s - 1.
```

Consequently, for `q = POIC_2(f)`,

```text
POIC_2(f) <= H*(f) <= 2^q - 1.
```

### Proof sketch

Write each denominator, after flipping negative orientations, as

```text
B_i = c_i + epsilon_i T_i,   epsilon_i in {+1,-1},
```

where every `T_i` has weakly nonnegative slopes. The numerator obtained after
clearing all denominators is a sum of expressions

```text
L(x) prod_{i in C} T_i(x),   C proper subset of [s],
```

because every incidence `J_t` is nonempty.

For `k = |C|`, finite-difference polarization gives

```text
k! prod_{i in C} T_i
  = sum_{empty != S subset C} (-1)^(k-|S|) (sum_{i in S} T_i)^k,
```

and the same alternating sum of every power `1,...,k-1` vanishes. A head with
denominator `1-h Z_S`, where `Z_S = sum_{i in S} T_i`, can carry all required
orders simultaneously by placing an affine Laurent polynomial in `h` in its
numerator. All nonconstant divergent orders cancel. The remaining affine
residue is removed by one shared weak cleanup head and then strictified.

There are `2^s-2` nonempty proper subsets and one cleanup head, giving
`2^s-1` heads. Equivalently, translated polarization uses all `2^s-1` nonempty
subset directions without a separate cleanup.

## 3. Polynomial converse for low pool-slope rank

Let `d` be the dimension of the linear span of the pool slope vectors after
flipping negative orientations. This is the **slope rank**, not
`dim span{1,B_1,...,B_s}`. Put

```text
K = max_t (s-|J_t|) <= s-1.
```

### Theorem

For `d >= 1`,

```text
H*(f) <= K * binom(K+d-1,d-1) + 1.
```

If `d=0`, then the cleared score is affine and `H*(f) <= 1`.

### Proof sketch

Choose positive-slope statistics `t_1,...,t_d` spanning the pool slopes. The
cleared polynomial can be written

```text
P(x) = sum_{|alpha| <= K} A_alpha(x) t^alpha,
```

with affine vector-valued coefficients `A_alpha`. Choose

```text
R = binom(K+d-1,d-1)
```

generic ridge directions in the positive cone. Their `m`-th powers span
`Sym^m(R^d)` simultaneously for every `m <= K`. Hence

```text
P = sum_{j=1}^R sum_{m=0}^K M_{j,m}(x) z_j^m,
```

where all `M_{j,m}` are affine. For each direction, `K` distinct denominator
scales and a Vandermonde system realize degrees `1,...,K`; one shared affine
cleanup removes all degree-zero residues.

Consequences:

```text
d=1  =>  H*(f) <= K+1 <= s <= q,
fixed d  =>  H*(f) = O_d(q^d).
```

This is stronger than Claude R14 because directions are shared across all POIC
terms. R14 also conflated slope rank with `dim span{1,B_i}`, producing an
off-by-one convention.

For proportional slopes, an exact partial fraction requires
`B_2 = lambda B_1 + c` with `c != 0`:

```text
1/(B_1 B_2) = (1/c)(1/B_1 - lambda/B_2).
```

If `c=0`, the pole is repeated and does not split exactly, although it is the
limit of two nearby simple poles.

## 4. Complete upper bounds at canonical budget at most three

After deleting unused pool elements, merging equal incidences, and cancelling a
common positive denominator factor, the nontrivial incidence types are:

| Type | Incidences | Cleared form | Proven head bound |
|---|---|---|---:|
| singletons | `{1},{2},{3}` | already three heads | 3 |
| A | `{1},{2},{12}` | `L_1B_2+L_2B_1+L_12` | 3 |
| C | `{12},{23},{31}` | `L_12B_3+L_23B_1+L_31B_2` | 4 |
| D | `{1},{23}` | `L_1B_2B_3+L_23B_1` | 5 |
| F' | `{1},{12},{23}` | `L_1B_2B_3+L_12B_3+L_23B_1` | 5 |
| B | `{1},{2},{13}` | `L_1B_2B_3+L_2B_1B_3+L_13B_2` | 6 |

The cubic terms use the three polarization directions `T_i`, `T_j`, and
`T_i+T_j`. Heads with the same direction merge, and one shared cleanup removes
all affine residues. Therefore

```text
POIC_2(f) <= 3  =>  H*(f) <= 6.
```

At budgets zero, one, and two the two measures are equal. Thus throughout the
currently proved small-budget range,

```text
H*(f) <= 2 POIC_2(f).
```

These are upper bounds; they do not prove equality at budget three.

### Variant with a free POIC bias

If a singleton incidence is present, the bias is absorbed into its numerator.
For a pure double-pole certificate the situation changes:

- at budget two, `c + L/(B_1B_2)` has the safe bound `H* <= 3`, not a proved
  equality at two;
- at budget three, a pure three-cycle produces `cB_1B_2B_3` after clearing.

The seven nonempty subset directions realize the cubic term, and the free bias
of the original `H*` model cancels the scalar residue. Therefore

```text
POIC_2^c(f) <= 3  =>  H*(f) <= 7.
```

Hence the no-bias convention is essential to the bound six.

## 5. Audit of the main Claude claims

### R6: conditioned converse

The mathematical construction is correct after strictification. For a mixed
pair `u>0`, `v=C-w>0`, with `delta <= u,v <= 1`, Chebyshev approximation gives
reciprocal polynomials of degree

```text
d_1 = O(delta^(-1/2) log(1/(epsilon delta))).
```

Their product has degree `d=2d_1` in `u,w`; `d+1` admissible ridge directions
span it, and `O(d)` heads per direction realize it. The resulting cost is
`O(d^2)` per double-pole term. Claude's `(d+1)(d+2)` count is safe but loose.

The theorem remains dependent on denominator floor, sign margin, and numerator
norm. It therefore proves a polynomial bound in certificate conditioning, not
in `q` alone. Standard effective real algebraic geometry gives bounds depending
on `n` and does not remove this gap.

### R29: Order Lemma

The expansion

```text
(L/h)/(1-hB) = L/h + LB + hLB^2 + O(h^2)
```

and its higher-order Vandermonde version are correct. The sentence that an
arbitrary affine cleanup is *exactly* a constant-denominator native head is
false. The strictification lemma repairs it without adding a head. Thus orbit A
still satisfies `H* <= 3`.

The exact-rational `f_8` artifact validates a weak generalized score. Together
with strictification it proves existence of a native three-head score, but the
artifact itself should not be described as a literal exact native certificate.

### R33

The polarization telescoping and direction-merging argument is valid after the
same cleanup repair. The orbit bounds `3,4,5,5,6` are theorem-grade upper bounds.

### R34.3: Waring barrier

The sentence that every realization literally factors through an ordinary
Waring decomposition is too strong because head numerators may vary. A rigorous
replacement uses border rank.

The highest homogeneous payload of one polynomial-chart head is

```text
M_j Z_j^k,
```

which lies in a tangent space to the Veronese and has border Waring rank at most
two. A generic product of `k+1` independent linear forms is linearly equivalent
to the squarefree monomial `x_0...x_k`, whose cactus rank, border rank, and Waring
rank equal `2^k`. Therefore an exact or border polynomial-payload realization
needs

```text
r >= 2^(k-1).
```

This is an exponential barrier for the Order-Lemma/polynomial-chart method. It
is not a lower bound on `H*(f)`, because sign equivalence on the Boolean cube may
use a different polynomial and cross-term cancellations.

## 6. Correct multi-chart normal form

Heads must be grouped by projective classes of their **slope vectors**, not by
proportionality of the full affine coefficient vectors. In a reduced chart,

```text
B_{nu,a}(x) = kappa_{nu,a}(W_nu(x)-lambda_{nu,a}).
```

After merging equal poles, every `H`-head score has the form

```text
S(x) = c + sum_nu P_nu(x,W_nu(x)) / D_nu(W_nu(x)),
```

where:

- `D_nu(z) = prod_a (z-lambda_{nu,a})` is squarefree;
- all roots are real and lie strictly outside
  `[min_X W_nu, max_X W_nu]`;
- `deg_W P_nu < deg D_nu`;
- the coefficients of `P_nu` are affine in `x`;
- the head count is `sum_nu deg D_nu`.

Conversely, partial fractions recover exact heads from every such family.

R37's condition "real-rooted denominator" alone is insufficient. Repeated roots
are higher-order poles, not sums of simple heads, and roots inside the statistic
range violate positivity.

This normal form does not currently yield a polynomial converse. Same-chart
double poles split exactly when their roots differ and split in closure when
they coincide. The genuine difficulty is a product of transverse poles from
different charts. Exact multivariate partial fractions do not generally remove
that product; polynomial jets meet the border-Waring barrier; rational
approximation remains conditioning-dependent.

Theorems 193/194 do not reverse this implication: they place tangent head
patterns inside a secant relaxation and analyze blowups internal to that
relaxation, but they do not prove that every feasible secant pattern has a
bounded-head representation.

## 7. Claims that remain numerical or overstated

- R1's statement that parameter counting can *never* separate the measures is
  too categorical. The existing coarse parameter counts are of the same order
  and cannot by themselves yield the desired superpolynomial gap.
- R8 establishes only that threshold degree, the known sign-rank bridge, and
  coarse Warren counting transfer almost equally to both measures. It is not a
  theorem excluding a bespoke obstruction.
- R28's quotient-ring proof is incomplete: a nonzero element of `R[x]/(W)` need
  not be a unit. A generic UFD version may be repairable, but the stated iff
  should not be cited without a full degeneracy analysis.
- R19's phrase "proof modulo floating point" is not a proof.
- R38/R39 do **not** rigorously establish
  `H*(R_5)=POIC_2(R_5)=4`. The positive certificates prove only

  ```text
  H*(R_5) <= 4,  POIC_2(R_5) <= 4.
  ```

  The reverse inequalities are based on nonconvex solver failures. The known
  `h^{-k}` limit certificates give a concrete mechanism for such false
  negatives.
- The same warning applies to claimed exact lower bounds for distance shells,
  `f_8 XOR z`, and failed POIC orbit searches. A feasible strict certificate can
  be made rigorous by independent evaluation and rational exactification; a
  failed search is only evidence.

## 8. Current rigorous landscape

For the canonical definition,

```text
deg_pm(f) <= POIC_2(f) <= H*(f) <= 2^POIC_2(f)-1.
```

Additionally,

```text
H*(f) <= K binom(K+d-1,d-1)+1
```

for pool slope rank `d`, and

```text
POIC_2(f) <= 3  =>  H*(f) <= 6.
```

No general proof or counterexample to

```text
H*(f) <= poly(POIC_2(f))
```

is presently established. Existing conversions divide into two regimes:

1. conditioning-dependent rational approximation, polynomial in analytic
   condition numbers but not known to be polynomial in the budget;
2. conditioning-free polynomial/polarization conversion, exponential in the
   general pool rank and provably exponential within its exact-payload method.

A successful general converse therefore needs a genuinely sign-theoretic
mixed-chart mechanism. One precise possible formulation is a Gordan/Farkas
dual-cone splitting theorem transporting witnesses between the first-omission
head cone and the second-omission POIC cone. No such theorem is currently in the
corpus or supplied by standard partial-fraction, Orlik--Terao, or effective
semialgebraic tools.
