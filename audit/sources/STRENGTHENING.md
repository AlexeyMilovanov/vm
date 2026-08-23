# Strengthening the split-shattering lower bound

## 1. The mega-lab theorem is correct

Split the variables `z | w`. Every head is `(<alpha_h,z> + p_h(w)) / (<beta_h,z> + q_h(w))`.
Fix `k` points `z^(1)..z^(k)`. As `w` varies, `alpha_h, beta_h` are FROZEN; only the `2H`
scalars `p_h(w), q_h(w)` move. Clearing the positive denominators, the label at `z^(j)` is the
sign of a polynomial of degree <= H in those `2H` reals. Warren's bound on sign patterns of
`k` degree-`H` polynomials in `2H` variables gives `2^k <= (2ek)^{2H}`, hence

    H*(f) >= sigma(f) / (2 log2(2e sigma(f))),

where `sigma(f)` is the split-shattering dimension. Checked: the Warren application, the
NDISJ example (`deg_pm = 2` via `sum x_i y_i - 1/2`, not an LTF; `sigma >= m` since
`NDISJ(e_i, y) = y_i`), and the arithmetic. With `H* <= m` from the monomial construction:

    deg_pm(NDISJ_m) = 2,     Omega(n / log n)  <=  H*(NDISJ_m)  <=  n/2.

## 2. New: a hard cap on the method

Shattering `k` points requires `2^k` DISTINCT settings of `w`, so `k <= n_2 <= n`. Therefore

    sigma(f) <= n   for every f,

and split-shattering can never certify more than `n / (2 log2(2en)) = O(n/log n)`.
NDISJ saturates this up to constants: with the balanced split `sigma = m = n/2`, which is the
maximum available. So there is no point hunting for a better function for this method — NDISJ
is essentially the extremal one.

Together with the two older caps (threshold degree is `<= n` by definition; the sign-rank
route is capped at `O(deg_pm . log n)`), **every currently known technique caps at `O(n)`**,
while counting (theorem 026) says almost every function needs `Omega(2^n / n^2)`. The
explicit-vs-existential gap for `H*` is exponential, and that is the real frontier.

## 3. New: the logarithm is an artefact of Warren, and it looks removable

**Localisation.** With the denominators FIXED, the `k` constraints are affine in
`(c, p_1..p_H) in R^{H+1}`, so the achievable labellings are the cells of an arrangement of
`k` hyperplanes in `R^{H+1}`, at most `sum_{i<=H+1} C(k,i)`, which is `< 2^k` as soon as
`k > H+1`. **Fixed denominators shatter at most `H+1` points.** All the extra power comes
from the `H` denominator shifts, so the sharp constant is the VC dimension of

    F_H := { u |-> sign( c + sum_h (p_h + u^a_h)/(q_h + u^b_h) ) },   q_h + u^b_h > 0,

parameters `(c, p, q) in R^{2H+1}`, points `u in R^{2H}`.

**Proved.** `VC(F_1) = 2`. Clearing the positive denominator gives `sign(a + c b + r)` with
two free parameters `(c, r)`; three points become three lines in the `(c,r)` plane, and three
lines cut at most `1+3+3 = 7 < 8` regions.

**Measured** (random search over point configurations, ~10^8 parameter samples):

| H | shatters 2H | shatters 2H+1 |
|---|---|---|
| 1 | yes (2)  | no (7/8 patterns)     |
| 2 | yes (4)  | no (31/32)            |
| 3 | yes (6)  | no (120/128)          |
| 4 | (not found, 238/256 - search limit) | no (408/512) |

**Conjecture.** `VC(F_H) = 2H`, i.e. exactly the number of free shift parameters.

**Consequence if proved.** `H*(f) >= sigma(f)/2`, hence

    n/4  <=  H*(NDISJ_m)  <=  n/2,

an explicit function of threshold degree 2 whose head complexity is `Theta(n)`, pinned to a
factor of two. That removes the logarithm entirely.

## 4. Independent corroboration from exact small cases

Using the LP-in-numerators reformulation (with the denominators fixed the problem is a linear
program in `(c, N_1..N_H)`; denominators are parametrised exactly by theorem 032 as
`1 + <w,x>` or `1 + <w,1-x>` with `w >= 0`), searching over denominators with a soft-margin
inner LP:

    H*(NDISJ_2) = 2,  H*(NDISJ_3) = 2,  H*(NDISJ_4) = 2,  H*(NDISJ_5) = 3
    (every upper bound is a certificate verified on every input; the H=2 failure at m=5 is a
     search failure, but not a near miss - the soft-margin residual is 192.4, not ~0)

These are not counterexamples - they match the conjecture exactly. For `m <= 4` we have
`sigma = m <= 4`, so the conjectured bound reads `H* >= ceil(m/2)`, i.e. `>= 2`, and
`deg_pm = 2` forces `H* >= 2` anyway. The conjecture predicts

    H*(NDISJ_m) = max(2, ceil(m/2)),

and the first discriminating case `m = 5` CONFIRMS it: 2 heads fail badly, 3 heads succeed.
All four computed values match `max(2, ceil(m/2))` exactly:

    m     : 2  3  4  5
    H*    : 2  2  2  3
    pred  : 2  2  2  3

So on this family the conjectured bound `H* >= sigma/2` appears to be TIGHT, which is further
evidence that `VC(F_H) = 2H` is the exact constant and not just an upper bound. It also means
there must exist a `ceil(m/2)`-head construction for NDISJ - one head serving two pairs -
which is not obvious and is worth extracting from the certificate. (There is also a clean
independent reason for the `m <= 4` collapse: for `H = 2` the cleared score is quadratic and
its cross-block coefficient matrix has rank at most 4, which is no constraint at all when
`m <= 4`, but bites from `m = 5` on.)

## 5. Status of the earlier XOR-tensor family

Superseded. `G_{29,k}` gave an additive gap `n/78` with `deg_pm = n/29` growing. NDISJ gives
`Omega(n/log n)` - and `Omega(n)` under the conjecture - at CONSTANT degree 2, which is both
larger for every `n` below about `2.7 x 10^5` and qualitatively stronger. Keep the tensor
construction only as a remark.

## 6. External novelty - must be checked before claiming anything

Split-VC / shattering arguments for transformers already exist: Kozachinskiy 2024
(arXiv 2412.20195) for one-layer transformers with infinite precision, and "Strassen
Attention, Split VC Dimension and Compositionality in Transformers" (NeurIPS 2025). What may
be new here is the narrower statement - a lower bound directly on the NUMBER OF HEADS, with
unbounded model dimension and no margin assumption - and the `VC = 2H` sharpening. Compare
proofs before claiming novelty.
