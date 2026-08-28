# K4 sorry-closure plan

Date: 2026-08-28
Repository: /home/lesha/vm
Target file: HeadComplexity/Separations/EightBitHammingThreshold.lean
Status: revised after three independent Gemini audits

## 1. Exact scope and acceptance criteria

The current target file has exactly two source-level sorries:

1. the final part of normalized_k4_probabilities;
2. the body of k4_choiceCone_allocation.

The task is to close both without changing their public statements and without weakening any
downstream theorem. The final patch must not introduce axioms, unsafe declarations, admit,
native_decide, maxHeartbeats/maxRecDepth overrides, or new sorries. Existing unrelated dirty
files under pipeline/ and pipeline_runs/ must remain untouched.

Completion means all of the following:

- normalized_k4_probabilities has a kernel-checked proof;
- k4_choiceCone_allocation has a kernel-checked proof;
- the target file contains no sorry or admit;
- a direct single-process compile of the target file succeeds;
- the relevant lake target succeeds;
- the final diff has been inspected for statement drift and accidental unrelated changes;
- only then is the Lean source committed and pushed.

## 2. Current trusted infrastructure

The following pieces are already present immediately before the two remaining sorries.

- exists_three_interval_sum: constructs three numbers inside intervals with prescribed sum.
- triangle_edge_allocation: realizes three vertex row masses by oriented triangle edges.
- k4_edge_allocation: realizes six undirected K4 capacities by a nonnegative directed matrix A
  with zero diagonal and prescribed row sums, assuming nonnegativity, total balance, all six
  pair cuts, and all four triple cuts.
- productProbability_mass: the product distribution on all pick maps has mass one.
- productProbability_expect_coordinate: computes one coordinate expectation.
- productProbability_choiceFunctional: computes the expectation of choiceFunctional.
- choiceCone_of_probabilities: converts a nonnegative row-stochastic zero-diagonal matrix p and
  six pair identities into the required nonnegative choice-cone representation.
- weighted_two_distance_le: proves the two-coordinate distance inequality used for c_ij >= 0.

Most of this infrastructure has compiled in earlier checkpoints. The current uncommitted source
must nevertheless be recompiled after the new proof is complete. In particular, the six current
pair-cut proofs use large-context nlinarith calls and are known to be a performance risk.

The intended dependency graph is:

~~~text
weighted three-term Cauchy
        |
centered-coordinate bound
        |
four incident-capacity lower bounds
        |
four triple cuts -----------+
                            |
six explicit pair cuts -----+--> k4_edge_allocation
                                      |
                                A -> stochastic p
                                      |
                         normalized_k4_probabilities
                                      |
center / variance / sqrt normalization
                                      |
                         k4_choiceCone_allocation
                                      |
                         existing downstream theorem
~~~

## 3. Mathematical invariant for the normalized lemma

Write

~~~text
v_i = 1 / q_i
S   = v_0 + v_1 + v_2 + v_3
d_ij = (y_i - y_j)^2.
~~~

The hypotheses become

~~~text
sum_i v_i y_i = 0,
sum_i v_i y_i^2 = 1,
v_i > 0,
q_i v_i = 1.
~~~

Define the six undirected capacities by

~~~text
c_ij = (v_i v_j / 2) * (q_i + q_j - d_ij)
     = ((v_i + v_j) - v_i v_j d_ij) / 2.
~~~

The second equality follows from

~~~text
v_i v_j (q_i + q_j) = v_i + v_j.
~~~

The proof must establish exactly the hypotheses consumed by k4_edge_allocation.

### 3.1 Capacity nonnegativity

For each pair i,j, use weighted_two_distance_le on the two corresponding energy terms:

~~~text
v_i v_j d_ij <= v_i + v_j
              = v_i v_j (q_i + q_j).
~~~

Since v_i v_j > 0, this gives d_ij <= q_i + q_j, hence c_ij >= 0.
This part is already implemented.

### 3.2 Total capacity

The weighted variance identity is

~~~text
sum_{i<j} v_i v_j (y_i-y_j)^2
  = S * sum_i v_i y_i^2 - (sum_i v_i y_i)^2
  = S.
~~~

Every v_i occurs in three pair-base terms, so

~~~text
sum_{i<j} c_ij
 = (1/2) * (3S - S)
 = S.
~~~

This is already implemented as hvariance followed by htotal.

### 3.2a Canonicalize the capacities before cut proofs

An independent Lean 4.31 audit found a lower-risk internal representation than the current
q-containing lets. Adopt it as the primary implementation, while preserving the theorem
statement.

After hd_ijv has established

~~~text
v_i*v_j*(y_i-y_j)^2 <= v_i+v_j,
~~~

define the six capacities directly by

~~~lean
set c₀₁ : Real :=
  (v₀ + v₁ - v₀*v₁*(y 0-y 1)^2)/2 with hc₀₁_def
~~~

and analogously for the other five edges. This is definitionally equal, using q_i*v_i=1, to the
old expression

~~~text
(v_i*v_j/2)*(q_i+q_j-(y_i-y_j)^2),
~~~

but it removes q from every cut calculation. With this representation, the six hb_ij identities,
the six conversions from hd_ijv to q-distance bounds, and the six timeout-prone pair nlinarith
calls are no longer needed after the capacity definitions.

Use two isolated helpers whose shapes were checked under the current Lean 4.31 toolchain:

~~~lean
private theorem canonical_capacity_nonneg
    (vi vj d : Real) (h : vi*vj*d <= vi+vj) :
    0 <= (vi+vj-vi*vj*d)/2 :=
  div_nonneg (sub_nonneg.mpr h) (by norm_num)

private theorem canonical_capacity_le
    (vi vj d : Real)
    (hvi : 0 <= vi) (hvj : 0 <= vj) (hd : 0 <= d) :
    (vi+vj-vi*vj*d)/2 <= vi+vj := by
  have hterm : 0 <= vi*vj*d :=
    mul_nonneg (mul_nonneg hvi hvj) hd
  linarith only [hvi, hvj, hterm]
~~~

Use set ... with rather than global dsimp so that v_i does not zeta-expand back to 1/q_i.

Reprove htotal after rewriting hc_01_def,...,hc_23_def. Once S is exposed locally, the goal is
the half of three vertex-base sums minus hvariance. A single small linear_combination on
hvariance closes it. Keep the already proved hvariance itself unchanged.

### 3.3 Pair cuts

k4_edge_allocation asks c_ij <= v_i+v_j. With canonical capacities, instantiate
canonical_capacity_le six times using hv_i.le, hv_j.le, and sq_nonneg. This proves the stronger
intermediate bound c_ij <= (v_i+v_j)/2 and completely removes the current six large-context
nlinarith calls.

If rewriting a set equality is awkward, use rw [hc_ij_def] at the individual goal. Do not unfold
all six capacities at once except in htotal.
### 3.4 Triple cuts reduce to vertex incidence

Let

~~~text
C_i = sum_{j != i} c_ij.
~~~

By total balance, the triple cut on the three vertices other than i is equivalent to

~~~text
v_i <= C_i.
~~~

Indeed,

~~~text
sum(capacities internal to complement(i))
  = S - C_i
  <= S - v_i
  = sum_{j != i} v_j.
~~~

Thus it is enough to prove four incident-capacity lower bounds.

### 3.5 Three-term weighted Cauchy helper

Use an exact sum-of-squares identity rather than nonlinear automation in a large context.

Proposed helper statement:

~~~lean
private theorem weighted_three_cauchy
    (a b c x y z : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) :
    (a*x + b*y + c*z)^2
      <= (a+b+c) * (a*x^2 + b*y^2 + c*z^2) := by
  have hab : 0 <= a*b*(x-y)^2 :=
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  have hac : 0 <= a*c*(x-z)^2 :=
    mul_nonneg (mul_nonneg ha hc) (sq_nonneg _)
  have hbc : 0 <= b*c*(y-z)^2 :=
    mul_nonneg (mul_nonneg hb hc) (sq_nonneg _)
  calc
    (a*x + b*y + c*z)^2
        <= (a*x + b*y + c*z)^2
          + (a*b*(x-y)^2 + a*c*(x-z)^2 + b*c*(y-z)^2) := by
            exact le_add_of_nonneg_right (add_nonneg (add_nonneg hab hac) hbc)
    _ = (a+b+c) * (a*x^2 + b*y^2 + c*z^2) := by ring
~~~

The explicit add_nonneg proof avoids asking positivity to rediscover named facts.
This helper must compile in isolation before it is used.

### 3.6 Centered-coordinate bound

Package the complement-Cauchy calculation into a helper with a small context.

Proposed statement:

~~~lean
private theorem weighted_centered_coordinate_bound
    (a b c d xa xb xc xd : Real)
    (hb : 0 <= b) (hc : 0 <= c) (hd : 0 <= d)
    (hmean : a*xa + b*xb + c*xc + d*xd = 0)
    (henergy : a*xa^2 + b*xb^2 + c*xc^2 + d*xd^2 = 1) :
    (a+b+c+d) * a * xa^2 <= b+c+d := by
  have hcs := weighted_three_cauchy b c d xb xc xd hb hc hd
  have hm : b*xb + c*xc + d*xd = -a*xa := by
    linarith only [hmean]
  have he : b*xb^2 + c*xc^2 + d*xd^2 = 1-a*xa^2 := by
    linarith only [henergy]
  rw [hm, he] at hcs
  have hrearrange :
      (b+c+d)*(1-a*xa^2) - (-a*xa)^2
        = (b+c+d) - (a+b+c+d)*a*xa^2 := by ring
  have hnonneg :
      0 <= (b+c+d) - (a+b+c+d)*a*xa^2 := by
    calc
      0 <= (b+c+d)*(1-a*xa^2) - (-a*xa)^2 :=
        sub_nonneg.mpr hcs
      _ = (b+c+d) - (a+b+c+d)*a*xa^2 := hrearrange
  exact sub_nonneg.mp hnonneg
~~~

The exact ring rearrangement is primary: two Gemini auditors independently flagged nonlinear
automation on the square of a negated product as an avoidable elaboration risk.

Instantiate the helper four times. For vertices 1,2,3, provide reordered hmean and henergy
facts proved by ring or linarith only; do not expose all other local hypotheses to automation.
The resulting bounds are

~~~text
S*v_0*y_0^2 <= v_1+v_2+v_3,
S*v_1*y_1^2 <= v_0+v_2+v_3,
S*v_2*y_2^2 <= v_0+v_1+v_3,
S*v_3*y_3^2 <= v_0+v_1+v_2.
~~~

### 3.6a Preferred direct vertex-bound helper

The primary route should skip four separate incident-distance and incident-capacity identities.
Use one scalar lemma that directly returns a vertex incident-capacity lower bound. The crucial
linear_combination sign and an equivalent version of this helper were checked in Lean 4.31.

~~~lean
private theorem normalized_vertex_bound
    (a b c d x y z t : Real)
    (hb : 0 <= b) (hc : 0 <= c) (hd : 0 <= d)
    (hm : a*x + b*y + c*z + d*t = 0)
    (he : a*x^2 + b*y^2 + c*z^2 + d*t^2 = 1) :
    a <= ((a+b)-a*b*(x-y)^2)/2
      + ((a+c)-a*c*(x-z)^2)/2
      + ((a+d)-a*d*(x-t)^2)/2 := by
  have hcs_le := weighted_three_cauchy b c d y z t hb hc hd
  have hcs :
      0 <= (b+c+d)*(b*y^2+c*z^2+d*t^2)
        - (b*y+c*z+d*t)^2 :=
    sub_nonneg.mpr hcs_le
  have hid :
      (((a+b)-a*b*(x-y)^2)/2
        + ((a+c)-a*c*(x-z)^2)/2
        + ((a+d)-a*d*(x-t)^2)/2) - a
        = ((b+c+d)*(b*y^2+c*z^2+d*t^2)
          - (b*y+c*z+d*t)^2)/2 := by
    linear_combination
      -((a+b+c+d)/2)*he
      + ((a*x+b*y+c*z+d*t)/2)*hm
  have hdiff :
      0 <= (((a+b)-a*b*(x-y)^2)/2
        + ((a+c)-a*c*(x-z)^2)/2
        + ((a+d)-a*d*(x-t)^2)/2) - a := by
    rw [hid]
    exact div_nonneg hcs (by norm_num)
  linarith only [hdiff]
~~~

Apply it literally for vertex 0. For vertices 1,2,3 first record permuted mean and energy
equalities with linear_combination or ring. Then use convert ... using 1 followed by ring; this
handles the harmless reversal between (y_i-y_j)^2 and (y_j-y_i)^2.

Rewrite each conclusion using hc_01_def,...,hc_23_def to obtain hinc_0,...,hinc_3. This route
proves all vertex cuts without exposing q, S, inverses, or unrelated pair hypotheses to
nonlinear automation.

The expanded identities in Section 3.7 remain a diagnostic fallback only.
### 3.7 Incident-distance and incident-capacity identities

For each vertex i prove

~~~text
sum_{j != i} v_j (y_i-y_j)^2 = 1 + S*y_i^2.
~~~

For i=0, the recommended proof shape is

~~~lean
have hdist0 :
    v1*(y 0-y 1)^2 + v2*(y 0-y 2)^2 + v3*(y 0-y 3)^2
      = 1 + S*(y 0)^2 := by
  dsimp [S]
  calc
    _ = (v0*y 0^2 + v1*y 1^2 + v2*y 2^2 + v3*y 3^2)
        + (v0+v1+v2+v3)*y 0^2
        - 2*y 0*(v0*y 0+v1*y 1+v2*y 2+v3*y 3) := by ring
    _ = 1 + (v0+v1+v2+v3)*y 0^2 := by
      rw [henergy, hmean]
      ring
~~~

Repeat by permutation, or first make a generic four-weight helper if duplication becomes
error-prone. Four explicit facts are acceptable because Fin 4 is fixed and they simplify later
linear_combination calls.

Then prove

~~~text
C_i = (S + v_i - S*v_i*y_i^2)/2.
~~~

For i=0, rewrite only hc_01_def, hc_02_def, hc_03_def and then hdist0. Expose S locally and
finish by ring. This canonical-capacity fallback must not refer to the deleted hb_ij facts.
Repeat by permutation for the other vertices. If the old q-containing capacity definitions are
temporarily retained during migration, re-prove hb_ij locally in that intermediate slice rather
than making the final fallback depend on them.

Finally, the centered-coordinate bound gives

~~~text
v_i <= (S + v_i - S*v_i*y_i^2)/2 = C_i.
~~~

This should need only rw of the incident identity followed by linarith only on the corresponding
coordinate bound.

### 3.8 Derive the four triple cuts

Use htotal and the incident lower bounds, not fresh nonlinear proofs.

For example:

~~~text
c_01+c_02+c_12
 = total capacities - (c_03+c_13+c_23)
 <= S-v_3
 = v_0+v_1+v_2.
~~~

The mapping is:

- ht_012 uses the incident lower bound at vertex 3;
- ht_013 uses the incident lower bound at vertex 2;
- ht_023 uses the incident lower bound at vertex 1;
- ht_123 uses the incident lower bound at vertex 0.

Each should be a small linarith only invocation with htotal and exactly one incident bound.
If linarith does not unfold S, add dsimp [S] at the local target, not globally.

### 3.9 Invoke k4_edge_allocation

Call k4_edge_allocation with:

- capacities c_01,...,c_23;
- row masses v_0,...,v_3;
- hc_ij;
- nonnegative forms hv_i.le;
- htotal;
- the six pair cuts;
- the four triple cuts.

Destructure the result as

~~~text
A, hA_nonneg, hA_diag, hA_row,
hA_01, hA_02, hA_03, hA_12, hA_13, hA_23.
~~~

At this point no probability or choiceFunctional algebra should be mixed into the cut proof.

### 3.10 Convert A to a stochastic matrix p

Define

~~~text
p i j = q i * A i j.
~~~

Then:

- p is nonnegative because q_i > 0 and A is nonnegative;
- p i i = 0 from hA_diag;
- row sum p i j = q_i * v_i = 1 from hA_row and hqv_i.

For the row proof, use rw [← Finset.mul_sum] explicitly to factor q i, then use hA_row.
A final fin_cases i reduces the vector literal ![v_0,v_1,v_2,v_3] and selects hqv_0,...,hqv_3.
Do not rely on simp to factor the sum, and do not simp all local hypotheses.


### 3.11 Generic edge-to-probability helper

Avoid six independent field_simp or nonlinear calls. Use the canonical-capacity version below;
its proof shape was checked under Lean 4.31.

~~~lean
private theorem probability_pair_of_edge
    (qi qj vi vj aij aji d : Real)
    (hqi : qi*vi = 1) (hqj : qj*vj = 1)
    (hedge : aij+aji = (vi+vj-vi*vj*d)/2) :
    qi+qj - 2*(qi*(qj*aji) + qj*(qi*aij)) = d := by
  have hprod : qi*qj*vi*vj = 1 := by
    calc
      qi*qj*vi*vj = (qi*vi)*(qj*vj) := by ring
      _ = 1 := by rw [hqi, hqj]; ring
  have hsum : qi*qj*(vi+vj) = qi+qj := by
    calc
      qi*qj*(vi+vj) = (qi*vi)*qj + (qj*vj)*qi := by ring
      _ = qi+qj := by rw [hqi, hqj]; ring
  have hscaled :
      2*(qi*qj)*(aij+aji) = qi+qj-d := by
    calc
      2*(qi*qj)*(aij+aji)
          = qi*qj*(vi+vj-vi*vj*d) := by rw [hedge]; ring
      _ = qi*qj*(vi+vj) - (qi*qj*vi*vj)*d := by ring
      _ = qi+qj-d := by rw [hsum, hprod]; ring
  calc
    qi+qj - 2*(qi*(qj*aji) + qj*(qi*aij))
        = qi+qj - 2*(qi*qj)*(aij+aji) := by ring
    _ = d := by rw [hscaled]; ring
~~~

Instantiate it for the six edges with d equal to the corresponding square. Rewrite p with its
set equality and supply hA_ij after rewriting the matching hc_ij_def. This completes
normalized_k4_probabilities.

## 4. Proof of k4_choiceCone_allocation

The normalized lemma handles centered weighted energy one. The final theorem has arbitrary z,
so use explicit centering and one variance split.

### 4.1 Explicit scalar setup

Reuse

~~~text
v_i = 1/q_i,
S = v_0+v_1+v_2+v_3 > 0.
~~~

Define

~~~text
m = (v_0 z_0 + v_1 z_1 + v_2 z_2 + v_3 z_3) / S,
x_i = z_i - m,
V = v_0 x_0^2 + v_1 x_1^2 + v_2 x_2^2 + v_3 x_3^2.
~~~

Prove immediately, in small contexts:

- each v_i > 0;
- S > 0 and S != 0;
- weighted center: sum_i v_i x_i = 0;
- each v_i*x_i^2 >= 0;
- V >= 0.

Use explicit Fin 4 sums rather than abstract sum API. For the center identity, unfold m and x only
inside that proof, field_simp with S != 0, then ring. Do not unfold q inverses in later steps.

Split with by_cases hV0 : V = 0.

### 4.2 Zero-variance branch

Expand V into its four nonnegative summands. From V=0 and nonnegativity derive each

~~~text
v_i*x_i^2 = 0.
~~~

Use four small linarith only calls, each supplied only hV0 and the four term nonnegativity facts.
Since v_i > 0, derive x_i^2=0 and then x_i=0. Prefer mul_eq_zero followed by the nonzero proof;
Use sq_eq_zero_iff as the primary square-elimination API; rewrite pow_two and use
mul_self_eq_zero only as a fallback.

Therefore every z_i equals m, so all six pairwise squared distances vanish.

Choose

~~~text
w pick = 0.
~~~

Then nonnegativity is simp, the support condition is vacuous because w pick != 0 is impossible,
and the final identity is simp using the six zero-distance facts. This branch must not call
normalized_k4_probabilities or construct p.

### 4.3 Positive-variance branch

From V >= 0 and V != 0 obtain V > 0. Define

~~~text
r = Real.sqrt V,
y_i = x_i / r.
~~~

Record separately:

~~~text
0 < r,
r != 0,
r^2 = V.
~~~

Use Real.sqrt_pos.2 and Real.sq_sqrt. Avoid repeated calls to positivity and repeated unfolding.

Prove normalized mean:

~~~text
sum_i v_i y_i = (sum_i v_i x_i)/r = 0.
~~~

Prove normalized energy:

~~~text
sum_i v_i y_i^2 = V/r^2 = 1.
~~~

For both, expand Fin 4 once, then use ring/field_simp with r != 0 and the previously named center,
variance, and r^2 facts. Convert v_i back to 1/q_i only at the boundary where
normalized_k4_probabilities is invoked.

For the energy algebra, prefer the following isolated helper; its exact proof was checked in the
current toolchain. Note that field_simp closes the goal, so do not append a redundant ring tactic.

~~~lean
private theorem div_sq_sum_four
    (a b c d x y z t r : Real) (hr : r ≠ 0) :
    a*(x/r)^2 + b*(y/r)^2 + c*(z/r)^2 + d*(t/r)^2
      = (a*x^2 + b*y^2 + c*z^2 + d*t^2)/r^2 := by
  field_simp [hr]
~~~


### 4.4 One generic scale-back fact

Prove for arbitrary i,j : Fin 4:

~~~text
V * (y i-y j)^2 = (z i-z j)^2.
~~~

After unfolding y and x, replace V by r^2, field_simp using r != 0, and ring. Center m cancels.
A generic quantified fact is preferable to six duplicate sqrt proofs.

Use this checked scalar helper and instantiate it for arbitrary i,j:

~~~lean
private theorem sqrt_scaled_sub
    (V r m zi zj : Real) (hr2 : r^2 = V) (hrne : r ≠ 0) :
    V*(((zi-m)/r)-((zj-m)/r))^2 = (zi-zj)^2 := by
  rw [← hr2]
  field_simp [hrne]
  ring
~~~

After unfolding the definition of y, sqrt_scaled_sub supplies the generic hscale fact.

### 4.5 Obtain p and scale its six equations

Invoke normalized_k4_probabilities q hq y with the normalized mean and energy. Destructure p,
its nonnegativity/diagonal/row facts, and six normalized pair equations.

For each pair, prove the equation required by choiceCone_of_probabilities with W=V:

~~~text
V*(q_i+q_j) - 2*V*(q_i*p j i + q_j*p i j)
  = V*((q_i+q_j)-2*(q_i*p j i+q_j*p i j))
  = V*(y_i-y_j)^2
  = (z_i-z_j)^2.
~~~

The first and last transformations are ring and the generic scale-back fact; the middle rewrite
uses exactly one normalized pair equation. No field_simp or nlinarith is needed here.

### 4.6 Final composition

Call choiceCone_of_probabilities with:

- q;
- W = V;
- the six original squared distances of z;
- p;
- V >= 0;
- p nonnegative, zero diagonal, row stochastic;
- the six scaled equations.

Its conclusion is definitionally the conclusion of k4_choiceCone_allocation, modulo harmless
association of the six subtractions. Finish with exact or simpa only; do not unfold
choiceFunctional again.

## 5. Lean implementation order and compile gates

Do not write the whole proof and then run the four-gigabyte file. Use these gates.

### Gate A: canonical capacities and pair cuts

1. Compile canonical_capacity_nonneg and canonical_capacity_le in a tiny stdin scratch.
2. Replace the six q-containing capacity lets by set definitions in canonical form.
3. Delete or bypass the obsolete hb_ij and q-distance conversion block.
4. Reprove capacity nonnegativity, htotal, and all six pair cuts.
5. Compile an isolated normalized prefix through htotal and the pair cuts.
6. Do not proceed while this slice has a timeout or syntax error.

### Gate B: complement Cauchy

1. Add weighted_three_cauchy.
2. Add normalized_vertex_bound; retain weighted_centered_coordinate_bound only if useful.
3. Compile the scalar helpers in a tiny stdin scratch.
4. Test all four vertex permutations with convert ... using 1 and ring.

### Gate C: cuts and allocation

1. Rewrite the four normalized_vertex_bound results with hc_ij_def.
2. Add the four triple cuts using htotal and the omitted vertex bound.
3. Invoke k4_edge_allocation.
4. If a generic instantiation fails, use the explicit Section 3.7 identities only for that vertex.
5. Compile the normalized theorem with a temporary sorry only after the A witness, if needed.

### Gate D: probabilities

1. Add probability_pair_of_edge and compile it alone.
2. Define p and prove nonnegativity, diagonal, and rows.
3. Close the six edge equations via the helper.
4. Confirm normalized_k4_probabilities has no sorry and slice-compiles.

### Gate E: arbitrary z

1. Implement scalar setup and center identity.
2. Close the V=0 branch.
3. Implement sqrt normalization and generic scale-back.
4. Compose with choiceCone_of_probabilities.
5. Confirm both target sorries are absent.

### Gate F: repository checks

Use a single heavy Lean process for the full target file because prior runs have approached four
GiB RSS. Jobs=2 is allowed only for small independent checks when current WSL load is low.

Recommended checks:

~~~text
rg -n "\bsorry\b|\badmit\b" HeadComplexity/Separations/EightBitHammingThreshold.lean

lake env lean HeadComplexity/Separations/EightBitHammingThreshold.lean \
  -o /tmp/EightBitHammingThreshold.olean

lake build HeadComplexity.Separations.EightBitHammingThreshold
~~~

Before each heavy check, inspect current Lean/Gemini processes and available memory. Do not kill
or interfere with unrelated WSL pipelines.

Finally inspect:

~~~text
git diff --check
git diff -- HeadComplexity/Separations/EightBitHammingThreshold.lean
git status --short
~~~

Commit only the intended Lean file and the final audited plan; leave pipeline.log, pipeline_runs,
and scripts/jules_wave2_status.py untouched.

## 6. Tactic discipline and performance rules

- Prefer ring for exact polynomial identities.
- Prefer calc for monotonicity.
- Prefer linear_combination when named equalities determine the target.
- Use linarith only or nlinarith only with the smallest explicit hypothesis set.
- Never run nlinarith against the entire normalized theorem context.
- Keep inverse facts hqv_i named; do not repeatedly field_simp all q_i inverses.
- Keep sqrt facts named; do not let simp repeatedly unfold Real.sqrt.
- Use change to expose only selected c_ij or p definitions.
- Avoid simp_all: it may unfold all six capacities and every inverse simultaneously.
- For Fin 4 row identities, fin_cases is preferable to general vector extensionality.
- If a repeated four-vertex proof is fragile, introduce a generic helper rather than copying a
  large tactic block four times.
- If a generic helper causes elaboration problems through heavy lets, use four explicit local
  facts but preserve the same small-context proof.
- Do not increase heartbeat or recursion limits. A timeout is a signal to split the lemma.

## 7. Fallbacks for known risky points

### Pair-cut timeout

Primary fix: canonical capacity definitions plus canonical_capacity_le.
Fallback: retain the old capacity definition but prove each pair cut by an explicit calc and
rewrite with hb_ij; never expose the full context to nlinarith.

### Complement-Cauchy nlinarith

Primary fix: exact sum-of-squares plus ring/sub_nonneg, as written in Sections 3.5 and 3.6.
Fallback: use the direct nonnegative-difference form three_weight_cauchy; do not return to a
large nlinarith call.

### Incident-capacity linear_combination

Primary fix: normalized_vertex_bound in canonical capacity form.
Fallback: use the explicit incident-distance and incident-capacity identities in Section 3.7,
with change exposing only the three selected capacities. Do not field_simp capacity definitions.

### Row stochasticity

Primary fix: rewrite sum(q_i*A_i_j) as q_i*sum(A_i_j), use hA_row, fin_cases.
Fallback: prove four row facts explicitly and assemble with intro i; fin_cases i.

### Edge equation elaboration

Primary fix: probability_pair_of_edge in canonical capacity form.
Fallback: inline hprod, hsum, and hscaled for one edge at a time; avoid field_simp at hA_ij.

### Center identity

Primary fix: explicit four-term formula and one field_simp using S != 0.
Fallback: multiply the desired identity by S, prove the multiplied equality by ring, and cancel
using S > 0.

### Zero variance

Primary fix: explicit four nonnegative terms and four linarith only calls.
Fallback: use a verified Finset sum_eq_zero lemma, but only after checking its exact mathlib API.

### Sqrt scaling

Primary fix: rewrite V by r^2, field_simp with r != 0, ring.
Fallback: prove x_i/r-x_j/r=(x_i-x_j)/r first, square it, then use r^2=V.

## 8. Semantic audit checklist

Before declaring success, independently verify:

1. p is indexed in the correct direction: p i j = q_i A i j.
2. In the pair equation, p j i contributes q_j A j i, so
   q_i p j i + q_j p i j = q_i q_j(A j i+A i j).
3. Every capacity contains the factor 1/2.
4. htotal has orientation row-mass sum = capacity sum expected by k4_edge_allocation.
5. Each triple cut uses the incident lower bound at the omitted vertex.
6. The Cauchy complement uses the other three vertices, not the same vertex twice.
7. V is the centered weighted energy, not the uncentered energy.
8. The zero-variance branch proves all z coordinates equal before choosing w=0.
9. In the positive branch, W passed to choiceCone_of_probabilities is V, not sqrt V.
10. The six d arguments passed to choiceCone_of_probabilities are the original z distances.
11. The support condition follows from p i i=0 and product weights exactly as already proved.
12. No downstream theorem statement changes.

## 9. Expected difficulty and work estimate

The first sorry is the main remaining proof. The mathematics is finite and explicit, but Lean
work is substantial because four cut inequalities and six edge equations must be kept out of
large nonlinear contexts. Expected new proof text is approximately 180-320 lines, depending on
how many generic helpers elaborate cleanly.

Once the normalized lemma is closed, the second sorry should require approximately 100-180 lines:
centering, a zero-variance branch, sqrt normalization, six short scaled equations, and one call
to choiceCone_of_probabilities.

There is no identified mathematical blocker. The main risks are tactic performance, let
unfolding, inverse normalization, and Real.sqrt API details. The gate structure above is designed
so each risk is detected before the full-file compile.

## 10. Questions for external auditors

Auditors should explicitly answer:

- Is c_ij nonnegative under exactly the normalized mean/energy hypotheses?
- Does the complement-Cauchy bound really imply every incident sum is at least v_i?
- Are the pair and triple cuts exactly sufficient for the already proved k4_edge_allocation?
- Is p i j = q_i A i j the correct orientation?
- Does probability_pair_of_edge have every q factor in the correct place?
- Is the V=0 branch complete with no hidden need for normalized probabilities?
- Does V times the normalized equation match the six hypotheses of choiceCone_of_probabilities?
- Can any helper be simplified to reduce Lean elaboration or timeout risk?
- Is any proposed Lean API or tactic shape likely wrong in Lean 4.31/mathlib?

## 11. External audit outcome and adopted changes

Three initial independent Gemini 3.1 Pro High auditors received an isolated copy of this plan in
read-only plan mode. They were deliberately not given access to the repository.
A fourth Gemini red-team auditor then inspected the revised plan, again from the isolated
read-only copy.

Verdicts:

- mathematical capacity/cut audit: ACCEPT;
- Lean 4.31 feasibility/performance audit: REVISE;
- end-to-end normalization/scaling audit: ACCEPT.
- revised-plan consistency red-team: REVISE.

No auditor found a false statement, missing hypothesis, sign error, factor-of-two error,
circular dependency, or mathematical obstruction.

The REVISE verdict concerned proof engineering. The final plan adopts every material point:

- explicit rewrites replace the fragile scalar linear_combination in the old pair helper;
- weighted_three_cauchy uses named add_nonneg facts rather than positivity;
- exact ring/sub_nonneg is primary for the complement-Cauchy rearrangement;
- the row proof explicitly uses the reverse Finset.mul_sum rewrite;
- sq_eq_zero_iff is primary in the zero-variance branch;
- selected capacities must be exposed with change or their set equalities before any remaining
  linear_combination call.

A separate source-aware Lean audit additionally tested the canonical-capacity helpers,
normalized_vertex_bound, probability_pair_of_edge, and the sqrt/division helper shapes. Its
stronger recommendation—to remove q from all cut calculations—was adopted in Sections 3.2a,
3.6a, and 3.11.

The final red-team found three concrete plan defects, all corrected before this version:

- Real nonzero hypotheses in Lean snippets now use propositional ≠ rather than boolean !=;
- the Section 3.7 fallback no longer references hb_ij facts removed by canonicalization;
- canonical_capacity_le uses a small linarith only proof instead of relying on a guessed
  division-order lemma name.
