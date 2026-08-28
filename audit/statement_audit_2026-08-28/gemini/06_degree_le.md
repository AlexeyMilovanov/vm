VERDICT: MISMATCH

1. LITERAL LEAN MEANING
- `computableWithHeadsN` (`HeadComplexity/Model/Head.lean:290`) asserts that there exist parameters such that the sum of the heads' attention updates, linearly projected by a vector `w`, is strictly greater than `τ` if and only if `f(x) = true`.
- `SignRepresents` (`HeadComplexity/Polynomial/ThresholdDegree.lean:34`) states that a polynomial `P` sign-represents `f` on the cube if `0 < P(x) ↔ f(x) = true`.
- `ThresholdDegLE f H` (`HeadComplexity/Polynomial/ThresholdDegree.lean:38`) asserts there exists a polynomial of total degree `≤ H` satisfying `SignRepresents`.
- `signReprDegLe_of_computableWithHeadsN` (`HeadComplexity/Polynomial/ModelToPolynomial.lean:178`) and its alias `degree_le_of_computableWithHeadsN` (`HeadComplexity/Results/ThresholdDegree.lean:17`) prove that `H`-head computability implies `ThresholdDegLE f H`. They do this by directly clearing the positive denominators from the raw score `U(x) - τ`.

2. INTENDED MEANING
- The model computes `f(x) = 1 \iff w^T r(x) > \tau`, where `r(x)` includes a fixed query residual skip connection (`model.md:95`).
- A polynomial **sign-represents** `f` if it is strictly positive when `f(x)=1` AND strictly negative (`P(x) < 0`) when `f(x)=0` (`006_threshold_degree_head_complexity_bound.md:13-19`).
- Theorem 1 explicitly constructs a shifted threshold `τ'` to achieve this strict sign separation before clearing denominators, deliberately avoiding `P(x) = 0`.
- Theorem 3 asserts that any `H`-head classifier admits a strict threshold degree `≤ H`.

3. QUANTIFIER/EDGE-CASE CHECK
- **Constant Functions:** Handled explicitly in the math text (degree 0 is trivial). The Lean proof does not case-split; if `f` is constantly false and the maximum score equals `τ`, Lean produces a polynomial `P(x) = 0`, which satisfies Lean's weak equivalence but fails strict sign representation.
- **Budget H=0 or n=0:** Both Lean and math gracefully handle empty sums and 0-degree constant polynomials.
- **Query Skip Connection:** Lean's `computableWithHeadsN` omits the query token's skip connection from the readout score. However, this is not a mismatch: it is an explicit, deliberate simplification formally noted in `model.md:164` ("can always be absorbed into the readout threshold").

4. ANY GAP OR OVERCLAIM
- **GENUINE MISMATCH (Weakened Definition):** Lean's `SignRepresents` allows `P(x) = 0` on negative examples because `0 < P(x) ↔ f(x) = true` merely forces `P(x) ≤ 0` when `f(x) = false`. The standard mathematical definition of threshold degree explicitly demands strict separation (`P(x) < 0`).
- By entirely skipping the threshold-shifting step (Theorem 1 in the math source), the polynomial constructed in `signReprDegLe_of_computableWithHeadsN` simply subtracts the original `τ`. This polynomial may evaluate exactly to `0` on negative examples, meaning Lean has inadvertently proven a weaker bound for "PTF degree with zeroes allowed" rather than true threshold degree.

5. RECOMMENDED ACTION
- Fix `SignRepresents` in `HeadComplexity/Polynomial/ThresholdDegree.lean:34` to require strict signs: `∀ x, if f x = true then 0 < eval ... P else eval ... P < 0`.
- Formalize Theorem 1 (threshold shifting) to produce a `τ'` that strictly separates positive and negative examples.
- Update `signReprDegLe_of_computableWithHeadsN` in `HeadComplexity/Polynomial/ModelToPolynomial.lean:178` to use this shifted `τ'` so the cleared polynomial strictly avoids `0`.
