VERDICT: MATCH

1. LITERAL LEAN MEANING
- `Bank` (`Bank.lean:117`): Defined noncomputably as the minimum natural number `H` such that there exists a family of `H` affine denominators (which are strictly positive on the cube and have identically oriented, strictly nonzero slopes) whose affine-numerator quotient spaces span the full space of functions `Cube n → ℝ`.
- `HStar_le_Bank` (`Bank.lean:209`): For every Boolean function `f` on `n` variables, its fractional complexity `HStar n f` is bounded above by `Bank n`.
- `bank_dimension_bound` (`Bank.lean:384`): For any `n`, the affine dimension inequality `2^n ≤ 1 + n * Bank n` holds.
- `bank_lower_bound` (`Bank.lean:389`): For any `n ≥ 1`, the explicit integer division `((2^n - 1) + (n - 1)) / n` is bounded above by `Bank n`.
- `bank_pow_two` (`Bank.lean:435`): For any `m ≥ 1`, `Bank (2^m) = 2^(2^m) / 2^m`.
- `bank_one` (`Bank.lean:502`): `Bank 1 = 1`.

2. INTENDED MEANING
The intended mathematical meaning from `branch-b-constant.md` and `POIC2_TYPICALITY_3H_SPRINT_2026-08-26_RESULTS.md` defines `Bank(n)` as the minimum size of a "fixed strict legal denominator bank" spanning every real table. It establishes:
- `H^*(f) \le \operatorname{Bank}(n)` (Eq 2.1).
- All head spaces share the constant function, yielding the dimension bound `\lceil(2^n-1)/n\rceil \le \operatorname{Bank}(n)` (Eq 2.2).
- For power-of-two `n`, the bounds meet exactly: `\operatorname{Bank}(n) = 2^n / n` (Eq 2.3).
- At the endpoint `n=1`, `\operatorname{Bank}(1) = 1`.

3. QUANTIFIER/EDGE-CASE CHECK
- `Bank`: The definition of `StrictAdmissible` (`AffineForm.lean:76`) correctly translates "strict positive, common-orientation legal" since it enforces both strictly positive evaluations (`StrictLegal`) and strictly nonzero, common-sign slopes (`StrictlyOriented`). Quantifiers correctly range over all `v : Cube n → ℝ`. The edge case `n=0` evaluates to `Bank 0 = 1`, which is correct since one positive pole spans a 0-dimensional cube.
- `bank_lower_bound`: Lean's natural number arithmetic division truncates toward zero, making `(A + B - 1) / B` the exact integer equivalent of `\lceil A / B \rceil`. The hypothesis `1 ≤ n` safely prevents both division by zero and underflow in the subtraction `2^n - 1` when `n=0`.
- `bank_pow_two`: The condition `1 ≤ m` is crucial. If `m=0` were allowed, it would erroneously claim `Bank(2^0) = 2^1 / 1 = 2`, violating `Bank 1 = 1`. The domain matching `n = 2^m \ge 2` is exact.
- `bank_one`: Evaluates exactly the `n=1` endpoint as required.

4. ANY GAP OR OVERCLAIM
There are no gaps, overclaims, or mismatched strictness. The `bank_dimension_bound` formulation `2^n ≤ 1 + n * Bank n` is algebraically equivalent to `(2^n - 1)/n ≤ Bank n` and accurately mimics the shared-constant affine dimension counting argument. The lack of the explicit asymptotic inequality `< 2^{n+1}/n` in Lean is a merely missing convenience corollary, as the structural upper bounds from the localization group counts are fully present.

5. RECOMMENDED ACTION
No action required. The Lean definitions and theorems perfectly formalize the intended exact results, integer arithmetic, and corner cases.
