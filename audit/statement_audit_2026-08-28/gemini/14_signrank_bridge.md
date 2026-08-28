VERDICT: MATCH_WITH_CAVEAT

1. LITERAL LEAN MEANING
`signRank_le_of_computableWithHeadsN` (in `SignRankBridge.lean:974`) states that if a boolean function `f` on an input of size `a + b` is computable with `H` heads, and `H ≥ 1`, then the sign-rank of its two-block sign matrix (partitioning the first `a` bits against the last `b` bits) is bounded above by `2^(H+1) - 2`.
`signRank_le_pow_HStar` (`SignRankBridge.lean:1003`) instantiates this specific bound for the exact head complexity `H = HStar (a + b) f`, requiring `HStar (a + b) f ≥ 1`.

2. INTENDED MEANING
The intended mathematical statements in `028_restrictions_and_sign_rank.md` and `EXPLICIT_GAP.md` assert that for any nonconstant function $f$ (implying $H^*(f) \ge 1$), computing $f$ with $H$ heads caps the sign-rank across any input partition $I \sqcup J$ at $2^{H+1}-2$. The `.md` file additionally wraps this in a `min` bound with the binomial sums derived from threshold degree (Theorem C) and gives the logarithmic inversion $H^* \ge \lceil \log_2(\text{srank} + 2) \rceil - 1$.

3. QUANTIFIER/EDGE-CASE CHECK
- **Nonconstant requirement:** Matches perfectly. The text assumes $f$ is nonconstant. Lean captures this via the hypothesis `hH : 1 ≤ HStar (a + b) f`. This crucially avoids evaluating the bound at $H=0$, where $2^{0+1}-2 = 0$, which would be false since a constant function has a sign-rank of 1.
- **Natural number subtraction:** Because `1 ≤ H`, $2^{H+1} \ge 4$. Thus $4 - 2 = 2$, and the natural number subtraction `2^(H+1) - 2` never truncates at 0, behaving identically to real arithmetic.
- **Trivial partitions ($a=0$ or $b=0$):** Handled safely. The sign matrix becomes a $1 \times 2^{a+b}$ vector with rank 1, and the bound $1 \le 2^{H+1}-2$ holds since $H \ge 1$.
- **Vacuous cases ($n=0$):** A 0-bit function is just a constant point, meaning $H^* = 0$. The hypothesis `1 ≤ HStar` fails, making the theorem safely vacuous.
- **Strictness:** `SignMatches` (`SignRank.lean:20`) dictates `0 < M i j * A i j`. Since `M` entries are precisely $\pm 1$, `A` must perfectly match the strict sign pattern (no zeroes allowed).

4. ANY GAP OR OVERCLAIM
There are no mathematical flaws, but there are two structural limitations to note:
- **Specific block partition (deliberately weaker explicit form):** The math text asserts the bound for an arbitrary partition $I \sqcup J$. The Lean statement uses the canonical contiguous blocks `Fin a` and `Fin b` (`blockJoin x y`). This is just as powerful (since coordinates can be permuted), but weaker in its explicit written form.
- **Missing `min` wrapper and inversion (missing convenience corollaries):** The combined bound taking the minimum over the algebraic $2^{H+1}-2$ cap and the threshold degree bounds $\sum \binom{|I|}{i}$ is absent from `signRank_le_pow_HStar`. (The threshold bound itself is successfully proved separately as `signRank_le_of_thresholdDegLE` in `SignRankBridge.lean:567`). The algebraic inversion into a lower bound on $H^*$ is also left implicit.

5. RECOMMENDED ACTION
The formalization is mathematically robust and faithfully implements the exact logic required for the sign-rank cap without edge-case violations. No action is strictly required for soundness. If verbatim parity with `028_restrictions_and_sign_rank.md` is desired, one could provide a wrapper corollary taking an arbitrary permutation equivalence $\text{Fin } n \simeq \text{Fin } a \oplus \text{Fin } b$ and a `min` operation combining the two available caps.
