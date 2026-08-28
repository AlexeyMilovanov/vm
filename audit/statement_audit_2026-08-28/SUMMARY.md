# Headline statement audit — 2026-08-28

Twenty-six independent read-only audits were run with Gemini 3.1 Pro High.
Each package compared the literal Lean declarations with the corresponding
mathematical source. Two transient `503 UNAVAILABLE` failures were retried once
and then completed. The raw reports are in `gemini/`.

## Raw model verdicts

- 20 `MATCH`
- 4 `MATCH_WITH_CAVEAT`
- 2 `MISMATCH`

## Manual disposition

### Real endpoint mismatch — fixed

`checkerboard_restriction_HStar_ge_two` covered only the XOR orientation,
whereas the mathematical statement quantifies a color and covers both XOR and
XNOR. The theorem now has an inferred `{c : Bool}` parameter and invokes the
already-general one-head obstruction. The existing XOR call site still
elaborates without an API change at the call site.

### Reported mismatch that was not a mathematical gap

The core `SignRepresents` convention permits zero on false inputs. Gemini
therefore called the head-to-threshold-degree statement weaker than standard
strict threshold degree. The audit omitted the existing theorem
`exists_strictSignRep_of_ThresholdDegLE`, which shifts a representing
polynomial on the finite cube and produces strict signs at the same degree.
The new wrapper `thresholdDegLE_iff_exists_strictSignRep` records the exact
equivalence in both directions.

### Benign caveats

- The additive-split endpoint omits the output projection; linear projection
  preserves the split.
- The fractional normal form absorbs the constant residual term into the
  threshold and uses independent-head embeddings equivalent to a shared
  block-diagonal construction.
- The sign-rank bridge uses the canonical contiguous two-block partition;
  arbitrary partitions follow by coordinate permutation. The min-bound and
