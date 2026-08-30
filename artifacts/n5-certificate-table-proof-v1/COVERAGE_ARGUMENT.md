# Why 9,340,584 rows cover every five-bit Boolean function

## The legal symmetry group

Encode a Boolean function by a 32-bit integer whose bit at vertex `x` is
`f(x)`.  The table quotients by exactly these transformations:

1. a permutation of the five input coordinates;
2. simultaneous complementation of all five input coordinates;
3. complementation of the output.

They form a group of order

    5! * 2 * 2 = 480.

These transformations preserve threshold degree, head complexity `H*`, and
`POIC_2`.  Partial, coordinate-by-coordinate input flips are deliberately
absent: they do not preserve the one-orientation legality condition for a
head.

## Independent orbit count

For each of the 240 input actions, let its permutation of the 32 cube vertices
have `c` cycles.

* Without output complementation, exactly `2^c` truth tables are fixed.
* With output complementation, a fixed truth table exists exactly when every
  vertex cycle has even length.  In that case there are again `2^c` fixed
  tables; otherwise there are none.

The verifier enumerates the 120 coordinate permutations and two global input
orientations, computes these cycle decompositions, and obtains

    sum of fixed points = 4,483,480,320
    group order         = 480
    number of orbits    = 9,340,584.

This is Burnside's lemma, evaluated with integer arithmetic.

## Why minimality plus the count proves coverage

The manifest contains 9,340,584 strictly increasing, hence distinct,
truth-table codes.  The compiled checker tests each code against all 240 input
actions and both possible output orientations and proves that the stored code
is the least integer in its 480-element group orbit.

Every orbit has one and only one least integer.  Thus the stored codes form a
subset of the set of orbit minima.  The subset has exactly as many elements as
there are orbits, by the independent Burnside count.  It follows that it is
the full set of orbit minima: every five-bit Boolean function is represented
by exactly one row.

The C program is only an accelerator for this finite comparison.  Its source
is included, compiled with warnings-as-errors, hashed in the final report, and
covered by both an accepting and a rejecting test.

