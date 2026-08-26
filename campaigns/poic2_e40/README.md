# POIC2 E40 Jules campaign

This campaign freezes the forty exact `6 x 5` E tables from the axis-GES
census.  There are ten reflection/global-sign orbits, four tables per orbit.

Important: `E` means only that every strict profile cubic has no split legal
section on the four extreme axis lines (and the representatives also have an
exact obstruction at infinity).  It does **not** mean `POIC_2 <= 3`, `H* > 3`,
or a counterexample.  No budget-three POIC source is presently known for these
tables.

Each `cases/E##_key_<key>/` directory is owned by one Jules session.  Common
inputs and references are read-only.  A session first searches for an exact
`POIC_2 <= 3` certificate; only after finding and independently verifying one
does it search for an exact three-head certificate.  Numerical failure never
proves a lower bound.

Run `python3 common/validate_case.py cases/<case>` to validate a case envelope.
