# Jules research task: E04_key_1647342

You own only this directory.  Read `../../README.md`, `../../common/`, and the
immutable `input.json`.  Do not edit common files or another case.

Use up to two hours as an autonomous experimental mathematician/programmer.
You may install `numpy`, `scipy`, or `sympy` if absent.  Start from the supplied
solvers but inspect and improve them locally when the diagnostics justify it.

## Ordered objectives

1. Revalidate the target with `../../common/validate_case.py .`.
2. Search for a legal budget-three `POIC_2` representation.  Explore genuinely
   different budget-three topologies/orientation cells, not just random seeds.
3. A numerical hit is only provisional.  Save all coefficients, legality
   margins and full-cube sign margins, rationalize them, and write an
   independent exact-arithmetic verifier in this directory.
4. If an exact `POIC_2 <= 3` certificate is obtained, seek an exact lower bound
   excluding budgets 1 and 2 (for example threshold-degree or an exact
   Gordan/Farkas witness).  Only then report `POIC2_EQ_3_EXACT`.
5. After an exact budget-three source exists, search adaptively for three legal
   heads.  If a numerical H3 hit appears, exactify and check all 512 vertices.
6. Do not infer `POIC_2 > 3` or `H* > 3` from timeout or solver failure.

## Persistence and deliverables

- Append a timestamped entry to `research_log.md` after every substantial
  attempt.  Preserve intermediate scripts, diagnostics and best checkpoints.
- Update `result.json` using the allowed status values checked by the common
  validator.  Include `case_id=E04_key_1647342` and the exact `input_sha256` from
  `input.json`.
- Commit useful partial work even without a certificate.  In the final report,
  distinguish exact facts, numerical evidence, and untested ideas.
- If a common solver improvement is broadly useful, save it as
  `proposed_common.patch` here rather than editing `../../common/`.
