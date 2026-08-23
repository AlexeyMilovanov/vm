# POIC_2 vs H* sweep

Self-contained, embarrassingly parallel sweep. Each shard runs a disjoint slice of
(candidate function) x (test) and appends one JSON line per completed cell.

## What is being decided

`H*(f)` is the minimum number of attention heads; `POIC_2(f)` is the same with up to two
poles per term over a shared denominator pool. Always `POIC_2(f) <= H*(f)`. No function is
known where the inequality is strict. At budget 3 the question reduces to five orbits
(A, B, C, D, Fp). A counterexample is a function that is **feasible in some orbit** while
**failing H = 3**.

## How to run one shard

    cd sweep && python3 run_shard.py <shard_index> <num_shards>

Requires only numpy and scipy. Results land in `results/shard_<i>.jsonl`; the run is
resumable (already-recorded keys are skipped).

## Reading a result line

- `kind: "H"` — head-complexity probe. `h1..h4` are hinge values; `0` means a certificate
  was found at that head count, so `Hstar` is that number.
- `kind: "O"` — orbit membership. `feasible: true` means an exact budget-3 POIC_2
  certificate exists.

**Interpretation rule:** a `feasible`/`Hstar` result is a certificate and is conclusive.
A nonzero hinge only means "not found" — treat `per_vertex < 0.1` as unreliable.
