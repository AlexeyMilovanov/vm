import Warren.Defs
import Warren.Assembly

/-!
# Frozen endpoints of the project

Two frozen endpoints (statement-locked by `scripts/smoke/FrozenGoals.lean`):

* `warren_sign_patterns_weak` — the primary target: a Warren-type bound with a
  deliberately generous constant, `#patterns ≤ (8·(d·k+1))^m`, hypothesis-free.
  Proving any SHARPER bound still closes this statement (`≤` is monotone), so
  intermediate work may aim at e.g. `(2·d·k+4)^m` and finish by arithmetic.
* `warren_sign_patterns_diag` — the diagonal instance actually consumed by the
  H* separation project (`m := 2H`, `d := H`). Already derived from the weak
  form; it must keep compiling unchanged.

`WarrenClassicalStatement` records Warren's 1968 sharp form (constant `4e`) as
an unasserted proposition. It is a stretch goal only: completion of this
project does NOT require it, and no proof placeholder may be introduced.
-/

/-- Primary frozen target (T1): weak Warren. The number of strict sign
patterns of `k` polynomials of total degree `≤ d` in `m` real variables is at
most `(8·(d·k+1))^m`. Hypothesis-free: all degenerate cases (`m = 0`, `k = 0`,
`d = 0`) are true and must be handled, not excluded. -/
theorem warren_sign_patterns_weak {m k d : ℕ}
    (P : Fin k → MvPolynomial (Fin m) ℝ)
    (hdeg : ∀ i, (P i).totalDegree ≤ d) :
    ((signPatterns P).ncard : ℝ) ≤ (8 * ((d : ℝ) * k + 1)) ^ m :=
  Warren.warren_sign_patterns_weak_aux P hdeg

/-- Consumer bridge (T2): the diagonal instance used by the H* project
(`k` polynomials of degree `≤ H` in `2H` variables). Kept as a separate frozen
endpoint so the downstream migration has a stable name and type. -/
theorem warren_sign_patterns_diag {H k : ℕ}
    (P : Fin k → MvPolynomial (Fin (2 * H)) ℝ)
    (hdeg : ∀ i, (P i).totalDegree ≤ H) :
    ((signPatterns P).ncard : ℝ) ≤ (8 * ((H : ℝ) * k + 1)) ^ (2 * H) :=
  warren_sign_patterns_weak P hdeg

/-- Warren's classical sharp bound (1968), recorded as an unasserted
proposition. Stretch goal only — do not introduce a proof placeholder for it. -/
def WarrenClassicalStatement : Prop :=
  ∀ {m k d : ℕ}, 1 ≤ m → m ≤ k → 1 ≤ d →
    ∀ P : Fin k → MvPolynomial (Fin m) ℝ,
      (∀ i, (P i).totalDegree ≤ d) →
      ((signPatterns P).ncard : ℝ) ≤ (4 * Real.exp 1 * d * k / m) ^ m
