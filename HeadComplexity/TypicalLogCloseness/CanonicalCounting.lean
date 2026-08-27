import HeadComplexity.TypicalLogCloseness.CanonicalPOIC
import HeadComplexity.TypicalLogCloseness.POICWarren

set_option linter.style.header false

/-!
# Counting consequences for canonical POIC₂

The Warren argument was proved for the larger relaxed certificate class.
Canonical sublevel sets are subsets of relaxed sublevel sets, so every explicit
counting estimate transfers without rerunning the algebraic geometry.
-/

namespace HeadComplexity.TypicalLogCloseness

/-- Canonical sublevel sets embed in the already-counted relaxed sublevels. -/
theorem canonical_sublevel_subset_relaxed (n Q : ℕ) :
    sublevel (POIC2 n) Q ⊆ sublevel (RelaxedPOIC2 n) Q := by
  intro f hf
  rw [mem_sublevel] at hf ⊢
  exact (relaxedPOIC2_le_POIC2 f).trans hf

/-- Warren sublevel estimate for the canonical measure. -/
theorem poic2_sublevel_card_le (n Q : ℕ) (hn : 2 ≤ n)
    (hQ0 : 1 ≤ Q) (hQN : Q ≤ 2 ^ n) :
    (sublevel (POIC2 n) Q).card ≤ 2 ^ (64 * n ^ 2 * Q) := by
  exact (Finset.card_le_card (canonical_sublevel_subset_relaxed n Q)).trans
    (relaxed_poic2_sublevel_card_le n Q hn hQ0 hQN)

end HeadComplexity.TypicalLogCloseness
