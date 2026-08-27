import HeadComplexity.TypicalLogCloseness.CanonicalCounting

set_option linter.style.header false

/-!
# Theorem 026: explicit counting lower bound for H*

The old asymptotic `2^(O(n^2 H))` statement is packaged here as the concrete
finite bound inherited from the canonical POIC₂ Warren estimate.
-/

namespace HeadComplexity.TypicalLogCloseness

/-- Every H* sublevel is contained in the canonical POIC₂ sublevel at the same
budget. -/
theorem hstar_sublevel_subset_poic2 (n H : ℕ) :
    sublevel (HeadComplexity.HStar n) H ⊆ sublevel (POIC2 n) H := by
  intro f hf
  rw [mem_sublevel] at hf ⊢
  exact (POIC2_le_HStar f).trans hf

/-- Quantitative finite form of theorem 026. -/
theorem theorem026_counting_lower_bound (n H : ℕ) (hn : 2 ≤ n)
    (hH0 : 1 ≤ H) (hHN : H ≤ 2 ^ n) :
    (sublevel (HeadComplexity.HStar n) H).card ≤
      2 ^ (64 * n ^ 2 * H) := by
  exact (Finset.card_le_card (hstar_sublevel_subset_poic2 n H)).trans
    (poic2_sublevel_card_le n H hn hH0 hHN)

/-- If the Warren exponent is smaller than the truth-table dimension, some
function lies outside the H-head sublevel. This is the finite witness form of
the worst-case lower bound `Omega(2^n / n^2)`. -/
theorem theorem026_exists_hard_function (n H : ℕ) (hn : 2 ≤ n)
    (hH0 : 1 ≤ H) (hHN : H ≤ 2 ^ n)
    (hexp : 64 * n ^ 2 * H < 2 ^ n) :
    ∃ f : BoolFn n, H < HeadComplexity.HStar n f := by
  sorry

end HeadComplexity.TypicalLogCloseness
