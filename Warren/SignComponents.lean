import Mathlib
import Warren.Defs

namespace Warren

def strictLocus {m k : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ) : Set (Fin m → ℝ) :=
  {x | ∀ i, MvPolynomial.eval x (P i) ≠ 0}

theorem strictLocus_isOpen {m k : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ) :
    IsOpen (strictLocus P) := by
  have : strictLocus P = ⋂ i, {x | MvPolynomial.eval x (P i) ≠ 0} := by
    ext; simp [strictLocus]
  rw [this]
  refine isOpen_iInter_of_finite (fun i => ?_)
  exact isOpen_ne_fun (MvPolynomial.continuous_eval (P i)) continuous_const

theorem strictLocus_eq_prodNonzero {m k : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    MvPolynomial.eval x (∏ i, P i) ≠ 0 ↔ (∀ i, MvPolynomial.eval x (P i) ≠ 0) := by
  simp [Finset.prod_ne_zero_iff]

theorem sign_const_of_isPreconnected {m k : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ) (i : Fin k)
    (C : Set (Fin m → ℝ)) (hC : IsPreconnected C) (hC_subset : C ⊆ strictLocus P) :
    (∀ x ∈ C, MvPolynomial.eval x (P i) < 0) ∨ (∀ x ∈ C, 0 < MvPolynomial.eval x (P i)) := by
  have h_cont : Continuous (fun x => MvPolynomial.eval x (P i)) :=
    MvPolynomial.continuous_eval (P i)
  have h_mapsTo : Set.MapsTo (fun x => MvPolynomial.eval x (P i)) C ({0}ᶜ) :=
    fun x hx => hC_subset hx i
  have := IsPreconnected.mapsTo_Ioi_or_Iio hC h_cont.continuousOn h_mapsTo
  cases this with
  | inl h => right; exact fun x hx => h hx
  | inr h => left; exact fun x hx => h hx

theorem pattern_eq_of_component_eq {m k : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ)
    (x y : Fin m → ℝ) (hx : x ∈ strictLocus P) (hy : y ∈ strictLocus P)
    (h_comp : connectedComponentIn (strictLocus P) x = connectedComponentIn (strictLocus P) y) :
    (fun i => decide (0 < MvPolynomial.eval x (P i))) =
      (fun i => decide (0 < MvPolynomial.eval y (P i))) := by
  ext i
  have h_preconn : IsPreconnected (connectedComponentIn (strictLocus P) x) :=
    isPreconnected_connectedComponentIn
  have h_subset : connectedComponentIn (strictLocus P) x ⊆ strictLocus P :=
    connectedComponentIn_subset _ _
  have h_x_mem : x ∈ connectedComponentIn (strictLocus P) x := mem_connectedComponentIn hx
  have h_y_mem : y ∈ connectedComponentIn (strictLocus P) x := by
    rw [h_comp]
    exact mem_connectedComponentIn hy
  rcases sign_const_of_isPreconnected P i _ h_preconn h_subset with h_neg | h_pos
  · have hx_neg : MvPolynomial.eval x (P i) < 0 := h_neg x h_x_mem
    have hy_neg : MvPolynomial.eval y (P i) < 0 := h_neg y h_y_mem
    have h1 : ¬ (0 < MvPolynomial.eval x (P i)) := not_lt.mpr (le_of_lt hx_neg)
    have h2 : ¬ (0 < MvPolynomial.eval y (P i)) := not_lt.mpr (le_of_lt hy_neg)
    simp [h1, h2]
  · have hx_pos : 0 < MvPolynomial.eval x (P i) := h_pos x h_x_mem
    have hy_pos : 0 < MvPolynomial.eval y (P i) := h_pos y h_y_mem
    simp [hx_pos, hy_pos]

/- Stage A aggregate -/
theorem exists_component_embedding {m k : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ) :
    ∃ x : signPatterns P → Fin m → ℝ,
      (∀ s, x s ∈ strictLocus P) ∧
      Function.Injective (fun s => connectedComponentIn (strictLocus P) (x s)) := by
  choose x hx using fun (s : signPatterns P) => s.2
  use x
  constructor
  · intro s
    exact (hx s).1
  · intro s1 s2 h_comp
    ext i
    have hx1 : x s1 ∈ strictLocus P := (hx s1).1
    have hx2 : x s2 ∈ strictLocus P := (hx s2).1
    have h_pat := pattern_eq_of_component_eq P (x s1) (x s2) hx1 hx2 h_comp
    have hs1 := (hx s1).2 i
    have hs2 := (hx s2).2 i
    have heq := congr_fun h_pat i
    rw [← hs1, ← hs2] at heq
    exact heq

end Warren
