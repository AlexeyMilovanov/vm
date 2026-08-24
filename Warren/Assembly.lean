import Mathlib
import Warren.SignComponents
import Warren.Critical
import Warren.Bezout.Defs

namespace Warren

theorem totalDegree_prod_le {m k d : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ)
    (hdeg : ∀ i, (P i).totalDegree ≤ d) :
    (∏ i, P i).totalDegree ≤ d * k := by
  have := MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin k)) P
  have h2 : (∑ i : Fin k, (P i).totalDegree) ≤ ∑ i : Fin k, d :=
    Finset.sum_le_sum (fun i _ => hdeg i)
  have h3 : (∑ i : Fin k, d) = d * k := by simp [mul_comm]
  linarith

theorem signPatterns_subsingleton_of_dim_zero {k : ℕ} (P : Fin k → MvPolynomial (Fin 0) ℝ) :
    (signPatterns P).ncard ≤ 1 := by
  rw [Set.ncard_le_one]
  rintro s1 hs1 s2 hs2
  ext i
  rcases hs1 with ⟨x1, -, h1⟩
  rcases hs2 with ⟨x2, -, h2⟩
  have hx : x1 = x2 := Subsingleton.elim x1 x2
  rw [h1, h2, hx]

theorem signPatterns_ncard_pos_bound {m k d : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ)
    (hemp : IsEmpty ↥(signPatterns P)) :
    ((signPatterns P).ncard : ℝ) ≤ (8 * ((d : ℝ) * k + 1)) ^ m := by
  have h1 : signPatterns P = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    exact hemp.false ⟨x, hx⟩
  rw [h1, Set.ncard_empty]
  simp only [Nat.cast_zero]
  positivity

theorem weak_bound_arith {m d k : ℕ} :
    (((4 * (d * k) + 8 : ℕ) : ℝ)) ^ m ≤ (8 * ((d : ℝ) * k + 1)) ^ m := by
  apply pow_le_pow_left₀
  · positivity
  · push_cast
    calc
      (4 : ℝ) * (d * k : ℝ) + 8 = 4 * (d : ℝ) * k + 8 := by ring
      _ ≤ 8 * (d : ℝ) * k + 8 := by
        have : 0 ≤ (d : ℝ) * k := by positivity
        linarith
      _ = 8 * ((d : ℝ) * k + 1) := by ring

theorem ncard_eq_natCard_subtype {m k : ℕ} (P : Fin k → MvPolynomial (Fin m) ℝ) :
    (signPatterns P).ncard = Nat.card ↥(signPatterns P) := by
  exact (Nat.card_coe_set_eq _).symm

theorem warren_sign_patterns_weak_aux {m k d : ℕ}
    (P : Fin k → MvPolynomial (Fin m) ℝ)
    (hdeg : ∀ i, (P i).totalDegree ≤ d) :
    ((signPatterns P).ncard : ℝ) ≤ (8 * ((d : ℝ) * k + 1)) ^ m := by
  classical
  rcases isEmpty_or_nonempty ↥(signPatterns P) with hemp | hne
  · exact signPatterns_ncard_pos_bound P hemp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 : (signPatterns P).ncard ≤ 1 := signPatterns_subsingleton_of_dim_zero P
    simpa using (by exact_mod_cast h1 : ((signPatterns P).ncard : ℝ) ≤ 1)
  obtain ⟨x, hx_mem, hx_inj⟩ := exists_component_embedding P
  set W := ∏ i, P i with hWdef
  have hWdeg : W.totalDegree ≤ d * k := totalDegree_prod_le P hdeg
  have hset : {y : Fin m → ℝ | MvPolynomial.eval y W ≠ 0} = strictLocus P := by
    ext y
    exact strictLocus_eq_prodNonzero P y
  have hxW : ∀ a, MvPolynomial.eval (x a) W ≠ 0 :=
    fun a => (strictLocus_eq_prodNonzero P (x a)).mpr (hx_mem a)
  have hcomp : Function.Injective
      (fun a => connectedComponentIn {y | MvPolynomial.eval y W ≠ 0} (x a)) := by
    simpa [hset] using hx_inj
  obtain ⟨v, z, hzinj, hz⟩ := exists_injective_criticalPoints hm W hWdeg x hxW hcomp
  have hdegF : ∀ j, (criticalSystem (d * k) W v j).totalDegree ≤ 2 * (d * k) + 4 :=
    fun j => totalDegree_criticalSystem_le _ W hWdeg v j
  have hcard := bezout_kernel (criticalSystem (d * k) W v) hdegF z hzinj hz
  have hnat : (signPatterns P).ncard ≤ (4 * (d * k) + 8) ^ m := by
    rw [ncard_eq_natCard_subtype]
    calc Nat.card ↥(signPatterns P) ≤ (2 * (2 * (d * k) + 4)) ^ m := hcard
      _ = (4 * (d * k) + 8) ^ m := by ring_nf
  calc ((signPatterns P).ncard : ℝ) ≤ (((4 * (d * k) + 8 : ℕ) : ℝ)) ^ m := by exact_mod_cast hnat
    _ ≤ (8 * ((d : ℝ) * k + 1)) ^ m := weak_bound_arith

end Warren
