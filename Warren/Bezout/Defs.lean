import Mathlib

namespace Warren

noncomputable def jacobianMatrix {m : ℕ}
    (F : Fin m → MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))

def IsNondegenerateSolution {m : ℕ}
    (F : Fin m → MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) : Prop :=
  (∀ i, MvPolynomial.eval x (F i) = 0) ∧ (jacobianMatrix F x).det ≠ 0

/-- Degenerate case `m = 0` of the Bézout kernel: an injective family of points
of `Fin 0 → ℝ` is a subsingleton. -/
theorem bezout_kernel_dim_zero {e : ℕ} {ι : Type} [Finite ι] (z : ι → Fin 0 → ℝ)
    (hinj : Function.Injective z) : Nat.card ι ≤ (2 * e) ^ 0 := by
  have hsub : Subsingleton ι := ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
  simpa using Finite.card_le_one_iff_subsingleton.mpr hsub

/-- Degenerate case `e = 0` (with `0 < m`) of the Bézout kernel: all equations are
constant, so the Jacobian vanishes identically and there is no nondegenerate
solution at all. -/
theorem bezout_kernel_deg_zero {m : ℕ} (hm : 0 < m) (F : Fin m → MvPolynomial (Fin m) ℝ)
    (hdeg : ∀ i, (F i).totalDegree ≤ 0)
    {ι : Type} [Finite ι] (z : ι → Fin m → ℝ)
    (hz : ∀ a, IsNondegenerateSolution F (z a)) : Nat.card ι ≤ (2 * 0) ^ m := by
  have hemp : IsEmpty ι := by
    refine ⟨fun a => ?_⟩
    have hjac : jacobianMatrix F (z a) = 0 := by
      funext i j
      have hC : F i = MvPolynomial.C (MvPolynomial.coeff 0 (F i)) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp (hdeg i))
      have hp : MvPolynomial.pderiv j (F i) = 0 := by
        rw [hC]; exact MvPolynomial.pderiv_C
      simp [jacobianMatrix, hp]
    have hdet := (hz a).2
    rw [hjac] at hdet
    exact hdet (Matrix.det_zero (Fin.pos_iff_nonempty.mp hm))
  simp [Nat.card_of_isEmpty]

section Perturbation

open Filter Topology

/-- The Fréchet derivative of a polynomial evaluation map is given by the partial
derivatives: `d(eval · p)(x) = ∑ j, (∂p/∂x_j)(x) • proj j`. -/
lemma hasStrictFDerivAt_eval {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    HasStrictFDerivAt (fun y : Fin m → ℝ => MvPolynomial.eval y p)
      (∑ j : Fin m, MvPolynomial.eval x (MvPolynomial.pderiv j p) •
        (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (hasStrictFDerivAt_const (a : ℝ) x)
  | add p q hp hq =>
      have hadd := hp.add hq
      have heq_fun : (fun y : Fin m → ℝ => MvPolynomial.eval y p) + (fun y : Fin m → ℝ => MvPolynomial.eval y q) =
          (fun y : Fin m → ℝ => MvPolynomial.eval y (p + q)) := by
        funext y
        simp
      have heq_deriv : (∑ j : Fin m, MvPolynomial.eval x (MvPolynomial.pderiv j p) • (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)) +
          (∑ j : Fin m, MvPolynomial.eval x (MvPolynomial.pderiv j q) • (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)) =
          (∑ j : Fin m, MvPolynomial.eval x (MvPolynomial.pderiv j (p + q)) • (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)) := by
        simp [Finset.sum_add_distrib, add_smul]
      rw [heq_fun, heq_deriv] at hadd
      exact hadd
  | mul_X p i hp =>
      have hcoord : HasStrictFDerivAt (fun y : Fin m → ℝ => y i)
          (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) x :=
        (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).hasStrictFDerivAt
      have hmul := hp.mul hcoord
      have heq_fun : (fun y : Fin m → ℝ => MvPolynomial.eval y p) * (fun y : Fin m → ℝ => y i) =
          (fun y : Fin m → ℝ => MvPolynomial.eval y (p * MvPolynomial.X i)) := by
        funext y
        simp
      have heq_deriv : MvPolynomial.eval x p • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) + x i • (∑ j : Fin m, MvPolynomial.eval x (MvPolynomial.pderiv j p) • (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)) =
          (∑ j : Fin m, MvPolynomial.eval x (MvPolynomial.pderiv j (p * MvPolynomial.X i)) • (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)) := by
        ext v
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
          smul_eq_mul, ContinuousLinearMap.add_apply, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply,
          Finset.mul_sum, map_add, map_mul, MvPolynomial.eval_X, apply_ite, map_zero, mul_zero, map_one]
        have H1 : (∑ x_1 : Fin m, (if i = x_1 then MvPolynomial.eval x (MvPolynomial.pderiv x_1 p) * x i + MvPolynomial.eval x p * 1 else MvPolynomial.eval x (MvPolynomial.pderiv x_1 p) * x i + 0) * v x_1) =
                  (∑ x_1 : Fin m, MvPolynomial.eval x (MvPolynomial.pderiv x_1 p) * x i * v x_1) +
                  (∑ x_1 : Fin m, if i = x_1 then MvPolynomial.eval x p * v x_1 else 0) := by
          rw [←Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          split_ifs with h
          · ring
          · ring
        rw [H1, Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      rw [heq_fun, heq_deriv] at hmul
      exact hmul

/-- The parametrised perturbation `(t, x) ↦ (t, F(x) + t · x^(e+1))`. -/
noncomputable def perturbMap {m : ℕ} (e : ℕ) (F : Fin m → MvPolynomial (Fin m) ℝ) :
    ℝ × (Fin m → ℝ) → ℝ × (Fin m → ℝ) :=
  fun p => (p.1, fun i => MvPolynomial.eval p.2 (F i) + p.1 * (p.2 i) ^ (e + 1))

/-- The derivative of `perturbMap e F` at a point `(0, z)`. -/
noncomputable def perturbDeriv {m : ℕ} (e : ℕ) (F : Fin m → MvPolynomial (Fin m) ℝ)
    (z : Fin m → ℝ) : (ℝ × (Fin m → ℝ)) →L[ℝ] (ℝ × (Fin m → ℝ)) :=
  (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).prod
    (ContinuousLinearMap.pi fun i =>
      (∑ j, MvPolynomial.eval z (MvPolynomial.pderiv j (F i)) •
        (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))
      + (z i) ^ (e + 1) • ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ))

lemma hasStrictFDerivAt_perturbMap {m e : ℕ} (F : Fin m → MvPolynomial (Fin m) ℝ)
    (z : Fin m → ℝ) :
    HasStrictFDerivAt (perturbMap e F) (perturbDeriv e F z) (0, z) := by
  refine HasStrictFDerivAt.prodMk hasStrictFDerivAt_fst ?_
  refine hasStrictFDerivAt_pi.mpr fun i => ?_
  have h1 : HasStrictFDerivAt (fun p : ℝ × (Fin m → ℝ) => MvPolynomial.eval p.2 (F i))
      ((∑ j, MvPolynomial.eval z (MvPolynomial.pderiv j (F i)) •
        (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))) (0, z) :=
    HasStrictFDerivAt.comp (x := ((0:ℝ), z))
      (g := fun y : Fin m → ℝ => MvPolynomial.eval y (F i))
      (f := fun p : ℝ × (Fin m → ℝ) => p.2)
      (hasStrictFDerivAt_eval (F i) z) hasStrictFDerivAt_snd
  have hB : HasStrictFDerivAt (fun p : ℝ × (Fin m → ℝ) => (p.2 i) ^ (e + 1))
      (((e + 1 : ℝ) * (z i) ^ e) •
        ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))) (0, z) := by
    have hA_base : HasStrictFDerivAt ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))
        ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))) (0, z) :=
      ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).hasStrictFDerivAt
    have heq : (fun p : ℝ × (Fin m → ℝ) => p.2 i) = ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))) := by ext p; rfl
    have hA : HasStrictFDerivAt (fun p : ℝ × (Fin m → ℝ) => p.2 i)
        ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))) (0, z) := by
      rw [heq]
      exact hA_base
    have hp_pow := hA.pow (e + 1)
    have heq_deriv : ((e + 1 : ℕ) • ((0:ℝ), z).2 i ^ ((e + 1) - 1)) • ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))) =
        (((e + 1 : ℝ) * z i ^ e) • ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))) := by
      apply ContinuousLinearMap.ext; intro v
      simp
    have hh : HasStrictFDerivAt (fun p : ℝ × (Fin m → ℝ) => (p.2 i) ^ (e + 1))
        (((e + 1 : ℕ) • ((0:ℝ), z).2 i ^ ((e + 1) - 1)) • ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))) (0, z) := hp_pow
    rw [heq_deriv] at hh
    exact hh
  have h2 : HasStrictFDerivAt (fun p : ℝ × (Fin m → ℝ) => p.1 * (p.2 i) ^ (e + 1))
      ((z i) ^ (e + 1) • ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)) (0, z) := by
    have hprod := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := ((0:ℝ), z))).mul hB
    have heq_fun : (fun p : ℝ × (Fin m → ℝ) => p.1 * p.2 i ^ (e + 1)) = (fun p : ℝ × (Fin m → ℝ) => p.1) * (fun p : ℝ × (Fin m → ℝ) => p.2 i ^ (e + 1)) := by
      funext p; rfl
    rw [heq_fun]
    have heq_deriv : ((0:ℝ), z).1 • (((e + 1 : ℝ) * z i ^ e) • ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))) + ((0:ℝ), z).2 i ^ (e + 1) • ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) =
        (z i) ^ (e + 1) • ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) := by
      apply ContinuousLinearMap.ext; intro v
      simp
    have hh : HasStrictFDerivAt ((fun p : ℝ × (Fin m → ℝ) => p.1) * (fun p : ℝ × (Fin m → ℝ) => p.2 i ^ (e + 1)))
        (((0:ℝ), z).1 • (((e + 1 : ℝ) * z i ^ e) • ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))) + ((0:ℝ), z).2 i ^ (e + 1) • ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)) (0, z) := hprod
    rw [heq_deriv] at hh
    exact hh
  have h_add := h1.add h2
  have heq_fun : (fun p : ℝ × (Fin m → ℝ) => MvPolynomial.eval p.2 (F i) + p.1 * p.2 i ^ (e + 1)) =
      (fun p : ℝ × (Fin m → ℝ) => MvPolynomial.eval p.2 (F i)) + (fun p : ℝ × (Fin m → ℝ) => p.1 * (p.2 i) ^ (e + 1)) := by
    funext p; rfl
  rw [heq_fun]
  exact h_add

lemma perturbDeriv_injective {m e : ℕ} (F : Fin m → MvPolynomial (Fin m) ℝ)
    (z : Fin m → ℝ) (hdet : (jacobianMatrix F z).det ≠ 0) :
    Function.Injective (perturbDeriv e F z) := by
  classical
  have key : ∀ v : ℝ × (Fin m → ℝ), perturbDeriv e F z v = 0 → v = 0 := by
    rintro ⟨dt, dx⟩ hv
    have h1 : dt = 0 := congrArg Prod.fst hv
    have h2 : (jacobianMatrix F z).mulVec dx = 0 := by
      funext i
      have := congrFun (congrArg Prod.snd hv) i
      simp [perturbDeriv, h1] at this
      simpa [Matrix.mulVec, dotProduct, jacobianMatrix] using this
    have hdx := Matrix.eq_zero_of_mulVec_eq_zero hdet h2
    simp [h1, hdx]
  intro a b hab
  have h0 : perturbDeriv e F z (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (key _ h0)

/-- At a nondegenerate solution the derivative of the perturbation map is invertible. -/
noncomputable def perturbEquiv {m : ℕ} (e : ℕ) (F : Fin m → MvPolynomial (Fin m) ℝ)
    (z : Fin m → ℝ) (hdet : (jacobianMatrix F z).det ≠ 0) :
    (ℝ × (Fin m → ℝ)) ≃L[ℝ] (ℝ × (Fin m → ℝ)) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective (perturbDeriv e F z).toLinearMap
      ⟨perturbDeriv_injective F z hdet,
       LinearMap.injective_iff_surjective.mp (perturbDeriv_injective F z hdet)⟩)

lemma coe_perturbEquiv {m : ℕ} (e : ℕ) (F : Fin m → MvPolynomial (Fin m) ℝ)
    (z : Fin m → ℝ) (hdet : (jacobianMatrix F z).det ≠ 0) :
    ((perturbEquiv e F z hdet : (ℝ × (Fin m → ℝ)) ≃L[ℝ] (ℝ × (Fin m → ℝ))) :
      (ℝ × (Fin m → ℝ)) →L[ℝ] (ℝ × (Fin m → ℝ))) = perturbDeriv e F z := by
  ext v <;> rfl

/-- Parametric persistence of a single nondegenerate root: there is a family `w`
of roots of the perturbed system, defined for all small parameters `s`, with
`w s → z` as `s → 0`. -/
theorem exists_perturbed_root {m e : ℕ} (F : Fin m → MvPolynomial (Fin m) ℝ)
    (z : Fin m → ℝ) (hz : IsNondegenerateSolution F z) :
    ∃ w : ℝ → Fin m → ℝ, Filter.Tendsto w (𝓝 0) (𝓝 z) ∧
      ∀ᶠ s in 𝓝 (0:ℝ), ∀ i,
        MvPolynomial.eval (w s) (F i) + s * (w s i) ^ (e + 1) = 0 := by
  have hf : HasStrictFDerivAt (perturbMap e F)
      ((perturbEquiv e F z hz.2 : (ℝ × (Fin m → ℝ)) ≃L[ℝ] (ℝ × (Fin m → ℝ))) :
        (ℝ × (Fin m → ℝ)) →L[ℝ] (ℝ × (Fin m → ℝ))) (0, z) := by
    rw [coe_perturbEquiv]
    exact hasStrictFDerivAt_perturbMap F z
  have hpt : perturbMap e F (0, z) = (0, 0) := by
    simp only [perturbMap, hz.1, zero_mul, add_zero]
    rfl
  set g := hf.localInverse (perturbMap e F) _ (0, z) with hgdef
  have hright : ∀ᶠ y in 𝓝 (perturbMap e F (0, z)), perturbMap e F (g y) = y :=
    hf.eventually_right_inverse
  have htend : Filter.Tendsto g (𝓝 (perturbMap e F (0, z))) (𝓝 (0, z)) :=
    hf.localInverse_tendsto
  have hs : Filter.Tendsto (fun s : ℝ => (s, (0 : Fin m → ℝ))) (𝓝 0)
      (𝓝 (perturbMap e F (0, z))) := by
    rw [hpt]
    exact Continuous.tendsto (by fun_prop) 0
  refine ⟨fun s => (g (s, 0)).2, ?_, ?_⟩
  · exact (htend.comp hs).snd_nhds
  · filter_upwards [hs.eventually hright] with s hsm
    intro i
    have h1 : (g (s, 0)).1 = s := congrArg Prod.fst hsm
    have h2 := congrFun (congrArg Prod.snd hsm) i
    simpa [perturbMap, h1] using h2

end Perturbation

/-- Stage D, Layer 1: Parametric IFT persistence.
There exists a common parameter `t ≠ 0` where all branches remain distinct and evaluate to 0.
`G_i(t, x) = F_i(x) + t * x_i^(e+1) = 0` at `z_a(t)`. -/
theorem exists_common_parameter_perturbation {m e : ℕ} (F : Fin m → MvPolynomial (Fin m) ℝ)
    {ι : Type} [Finite ι] (z : ι → Fin m → ℝ) (hinj : Function.Injective z)
    (hz : ∀ a, IsNondegenerateSolution F (z a)) :
    ∃ (t : ℝ) (z' : ι → Fin m → ℝ), t ≠ 0 ∧ Function.Injective z' ∧
      ∀ a i, MvPolynomial.eval (z' a) (F i) + t * (z' a i)^(e + 1) = 0 := by
  classical
  choose w hw1 hw2 using fun a => exists_perturbed_root (e := e) F (z a) (hz a)
  have hne : ∀ a b : ι, a ≠ b → ∀ᶠ s in nhds (0:ℝ), w a s ≠ w b s := by
    intro a b hab
    have hopen : IsOpen {p : (Fin m → ℝ) × (Fin m → ℝ) | p.1 ≠ p.2} :=
      isOpen_ne_fun continuous_fst continuous_snd
    have hmem : {p : (Fin m → ℝ) × (Fin m → ℝ) | p.1 ≠ p.2} ∈ nhds (z a, z b) :=
      hopen.mem_nhds (by simpa using fun h => hab (hinj h))
    exact ((hw1 a).prodMk_nhds (hw1 b)).eventually hmem
  have hall : ∀ᶠ s in nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ,
      (∀ a i, MvPolynomial.eval (w a s) (F i) + s * (w a s i) ^ (e + 1) = 0) ∧
      (∀ a b : ι, a ≠ b → w a s ≠ w b s) := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all]
      intro a
      exact (hw2 a).filter_mono nhdsWithin_le_nhds
    · rw [Filter.eventually_all]
      intro a
      rw [Filter.eventually_all]
      intro b
      by_cases hab : a = b
      · exact Filter.Eventually.of_forall (fun s h => absurd hab h)
      · exact ((hne a b hab).filter_mono nhdsWithin_le_nhds).mono (fun s hs _ => hs)
  obtain ⟨s, ⟨hs1, hs2⟩, hs0⟩ := (hall.and self_mem_nhdsWithin).exists
  refine ⟨s, fun a => w a s, hs0, ?_, hs1⟩
  intro a b hab
  by_contra hne'
  exact hs2 a b hne' hab

/-- The box exponents are those with degree ≤ e in each coordinate. -/
noncomputable def boxMonomials (m e : ℕ) : Finset (Fin m →₀ ℕ) :=
  Finset.map (Finsupp.equivFunOnFinite (α := Fin m) (M := ℕ)).symm.toEmbedding
    (Fintype.piFinset (fun _ => Finset.Iic e))

theorem card_boxMonomials (m e : ℕ) : (boxMonomials m e).card = (e + 1) ^ m := by
  rw [boxMonomials, Finset.card_map, Fintype.card_piFinset]
  simp

/-- Membership in `boxMonomials`: exponent vectors bounded by `e` in each coordinate. -/
lemma mem_boxMonomials {m e : ℕ} (v : Fin m →₀ ℕ) :
    v ∈ boxMonomials m e ↔ ∀ i, v i ≤ e := by
  classical
  simp only [boxMonomials, Finset.mem_map, Fintype.mem_piFinset, Finset.mem_Iic,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨f, hf, rfl⟩ i
    simpa using hf i
  · intro h
    exact ⟨⇑v, h, by ext i; simp⟩

/-- Stage D, Layer 2: Evaluation reduction by strong induction on total degree.
The evaluation vectors of all monomials lie in the span of the box monomials,
under the relations `x_i^(e+1) = -t⁻¹ F_i(x)`. -/
theorem eval_span_box_monomials {m e : ℕ} (F : Fin m → MvPolynomial (Fin m) ℝ)
    (hdeg : ∀ i, (F i).totalDegree ≤ e)
    {ι : Type} [Finite ι]
    (t : ℝ) (ht : t ≠ 0)
    (z' : ι → Fin m → ℝ)
    (hz' : ∀ a i, MvPolynomial.eval (z' a) (F i) + t * (z' a i) ^ (e + 1) = 0) :
    ∀ p : MvPolynomial (Fin m) ℝ,
      (fun a => MvPolynomial.eval (z' a) p) ∈ Submodule.span ℝ
        (Set.range fun (α : boxMonomials m e) =>
          (fun a => MvPolynomial.eval (z' a) (MvPolynomial.monomial (α : Fin m →₀ ℕ) 1))) := by
  classical
  set S := Submodule.span ℝ
        (Set.range fun (α : boxMonomials m e) =>
          (fun a => MvPolynomial.eval (z' a)
            (MvPolynomial.monomial (α : Fin m →₀ ℕ) (1:ℝ)))) with hSdef
  have hbox : ∀ v : Fin m →₀ ℕ, v ∈ boxMonomials m e →
      (fun a => MvPolynomial.eval (z' a) (MvPolynomial.monomial v (1:ℝ))) ∈ S := by
    intro v hv
    exact Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩
  have key : ∀ d : ℕ, ∀ p : MvPolynomial (Fin m) ℝ, p.totalDegree ≤ d →
      (fun a => MvPolynomial.eval (z' a) p) ∈ S := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro p hp
      have hmono : ∀ v : Fin m →₀ ℕ, (v.sum fun _ n => n) ≤ d →
          (fun a => MvPolynomial.eval (z' a) (MvPolynomial.monomial v (1:ℝ))) ∈ S := by
        intro v hv
        by_cases hb : ∀ i, v i ≤ e
        · exact hbox v ((mem_boxMonomials v).mpr hb)
        · push_neg at hb
          obtain ⟨i, hi⟩ := hb
          set β := v.update i (v i - (e+1)) with hβ
          have hsplit : v = β + Finsupp.single i (e+1) := by
            ext j
            by_cases hj : j = i
            · subst hj
              simp [hβ, Finsupp.coe_update]
              omega
            · have hij : i ≠ j := fun h => hj h.symm
              simp [hβ, Finsupp.coe_update, Function.update_of_ne hj,
                hij]
          have hsum : (v.sum fun _ n => n) = (β.sum fun _ n => n) + (e + 1) := by
            conv_lhs => rw [hsplit]
            rw [Finsupp.sum_add_index' (by intro a; rfl) (by intro a b₁ b₂; rfl)]
            congr 1
            exact Finsupp.sum_single_index rfl
          have hmv : (MvPolynomial.monomial v (1:ℝ))
              = MvPolynomial.monomial β 1 * MvPolynomial.X i ^ (e+1) := by
            rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, ← hsplit, mul_one]
          set q : MvPolynomial (Fin m) ℝ :=
            MvPolynomial.C (-t⁻¹) * (MvPolynomial.monomial β 1 * F i) with hq
          have hev : (fun a => MvPolynomial.eval (z' a) (MvPolynomial.monomial v (1:ℝ)))
              = (fun a => MvPolynomial.eval (z' a) q) := by
            funext a
            have h1 := hz' a i
            have h2 : (z' a i) ^ (e+1) = -t⁻¹ * MvPolynomial.eval (z' a) (F i) := by
              field_simp
              linarith [h1]
            rw [hmv, hq]
            simp only [map_mul, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C, h2]
            ring
          have hdegq : q.totalDegree ≤ (β.sum fun _ n => n) + e := by
            calc q.totalDegree ≤ (MvPolynomial.C (-t⁻¹) : MvPolynomial (Fin m) ℝ).totalDegree
                  + (MvPolynomial.monomial β (1:ℝ) * F i).totalDegree :=
                  MvPolynomial.totalDegree_mul _ _
              _ ≤ 0 + ((MvPolynomial.monomial β (1:ℝ)).totalDegree + (F i).totalDegree) := by
                  gcongr
                  · exact le_of_eq (MvPolynomial.totalDegree_C _)
                  · exact MvPolynomial.totalDegree_mul _ _
              _ ≤ (β.sum fun _ n => n) + e := by
                  rw [MvPolynomial.totalDegree_monomial β one_ne_zero]
                  simpa using hdeg i
          rw [hev]
          have hlt : (β.sum fun _ n => n) + e < d := by omega
          exact IH _ hlt q hdegq
      have hpe : (fun a => MvPolynomial.eval (z' a) p)
          = ∑ v ∈ p.support, (fun a => MvPolynomial.eval (z' a)
              (MvPolynomial.monomial v (MvPolynomial.coeff v p))) := by
        funext a
        rw [Finset.sum_apply]
        conv_lhs => rw [MvPolynomial.as_sum p]
        rw [map_sum]
      rw [hpe]
      refine Submodule.sum_mem _ ?_
      intro v hv
      have hdv : (v.sum fun _ n => n) ≤ d := le_trans (MvPolynomial.le_totalDegree hv) hp
      have := Submodule.smul_mem S (MvPolynomial.coeff v p) (hmono v hdv)
      convert this using 1
      funext a
      simp [MvPolynomial.eval_monomial]
  intro p
  exact key p.totalDegree p le_rfl

/-- Existence of a coordinate separating two distinct points. -/
theorem exists_coordinate_separating {m : ℕ} {z1 z2 : Fin m → ℝ} (h : z1 ≠ z2) :
    ∃ j : Fin m, z1 j ≠ z2 j := by
  contrapose! h
  ext j
  exact h j

noncomputable def separator_poly {m : ℕ} (z1 z2 : Fin m → ℝ) (h : z1 ≠ z2) :
    MvPolynomial (Fin m) ℝ :=
  let j := Classical.choose (exists_coordinate_separating h)
  let c := z1 j - z2 j
  (MvPolynomial.X j - MvPolynomial.C (z2 j)) * MvPolynomial.C c⁻¹

lemma eval_separator_poly_self {m : ℕ} (z1 z2 : Fin m → ℝ) (h : z1 ≠ z2) :
    MvPolynomial.eval z1 (separator_poly z1 z2 h) = 1 := by
  dsimp [separator_poly]
  have hj : z1 (Classical.choose (exists_coordinate_separating h)) ≠
      z2 (Classical.choose (exists_coordinate_separating h)) :=
    Classical.choose_spec (exists_coordinate_separating h)
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
  exact mul_inv_cancel₀ (sub_ne_zero.mpr hj)

lemma eval_separator_poly_other {m : ℕ} (z1 z2 : Fin m → ℝ) (h : z1 ≠ z2) :
    MvPolynomial.eval z2 (separator_poly z1 z2 h) = 0 := by
  dsimp [separator_poly]
  simp

noncomputable def point_separator {m : ℕ} {ι : Type} [Fintype ι]
    (z' : ι → Fin m → ℝ) (hinj : Function.Injective z') (a : ι) : MvPolynomial (Fin m) ℝ :=
  by classical exact
    let s := Finset.univ \ {a}
    Finset.prod s (fun b =>
      if h : a = b then 1
      else separator_poly (z' a) (z' b) (fun heq => h (hinj heq)))

lemma eval_point_separator_self {m : ℕ} {ι : Type} [Fintype ι]
    (z' : ι → Fin m → ℝ) (hinj : Function.Injective z') (a : ι) :
    MvPolynomial.eval (z' a) (point_separator z' hinj a) = 1 := by
  dsimp [point_separator]
  rw [map_prod]
  apply Finset.prod_eq_one
  intro b hb
  have hne : a ≠ b := by
    intro heq
    subst heq
    simp at hb
  rw [dif_neg hne]
  exact eval_separator_poly_self _ _ _

lemma eval_point_separator_other {m : ℕ} {ι : Type} [Fintype ι]
    (z' : ι → Fin m → ℝ) (hinj : Function.Injective z') (a b : ι) (hneq : a ≠ b) :
    MvPolynomial.eval (z' b) (point_separator z' hinj a) = 0 := by
  dsimp [point_separator]
  rw [map_prod]
  apply Finset.prod_eq_zero (i := b)
  · simp [hneq.symm]
  · rw [dif_neg hneq]
    exact eval_separator_poly_other _ _ _

/-- Stage D, Layer 4: Explicit Lagrange separators plus finrank.
Polynomial evaluations span the full function space on the selected distinct roots. -/
theorem span_eval_eq_top {m : ℕ} {ι : Type} [Finite ι] (z' : ι → Fin m → ℝ)
    (hinj : Function.Injective z') :
    Submodule.span ℝ (Set.range (fun p : MvPolynomial (Fin m) ℝ =>
      (fun a => MvPolynomial.eval (z' a) p))) = ⊤ := by
  haveI := Fintype.ofFinite ι
  rw [eq_top_iff]
  intro f _
  let p := ∑ a : ι, MvPolynomial.C (f a) * point_separator z' hinj a
  have hp : f ∈ Submodule.span ℝ (Set.range (fun p : MvPolynomial (Fin m) ℝ =>
      (fun a => MvPolynomial.eval (z' a) p))) := by
    apply Submodule.subset_span
    refine ⟨p, ?_⟩
    ext b
    dsimp [p]
    rw [map_sum]
    simp only [map_mul, MvPolynomial.eval_C]
    rw [Fintype.sum_eq_single b]
    · simp [eval_point_separator_self]
    · intro c hcb
      simp [eval_point_separator_other _ _ _ _ hcb]
  exact hp

/- Stage D kernel (THE monument), remaining nondegenerate case `0 < m`, `0 < e`. -/
theorem bezout_kernel_main {m e : ℕ} (_hm : 0 < m) (_he : 0 < e)
    (F : Fin m → MvPolynomial (Fin m) ℝ)
    (hdeg : ∀ i, (F i).totalDegree ≤ e)
    {ι : Type} [Finite ι] (z : ι → Fin m → ℝ) (hinj : Function.Injective z)
    (hz : ∀ a, IsNondegenerateSolution F (z a)) :
    Nat.card ι ≤ (2 * e) ^ m := by
  have he_bound : (e + 1) ^ m ≤ (2 * e) ^ m := by
    apply Nat.pow_le_pow_left
    omega
  obtain ⟨t, z', ht, hz'inj, hz'⟩ := exists_common_parameter_perturbation F z hinj hz
  have htop := span_eval_eq_top z' hz'inj
  have hsub : ⊤ ≤ Submodule.span ℝ
      (Set.range fun (α : boxMonomials m e) =>
        (fun a => MvPolynomial.eval (z' a) (MvPolynomial.monomial (α : Fin m →₀ ℕ) 1))) := by
    rw [← htop]
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact eval_span_box_monomials F hdeg t ht z' hz' p
  have htop_eq : Submodule.span ℝ
      (Set.range fun (α : boxMonomials m e) =>
        (fun a => MvPolynomial.eval (z' a) (MvPolynomial.monomial (α : Fin m →₀ ℕ) 1))) = ⊤ :=
    top_le_iff.mp hsub
  have hdim := finrank_le_of_span_eq_top htop_eq
  haveI := Fintype.ofFinite ι
  have hcard_pi : Module.finrank ℝ (ι → ℝ) = Fintype.card ι := Module.finrank_pi ℝ
  have hcard_box : Fintype.card (boxMonomials m e) = (e + 1) ^ m := by
    rw [Fintype.card_coe, card_boxMonomials]
  rw [hcard_pi] at hdim
  rw [Nat.card_eq_fintype_card]
  have hdim2 : Fintype.card ι ≤ (e + 1) ^ m := by
    calc Fintype.card ι ≤ Fintype.card (boxMonomials m e) := hdim
      _ = (e + 1) ^ m := hcard_box
  exact le_trans hdim2 he_bound

/- Stage D kernel (THE monument) -/
theorem bezout_kernel {m e : ℕ} (F : Fin m → MvPolynomial (Fin m) ℝ)
    (hdeg : ∀ i, (F i).totalDegree ≤ e)
    {ι : Type} [Finite ι] (z : ι → Fin m → ℝ) (hinj : Function.Injective z)
    (hz : ∀ a, IsNondegenerateSolution F (z a)) :
    Nat.card ι ≤ (2 * e) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact bezout_kernel_dim_zero z hinj
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact bezout_kernel_deg_zero hm F hdeg z hz
  · exact bezout_kernel_main hm he F hdeg z hinj hz

end Warren
