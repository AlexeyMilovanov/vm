import Warren.Bezout.Defs
import Warren.Phi
import Mathlib

namespace Warren

noncomputable def criticalSystem {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (v : Fin m → ℝ) : Fin m → MvPolynomial (Fin m) ℝ :=
  fun j => (1 + sigmaSq m) * MvPolynomial.pderiv j (W^2) - (2*(D+1) : ℝ) • (W^2 * MvPolynomial.X j)
             - (v j) • (1 + sigmaSq m)^(D+2)

/-- Denominator-cleared form of the Stage C critical system: evaluating the `j`-th
equation at `x` is `(1+σ²(x))^(D+2)` times the `j`-th coordinate derivative of `phi`
shifted by the perturbation `v j`. In particular `x` solves the system iff
`∇ phi (x) = v`. -/
theorem eval_criticalSystem_eq {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (v : Fin m → ℝ) (x : Fin m → ℝ) (j : Fin m) :
    MvPolynomial.eval x (criticalSystem D W v j)
      = (1 + MvPolynomial.eval x (sigmaSq m)) ^ (D + 2) *
          (fderiv ℝ (phi D W) x (fun i => if i = j then 1 else 0) - v j) := by
  have hpos : 0 < 1 + MvPolynomial.eval x (sigmaSq m) := one_add_eval_sigmaSq_pos x
  have hne : (1 + MvPolynomial.eval x (sigmaSq m)) ^ (D + 2) ≠ 0 := by positivity
  rw [fderiv_phi_apply_coord]
  simp only [criticalSystem, map_sub, map_mul, map_add, map_one, map_pow,
    MvPolynomial.smul_eval, MvPolynomial.eval_X]
  field_simp

/-- `x` is a zero of the Stage C critical system exactly when the gradient of `phi`
at `x` equals the perturbation vector `v`. -/
theorem eval_criticalSystem_eq_zero_iff {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (v : Fin m → ℝ) (x : Fin m → ℝ) (j : Fin m) :
    MvPolynomial.eval x (criticalSystem D W v j) = 0 ↔
      fderiv ℝ (phi D W) x (fun i => if i = j then 1 else 0) = v j := by
  have hne : (1 + MvPolynomial.eval x (sigmaSq m)) ^ (D + 2) ≠ 0 := by
    have := one_add_eval_sigmaSq_pos (m := m) x
    positivity
  rw [eval_criticalSystem_eq, mul_eq_zero, sub_eq_zero]
  simp [hne]

theorem totalDegree_sigmaSq_le (m : ℕ) : (sigmaSq m).totalDegree ≤ 2 := by
  refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le ?_)
  intro j _
  exact le_trans (MvPolynomial.totalDegree_pow _ _) (by simp [MvPolynomial.totalDegree_X])

theorem totalDegree_one_add_sigmaSq_le (m : ℕ) : (1 + sigmaSq m).totalDegree ≤ 2 := by
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  simp [MvPolynomial.totalDegree_one, totalDegree_sigmaSq_le m]

/-- Every equation of the Stage C critical system built from a polynomial `W` of
total degree `≤ D` has total degree at most `2 * D + 4`. -/
theorem totalDegree_criticalSystem_le {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (hW : W.totalDegree ≤ D) (v : Fin m → ℝ) (j : Fin m) :
    (criticalSystem D W v j).totalDegree ≤ 2 * D + 4 := by
  have hS : (1 + sigmaSq m).totalDegree ≤ 2 := totalDegree_one_add_sigmaSq_le m
  have hW2 : (W ^ 2).totalDegree ≤ 2 * D :=
    le_trans (MvPolynomial.totalDegree_pow _ _) (Nat.mul_le_mul_left 2 hW)
  have hT1 : ((1 + sigmaSq m) * MvPolynomial.pderiv j (W ^ 2)).totalDegree ≤ 2 * D + 4 := by
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have := totalDegree_pderiv_le m j (W ^ 2)
    omega
  have hT2 : (((2 * (D + 1) : ℝ)) • (W ^ 2 * MvPolynomial.X j)).totalDegree ≤ 2 * D + 4 := by
    refine le_trans (MvPolynomial.totalDegree_smul_le _ _) ?_
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have hX : (MvPolynomial.X j : MvPolynomial (Fin m) ℝ).totalDegree = 1 :=
      MvPolynomial.totalDegree_X j
    omega
  have hT3 : ((v j) • (1 + sigmaSq m) ^ (D + 2)).totalDegree ≤ 2 * D + 4 := by
    refine le_trans (MvPolynomial.totalDegree_smul_le _ _) ?_
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    calc (D + 2) * (1 + sigmaSq m).totalDegree ≤ (D + 2) * 2 := Nat.mul_le_mul_left _ hS
      _ = 2 * D + 4 := by ring
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  exact max_le (le_trans (MvPolynomial.totalDegree_sub _ _) (max_le hT1 hT2)) hT3

open MeasureTheory Metric Set

theorem exists_regularValue_mem_ball {m : ℕ} (g : (Fin m → ℝ) → (Fin m → ℝ))
    (g' : (Fin m → ℝ) → ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ)))
    (hg : ∀ x, HasFDerivAt g (g' x) x) {r : ℝ} (hr : 0 < r) :
    ∃ v, ‖v‖ < r ∧ ∀ x, g x = v → (g' x).det ≠ 0 := by
  let s := {x | (g' x).det = 0}
  have H : volume (g '' s) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    · intro x hx
      exact (hg x).hasFDerivWithinAt
    · intro x hx
      exact hx
  have H2 : 0 < volume (ball (0 : Fin m → ℝ) r) := measure_ball_pos volume 0 hr
  have H3 : ¬ (ball (0 : Fin m → ℝ) r ⊆ g '' s) := by
    intro h
    have : volume (ball (0 : Fin m → ℝ) r) ≤ volume (g '' s) := measure_mono h
    rw [H] at this
    exact lt_irrefl _ (lt_of_lt_of_le H2 this)
  obtain ⟨v, hv, hns⟩ : ∃ v ∈ ball (0 : Fin m → ℝ) r, v ∉ g '' s := not_subset.mp H3
  use v
  constructor
  · simpa using hv
  · intro x hx hd
    have : v ∈ g '' s := ⟨x, hd, hx⟩
    contradiction

theorem closure_connectedComponentIn_diff_subset_compl {X : Type*}
    [TopologicalSpace X] [LocallyConnectedSpace X]
    (O : Set X) (x : X) (hO : IsOpen O) (hx : x ∈ O) :
    frontier (connectedComponentIn O x) ∩ O = ∅ := by
  have op_S : IsOpen (connectedComponentIn O x) := IsOpen.connectedComponentIn hO
  ext y
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hy_front hyO
  have eq_S : connectedComponentIn O x =
      (Subtype.val : O → X) '' connectedComponent (⟨x, hx⟩ : O) :=
    connectedComponentIn_eq_image hx
  have h_cl : IsClosed (connectedComponent (⟨x, hx⟩ : O)) := isClosed_connectedComponent
  have hy_clos : y ∈ closure (connectedComponentIn O x) := by
    change y ∈ closure _ \ interior _ at hy_front
    exact hy_front.1
  have hy_nint : y ∉ interior (connectedComponentIn O x) := by
    change y ∈ closure _ \ interior _ at hy_front
    exact hy_front.2
  rw [interior_eq_iff_isOpen.mpr op_S] at hy_nint
  let y' : O := ⟨y, hyO⟩
  have hy_clos' : y ∈ closure ((Subtype.val : O → X) '' connectedComponent (⟨x, hx⟩ : O)) :=
    by rwa [←eq_S]
  have hy_clos_sub : y' ∈ closure (connectedComponent (⟨x, hx⟩ : O)) := by rwa [closure_subtype]
  have hy_in_comp : y' ∈ connectedComponent (⟨x, hx⟩ : O) :=
    by rwa [IsClosed.closure_eq h_cl] at hy_clos_sub
  have hy_in_S : y ∈ connectedComponentIn O x := by
    rw [eq_S]
    exact ⟨y', hy_in_comp, rfl⟩
  exact hy_nint hy_in_S

theorem exists_interior_localMax_of_frontier_gap
    {X : Type*} [MetricSpace X] {f : X → ℝ} {s : Set X} {x : X}
    (hs : IsCompact (closure s)) (hx : x ∈ s)
    (hcont : ContinuousOn f (closure s))
    (hgap : ∀ y ∈ frontier s, f y < f x) :
    ∃ z ∈ s, IsLocalMax f z := by
  have hne : (closure s).Nonempty := ⟨x, subset_closure hx⟩
  obtain ⟨z, hz_clos, hz_max⟩ := hs.exists_isMaxOn hne hcont
  have h_zx : f x ≤ f z := hz_max (subset_closure hx)
  have hz_not_front : z ∉ frontier s := by
    intro hz_front
    have : f z < f x := hgap z hz_front
    linarith
  have hz_int : z ∈ interior s := by
    have hf : frontier s = closure s \ interior s := rfl
    rw [hf] at hz_not_front
    simp only [mem_diff, not_and, not_not] at hz_not_front
    exact hz_not_front hz_clos
  have hz_s : z ∈ s := interior_subset hz_int
  use z, hz_s
  have h_max_int : IsMaxOn f (interior s) z := by
    intro y hy
    exact hz_max (interior_subset_closure hy)
  have h_nhds : interior s ∈ nhds z := IsOpen.mem_nhds isOpen_interior hz_int
  exact IsMaxOn.isLocalMax h_max_int h_nhds

/-- Sup-norm perturbation estimate for the linear term of the Stage C argument.
On `Fin m → ℝ` (which carries the sup norm) the coordinate pairing obeys
`|∑ i, v i * x i| ≤ m * ‖v‖ * ‖x‖`; the factor `m` is essential and must not be
dropped. -/
theorem abs_sum_mul_le {m : ℕ} (v x : Fin m → ℝ) :
    |∑ i, v i * x i| ≤ m * ‖v‖ * ‖x‖ := by
  have hpt : ∀ i : Fin m, |v i * x i| ≤ ‖v‖ * ‖x‖ := by
    intro i
    rw [abs_mul]
    have hv : |v i| ≤ ‖v‖ := by simpa using norm_le_pi_norm v i
    have hx : |x i| ≤ ‖x‖ := by simpa using norm_le_pi_norm x i
    exact mul_le_mul hv hx (abs_nonneg _) (norm_nonneg _)
  calc |∑ i, v i * x i| ≤ ∑ i, |v i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, ‖v‖ * ‖x‖ := Finset.sum_le_sum (fun i _ => hpt i)
    _ = m * ‖v‖ * ‖x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Bridge from a perturbed interior local maximum to the gradient equation
`∇ φ (z) = v`: if `z` is a local maximum of `x ↦ φ(x) − ⟨v, x⟩`, then each
coordinate derivative of `phi` at `z` equals the corresponding entry of `v`.
Combined with `eval_criticalSystem_eq_zero_iff`, this shows `z` is a zero of the
Stage C critical system. -/
theorem fderiv_phi_apply_eq_of_isLocalMax {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (v : Fin m → ℝ) (z : Fin m → ℝ)
    (hmax : IsLocalMax (fun x => phi D W x - ∑ i, v i * x i) z) (j : Fin m) :
    fderiv ℝ (phi D W) z (fun i => if i = j then 1 else 0) = v j := by
  set L : (Fin m → ℝ) →L[ℝ] ℝ := ∑ i, v i • (ContinuousLinearMap.proj i) with hL
  have hLfun : (fun y : Fin m → ℝ => ∑ i, v i * y i) = (L : (Fin m → ℝ) → ℝ) := by
    funext y
    simp [hL, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply]
  have hLderiv : HasFDerivAt (fun y : Fin m → ℝ => ∑ i, v i * y i) L z := by
    rw [hLfun]; exact L.hasFDerivAt
  have hphiD : HasFDerivAt (phi D W) (fderiv ℝ (phi D W) z) z :=
    (differentiableAt_phi D W z).hasFDerivAt
  have hsub : HasFDerivAt (fun x => phi D W x - ∑ i, v i * x i)
      (fderiv ℝ (phi D W) z - L) z := hphiD.sub hLderiv
  have hzero : fderiv ℝ (phi D W) z - L = 0 := hmax.hasFDerivAt_eq_zero hsub
  have hfeq : fderiv ℝ (phi D W) z = L := sub_eq_zero.mp hzero
  rw [hfeq, hL]
  simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, mul_ite, Finset.sum_ite_eq']


/-- Components of a smaller set inject into components of a larger one: if `U ⊆ V`
and the points `x a` lie in `U`, injectivity of `a ↦ connectedComponentIn V (x a)`
forces injectivity of `a ↦ connectedComponentIn U (x a)`. -/
theorem injective_connectedComponentIn_of_subset {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUV : U ⊆ V) {ι : Type*} (x : ι → X) (hx : ∀ a, x a ∈ U)
    (hinj : Function.Injective (fun a => connectedComponentIn V (x a))) :
    Function.Injective (fun a => connectedComponentIn U (x a)) := by
  intro a b hab
  simp only at hab
  have hb : x b ∈ connectedComponentIn U (x a) := by
    rw [hab]; exact mem_connectedComponentIn (hx b)
  have hbV : x b ∈ connectedComponentIn V (x a) := connectedComponentIn_mono (x a) hUV hb
  exact hinj (connectedComponentIn_eq hbV)

/-- Where `phi` is positive, `W` does not vanish; hence `{φ > δ} ⊆ {W ≠ 0}` for `δ ≥ 0`. -/
theorem eval_ne_zero_of_phi_pos {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ) {x : Fin m → ℝ}
    (hx : 0 < phi D W x) : MvPolynomial.eval x W ≠ 0 := by
  intro h
  rw [phi, h] at hx
  simp at hx

/-- Strict superlevel sets of `phi` are open. -/
theorem isOpen_phi_gt {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ) (δ : ℝ) :
    IsOpen {x : Fin m → ℝ | δ < phi D W x} :=
  isOpen_lt continuous_const (differentiable_phi D W).continuous

/-- Boundary level bound: on the frontier of a connected component of `{φ > δ}` the
functional `phi` is at most `δ`. -/
theorem phi_le_of_mem_frontier_component {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    {δ : ℝ} (x₀ : Fin m → ℝ) (hx₀ : δ < phi D W x₀)
    {y : Fin m → ℝ} (hy : y ∈ frontier (connectedComponentIn {x | δ < phi D W x} x₀)) :
    phi D W y ≤ δ := by
  by_contra h
  push_neg at h
  have hdisj := closure_connectedComponentIn_diff_subset_compl
    {x : Fin m → ℝ | δ < phi D W x} x₀ (isOpen_phi_gt D W δ) hx₀
  have hmem : y ∈ frontier (connectedComponentIn {x : Fin m → ℝ | δ < phi D W x} x₀) ∩
      {x : Fin m → ℝ | δ < phi D W x} := ⟨hy, h⟩
  rw [hdisj] at hmem
  exact hmem

/-- Each connected component of `{φ > δ}` (with `δ > 0`) has compact closure: it sits
inside the compact superlevel set `{φ ≥ δ}`. -/
theorem isCompact_closure_component_phi {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (hW : W.totalDegree ≤ D) {δ : ℝ} (hδ : 0 < δ) (x₀ : Fin m → ℝ) :
    IsCompact (closure (connectedComponentIn {x : Fin m → ℝ | δ < phi D W x} x₀)) := by
  refine IsCompact.of_isClosed_subset (phi_superlevel_isCompact D W hW hδ) isClosed_closure ?_
  refine closure_minimal ?_ (isClosed_le continuous_const (differentiable_phi D W).continuous)
  intro y hy
  have h := connectedComponentIn_subset {x : Fin m → ℝ | δ < phi D W x} x₀ hy
  simp only [Set.mem_setOf_eq] at h ⊢
  exact le_of_lt h

/-- The closure of a connected component of `{φ > δ}` sits inside the closed
superlevel set `{φ ≥ δ}`. -/
theorem closure_component_subset_superlevel {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    {δ : ℝ} (x₀ : Fin m → ℝ) :
    closure (connectedComponentIn {x : Fin m → ℝ | δ < phi D W x} x₀)
      ⊆ {x : Fin m → ℝ | δ ≤ phi D W x} := by
  refine closure_minimal ?_ (isClosed_le continuous_const (differentiable_phi D W).continuous)
  intro y hy
  have h := connectedComponentIn_subset {x : Fin m → ℝ | δ < phi D W x} x₀ hy
  simp only [Set.mem_setOf_eq] at h ⊢
  exact le_of_lt h

/-- A uniform radius bound for the compact superlevel set `{φ ≥ δ}`. -/
theorem exists_bound_on_phi_superlevel {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (hW : W.totalDegree ≤ D) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y : Fin m → ℝ, δ ≤ phi D W y → ‖y‖ ≤ R := by
  obtain ⟨R, hR⟩ := (phi_superlevel_isCompact D W hW hδ).isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun y hy => ?_⟩
  have hmem := hR hy
  simp only [Metric.mem_closedBall, dist_zero_right] at hmem
  exact le_trans hmem (le_max_left _ _)

/-- Stage C perturbed maximum: for a perturbation `v` small enough that
`2m‖v‖R < φ(x₀) − δ` (where `R` bounds the superlevel set `{φ ≥ δ}`), the function
`x ↦ φ(x) − ⟨v, x⟩` attains a local maximum at some point of the connected component
of `{φ > δ}` containing `x₀`. -/
theorem exists_localMax_in_component {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (hW : W.totalDegree ≤ D) {δ : ℝ} (hδ : 0 < δ) (x₀ : Fin m → ℝ) (hx₀ : δ < phi D W x₀)
    {R : ℝ} (hR : ∀ y : Fin m → ℝ, δ ≤ phi D W y → ‖y‖ ≤ R)
    (v : Fin m → ℝ) (hv : 2 * m * ‖v‖ * R < phi D W x₀ - δ) :
    ∃ z ∈ connectedComponentIn {x : Fin m → ℝ | δ < phi D W x} x₀,
      IsLocalMax (fun x => phi D W x - ∑ i, v i * x i) z := by
  have hcont : Continuous fun x : Fin m → ℝ => phi D W x - ∑ i, v i * x i :=
    (differentiable_phi D W).continuous.sub
      (continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i))
  have hx₀S : x₀ ∈ connectedComponentIn {x : Fin m → ℝ | δ < phi D W x} x₀ :=
    mem_connectedComponentIn hx₀
  have hx₀R : ‖x₀‖ ≤ R := hR x₀ (le_of_lt hx₀)
  refine exists_interior_localMax_of_frontier_gap
    (isCompact_closure_component_phi D W hW hδ x₀) hx₀S hcont.continuousOn ?_
  intro y hy
  have hyd : δ ≤ phi D W y := closure_component_subset_superlevel D W x₀ hy.1
  have hyR : ‖y‖ ≤ R := hR y hyd
  have hφy : phi D W y ≤ δ := phi_le_of_mem_frontier_component D W x₀ hx₀ hy
  have hby : |∑ i, v i * y i| ≤ m * ‖v‖ * R :=
    le_trans (abs_sum_mul_le v y) (mul_le_mul_of_nonneg_left hyR (by positivity))
  have hbx : |∑ i, v i * x₀ i| ≤ m * ‖v‖ * R :=
    le_trans (abs_sum_mul_le v x₀) (mul_le_mul_of_nonneg_left hx₀R (by positivity))
  have h1 := (abs_le.mp hby).1
  have h2 := (abs_le.mp hbx).2
  change phi D W y - ∑ i, v i * y i < phi D W x₀ - ∑ i, v i * x₀ i
  linarith

/-- Sard for the gradient map of `phi`: in every ball around the origin there is a
perturbation `v` which is a regular value of `∇φ`, i.e. at every solution of
`∇φ(x) = v` the derivative of the gradient map (the Hessian of `φ`) is invertible. -/
theorem exists_regularValue_gradPhi {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    {r : ℝ} (hr : 0 < r) :
    ∃ v : Fin m → ℝ, ‖v‖ < r ∧
      ∀ x : Fin m → ℝ, gradPhi D W x = v → (fderiv ℝ (gradPhi D W) x).det ≠ 0 :=
  exists_regularValue_mem_ball (gradPhi D W) (fun x => fderiv ℝ (gradPhi D W) x)
    (fun x => (differentiable_gradPhi D W x).hasFDerivAt) hr

/-- Derivative of the `i`-th equation of the critical system at a solution point: the
factor `(1+σ²)^(D+2)` differentiates out because the second factor `∂_i φ − v i`
vanishes there. -/
theorem hasFDerivAt_eval_criticalSystem {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (v : Fin m → ℝ) (z : Fin m → ℝ) (hz : gradPhi D W z = v) (i : Fin m) :
    HasFDerivAt (fun y => MvPolynomial.eval y (criticalSystem D W v i))
      ((1 + MvPolynomial.eval z (sigmaSq m)) ^ (D + 2) •
        (fderiv ℝ (fun y => gradPhi D W y i) z)) z := by
  have hgfun : (fun y : Fin m → ℝ => MvPolynomial.eval y (criticalSystem D W v i))
      = fun y => (1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 2) * (gradPhi D W y i - v i) := by
    funext y
    exact eval_criticalSystem_eq D W v y i
  have hg : HasFDerivAt (fun y : Fin m → ℝ => (1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 2))
      (fderiv ℝ (fun y : Fin m → ℝ => (1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 2)) z) z := by
    apply DifferentiableAt.hasFDerivAt
    exact ((differentiableAt_const _).add
      ((contDiff_eval_mvPolynomial m (sigmaSq m) 1).differentiable one_ne_zero z)).pow _
  have hcomp : DifferentiableAt ℝ (fun y : Fin m → ℝ => gradPhi D W y i) z :=
    ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).differentiableAt).comp z
      (differentiable_gradPhi D W z)
  have hh : HasFDerivAt (fun y : Fin m → ℝ => gradPhi D W y i - v i)
      (fderiv ℝ (fun y : Fin m → ℝ => gradPhi D W y i) z) z :=
    (hcomp.hasFDerivAt).sub_const (v i)
  have hprod := hg.mul hh
  have heq_fun : (fun y : Fin m → ℝ => (1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 2)) * (fun y : Fin m → ℝ => gradPhi D W y i - v i) =
      (fun y : Fin m → ℝ => (1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 2) * (gradPhi D W y i - v i)) := by
    funext y; rfl
  rw [heq_fun] at hprod
  have hzero : gradPhi D W z i - v i = 0 := by rw [hz]; ring
  have heq_deriv : (1 + MvPolynomial.eval z (sigmaSq m)) ^ (D + 2) • fderiv ℝ (fun y : Fin m → ℝ => gradPhi D W y i) z + (gradPhi D W z i - v i) • fderiv ℝ (fun y : Fin m → ℝ => (1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 2)) z =
      (1 + MvPolynomial.eval z (sigmaSq m)) ^ (D + 2) • (fderiv ℝ (fun y : Fin m → ℝ => gradPhi D W y i) z) := by
    rw [hzero]
    ext y
    simp
  rw [heq_deriv] at hprod
  rw [hgfun]
  exact hprod

/-- Coordinate form of the derivative of the gradient map. -/
theorem fderiv_gradPhi_coord {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ) (z w : Fin m → ℝ)
    (i : Fin m) :
    fderiv ℝ (fun y => gradPhi D W y i) z w = (fderiv ℝ (gradPhi D W) z w) i := by
  have h : HasFDerivAt (fun y => gradPhi D W y i)
      ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ (gradPhi D W) z)) z :=
    (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z
      (differentiable_gradPhi D W z).hasFDerivAt
  rw [h.fderiv]
  rfl

/-- Jacobian transfer: at a point `z` where `∇φ(z) = v` and the Hessian of `φ` is
invertible, the Jacobian of the polynomial critical system is
`(1+σ²(z))^(D+2)` times the Hessian, hence nonsingular. -/
theorem det_jacobianMatrix_criticalSystem_ne_zero {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (v : Fin m → ℝ) (z : Fin m → ℝ) (hz : gradPhi D W z = v)
    (hdet : (fderiv ℝ (gradPhi D W) z).det ≠ 0) :
    (jacobianMatrix (criticalSystem D W v) z).det ≠ 0 := by
  classical
  set c : ℝ := (1 + MvPolynomial.eval z (sigmaSq m)) ^ (D + 2) with hc
  have hcpos : 0 < c := by
    have := one_add_eval_sigmaSq_pos (m := m) z
    rw [hc]; positivity
  set H : Matrix (Fin m) (Fin m) ℝ :=
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin m))
      ((fderiv ℝ (gradPhi D W) z : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))) with hH
  have hHdet : H.det ≠ 0 := by
    rw [hH, LinearMap.det_toMatrix]
    exact hdet
  have hJ : jacobianMatrix (criticalSystem D W v) z = c • H := by
    funext i j
    have h1 := hasFDerivAt_eval_mvPolynomial m (criticalSystem D W v i) z
    have h2 := hasFDerivAt_eval_criticalSystem D W v z hz i
    have heq := h1.unique h2
    have hap := congrArg (fun L : (Fin m → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ))) heq
    simp only [FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, smul_apply] at hap
    rw [show ∑ k, MvPolynomial.eval z (MvPolynomial.pderiv k (criticalSystem D W v i)) *
        (Pi.single j (1 : ℝ) : Fin m → ℝ) k
        = MvPolynomial.eval z (MvPolynomial.pderiv j (criticalSystem D W v i)) from by
      simp [Pi.single_apply]] at hap
    simp only [jacobianMatrix, Matrix.smul_apply, smul_eq_mul, hH, LinearMap.toMatrix_apply,
      Pi.basisFun_apply, Pi.basisFun_repr, ContinuousLinearMap.coe_coe]
    rw [← fderiv_gradPhi_coord D W z (Pi.single j (1 : ℝ)) i]
    exact hap
  rw [hJ, Matrix.det_smul]
  simp only [Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero _ (ne_of_gt hcpos)) hHdet

/- Stage C aggregate -/
theorem exists_injective_criticalPoints {m D : ℕ} (hm : 0 < m)
    (W : MvPolynomial (Fin m) ℝ) (hW : W.totalDegree ≤ D)
    {ι : Type} [Finite ι] [Nonempty ι] (x : ι → Fin m → ℝ)
    (hx : ∀ a, MvPolynomial.eval (x a) W ≠ 0)
    (hcomp : Function.Injective
      (fun a => connectedComponentIn {y | MvPolynomial.eval y W ≠ 0} (x a))) :
    ∃ (v : Fin m → ℝ) (z : ι → Fin m → ℝ), Function.Injective z ∧
      ∀ a, IsNondegenerateSolution (criticalSystem D W v) (z a) := by
  classical
  have hphipos : ∀ a, 0 < phi D W (x a) := by
    intro a
    have h1 : 0 < (MvPolynomial.eval (x a) W) ^ 2 := pow_two_pos_of_ne_zero (hx a)
    have h2 : 0 < (1 + MvPolynomial.eval (x a) (sigmaSq m)) ^ (D + 1) := by
      have := one_add_eval_sigmaSq_pos (m := m) (x a)
      positivity
    exact div_pos h1 h2
  obtain ⟨a₀, ha₀⟩ := Finite.exists_min (fun a => phi D W (x a))
  set δ : ℝ := phi D W (x a₀) / 2 with hδdef
  have hδ : 0 < δ := by
    have := hphipos a₀
    rw [hδdef]; linarith
  have hxδ : ∀ a, δ < phi D W (x a) := by
    intro a
    have h := ha₀ a
    have h0 := hphipos a₀
    rw [hδdef]
    linarith
  have hgap : ∀ a, δ ≤ phi D W (x a) - δ := by
    intro a
    have h := ha₀ a
    rw [hδdef]
    linarith
  obtain ⟨R, hR0, hR⟩ := exists_bound_on_phi_superlevel D W hW hδ
  have hden : 0 < 2 * (m : ℝ) * R + 1 := by positivity
  set r : ℝ := δ / (2 * (m : ℝ) * R + 1) with hrdef
  have hr : 0 < r := div_pos hδ hden
  obtain ⟨v, hvnorm, hvreg⟩ := exists_regularValue_gradPhi D W hr
  have hvsmall : ∀ a, 2 * (m : ℝ) * ‖v‖ * R < phi D W (x a) - δ := by
    intro a
    have h1 : 2 * (m : ℝ) * ‖v‖ * R ≤ ‖v‖ * (2 * (m : ℝ) * R + 1) := by
      nlinarith [norm_nonneg v]
    have h2 : ‖v‖ * (2 * (m : ℝ) * R + 1) < r * (2 * (m : ℝ) * R + 1) :=
      mul_lt_mul_of_pos_right hvnorm hden
    have h3 : r * (2 * (m : ℝ) * R + 1) = δ := by
      rw [hrdef]; field_simp
    have h4 := hgap a
    linarith
  have hzex : ∀ a, ∃ z ∈ connectedComponentIn {y : Fin m → ℝ | δ < phi D W y} (x a),
      IsLocalMax (fun y => phi D W y - ∑ i, v i * y i) z := fun a =>
    exists_localMax_in_component D W hW hδ (x a) (hxδ a) hR v (hvsmall a)
  choose z hzmem hzmax using hzex
  have hgrad : ∀ a, gradPhi D W (z a) = v := by
    intro a
    funext j
    exact fderiv_phi_apply_eq_of_isLocalMax D W v (z a) (hzmax a) j
  refine ⟨v, z, ?_, ?_⟩
  · have hUV : {y : Fin m → ℝ | δ < phi D W y} ⊆ {y : Fin m → ℝ | MvPolynomial.eval y W ≠ 0} :=
      fun y hy => eval_ne_zero_of_phi_pos D W (lt_trans hδ hy)
    have hinjU : Function.Injective
        (fun a => connectedComponentIn {y : Fin m → ℝ | δ < phi D W y} (x a)) :=
      injective_connectedComponentIn_of_subset hUV x (fun a => hxδ a) hcomp
    intro a b hab
    apply hinjU
    have h1 : connectedComponentIn {y : Fin m → ℝ | δ < phi D W y} (x a)
        = connectedComponentIn {y : Fin m → ℝ | δ < phi D W y} (z a) :=
      connectedComponentIn_eq (hzmem a)
    have h2 : connectedComponentIn {y : Fin m → ℝ | δ < phi D W y} (x b)
        = connectedComponentIn {y : Fin m → ℝ | δ < phi D W y} (z b) :=
      connectedComponentIn_eq (hzmem b)
    simp only
    rw [h1, h2, hab]
  · refine fun a => ⟨fun i => ?_, ?_⟩
    · rw [eval_criticalSystem_eq_zero_iff]
      exact fderiv_phi_apply_eq_of_isLocalMax D W v (z a) (hzmax a) i
    · exact det_jacobianMatrix_criticalSystem_ne_zero D W v (z a) (hgrad a)
        (hvreg (z a) (hgrad a))

end Warren
