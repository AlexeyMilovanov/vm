import Warren.Growth

namespace Warren

noncomputable def phi {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) : ℝ :=
  (MvPolynomial.eval x W)^2 / (1 + MvPolynomial.eval x (sigmaSq m))^(D+1)

theorem eval_sigmaSq {m : ℕ} (x : Fin m → ℝ) :
    MvPolynomial.eval x (sigmaSq m) = ∑ i, (x i) ^ 2 := by
  simp [sigmaSq]

theorem one_add_eval_sigmaSq_pos {m : ℕ} (x : Fin m → ℝ) :
    0 < 1 + MvPolynomial.eval x (sigmaSq m) := by
  have h : 0 ≤ MvPolynomial.eval x (sigmaSq m) := by
    rw [eval_sigmaSq]
    positivity
  linarith

theorem pderiv_sigmaSq {m : ℕ} (j : Fin m) :
    MvPolynomial.pderiv j (sigmaSq m) = 2 * MvPolynomial.X j := by
  classical
  rw [sigmaSq, map_sum, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [MvPolynomial.pderiv_X_of_ne hij]
  · simp

/-- Elementary quotient-rule arithmetic used to normalise the gradient of `phi`. -/
private theorem quot_aux (t P Wv xj : ℝ) (D : ℕ) (ht : 0 < t) :
    Wv * (-((t ^ (D + 1)) ^ 2)⁻¹ * (((D : ℝ) + 1) * t ^ D * (2 * xj))) + (t ^ (D + 1))⁻¹ * P
      = (t * P - 2 * ((D : ℝ) + 1) * Wv * xj) / t ^ (D + 2) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ha0 : t ^ D ≠ 0 := pow_ne_zero _ ht0
  rw [pow_succ t D, show t ^ (D + 2) = t ^ D * t ^ 2 by rw [pow_add]]
  field_simp
  ring

/-- Coordinate gradient of the compactifying functional `phi`, with the denominator
cleared: `∂_j φ = ((1+σ²)·∂_j(W²) - 2(D+1)·W²·x_j) / (1+σ²)^(D+2)`. -/
theorem fderiv_phi_apply_coord {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) (j : Fin m) :
    fderiv ℝ (phi D W) x (fun i => if i = j then 1 else 0)
      = ((1 + MvPolynomial.eval x (sigmaSq m))
            * MvPolynomial.eval x (MvPolynomial.pderiv j (W ^ 2))
          - 2 * ((D : ℝ) + 1) * MvPolynomial.eval x (W ^ 2) * x j)
        / (1 + MvPolynomial.eval x (sigmaSq m)) ^ (D + 2) := by
  classical
  have hpos : 0 < 1 + MvPolynomial.eval x (sigmaSq m) := one_add_eval_sigmaSq_pos x
  set Q : MvPolynomial (Fin m) ℝ := (1 + sigmaSq m) ^ (D + 1) with hQ
  have hfun : (fun y : Fin m → ℝ => MvPolynomial.eval y (W ^ 2))
      = fun y => (MvPolynomial.eval y W) ^ 2 := by funext y; simp
  have hN : HasFDerivAt (fun y => (MvPolynomial.eval y W) ^ 2)
      (∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i (W ^ 2)) •
        (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) x := by
    have h := hasFDerivAt_eval_mvPolynomial m (W ^ 2) x
    rwa [hfun] at h
  have hDen : HasFDerivAt (fun y => (1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 1))
      (∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i Q) •
        (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) x := by
    simpa [hQ] using hasFDerivAt_eval_mvPolynomial m Q x
  have hne : ((1 + MvPolynomial.eval x (sigmaSq m)) ^ (D + 1)) ≠ 0 := by positivity
  have hinv : HasFDerivAt (fun y => ((1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 1))⁻¹)
      ((-((((1 + MvPolynomial.eval x (sigmaSq m)) ^ (D + 1))) ^ 2)⁻¹) •
        (∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i Q) •
          (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ))) x :=
    (hasDerivAt_inv hne).comp_hasFDerivAt x hDen
  have hmul := hN.mul hinv
  have hphi : phi D W = (fun y => (MvPolynomial.eval y W) ^ 2)
      * (fun y => ((1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 1))⁻¹) := by
    funext y
    simp [phi, div_eq_mul_inv]
  rw [hphi, hmul.fderiv]
  have hQd : MvPolynomial.eval x (MvPolynomial.pderiv j Q)
      = ((D : ℝ) + 1) * (1 + MvPolynomial.eval x (sigmaSq m)) ^ D * (2 * x j) := by
    rw [hQ, MvPolynomial.pderiv_pow]
    simp [pderiv_sigmaSq]
  have hW2 : MvPolynomial.eval x (W ^ 2) = (MvPolynomial.eval x W) ^ 2 := by simp
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j, Finset.sum_ite_eq' Finset.univ j]
  simp only [Finset.mem_univ, if_true, hQd, hW2]
  exact quot_aux _ _ _ _ D hpos

/-- `phi D W` is differentiable at every point: it is the quotient of the
polynomial evaluation `(eval · W)^2` by the everywhere-positive polynomial
`(1 + eval · σ²)^(D+1)`. -/
theorem differentiableAt_phi {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    DifferentiableAt ℝ (phi D W) x := by
  have hW : DifferentiableAt ℝ (fun y => MvPolynomial.eval y W) x :=
    (hasFDerivAt_eval_mvPolynomial m W x).differentiableAt
  have hS : DifferentiableAt ℝ (fun y => MvPolynomial.eval y (sigmaSq m)) x :=
    (hasFDerivAt_eval_mvPolynomial m (sigmaSq m) x).differentiableAt
  have hnum : DifferentiableAt ℝ (fun y => (MvPolynomial.eval y W) ^ 2) x := hW.pow 2
  have hden : DifferentiableAt ℝ (fun y => (1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 1)) x :=
    ((differentiableAt_const (1 : ℝ)).add hS).pow (D + 1)
  have hne : (1 + MvPolynomial.eval x (sigmaSq m)) ^ (D + 1) ≠ 0 := by
    have := one_add_eval_sigmaSq_pos (m := m) x; positivity
  have hinv : DifferentiableAt ℝ
      (fun y => ((1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 1))⁻¹) x := hden.inv hne
  have hmul : DifferentiableAt ℝ
      (fun y => (MvPolynomial.eval y W) ^ 2
        * ((1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 1))⁻¹) x := hnum.mul hinv
  have hEq : phi D W = fun y => (MvPolynomial.eval y W) ^ 2
      * ((1 + MvPolynomial.eval y (sigmaSq m)) ^ (D + 1))⁻¹ := by
    funext y; rw [phi, div_eq_mul_inv]
  rw [hEq]; exact hmul

/-- `phi D W` is differentiable (everywhere). -/
theorem differentiable_phi {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ) :
    Differentiable ℝ (phi D W) := fun x => differentiableAt_phi D W x

/-- `phi` is nonnegative: its numerator is a square and its denominator positive. -/
theorem phi_nonneg {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    0 ≤ phi D W x := by
  have := one_add_eval_sigmaSq_pos (m := m) x
  unfold phi
  positivity

/-- On `Fin m → ℝ` (sup norm) the squared norm is dominated by `σ²(x) = ∑ i, (x i)^2`. -/
theorem sq_norm_le_eval_sigmaSq {m : ℕ} (x : Fin m → ℝ) :
    ‖x‖ ^ 2 ≤ MvPolynomial.eval x (sigmaSq m) := by
  rw [eval_sigmaSq]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [show x = 0 from Subsingleton.elim _ _]
  · have hne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin m))
      Finset.univ_nonempty (fun j => ‖x j‖₊)
    have hnn : ‖x‖₊ = ‖x i‖₊ := by rw [Pi.nnnorm_def, hi]
    have hnx : ‖x‖ = ‖x i‖ := congrArg NNReal.toReal hnn
    rw [hnx, Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (f := fun j => (x j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)

/-- Quantitative Stage B decay: since `deg (W²) ≤ 2D` while the denominator grows
like `(1 + ‖x‖²)^(D+1)`, the functional `phi` decays at least like `‖x‖⁻²`.
Precisely, `φ(x) · (1 + ‖x‖)² ≤ C² · 2^(D+1)` where `C` is the coefficient
`ℓ¹`-norm of `W`. -/
theorem phi_mul_sq_one_add_norm_le {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (hW : W.totalDegree ≤ D) (x : Fin m → ℝ) :
    phi D W x * (1 + ‖x‖) ^ 2
      ≤ ((∑ α ∈ W.support, |W.coeff α|) ^ 2 * 2 ^ (D + 1)) := by
  set C : ℝ := ∑ α ∈ W.support, |W.coeff α| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set r : ℝ := ‖x‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg x
  set t : ℝ := 1 + MvPolynomial.eval x (sigmaSq m) with ht
  have htpos : 0 < t := one_add_eval_sigmaSq_pos x
  have hrt : r ^ 2 ≤ t - 1 := by
    have h := sq_norm_le_eval_sigmaSq x
    rw [hr, ht]; linarith
  have hnum : (MvPolynomial.eval x W) ^ 2 ≤ C ^ 2 * (1 + r) ^ (2 * D) := by
    have h1 : |MvPolynomial.eval x W| ≤ C * (1 + r) ^ D := by
      refine le_trans (abs_eval_le_coeffNorm_mul m W x) ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hW) hC0
    calc (MvPolynomial.eval x W) ^ 2 = |MvPolynomial.eval x W| ^ 2 := (sq_abs _).symm
      _ ≤ (C * (1 + r) ^ D) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = C ^ 2 * (1 + r) ^ (2 * D) := by rw [mul_pow, ← pow_mul, mul_comm D 2]
  have hden : ((1 + r) ^ 2) ^ (D + 1) ≤ (2 * t) ^ (D + 1) := by
    refine pow_le_pow_left₀ (by positivity) ?_ _
    nlinarith [sq_nonneg (1 - r)]
  have hkey : (1 + r) ^ (2 * D) * (1 + r) ^ 2 = ((1 + r) ^ 2) ^ (D + 1) := by
    rw [← pow_add, ← pow_mul]; ring_nf
  have hexp : (2 * t) ^ (D + 1) = 2 ^ (D + 1) * t ^ (D + 1) := mul_pow 2 t (D + 1)
  rw [phi, div_mul_eq_mul_div, ← ht, div_le_iff₀ (by positivity)]
  calc (MvPolynomial.eval x W) ^ 2 * (1 + r) ^ 2
      ≤ (C ^ 2 * (1 + r) ^ (2 * D)) * (1 + r) ^ 2 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = C ^ 2 * ((1 + r) ^ 2) ^ (D + 1) := by rw [mul_assoc, hkey]
    _ ≤ C ^ 2 * ((2 : ℝ) ^ (D + 1) * t ^ (D + 1)) := by
        rw [← hexp]; exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ = C ^ 2 * 2 ^ (D + 1) * t ^ (D + 1) := by ring

/-- Stage B: every superlevel set `{x | δ ≤ φ(x)}` of the compactifying functional
`phi D W` (for `W` of total degree `≤ D` and `δ > 0`) is compact. Closedness comes
from continuity of `phi`; boundedness from the decay estimate
`phi_mul_sq_one_add_norm_le`. -/
theorem phi_superlevel_isCompact {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ)
    (hW : W.totalDegree ≤ D) {δ : ℝ} (hδ : 0 < δ) :
    IsCompact {x : Fin m → ℝ | δ ≤ phi D W x} := by
  set K : ℝ := ((∑ α ∈ W.support, |W.coeff α|) ^ 2 * 2 ^ (D + 1)) with hK
  have hclosed : IsClosed {x : Fin m → ℝ | δ ≤ phi D W x} :=
    isClosed_le continuous_const (differentiable_phi D W).continuous
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin m → ℝ) (K / δ)) hclosed ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  have hb := phi_mul_sq_one_add_norm_le D W hW x
  have hr0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have h1 : δ * (1 + ‖x‖) ^ 2 ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right hx (by positivity)) hb
  have h2 : ‖x‖ ≤ K / δ := by
    rw [le_div_iff₀ hδ]
    have h3 : ‖x‖ * δ ≤ δ * (1 + ‖x‖) ^ 2 := by nlinarith [sq_nonneg ‖x‖]
    linarith
  simpa [Metric.mem_closedBall, dist_eq_norm] using h2

/-- `phi D W` is `C^n` for every `n`: a quotient of polynomial evaluations by a
nowhere-vanishing polynomial evaluation. -/
theorem contDiff_phi {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (phi D W) := by
  have hnum : ContDiff ℝ n (fun x : Fin m → ℝ => (MvPolynomial.eval x W) ^ 2) :=
    (contDiff_eval_mvPolynomial m W n).pow 2
  have hden : ContDiff ℝ n
      (fun x : Fin m → ℝ => (1 + MvPolynomial.eval x (sigmaSq m)) ^ (D + 1)) :=
    (contDiff_const.add (contDiff_eval_mvPolynomial m (sigmaSq m) n)).pow (D + 1)
  have hne : ∀ x : Fin m → ℝ, (1 + MvPolynomial.eval x (sigmaSq m)) ^ (D + 1) ≠ 0 := by
    intro x
    have := one_add_eval_sigmaSq_pos (m := m) x
    positivity
  exact hnum.div hden hne

/-- The gradient of `phi`, recorded coordinatewise as a map `(Fin m → ℝ) → (Fin m → ℝ)`. -/
noncomputable def gradPhi {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    Fin m → ℝ :=
  fun j => fderiv ℝ (phi D W) x (fun i => if i = j then 1 else 0)

/-- The gradient map of `phi` is `C^n` for every `n`. -/
theorem contDiff_gradPhi {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (gradPhi D W) := by
  set L : ((Fin m → ℝ) →L[ℝ] ℝ) →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.pi (fun j =>
      ContinuousLinearMap.apply ℝ ℝ (fun i => if i = j then (1 : ℝ) else 0)) with hL
  have hfd : ContDiff ℝ n (fderiv ℝ (phi D W)) := (contDiff_phi D W ⊤).fderiv_right le_top
  have heq : gradPhi D W = fun x => L (fderiv ℝ (phi D W) x) := by
    funext x j
    simp [gradPhi, hL, ContinuousLinearMap.pi_apply, ContinuousLinearMap.apply_apply]
  rw [heq]
  exact L.contDiff.comp hfd

/-- The gradient map of `phi` is differentiable. -/
theorem differentiable_gradPhi {m : ℕ} (D : ℕ) (W : MvPolynomial (Fin m) ℝ) :
    Differentiable ℝ (gradPhi D W) :=
  (contDiff_gradPhi D W 1).differentiable one_ne_zero

end Warren
