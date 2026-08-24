import Mathlib

namespace Warren

/-- Monotonicity of the total-degree functional `α ↦ ∑ i, α i` on `Finsupp`s. -/
private theorem finsupp_sum_le_of_le {m : ℕ} {α β : Fin m →₀ ℕ} (h : α ≤ β) :
    (α.sum fun _ v => v) ≤ (β.sum fun _ v => v) := by
  rw [Finsupp.sum_of_support_subset α (Finsupp.support_mono h) _ (by simp), Finsupp.sum]
  exact Finset.sum_le_sum fun i _ => h i

theorem abs_monomial_eval_le (m : ℕ) (α : Fin m →₀ ℕ) (x : Fin m → ℝ) :
    |MvPolynomial.eval x (MvPolynomial.monomial α 1)| ≤
      (1 + ‖x‖) ^ (α.sum fun _ v => v) := by
  simp only [MvPolynomial.eval_monomial, one_mul]
  change |α.prod fun i v => x i ^ v| ≤ _
  rw [Finsupp.prod, Finsupp.sum, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => abs_nonneg _) ?_
  intro i _
  rw [abs_pow]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
  have hxi : |x i| ≤ ‖x‖ := by simpa using norm_le_pi_norm x i
  linarith

theorem abs_eval_le_coeffNorm_mul (m : ℕ) (P : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    |MvPolynomial.eval x P| ≤
      (∑ α ∈ P.support, |P.coeff α|) * (1 + ‖x‖) ^ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro α hα
  rw [MvPolynomial.eval_monomial, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : |α.prod fun i k => x i ^ k| ≤ (1 + ‖x‖) ^ (α.sum fun _ v => v) := by
    simpa [MvPolynomial.eval_monomial] using abs_monomial_eval_le m α x
  exact le_trans h1
    (pow_le_pow_right₀ (by linarith [norm_nonneg x]) (MvPolynomial.le_totalDegree hα))

theorem totalDegree_pderiv_le (m : ℕ) (j : Fin m) (P : MvPolynomial (Fin m) ℝ) :
    (MvPolynomial.pderiv j P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le ?_)
  intro α hα
  rw [MvPolynomial.pderiv_monomial]
  refine le_trans (MvPolynomial.totalDegree_monomial_le _ _) ?_
  exact le_trans (finsupp_sum_le_of_le tsub_le_self) (MvPolynomial.le_totalDegree hα)

theorem hasFDerivAt_eval_mvPolynomial (m : ℕ) (P : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    HasFDerivAt (fun y => MvPolynomial.eval y P)
      (∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j P) •
        (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)) x := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const a x
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
      have hcoord : HasFDerivAt (fun y : Fin m → ℝ => y i)
          (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) x :=
        (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).hasFDerivAt
      have hmul := hp.mul hcoord
      have heq_fun : (fun y : Fin m → ℝ => MvPolynomial.eval y p) * (fun y : Fin m → ℝ => y i) =
          (fun y : Fin m → ℝ => MvPolynomial.eval y (p * MvPolynomial.X i)) := by
        funext y
        simp
      have heq_deriv : MvPolynomial.eval x p • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) + x i • (∑ j : Fin m, MvPolynomial.eval x (MvPolynomial.pderiv j p) • (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)) =
          (∑ j : Fin m, MvPolynomial.eval x (MvPolynomial.pderiv j (p * MvPolynomial.X i)) • (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)) := by
        ext v
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, ContinuousLinearMap.add_apply,
          MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply,
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

theorem eval_pderiv_eq_deriv_coord (m : ℕ) (j : Fin m)
    (P : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    MvPolynomial.eval x (MvPolynomial.pderiv j P) =
      (fderiv ℝ (fun y => MvPolynomial.eval y P) x)
        (fun i => if i = j then 1 else 0) := by
  rw [(hasFDerivAt_eval_mvPolynomial m P x).fderiv]
  simp [eq_comm]

noncomputable def sigmaSq (m : ℕ) : MvPolynomial (Fin m) ℝ := ∑ j, (MvPolynomial.X j)^2

/-- Polynomial evaluation `x ↦ eval x P` on `Fin m → ℝ` is `C^n` for every `n`. -/
theorem contDiff_eval_mvPolynomial (m : ℕ) (P : MvPolynomial (Fin m) ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x : Fin m → ℝ => MvPolynomial.eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa [map_add] using hp.add hq
  | mul_X p i hp =>
      have hco : ContDiff ℝ n (fun x : Fin m → ℝ => x i) :=
        (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).contDiff
      simpa using hp.mul hco

end Warren
