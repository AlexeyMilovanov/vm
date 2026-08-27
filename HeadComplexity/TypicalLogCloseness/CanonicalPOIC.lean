import HeadComplexity.TypicalLogCloseness.FracAtomBridge

set_option linter.style.header false

/-!
# Canonical POIC₂

The previously formalized certificate class only required denominators to be
positive on the Boolean cube.  It is retained as the relaxed model
`RelaxedPOIC2`.  The canonical model below additionally requires every
variable slope of a denominator to be nonzero and all slopes to have one common
orientation.  Weak and constant denominators enter only through the explicit
finite-cube strictification theorem.
-/

namespace HeadComplexity.TypicalLogCloseness

/-- A canonical certificate is a relaxed certificate whose denominator pool
lies in the exact native one-head cone. -/
structure CanonicalCertificate (n : ℕ) (T : Topology)
    extends Certificate n T where
  oriented : ∀ j, (denominators j).StrictlyOriented

namespace CanonicalCertificate

variable {T : Topology}

/-- Strict sign representation by a canonical certificate. -/
def Represents (C : CanonicalCertificate n T) (f : BoolFn n) : Prop :=
  C.toCertificate.Represents f

theorem admissible (C : CanonicalCertificate n T) (j : Fin T.denominatorCount) :
    (C.denominators j).StrictAdmissible :=
  ⟨C.legal j, C.oriented j⟩

/-- Forgetting slope orientation gives a certificate in the relaxed model. -/
def forget (C : CanonicalCertificate n T) : Certificate n T :=
  C.toCertificate

theorem forget_represents {C : CanonicalCertificate n T} {f : BoolFn n}
    (h : C.Represents f) : C.forget.Represents f :=
  h

end CanonicalCertificate

/-- Canonical certificate existence at budget `Q`, including the two constant
truth tables at cost zero. -/
def HasCanonicalCertificate (n Q : ℕ) (f : BoolFn n) : Prop :=
  IsConstant f ∨
    ∃ (T : Topology) (C : CanonicalCertificate n T),
      T.score ≤ Q ∧ C.Represents f

theorem HasCanonicalCertificate.mono {Q R : ℕ} (hQR : Q ≤ R) {f : BoolFn n}
    (h : HasCanonicalCertificate n Q f) : HasCanonicalCertificate n R f := by
  rcases h with hc | ⟨T, C, hT, hC⟩
  · exact Or.inl hc
  · exact Or.inr ⟨T, C, hT.trans hQR, hC⟩

open AffineForm

/-- Direction affine form with negative slopes `-1` and constant `n + 1`. -/
def negDirection (n : ℕ) : AffineForm n where
  constant := (n : ℝ) + 1
  linear _ := -1

theorem negDirection_eval (n : ℕ) (x : Cube n) :
    (negDirection n).eval x = (n : ℝ) + 1 - ∑ i, bitReal (x i) := by
  simp only [AffineForm.eval, negDirection]
  have h1 : (∑ i, -1 * bitReal (x i)) = - ∑ i, bitReal (x i) := by
    rw [← Finset.mul_sum]
    ring
  rw [h1]
  ring

theorem negDirection_strictLegal (n : ℕ) : (negDirection n).StrictLegal := by
  intro x
  rw [negDirection_eval]
  have hsum : ∑ i, bitReal (x i) ≤ (n : ℝ) := by
    have h1 : ∀ i ∈ Finset.univ, bitReal (x i) ≤ 1 := fun i _ => by
      cases x i <;> simp [bitReal]
    have h2 := Finset.sum_le_card_nsmul Finset.univ (fun i => bitReal (x i)) 1 h1
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h2
    exact h2
  linarith

theorem negDirection_strictlyOriented (n : ℕ) :
    (negDirection n).StrictlyOriented :=
  Or.inr fun _ => by simp [negDirection]

/-- For a weakly oriented form `B`, choose a strictly oriented form `dir B`
such that `dir B` is strictly legal and `B.linear i + dir B.linear i` has the
same sign for all `i`. -/
noncomputable def directionForm (B : AffineForm n) : AffineForm n :=
  if h : ∀ i, 0 ≤ B.linear i then positiveDirection n else negDirection n

theorem directionForm_strictLegal (B : AffineForm n) :
    (directionForm B).StrictLegal := by
  classical
  dsimp [directionForm]
  split_ifs
  · exact positiveDirection_strictLegal
  · exact negDirection_strictLegal n

theorem directionForm_strictlyOriented (B : AffineForm n)
    (hweak : B.WeaklyOriented) : (directionForm B).StrictlyOriented := by
  classical
  dsimp [directionForm]
  split_ifs with hpos
  · exact positiveDirection_positiveCoefficients.strictlyOriented
  · exact negDirection_strictlyOriented n

theorem directionForm_aligned (B : AffineForm n) (hweak : B.WeaklyOriented)
    (ε : ℝ) (hε : 0 < ε) :
    ((B.add ((directionForm B).smul ε)).StrictlyOriented) := by
  classical
  dsimp [directionForm]
  split_ifs with hpos
  · left
    intro i
    have h1 : 0 ≤ B.linear i := hpos i
    have h2 : 0 < ((positiveDirection n).smul ε).linear i := by
      simp [smul, positiveDirection, hε]
    simp only [add, smul, positiveDirection]
    linarith
  · right
    intro i
    have hneg : ∀ i, B.linear i ≤ 0 := by
      rcases hweak with h | h
      · contradiction
      · exact h
    have h1 : B.linear i ≤ 0 := hneg i
    have h2 : ((negDirection n).smul ε).linear i < 0 := by
      simp [smul, negDirection]
      linarith
    simp only [add, smul, negDirection]
    linarith

/-- Perturbed denominator pool. -/
noncomputable def perturbedDenom {T : Topology} (C : Certificate n T) (ε : ℝ)
    (j : Fin T.denominatorCount) : AffineForm n :=
  (C.denominators j).add ((directionForm (C.denominators j)).smul ε)

theorem perturbedDenom_eval {T : Topology} (C : Certificate n T) (ε : ℝ)
    (j : Fin T.denominatorCount) (x : Cube n) :
    (perturbedDenom C ε j).eval x =
      (C.denominators j).eval x + ε * (directionForm (C.denominators j)).eval x := by
  simp [perturbedDenom]

theorem perturbedDenom_pos {T : Topology} (C : Certificate n T)
    (ε : ℝ) (hε : 0 ≤ ε) (j : Fin T.denominatorCount) (x : Cube n) :
    0 < (perturbedDenom C ε j).eval x := by
  rw [perturbedDenom_eval]
  have h1 : 0 < (C.denominators j).eval x := (C.denominators j).eval_pos (C.legal j) x
  have h2 : 0 < (directionForm (C.denominators j)).eval x :=
    directionForm_strictLegal (C.denominators j) x
  have h3 : 0 ≤ ε * (directionForm (C.denominators j)).eval x := mul_nonneg hε h2.le
  linarith

theorem perturbedDenom_strictlyOriented {T : Topology} (C : Certificate n T)
    (hweak : ∀ j, (C.denominators j).WeaklyOriented)
    (ε : ℝ) (hε : 0 < ε) (j : Fin T.denominatorCount) :
    (perturbedDenom C ε j).StrictlyOriented :=
  directionForm_aligned (C.denominators j) (hweak j) ε hε

theorem perturbedDenom_strictAdmissible {T : Topology} (C : Certificate n T)
    (hweak : ∀ j, (C.denominators j).WeaklyOriented)
    (ε : ℝ) (hε : 0 < ε) (j : Fin T.denominatorCount) :
    (perturbedDenom C ε j).StrictAdmissible :=
  ⟨fun x => perturbedDenom_pos C ε hε.le j x,
   perturbedDenom_strictlyOriented C hweak ε hε j⟩

/-- Perturbed certificate at parameter `ε`. -/
noncomputable def perturbedCert {T : Topology} (C : Certificate n T)
    (hweak : ∀ j, (C.denominators j).WeaklyOriented)
    (ε : ℝ) (hε : 0 < ε) : CanonicalCertificate n T where
  denominators j := perturbedDenom C ε j
  numerators t := C.numerators t
  legal j := perturbedDenom_pos C ε hε.le j
  oriented j := perturbedDenom_strictlyOriented C hweak ε hε j

theorem perturbedCert_forget_eval {T : Topology} (C : Certificate n T)
    (hweak : ∀ j, (C.denominators j).WeaklyOriented)
    (ε : ℝ) (hε : 0 < ε) (x : Cube n) :
    (perturbedCert C hweak ε hε).forget.eval x =
      ∑ t, (C.numerators t).eval x /
        ∏ j ∈ (T.incidence t).denoms,
          ((C.denominators j).eval x + ε * (directionForm (C.denominators j)).eval x) := by
  simp [perturbedCert, CanonicalCertificate.forget, Certificate.eval,
    Certificate.termDenominator, perturbedDenom]

/-- The scalar evaluation path before packaging the perturbed certificate. -/
noncomputable def perturbationEval {T : Topology} (C : Certificate n T)
    (ε : ℝ) (x : Cube n) : ℝ :=
  ∑ t, (C.numerators t).eval x /
    ∏ j ∈ (T.incidence t).denoms,
      ((C.denominators j).eval x +
        ε * (directionForm (C.denominators j)).eval x)

@[simp] theorem perturbationEval_zero {T : Topology} (C : Certificate n T)
    (x : Cube n) : perturbationEval C 0 x = C.eval x := by
  simp [perturbationEval, Certificate.eval, Certificate.termDenominator]

/-- Each pointwise perturbed score is continuous at the unperturbed parameter. -/
theorem continuousAt_perturbationEval_zero {T : Topology}
    (C : Certificate n T) (x : Cube n) :
    ContinuousAt (fun ε : ℝ => perturbationEval C ε x) 0 := by
  unfold perturbationEval
  apply tendsto_finsetSum
  intro t _
  refine tendsto_const_nhds.div ?_ ?_
  · apply tendsto_finsetProd
    intro j _
    exact tendsto_const_nhds.add
      (Filter.Tendsto.mul Filter.tendsto_id tendsto_const_nhds)
  · simp only [zero_mul, add_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact (C.denominators j).eval_ne_zero (C.legal j) x

/-- A finite family of continuous nonzero values keeps its sign at one common
strictly positive parameter. -/
theorem exists_positive_parameter_preserving_sign
    (g : ℝ → Cube n → ℝ)
    (hcont : ∀ x, ContinuousAt (fun ε => g ε x) 0)
    (hne : ∀ x, g 0 x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < g ε x * g 0 x := by
  have hevent :
      ∀ᶠ ε in nhds (0 : ℝ), ∀ x, 0 < g ε x * g 0 x := by
    rw [Filter.eventually_all]
    intro x
    have hc : ContinuousAt (fun ε => g ε x * g 0 x) 0 :=
      (hcont x).mul continuousAt_const
    have h0 : 0 < g 0 x * g 0 x := mul_self_pos.mpr (hne x)
    exact hc.eventually (isOpen_Ioi.mem_nhds h0)
  rw [Metric.eventually_nhds_iff] at hevent
  obtain ⟨δ, hδ, hall⟩ := hevent
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro x
  apply hall
  rw [Real.dist_0_eq_abs, abs_of_pos (half_pos hδ)]
  linarith

/-- Finite-cube closure lemma. A positive weakly oriented certificate can be
perturbed, without changing its topology or truth-table signs, to an exact
strictly oriented canonical certificate. -/
theorem strictify_weak_certificate {T : Topology} (C : Certificate n T)
    (hweak : ∀ j, (C.denominators j).WeaklyOriented)
    {f : BoolFn n} (hrep : C.Represents f) :
    ∃ C' : CanonicalCertificate n T, C'.Represents f := by
  let g : ℝ → Cube n → ℝ := fun ε x => perturbationEval C ε x
  have hcont : ∀ x, ContinuousAt (fun ε => g ε x) 0 := by
    intro x
    exact continuousAt_perturbationEval_zero C x
  have hne : ∀ x, g 0 x ≠ 0 := by
    intro x
    simpa [g] using Certificate.eval_ne_zero_of_represents hrep x
  obtain ⟨ε, hε, hsign⟩ :=
    exists_positive_parameter_preserving_sign g hcont hne
  refine ⟨perturbedCert C hweak ε hε, ?_⟩
  intro x
  have heval :
      (perturbedCert C hweak ε hε).forget.eval x = g ε x := by
    rw [perturbedCert_forget_eval]
    rfl
  have hzero : g 0 x = C.eval x := by simp [g]
  constructor
  · intro hx
    have hbase : 0 < g 0 x := by
      rw [hzero]
      exact (hrep x).1 hx
    have hp := hsign x
    change 0 < (perturbedCert C hweak ε hε).forget.eval x
    rw [heval]
    nlinarith
  · intro hx
    have hbase : g 0 x < 0 := by
      rw [hzero]
      exact (hrep x).2 hx
    have hp := hsign x
    change (perturbedCert C hweak ε hε).forget.eval x < 0
    rw [heval]
    nlinarith

private theorem fracDenominator_weaklyOriented (φ : HeadComplexity.FracAtom n) :
    (fracDenominator φ).WeaklyOriented := by
  by_cases hα : φ.α ≤ 1
  · right
    intro i
    dsimp [fracDenominator]
    have h1 : φ.α - 1 ≤ 0 := sub_nonpos.mpr hα
    have h2 : 0 < φ.ρ i := φ.hρ i
    nlinarith
  · left
    intro i
    dsimp [fracDenominator]
    have h1 : 0 ≤ φ.α - 1 := sub_nonneg.mpr (le_of_not_ge hα)
    have h2 : 0 < φ.ρ i := φ.hρ i
    positivity

/-- Every H* representation gives a canonical singleton-incidence
certificate at the same budget. This includes strictification of native atoms
whose temperature is one. -/
private theorem exists_uniform_strict_margin
    (p : Cube n → Prop) (a : Cube n → ℝ)
    (ha : ∀ x, p x → 0 < a x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, p x → ε < a x := by
  classical
  let S : Finset ℝ := (Finset.univ.filter p).image a
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : 0 < m := by
      rw [Finset.lt_min'_iff]
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact ha x (Finset.mem_filter.mp hx).2
    refine ⟨m / 2, by positivity, ?_⟩
    intro x hpx
    have hmem : a x ∈ S := by
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hpx⟩, rfl⟩
    have hmin : m ≤ a x := Finset.min'_le S (a x) hmem
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hpx
    exfalso
    apply hS
    refine ⟨a x, ?_⟩
    exact Finset.mem_image.mpr
      ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hpx⟩, rfl⟩

/-- Every H* representation gives a canonical singleton-incidence
certificate at the same budget. This includes strictification of native atoms
whose temperature is one. -/
theorem fracComputable_hasCanonicalCertificate {H : ℕ} {f : BoolFn n}
    (h : HeadComplexity.fracComputable n H f) :
    HasCanonicalCertificate n H f := by
  classical
  rcases h with ⟨φ, c, hrep⟩
  by_cases hH : H = 0
  · subst H
    left
    by_cases hc : 0 < c
    · refine ⟨true, fun x => ?_⟩
      apply (hrep x).mp
      simpa using hc
    · refine ⟨false, fun x => ?_⟩
      cases hx : f x
      · rfl
      · exfalso
        apply hc
        have hs := (hrep x).mpr hx
        simpa using hs
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    let i0 : Fin H := ⟨0, hHpos⟩
    let score : Cube n → ℝ := fun x => c + ∑ t, (φ t).eval x
    have hscore : ∀ x, f x = true → 0 < score x := by
      intro x hx
      exact (hrep x).mpr hx
    obtain ⟨ε, hε, hmargin⟩ :=
      exists_uniform_strict_margin (fun x => f x = true) score hscore
    let shiftedBias : ℝ := c - ε
    let T : Topology := {
      denominatorCount := H
      termCount := H
      incidence t := {
        denoms := {t}
        nonempty := Finset.singleton_nonempty t
        card_le_two := by simp
      }
    }
    let C : Certificate n T := {
      denominators t := fracDenominator (φ t)
      numerators t :=
        (fracNumerator (φ t)).add
          ((fracDenominator (φ t)).smul
            (if t = i0 then shiftedBias else 0))
      legal t := fracDenominator_strictLegal (φ t)
    }
    have hEval : ∀ x, C.eval x = score x - ε := by
      intro x
      have hquot : ∀ t,
          (C.numerators t).eval x / C.termDenominator t x =
            (φ t).eval x + (if t = i0 then shiftedBias else 0) := by
        intro t
        have hden :
            C.termDenominator t x = (fracDenominator (φ t)).eval x := by
          simp [Certificate.termDenominator, C, T]
        rw [hden]
        simp only [C, AffineForm.eval_add, AffineForm.eval_smul,
          fracAtom_eval_eq_affine]
        have hnz := (fracDenominator_strictLegal (φ t) x).ne'
        field_simp
      unfold Certificate.eval
      rw [Finset.sum_congr rfl (fun t _ => hquot t)]
      rw [Finset.sum_add_distrib]
      simp [score, shiftedBias, i0]
      ring
    have hC : C.Represents f := by
      intro x
      constructor
      · intro hx
        rw [hEval]
        exact sub_pos.mpr (hmargin x hx)
      · intro hx
        rw [hEval]
        have hnonpos : score x ≤ 0 := by
          apply le_of_not_gt
          intro hpos
          have htrue : f x = true := (hrep x).mp hpos
          simp [hx] at htrue
        linarith
    have hweak : ∀ j, (C.denominators j).WeaklyOriented := fun j =>
      fracDenominator_weaklyOriented (φ j)
    obtain ⟨C', hC'⟩ := strictify_weak_certificate C hweak hC
    right
    refine ⟨T, C', ?_, hC'⟩
    simp [T, Topology.score]

/-- Totality of canonical POIC₂. -/
theorem exists_hasCanonicalCertificate (f : BoolFn n) :
    ∃ Q, HasCanonicalCertificate n Q f := by
  rcases HeadComplexity.exists_computable f with ⟨H, hH⟩
  refine ⟨H, fracComputable_hasCanonicalCertificate ?_⟩
  exact (HeadComplexity.computableWithHeadsN_iff_fracComputable H f).mp hH

/-- Canonical no-bias POIC₂ complexity. -/
noncomputable def POIC2 (n : ℕ) (f : BoolFn n) : ℕ := by
  classical
  exact Nat.find (exists_hasCanonicalCertificate f)

theorem hasCanonicalCertificate_at_POIC2 (f : BoolFn n) :
    HasCanonicalCertificate n (POIC2 n f) f := by
  classical
  exact Nat.find_spec (exists_hasCanonicalCertificate f)

theorem POIC2_le_of_hasCanonicalCertificate {Q : ℕ} {f : BoolFn n}
    (h : HasCanonicalCertificate n Q f) : POIC2 n f ≤ Q := by
  classical
  exact Nat.find_min' (exists_hasCanonicalCertificate f) h

theorem hasCanonicalCertificate_of_POIC2_le {Q : ℕ} {f : BoolFn n}
    (hQ : POIC2 n f ≤ Q) : HasCanonicalCertificate n Q f :=
  (hasCanonicalCertificate_at_POIC2 f).mono hQ

theorem POIC2_eq_zero_of_constant {f : BoolFn n} (hf : IsConstant f) :
    POIC2 n f = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact POIC2_le_of_hasCanonicalCertificate (Q := 0) (Or.inl hf)

/-- A canonical certificate is, after forgetting orientation, a relaxed
certificate of the same score. -/
theorem hasCertificate_of_hasCanonicalCertificate {Q : ℕ} {f : BoolFn n}
    (h : HasCanonicalCertificate n Q f) : HasCertificate n Q f := by
  rcases h with hc | ⟨T, C, hT, hC⟩
  · exact Or.inl hc
  · exact Or.inr ⟨T, C.forget, hT, C.forget_represents hC⟩

/-- The relaxed measure can only be smaller than the canonical one. -/
theorem relaxedPOIC2_le_POIC2 (f : BoolFn n) :
    RelaxedPOIC2 n f ≤ POIC2 n f :=
  relaxedPOIC2_le_of_hasCertificate
    (hasCertificate_of_hasCanonicalCertificate
      (hasCanonicalCertificate_at_POIC2 f))

/-- Explicit right-hand bridge in the canonical hierarchy. -/
theorem POIC2_le_HStar (f : BoolFn n) :
    POIC2 n f ≤ HeadComplexity.HStar n f := by
  have h_comp : HeadComplexity.computableWithHeadsN n (HeadComplexity.HStar n f) f :=
    HeadComplexity.HStar_computable f
  have h_frac : HeadComplexity.fracComputable n (HeadComplexity.HStar n f) f :=
    (HeadComplexity.computableWithHeadsN_iff_fracComputable _ _).mp h_comp
  exact POIC2_le_of_hasCanonicalCertificate (fracComputable_hasCanonicalCertificate h_frac)

/-- The comparison chain that must be used when transferring results proved
for the relaxed model. -/
theorem relaxedPOIC2_le_POIC2_le_HStar (f : BoolFn n) :
    RelaxedPOIC2 n f ≤ POIC2 n f ∧
      POIC2 n f ≤ HeadComplexity.HStar n f :=
  ⟨relaxedPOIC2_le_POIC2 f, POIC2_le_HStar f⟩

end HeadComplexity.TypicalLogCloseness
