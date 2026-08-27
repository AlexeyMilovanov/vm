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

/-- Finite-cube closure lemma. A positive weakly oriented certificate can be
perturbed, without changing its topology or truth-table signs, to an exact
strictly oriented canonical certificate. -/
theorem strictify_weak_certificate {T : Topology} (C : Certificate n T)
    (hweak : ∀ j, (C.denominators j).WeaklyOriented)
    {f : BoolFn n} (hrep : C.Represents f) :
    ∃ C' : CanonicalCertificate n T, C'.Represents f := by
  sorry

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
