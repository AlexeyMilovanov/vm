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

/-- Every H* representation gives a canonical singleton-incidence
certificate at the same budget. This includes strictification of native atoms
whose temperature is one. -/
theorem fracComputable_hasCanonicalCertificate {H : ℕ} {f : BoolFn n}
    (h : HeadComplexity.fracComputable n H f) :
    HasCanonicalCertificate n H f := by
  sorry

/-- Totality of canonical POIC₂. -/
theorem exists_hasCanonicalCertificate (f : BoolFn n) :
    ∃ Q, HasCanonicalCertificate n Q f := by
  sorry

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
  sorry

/-- The comparison chain that must be used when transferring results proved
for the relaxed model. -/
theorem relaxedPOIC2_le_POIC2_le_HStar (f : BoolFn n) :
    RelaxedPOIC2 n f ≤ POIC2 n f ∧
      POIC2 n f ≤ HeadComplexity.HStar n f :=
  ⟨relaxedPOIC2_le_POIC2 f, POIC2_le_HStar f⟩

end HeadComplexity.TypicalLogCloseness
