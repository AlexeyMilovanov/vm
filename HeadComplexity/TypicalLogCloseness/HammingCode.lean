import HeadComplexity.TypicalLogCloseness.AffineForm
import Mathlib

set_option linter.style.header false

/-!
# Total Hamming-star code on a power-of-two cube

Coordinates are the nonzero vectors of (Z/2Z)^m plus one distinguished
coordinate. The main endpoint is an explicit center/direction equivalence.
-/

namespace HeadComplexity.TypicalLogCloseness

open Finset
open scoped BigOperators

abbrev BinaryVector (m : ℕ) := Fin m → ZMod 2
abbrev NonzeroVector (m : ℕ) := {v : BinaryVector m // v ≠ 0}
abbrev StarCoord (m : ℕ) := NonzeroVector m ⊕ Unit
abbrev StarCube (m : ℕ) := StarCoord m → Bool

/-- Toggle one coordinate of a Boolean cube vertex. -/
def toggle {ι : Type*} [DecidableEq ι] (x : ι → Bool) (i : ι) : ι → Bool :=
  fun j => if j = i then !(x j) else x j

@[simp] theorem toggle_same {ι : Type*} [DecidableEq ι] (x : ι → Bool) (i : ι) :
    toggle x i i = !(x i) := by simp [toggle]

@[simp] theorem toggle_ne {ι : Type*} [DecidableEq ι] (x : ι → Bool) {i j : ι}
    (h : j ≠ i) : toggle x i j = x j := by simp [toggle, h]

@[simp] theorem toggle_toggle {ι : Type*} [DecidableEq ι] (x : ι → Bool) (i : ι) :
    toggle (toggle x i) i = x := by
  funext j
  by_cases h : j = i
  · subst j
    simp [toggle]
  · simp [toggle, h]

/-- The prefix syndrome, ignoring the distinguished extra coordinate. -/
noncomputable def syndrome (x : StarCube m) : BinaryVector m :=
  ∑ v : NonzeroVector m, if x (Sum.inl v) = true then v.1 else 0

@[simp] theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rw [← two_mul]
  have h : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  rw [h, zero_mul]

/-- Centers of the total perfect code. -/
abbrev StarCenter (m : ℕ) := {x : StarCube m // syndrome x = 0}

/-- The open star around a center. -/
noncomputable def openStar (c : StarCenter m) : Finset (StarCube m) :=
  Finset.univ.image fun i : StarCoord m => toggle c.1 i

@[simp] theorem syndrome_toggle_extra (x : StarCube m) :
    syndrome (toggle x (Sum.inr ())) = syndrome x := by
  classical
  unfold syndrome
  apply Finset.sum_congr rfl
  intro v _
  have hne : (Sum.inl v : StarCoord m) ≠ Sum.inr () := by simp
  simp only [toggle_ne x hne]

@[simp] theorem syndrome_toggle_prefix (x : StarCube m) (v : NonzeroVector m) :
    syndrome (toggle x (Sum.inl v)) = syndrome x + v.1 := by
  classical
  let f : NonzeroVector m → BinaryVector m :=
    fun w => if x (Sum.inl w) = true then w.1 else 0
  let g : NonzeroVector m → BinaryVector m :=
    fun w => if toggle x (Sum.inl v) (Sum.inl w) = true then w.1 else 0
  have hsum :
      ∑ w ∈ Finset.univ.erase v, g w = ∑ w ∈ Finset.univ.erase v, f w := by
    apply Finset.sum_congr rfl
    intro w hw
    have hwv : w ≠ v := Finset.ne_of_mem_erase hw
    have hcoord : (Sum.inl w : StarCoord m) ≠ Sum.inl v := by
      intro h
      exact hwv (Sum.inl.inj h)
    simp only [g, f, toggle_ne x hcoord]
  have hterm : g v = f v + v.1 := by
    by_cases hx : x (Sum.inl v) = true
    · simp only [g, f, toggle_same, hx, Bool.not_true, if_false, if_true]
      funext i
      exact (zmod2_add_self (v.1 i)).symm
    · have hx' : x (Sum.inl v) = false := Bool.eq_false_of_not_eq_true hx
      simp [g, f, toggle, hx']
  change (∑ w, g w) = (∑ w, f w) + v.1
  calc
    ∑ w, g w =
        (∑ w ∈ Finset.univ.erase v, g w) + g v := by
          symm
          exact Finset.sum_erase_add _ _ (Finset.mem_univ v)
    _ = (∑ w ∈ Finset.univ.erase v, f w) + (f v + v.1) := by
          rw [hsum, hterm]
    _ = ((∑ w ∈ Finset.univ.erase v, f w) + f v) + v.1 := by
          ac_rfl
    _ = (∑ w, f w) + v.1 := by
          rw [Finset.sum_erase_add _ _ (Finset.mem_univ v)]

/-- Recover the toggled coordinate from the syndrome of a cube vertex. -/
noncomputable def decodeDirection (x : StarCube m) : StarCoord m :=
  if h : syndrome x = 0 then Sum.inr ()
  else Sum.inl ⟨syndrome x, h⟩

@[simp] theorem syndrome_toggle_decodeDirection (x : StarCube m) :
    syndrome (toggle x (decodeDirection x)) = 0 := by
  classical
  by_cases h : syndrome x = 0
  · simp [decodeDirection, h]
  · rw [decodeDirection, dif_neg h, syndrome_toggle_prefix]
    funext i
    simp

@[simp] theorem decodeDirection_toggle_center
    (c : StarCenter m) (i : StarCoord m) :
    decodeDirection (toggle c.1 i) = i := by
  classical
  rcases i with v | u
  · have hv : syndrome (toggle c.1 (Sum.inl v)) = v.1 := by
      rw [syndrome_toggle_prefix, c.2, zero_add]
    have hv0 : syndrome (toggle c.1 (Sum.inl v)) ≠ 0 := by
      rw [hv]
      exact v.2
    have hvne : (v.1 : BinaryVector m) ≠ 0 := v.2
    simp [decodeDirection, hv, hvne]
  · rcases u with ⟨⟩
    have h0 : syndrome (toggle c.1 (Sum.inr ())) = 0 := by
      rw [syndrome_toggle_extra, c.2]
    simp [decodeDirection, h0]

/-- The explicit center/direction map is bijective.  Its inverse decodes the
syndrome: a nonzero syndrome selects that prefix coordinate, while zero selects
the distinguished extra coordinate. -/
theorem centerDirection_bijective (m : ℕ) (hm : 1 ≤ m) :
    Function.Bijective
      (fun z : StarCenter m × StarCoord m => toggle z.1.1 z.2) := by
  classical
  constructor
  · rintro ⟨c, i⟩ ⟨d, j⟩ hij
    have hdirection : i = j := by
      calc
        i = decodeDirection (toggle c.1 i) :=
          (decodeDirection_toggle_center c i).symm
        _ = decodeDirection (toggle d.1 j) := congrArg decodeDirection hij
        _ = j := decodeDirection_toggle_center d j
    subst j
    have hcenter : c = d := by
      apply Subtype.ext
      have htoggle := congrArg (fun y => toggle y i) hij
      simpa using htoggle
    subst d
    rfl
  · intro x
    let i := decodeDirection x
    let c : StarCenter m :=
      ⟨toggle x i, syndrome_toggle_decodeDirection x⟩
    refine ⟨(c, i), ?_⟩
    simp [c, i]

/-- Every vertex has a unique representation as a center with one toggled
coordinate. This is the total-perfect-code equivalence used downstream. -/
noncomputable def centerDirectionEquiv (m : ℕ) (hm : 1 ≤ m) :
    StarCenter m × StarCoord m ≃ StarCube m :=
  Equiv.ofBijective _ (centerDirection_bijective m hm)

theorem centerDirectionEquiv_apply (m : ℕ) (hm : 1 ≤ m)
    (z : StarCenter m × StarCoord m) :
    centerDirectionEquiv m hm z = toggle z.1.1 z.2 := rfl

theorem openStar_partition (m : ℕ) (hm : 1 ≤ m) (x : StarCube m) :
    ∃! z : StarCenter m × StarCoord m, toggle z.1.1 z.2 = x := by
  let e := centerDirectionEquiv m hm
  refine ⟨e.symm x, ?_, ?_⟩
  · change toggle (e.symm x).1.1 (e.symm x).2 = x
    calc
      _ = centerDirectionEquiv m hm (e.symm x) :=
        (centerDirectionEquiv_apply m hm (e.symm x)).symm
      _ = x := (centerDirectionEquiv m hm).apply_symm_apply x
  · intro y hy
    apply e.injective
    change e y = e (e.symm x)
    calc
      e y = toggle y.1.1 y.2 := centerDirectionEquiv_apply m hm y
      _ = x := hy
      _ = e (e.symm x) := (e.apply_symm_apply x).symm

end HeadComplexity.TypicalLogCloseness
