/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.NineSR
import Mathlib.CategoryTheory.Generator.Preadditive

/-!
# Zero detection versus separation (Section 2.1.2)

The library's `IsGenerator G` is separation by the strictly full shift class of
`G`.  The paper's formulation is *zero detection*: an object receiving only zero
maps from the shifts of `G` is zero.  The two are not equivalent, and this file
determines the exact relation.

* `IsPaperGenerator G` (the paper's condition) is equivalent to zero detection by
  the whole shift class (`IsShiftClassZeroDetector`).
* `IsGenerator G` is equivalent to `SeparatesMorphismsFromShifts G`, i.e. to
  separation using only the displayed shifts as sources, and to the absence of
  nonzero *ghosts* `f` with `a ≫ f = 0` for every `a` out of a shift of `G`.
* Separation implies zero detection, but not conversely: the converse would have
  to exclude every nonzero ghost, and zero detection only covers the case where
  all maps into the target vanish.

So `IsGenerator` is strictly stronger than the paper's condition; the direction
the paper uses is separation ⟹ zero detection.

Found by a member of the Ultramath run `smwur4wqg` (direction D3).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The generation condition in **Section 2.1.2** of Lank--Pauwels: an object
receiving only zero maps from every integer shift of `G` is zero.  Unlike
`IsGenerator`, this predicate only tests objects, not arbitrary morphisms. -/
def IsPaperGenerator (G : C) : Prop :=
  ∀ {E : C}, (∀ n : ℤ, ∀ f : G⟦n⟧ ⟶ E, f = 0) → IsZero E

/-- Zero detection using every object of the strictly full shift-class of `G`.
The hypothesis is literally membership in the right orthogonal of that class,
so it quantifies over all maps out of all objects isomorphic to a shift of `G`.
This is the whole-shift-class form of **Section 2.1.2**. -/
def IsShiftClassZeroDetector (G : C) : Prop :=
  ∀ {E : C}, ((ObjectProperty.singleton G).shiftClosure ℤ).rightOrthogonal E →
    IsZero E

/-- The direct morphism-separation form of the shift-class in **Section
2.1.2**.  A nonzero morphism satisfying the premise is a ghost for the shifts
of `G`; consequently this condition is exactly what zero detection alone does
not address. -/
def SeparatesMorphismsFromShifts (G : C) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y),
    (∀ n : ℤ, ∀ a : G⟦n⟧ ⟶ X, a ≫ f = 0) → f = 0

/-- A nonzero ghost for the shifts of `G`, in the terminology relevant to the
bridge in **Section 2.1.2**: all composites from shifts of `G` vanish, but the
morphism itself does not. -/
def IsGhostFromShifts (G : C) {X Y : C} (f : X ⟶ Y) : Prop :=
  f ≠ 0 ∧ ∀ n : ℤ, ∀ a : G⟦n⟧ ⟶ X, a ≫ f = 0

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- **Section 2.1.2:** the paper's zero-detection condition is equivalent to
orthogonality to the
whole strictly full shift-class.  The only step is transport along the
isomorphism witnessing membership in `shiftClosure`; no triangulated argument
is needed. -/
theorem rightOrthogonal_shiftClosure_singleton_iff (G E : C) :
    ((ObjectProperty.singleton G).shiftClosure ℤ).rightOrthogonal E ↔
      ∀ n : ℤ, ∀ f : G⟦n⟧ ⟶ E, f = 0 := by
  constructor
  · intro h n f
    exact h f ⟨G, n, Iso.refl _, by simp⟩
  · intro h X f hX
    obtain ⟨A, n, e, hA⟩ := hX
    obtain rfl : G = A := (ObjectProperty.singleton_iff _ _).1 hA
    rw [← cancel_epi e.inv, comp_zero]
    exact h n (e.inv ≫ f)

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- **Section 2.1.2:** zero detection by the displayed shifts of `G` and zero
detection by its whole strictly full shift-class are equivalent. -/
theorem isPaperGenerator_iff_isShiftClassZeroDetector (G : C) :
    IsPaperGenerator G ↔ IsShiftClassZeroDetector G := by
  constructor
  · intro hG E hE
    exact hG ((rightOrthogonal_shiftClosure_singleton_iff G E).1 hE)
  · intro hG E hE
    exact hG ((rightOrthogonal_shiftClosure_singleton_iff G E).2 hE)

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- **Section 2.1.2:** separation by maps from a strictly full shift-class is
equivalent to separation by maps from its displayed representatives. -/
theorem isGenerator_iff_separatesMorphismsFromShifts (G : C) :
    IsGenerator G ↔ SeparatesMorphismsFromShifts G := by
  rw [IsGenerator, Preadditive.isSeparating_iff]
  constructor
  · intro h X Y f hf
    apply h f
    intro Z hZ a
    obtain ⟨A, n, e, hA⟩ := hZ
    obtain rfl : G = A := (ObjectProperty.singleton_iff _ _).1 hA
    rw [← cancel_epi e.inv, comp_zero]
    simpa only [Category.assoc] using hf n (e.inv ≫ a)
  · intro h X Y f hf
    apply h f
    intro n a
    exact hf (G⟦n⟧) ⟨G, n, Iso.refl _, by simp⟩ a

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- A concrete obstruction to upgrading the paper's condition in **Section
2.1.2** to `IsGenerator`: any nonzero ghost from the shifts refutes separation.
This isolates exactly the additional input required for the converse. -/
theorem not_isGenerator_of_isGhostFromShifts {G X Y : C} {f : X ⟶ Y}
    (hf : IsGhostFromShifts G f) : ¬ IsGenerator G := by
  intro hG
  exact hf.1 ((isGenerator_iff_separatesMorphismsFromShifts G).1 hG f hf.2)

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- A ghost-free formulation of `IsGenerator`, sharpening the comparison with
zero detection in **Section 2.1.2**. -/
theorem isGenerator_iff_no_isGhostFromShifts (G : C) :
    IsGenerator G ↔ ∀ {X Y : C} (f : X ⟶ Y), ¬ IsGhostFromShifts G f := by
  constructor
  · intro hG X Y f hf
    exact not_isGenerator_of_isGhostFromShifts hf hG
  · intro h
    apply (isGenerator_iff_separatesMorphismsFromShifts G).2
    intro X Y f hf
    by_contra hf0
    exact h f ⟨hf0, hf⟩

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The soft bridge to **Section 2.1.2**: the library's separating-family
`IsGenerator` implies the paper's zero-detection condition.  This is the
direction already used at the object level by
`isZero_of_isGenerator_of_hom_eq_zero`. -/
theorem isPaperGenerator_of_isGenerator {G : C} (hG : IsGenerator G) :
    IsPaperGenerator G := by
  intro E hE
  exact isZero_of_isGenerator_of_hom_eq_zero hG hE

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The whole-shift-class zero-detection consequence of `IsGenerator`, obtained
by combining separation with the strictly full formulation of **Section
2.1.2**. -/
theorem isShiftClassZeroDetector_of_isGenerator {G : C} (hG : IsGenerator G) :
    IsShiftClassZeroDetector G :=
  (isPaperGenerator_iff_isShiftClassZeroDetector G).1
    (isPaperGenerator_of_isGenerator hG)

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Summary of the valid implications for **Section 2.1.2** and Lemma 4.3(2).
Separation implies paper-style zero detection; paper-style zero detection is
equivalent to detection by the whole shift-class; and separation has the
displayed direct morphismwise characterization.

There is no general converse from the first conclusion to `IsGenerator`: that
would require proving `SeparatesMorphismsFromShifts G`, i.e. excluding every
nonzero ghost morphism.  Zero detection only supplies the special case in
which all maps into the *target object itself* vanish. -/
theorem isGenerator_zeroDetection_relation (G : C) :
    (IsGenerator G → IsPaperGenerator G) ∧
      (IsPaperGenerator G ↔ IsShiftClassZeroDetector G) ∧
      (IsGenerator G ↔ SeparatesMorphismsFromShifts G) :=
  ⟨isPaperGenerator_of_isGenerator,
    isPaperGenerator_iff_isShiftClassZeroDetector G,
    isGenerator_iff_separatesMorphismsFromShifts G⟩

end RelativeWeakApprox

#print axioms RelativeWeakApprox.rightOrthogonal_shiftClosure_singleton_iff
#print axioms RelativeWeakApprox.isPaperGenerator_iff_isShiftClassZeroDetector
#print axioms RelativeWeakApprox.isGenerator_iff_separatesMorphismsFromShifts
#print axioms RelativeWeakApprox.isGenerator_iff_no_isGhostFromShifts
#print axioms RelativeWeakApprox.isPaperGenerator_of_isGenerator
#print axioms RelativeWeakApprox.isGenerator_zeroDetection_relation
