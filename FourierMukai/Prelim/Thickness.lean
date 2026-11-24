/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Prelim.Triangulated
import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Thickness of the iso-locus (Lemma 2.3(2), retract part)

This file completes Lemma 2.3(2) of

  E. Guisado Villalgordo, P. Lank, *Relative Fourier--Mukai theory for algebraic spaces*:

the full subcategory of objects at which a trinatural transformation is an
isomorphism is closed under direct summands, hence thick (being already
triangulated, `Trinatural.isoLocus_isTriangulated`).

The key observation is that no triangulated or additive structure is needed for
this part: naturality exhibits the component at a retract of `Y` as a retract of
the arrow `η.app Y`, and isomorphisms are stable under retracts of arrows.

The proof of `isIso_app_of_retract` was found by a member of the Ultramath run
`smwufdjq4` (direction D4); the generator corollary at the end is a consequence
used repeatedly in the paper (an isomorphism only has to be checked on a
classical generator).

## Main results

* `RelativeFM.isIso_app_of_retract`
* `RelativeFM.Trinatural.isoLocus_isStableUnderRetracts`
* `RelativeFM.Trinatural.isIso_of_isClassicalGenerator`
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D]

/-- If a natural transformation is an isomorphism at `Y`, then it is an
isomorphism at every retract of `Y`. -/
lemma isIso_app_of_retract {F G : C ⥤ D} (η : F ⟶ G) {X Y : C}
    (h : Retract X Y) [IsIso (η.app Y)] : IsIso (η.app X) :=
  MorphismProperty.of_retract (η.retractArrowApp h) inferInstance

namespace Trinatural

variable [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

variable {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]

/-- **Lemma 2.3(2), binary direct-summand part.** If a trinatural
transformation is an isomorphism at `X ⊞ Y`, then it is an isomorphism at `X`.
The proof uses only naturality and the retract `X ⇄ X ⊞ Y`. -/
lemma isIso_app_of_isIso_app_biprod_left (η : Trinatural F G) (X Y : C)
    [HasBinaryBiproduct X Y] (h : IsIso (η.toNatTrans.app (X ⊞ Y))) :
    IsIso (η.toNatTrans.app X) := by
  letI : IsIso (η.toNatTrans.app (X ⊞ Y)) := h
  exact isIso_app_of_retract η.toNatTrans (BinaryBiproduct.bicone X Y).retract_left

/-- The iso-locus of a trinatural transformation is stable under arbitrary
retracts.  This is the thickness assertion of Lemma 2.3(2). -/
instance isoLocus_isStableUnderRetracts (η : Trinatural F G) :
    η.isoLocus.IsStableUnderRetracts where
  of_retract h hY := by
    letI : IsIso (η.toNatTrans.app _) := hY
    exact isIso_app_of_retract η.toNatTrans h

/-- If a trinatural transformation is an isomorphism on a classical generator,
then it is an isomorphism at every object.  (In the paper this is used in the
form: it suffices to check an isomorphism of exact functors on compact
generators, e.g. in the proof of Lemma 2.5.) -/
theorem isIso_of_isClassicalGenerator (η : Trinatural F G) {P : ObjectProperty C}
    (hP : P.IsClassicalTriangulatedGenerator)
    (h : ∀ X : C, P X → IsIso (η.toNatTrans.app X)) :
    ∀ X : C, IsIso (η.toNatTrans.app X) := by
  have hle : P ≤ η.isoLocus := h
  have htop : (⊤ : ObjectProperty C) ≤ η.isoLocus := by
    rw [← hP]
    exact (ObjectProperty.triangEnvelope_le_iff (P := P) (Q := η.isoLocus)).2 hle
  exact fun X => htop X trivial

end Trinatural

end RelativeFM
