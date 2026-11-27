/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# A triangulated model with `w`-small morphisms

Let `C` be a pretriangulated category whose morphism types are `w`-small
(`LocallySmall.{w} C`).  Then `ShrinkHoms.{w} C`, the same objects with morphism types replaced
by models in `Type w`, carries a pretriangulated structure for which
`ShrinkHoms.functor C` is additive, commutes with the shift and is triangulated, and which is
triangulated when `C` is.  This is how results stated for categories whose direct sums are
indexed by the Hom universe apply to a category, such as AxiomMath's `D(𝒪_X)`, whose morphisms
live one universe above the index types of its direct sums.

The structure is obtained by viewing `ShrinkHoms.functor C` as the localization of `C` at its
isomorphisms (`Triangulated.Localization.pretriangulated`).  The same construction, with the
same three lemmas on the isomorphisms, is AxiomMath's
`CategoryTheory.Pretriangulated.exists_triangulatedEquivalence_of_locallySmall`
(`StacksFrontier/CategoryTheory/Triangulated/ShrinkHomsTriangulated.lean`, outside the `Spaces`
import list); it is reproved here from Mathlib so that the `WeakApprox` library can use it.

## Main result

* `RelativeWeakApprox.SumUniverse.exists_triangulatedEquivalence_of_locallySmall`.

## Assumptions

None.  Mathlib only.
-/

@[expose] public section

namespace RelativeWeakApprox.SumUniverse

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe w v u

/-- The isomorphisms of any category have a left calculus of fractions. -/
theorem isomorphisms_hasLeftCalculusOfFractions (C : Type u) [Category.{v} C] :
    (MorphismProperty.isomorphisms C).HasLeftCalculusOfFractions := by
  constructor
  · intro X Y φ
    have : IsIso φ.s := φ.hs
    exact ⟨MorphismProperty.LeftFraction.mk (inv φ.s ≫ φ.f) (𝟙 Y) inferInstance, by simp⟩
  · intro X' X Y f₁ f₂ s hs h
    have : IsIso s := hs
    exact ⟨Y, 𝟙 Y, inferInstance, by simpa using (cancel_epi s).1 h⟩

/-- The isomorphisms are stable under the shift. -/
theorem isomorphisms_isCompatibleWithShift (C : Type u) [Category.{v} C] [HasShift C ℤ] :
    (MorphismProperty.isomorphisms C).IsCompatibleWithShift ℤ := by
  constructor
  intro n
  ext X Y f
  change IsIso ((shiftFunctor C n).map f) ↔ IsIso f
  constructor
  · intro h
    exact isIso_of_reflects_iso f (shiftFunctor C n)
  · intro h
    infer_instance

/-- The isomorphisms are compatible with the triangulation (TR3 and the two-out-of-three
property of isomorphisms of triangles). -/
theorem isomorphisms_isCompatibleWithTriangulation (C : Type u) [Category.{v} C]
    [HasShift C ℤ] [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] :
    (MorphismProperty.isomorphisms C).IsCompatibleWithTriangulation := by
  let := isomorphisms_isCompatibleWithShift C
  constructor
  intro T₁ T₂ hT₁ hT₂ a b ha hb fac
  let φ := completeDistinguishedTriangleMorphism T₁ T₂ hT₁ hT₂ a b fac
  exact ⟨φ.hom₃, isIso₃_of_isIso₁₂ φ hT₁ hT₂ ha hb, φ.comm₂, φ.comm₃⟩

/-- **A locally `w`-small pretriangulated category has a triangulated model with morphisms in
`Type w`**: a pretriangulated `D` with `Category.{w} D` and an equivalence `e : C ≌ D` both of
whose halves are additive, commute with the shift and are triangulated; `D` is triangulated
when `C` is.  The model is `ShrinkHoms.{w} C` with the structure descended along
`ShrinkHoms.functor C`.  (AxiomMath:
`CategoryTheory.Pretriangulated.exists_triangulatedEquivalence_of_locallySmall`; reproved here
from Mathlib.) -/
theorem exists_triangulatedEquivalence_of_locallySmall
    (C : Type u) [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [LocallySmall.{w} C] :
    ∃ (D : Type u) (_ : Category.{w} D) (_ : Preadditive D) (_ : HasZeroObject D)
      (_ : HasShift D ℤ) (_ : ∀ n : ℤ, (shiftFunctor D n).Additive) (_ : Pretriangulated D)
      (e : C ≌ D) (_ : e.functor.Additive) (_ : e.inverse.Additive)
      (_ : e.functor.CommShift ℤ) (_ : e.inverse.CommShift ℤ)
      (_ : e.functor.IsTriangulated) (_ : e.inverse.IsTriangulated),
      IsTriangulated C → IsTriangulated D := by
  let : Category.{w} (ShrinkHoms C) := inferInstance
  let e := ShrinkHoms.equivalence.{w} C
  let W := MorphismProperty.isomorphisms C
  let := isomorphisms_hasLeftCalculusOfFractions C
  let := isomorphisms_isCompatibleWithShift C
  let := isomorphisms_isCompatibleWithTriangulation C
  let := Functor.IsLocalization.of_isEquivalence e.functor W le_rfl
  let := HasShift.localized e.functor W ℤ
  let := Functor.CommShift.localized e.functor W ℤ
  let : e.functor.Additive := ShrinkHoms.instAdditiveFunctor C
  let : e.inverse.Additive := e.toAdjunction.right_adjoint_additive
  let : HasZeroObject (ShrinkHoms C) :=
    ⟨⟨e.functor.obj 0, Functor.map_isZero e.functor (isZero_zero C)⟩⟩
  have hshift : ∀ n : ℤ, (shiftFunctor (ShrinkHoms C) n).Additive := fun n => by
    rw [Localization.functor_additive_iff e.functor W]
    exact Functor.additive_of_iso (e.functor.commShiftIso n)
  let := Triangulated.Localization.pretriangulated e.functor W
  let : e.functor.IsTriangulated :=
    Triangulated.Localization.isTriangulated_functor e.functor W
  let := e.commShiftInverse ℤ
  let := e.commShift_of_functor ℤ
  let : e.inverse.IsTriangulated := e.toAdjunction.isTriangulated_rightAdjoint
  exact ⟨ShrinkHoms C, inferInstance, inferInstance, inferInstance, inferInstance, hshift,
    inferInstance, e, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, fun _ => Triangulated.Localization.isTriangulated e.functor W⟩

end RelativeWeakApprox.SumUniverse

#print axioms RelativeWeakApprox.SumUniverse.exists_triangulatedEquivalence_of_locallySmall
