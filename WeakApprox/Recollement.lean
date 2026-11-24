/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Basic
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Recollements and their two gluing triangles

This file defines recollements of triangulated categories, following §2.1.4 and
Setup 4.1 of Lank--Pauwels, *Gluing weak approximability along recollements*.

Found by a member of the Ultramath run `smwun9hk2` (direction D1).

The six functors are exact: their `CommShift` and `IsTriangulated` data are
fields (Mathlib derives additivity from the latter).  The kernel condition is
written with chosen isomorphisms, as in the paper.  The two connecting maps are
natural transformations, which packages the functoriality in Setup 4.1.  The
first two maps in each gluing triangle are definitionally the relevant adjoint
(co)unit, rather than arbitrary maps later assumed to be equal to them.
No gluing theorem is proved here.
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe vZ uZ vD uD vU uU

/-- A recollement of triangulated categories.  Here `iStar`, `iLower`, `iShriek`
are `i^*`, `i_*`, `i^!`, and `jShriek`, `jStar`, `jUpper` are `j_!`, `j^*`,
`j_*`.

The three zero-composite conditions and the two distinguished gluing triangles
are fields, as required for the subsequent development.  Naturality of the
connecting transformations is the third-square functoriality condition; the
other two squares follow from naturality of the adjunction (co)units. -/
structure Recollement (DZ : Type uZ) (D : Type uD) (DU : Type uU)
    [Category.{vZ} DZ] [Category.{vD} D] [Category.{vU} DU]
    [Preadditive DZ] [Preadditive D] [Preadditive DU]
    [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
    [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
    [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [∀ (n : ℤ), (shiftFunctor DU n).Additive]
    [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
    [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
    [CategoryTheory.IsTriangulated DU] where
  /-- The upper-star functor `i^* : D ⥤ D_Z`. -/
  iStar : D ⥤ DZ
  /-- The lower-star functor `i_* : D_Z ⥤ D`. -/
  iLower : DZ ⥤ D
  /-- The upper-shriek functor `i^! : D ⥤ D_Z`. -/
  iShriek : D ⥤ DZ
  /-- The lower-shriek functor `j_! : D_U ⥤ D`. -/
  jShriek : DU ⥤ D
  /-- The upper-star functor `j^* : D ⥤ D_U`. -/
  jStar : D ⥤ DU
  /-- The lower-star functor `j_* : D_U ⥤ D`. -/
  jUpper : DU ⥤ D
  /-- `i^*` commutes with integer shifts. -/
  [iStar_commShift : iStar.CommShift ℤ]
  /-- `i_*` commutes with integer shifts. -/
  [iLower_commShift : iLower.CommShift ℤ]
  /-- `i^!` commutes with integer shifts. -/
  [iShriek_commShift : iShriek.CommShift ℤ]
  /-- `j_!` commutes with integer shifts. -/
  [jShriek_commShift : jShriek.CommShift ℤ]
  /-- `j^*` commutes with integer shifts. -/
  [jStar_commShift : jStar.CommShift ℤ]
  /-- `j_*` commutes with integer shifts. -/
  [jUpper_commShift : jUpper.CommShift ℤ]
  /-- `i^*` is exact. -/
  [iStar_exact : iStar.IsTriangulated]
  /-- `i_*` is exact. -/
  [iLower_exact : iLower.IsTriangulated]
  /-- `i^!` is exact. -/
  [iShriek_exact : iShriek.IsTriangulated]
  /-- `j_!` is exact. -/
  [jShriek_exact : jShriek.IsTriangulated]
  /-- `j^*` is exact. -/
  [jStar_exact : jStar.IsTriangulated]
  /-- `j_*` is exact. -/
  [jUpper_exact : jUpper.IsTriangulated]
  /-- The adjunction `i^* ⊣ i_*`. -/
  iStarAdj : iStar ⊣ iLower
  /-- The adjunction `i_* ⊣ i^!`. -/
  iLowerAdj : iLower ⊣ iShriek
  /-- The adjunction `j_! ⊣ j^*`. -/
  jShriekAdj : jShriek ⊣ jStar
  /-- The adjunction `j^* ⊣ j_*`. -/
  jStarAdj : jStar ⊣ jUpper
  /-- `i_*` is full. -/
  [iLower_full : iLower.Full]
  /-- `i_*` is faithful. -/
  [iLower_faithful : iLower.Faithful]
  /-- `j_!` is full. -/
  [jShriek_full : jShriek.Full]
  /-- `j_!` is faithful. -/
  [jShriek_faithful : jShriek.Faithful]
  /-- `j_*` is full. -/
  [jUpper_full : jUpper.Full]
  /-- `j_*` is faithful. -/
  [jUpper_faithful : jUpper.Faithful]
  /-- The kernel of `j^*` is the essential image of `i_*`. -/
  kernel (X : D) :
    Nonempty (jStar.obj X ≅ 0) ↔ ∃ Y : DZ, Nonempty (X ≅ iLower.obj Y)
  /-- The composite `j^* i_*` is naturally isomorphic to zero. -/
  jStar_iLower : iLower ⋙ jStar ≅ 0
  /-- The composite `i^! j_*` is naturally isomorphic to zero. -/
  iShriek_jUpper : jUpper ⋙ iShriek ≅ 0
  /-- The composite `i^* j_!` is naturally isomorphic to zero. -/
  iStar_jShriek : jShriek ⋙ iStar ≅ 0
  /-- The natural connecting map in the first gluing triangle. -/
  firstConnecting :
    iStar ⋙ iLower ⟶ jStar ⋙ jShriek ⋙ shiftFunctor D (1 : ℤ)
  /-- The natural connecting map in the second gluing triangle. -/
  secondConnecting :
    jStar ⋙ jUpper ⟶ iShriek ⋙ iLower ⋙ shiftFunctor D (1 : ℤ)
  /-- Distinguishedness of the first gluing triangle of Setup 4.1. -/
  first_distinguished (X : D) :
    Triangle.mk (jShriekAdj.counit.app X) (iStarAdj.unit.app X)
      (firstConnecting.app X) ∈ distTriang D
  /-- Distinguishedness of the second gluing triangle of Setup 4.1. -/
  second_distinguished (X : D) :
    Triangle.mk (iLowerAdj.counit.app X) (jStarAdj.unit.app X)
      (secondConnecting.app X) ∈ distTriang D

attribute [instance] Recollement.iStar_commShift Recollement.iLower_commShift
  Recollement.iShriek_commShift Recollement.jShriek_commShift
  Recollement.jStar_commShift Recollement.jUpper_commShift
  Recollement.iStar_exact Recollement.iLower_exact Recollement.iShriek_exact
  Recollement.jShriek_exact Recollement.jStar_exact Recollement.jUpper_exact
  Recollement.iLower_full Recollement.iLower_faithful
  Recollement.jShriek_full Recollement.jShriek_faithful
  Recollement.jUpper_full Recollement.jUpper_faithful

namespace Recollement

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{vZ} DZ] [Category.{vD} D] [Category.{vU} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

variable (R : Recollement DZ D DU)

/-- The first gluing triangle `j_!j^*X → X → i_*i^*X → j_!j^*X[1]`. -/
def firstTriangle (X : D) : Triangle D :=
  Triangle.mk (R.jShriekAdj.counit.app X) (R.iStarAdj.unit.app X)
    (R.firstConnecting.app X)

/-- The second gluing triangle `i_*i^!X → X → j_*j^*X → i_*i^!X[1]`. -/
def secondTriangle (X : D) : Triangle D :=
  Triangle.mk (R.iLowerAdj.counit.app X) (R.jStarAdj.unit.app X)
    (R.secondConnecting.app X)

/-- Naturality of the first gluing triangle. -/
def firstTriangleMap {X Y : D} (f : X ⟶ Y) :
    R.firstTriangle X ⟶ R.firstTriangle Y where
  hom₁ := R.jShriek.map (R.jStar.map f)
  hom₂ := f
  hom₃ := R.iLower.map (R.iStar.map f)
  comm₁ := by
    dsimp [firstTriangle]
    exact (R.jShriekAdj.counit.naturality f).symm
  comm₂ := by
    dsimp [firstTriangle]
    exact (R.iStarAdj.unit.naturality f).symm
  comm₃ := by
    dsimp [firstTriangle]
    exact (R.firstConnecting.naturality f).symm

/-- Naturality of the second gluing triangle. -/
def secondTriangleMap {X Y : D} (f : X ⟶ Y) :
    R.secondTriangle X ⟶ R.secondTriangle Y where
  hom₁ := R.iLower.map (R.iShriek.map f)
  hom₂ := f
  hom₃ := R.jUpper.map (R.jStar.map f)
  comm₁ := by
    dsimp [secondTriangle]
    exact (R.iLowerAdj.counit.naturality f).symm
  comm₂ := by
    dsimp [secondTriangle]
    exact (R.jStarAdj.unit.naturality f).symm
  comm₃ := by
    dsimp [secondTriangle]
    exact (R.secondConnecting.naturality f).symm

/-- The first gluing triangle as a functor `D ⥤ Triangle D`. -/
def firstTriangleFunctor : D ⥤ Triangle D where
  obj := R.firstTriangle
  map := R.firstTriangleMap
  map_id X := by
    ext <;> simp [firstTriangleMap] <;> rfl
  map_comp f g := by
    ext <;> simp [firstTriangleMap] <;> rfl

/-- The second gluing triangle as a functor `D ⥤ Triangle D`. -/
def secondTriangleFunctor : D ⥤ Triangle D where
  obj := R.secondTriangle
  map := R.secondTriangleMap
  map_id X := by
    ext <;> simp [secondTriangleMap] <;> rfl
  map_comp f g := by
    ext <;> simp [secondTriangleMap] <;> rfl

@[simp] lemma firstTriangleFunctor_obj (X : D) :
    R.firstTriangleFunctor.obj X = R.firstTriangle X := rfl

@[simp] lemma secondTriangleFunctor_obj (X : D) :
    R.secondTriangleFunctor.obj X = R.secondTriangle X := rfl

/-- Objectwise vanishing of `j^* i_*`. -/
lemma jStar_iLower_isZero (X : DZ) : IsZero (R.jStar.obj (R.iLower.obj X)) :=
  (Functor.zero_obj X).of_iso (R.jStar_iLower.app X)

/-- Objectwise vanishing of `i^! j_*`. -/
lemma iShriek_jUpper_isZero (X : DU) : IsZero (R.iShriek.obj (R.jUpper.obj X)) :=
  (Functor.zero_obj X).of_iso (R.iShriek_jUpper.app X)

/-- Objectwise vanishing of `i^* j_!`. -/
lemma iStar_jShriek_isZero (X : DU) : IsZero (R.iStar.obj (R.jShriek.obj X)) :=
  (Functor.zero_obj X).of_iso (R.iStar_jShriek.app X)

end Recollement
end RelativeWeakApprox
