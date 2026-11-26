/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Trinatural transformations and the iso-locus of a natural transformation

This file formalizes Appendix B and Lemma 2.3(2) of

  E. Guisado Villalgordo, P. Lank, *Relative Fourier--Mukai theory for algebraic spaces*.

The paper works with the 2-category `Triang` of triangulated categories, whose
2-morphisms are *trinatural* transformations (Definition B.9).  We take the
following equivalent formulation: a trinatural transformation `F ⟶ G` between
triangulated functors is a natural transformation whose components are compatible
with the translation (the `CommShift` isomorphisms of Mathlib) and which, on every
distinguished triangle, is induced by a morphism of triangles.

## Main results

* `Trinatural.isIso_app_shift` : the iso-locus is stable under shifts.
* `Trinatural.isIso_app_zero` : the iso-locus contains a zero object.
* `Trinatural.isIso_app_of_distinguished` : the iso-locus is closed under cones
  (Lemma 2.3(2)).
* `Trinatural.isoLocus_isTriangulated` : the iso-locus is a triangulated
  subcategory (the triangulated part of Lemma 2.3(2)).

The thickness part of Lemma 2.3(2) (closure under direct summands) is *not*
formalized here; see `results/archive/REPORT.md`.

## Implementation notes

Mathlib's `ObjectProperty.IsTriangulated` does not ask for closure under direct
summands, so the triangulated part is exactly what is proved below.

## References

* [Guisado Villalgordo, Lank, *Relative Fourier--Mukai theory for algebraic spaces*]
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- A *trinatural transformation* between triangulated functors, i.e. a
2-morphism of the 2-category `Triang` of triangulated categories (Definition B.9).

Compared with a natural transformation `F ⟶ G`, we ask that the components be
compatible with the translation isomorphisms (`comm_shift`, equation (B.1) of the
paper) and that on every distinguished triangle the components fit into a
morphism of triangles (`triangle_lift`, equation (B.3) of the paper). -/
structure Trinatural (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] extends F ⟶ G where
  /-- Compatibility with the translation isomorphisms (paper, (B.1)). -/
  comm_shift (X : C) (n : ℤ) :
    (F.commShiftIso n).hom.app X ≫ (toNatTrans.app X)⟦n⟧' =
      toNatTrans.app (X⟦n⟧) ≫ (G.commShiftIso n).hom.app X
  /-- On a distinguished triangle, the components are induced by a morphism of
  triangles (paper, (B.3)). -/
  triangle_lift (T : Triangle C) (hT : T ∈ distTriang C) :
    ∃ θ : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T,
      θ.hom₁ = toNatTrans.app T.obj₁ ∧ θ.hom₂ = toNatTrans.app T.obj₂ ∧
        θ.hom₃ = toNatTrans.app T.obj₃

namespace Trinatural

variable {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]

instance instCoeNatTrans : Coe (Trinatural F G) (F ⟶ G) := ⟨fun η => η.toNatTrans⟩

/-- The underlying natural transformation of a trinatural transformation. -/
add_decl_doc Trinatural.toNatTrans

/-- The object property "`η` is an isomorphism at `X`". -/
def isoLocus (η : Trinatural F G) : ObjectProperty C := fun X => IsIso (η.toNatTrans.app X)

/-- The identity trinatural transformation of a functor commuting with the shift.
(It is trinatural for any `F` with a `CommShift`, triangulatedness is not needed.) -/
def id (F : C ⥤ D) [F.CommShift ℤ] : Trinatural F F where
  app X := 𝟙 _
  naturality X Y f := by simp
  comm_shift X n := by simp
  triangle_lift T _ := ⟨𝟙 _, rfl, rfl, rfl⟩

/-- Vertical composition of trinatural transformations (the composition of
2-cells in the 2-category `Triang` of the paper, Definition B.9). -/
def comp {F G H : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (η : Trinatural F G) (θ : Trinatural G H) : Trinatural F H where
  toNatTrans := NatTrans.vcomp η.toNatTrans θ.toNatTrans
  comm_shift X n := by
    show (F.commShiftIso n).hom.app X ≫
        (shiftFunctor D n).map (η.toNatTrans.app X ≫ θ.toNatTrans.app X) =
      (η.toNatTrans.app (X⟦n⟧) ≫ θ.toNatTrans.app (X⟦n⟧)) ≫
        (H.commShiftIso n).hom.app X
    rw [Functor.map_comp]
    calc (F.commShiftIso n).hom.app X ≫
          ((η.toNatTrans.app X)⟦n⟧' ≫ (θ.toNatTrans.app X)⟦n⟧')
        = ((F.commShiftIso n).hom.app X ≫ (η.toNatTrans.app X)⟦n⟧') ≫
            (θ.toNatTrans.app X)⟦n⟧' := (Category.assoc _ _ _).symm
      _ = (η.toNatTrans.app (X⟦n⟧) ≫ (G.commShiftIso n).hom.app X) ≫
            (θ.toNatTrans.app X)⟦n⟧' := by rw [η.comm_shift]
      _ = η.toNatTrans.app (X⟦n⟧) ≫
            ((G.commShiftIso n).hom.app X ≫ (θ.toNatTrans.app X)⟦n⟧') :=
            Category.assoc _ _ _
      _ = η.toNatTrans.app (X⟦n⟧) ≫
            (θ.toNatTrans.app (X⟦n⟧) ≫ (H.commShiftIso n).hom.app X) :=
            by rw [θ.comm_shift]
      _ = (η.toNatTrans.app (X⟦n⟧) ≫ θ.toNatTrans.app (X⟦n⟧)) ≫
            (H.commShiftIso n).hom.app X := (Category.assoc _ _ _).symm
  triangle_lift T hT := by
    obtain ⟨θ₁, h₁, h₂, h₃⟩ := η.triangle_lift T hT
    obtain ⟨θ₂, k₁, k₂, k₃⟩ := θ.triangle_lift T hT
    refine ⟨θ₁ ≫ θ₂, ?_, ?_, ?_⟩
    · show θ₁.hom₁ ≫ θ₂.hom₁ = η.toNatTrans.app T.obj₁ ≫ θ.toNatTrans.app T.obj₁
      rw [h₁, k₁]
    · show θ₁.hom₂ ≫ θ₂.hom₂ = η.toNatTrans.app T.obj₂ ≫ θ.toNatTrans.app T.obj₂
      rw [h₂, k₂]
    · show θ₁.hom₃ ≫ θ₂.hom₃ = η.toNatTrans.app T.obj₃ ≫ θ.toNatTrans.app T.obj₃
      rw [h₃, k₃]

@[simp] lemma id_app (F : C ⥤ D) [F.CommShift ℤ] (X : C) :
    (id F).toNatTrans.app X = 𝟙 _ := rfl

@[simp] lemma comp_app {F G H : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (η : Trinatural F G) (θ : Trinatural G H) (X : C) :
    (η.comp θ).toNatTrans.app X = η.toNatTrans.app X ≫ θ.toNatTrans.app X := rfl

variable (η : Trinatural F G)

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [F.IsTriangulated] [G.IsTriangulated] in
lemma isoLocus_def (X : C) : η.isoLocus X ↔ IsIso (η.toNatTrans.app X) := Iff.rfl

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [F.IsTriangulated] [G.IsTriangulated] in
/-- The iso-locus is stable under shifts.  This is where compatibility with the
translation (paper, (B.1)) is used. -/
lemma isIso_app_shift (X : C) (n : ℤ) (hX : IsIso (η.toNatTrans.app X)) :
    IsIso (η.toNatTrans.app (X⟦n⟧)) := by
  have h := η.comm_shift X n
  have h' : η.toNatTrans.app (X⟦n⟧) =
      ((F.commShiftIso n).hom.app X ≫ (η.toNatTrans.app X)⟦n⟧') ≫
        ((G.commShiftIso n).app X).inv :=
    (Iso.eq_comp_inv ((G.commShiftIso n).app X)).2 h.symm
  rw [h']
  infer_instance

/-- The iso-locus contains a zero object. -/
lemma isIso_app_zero :
    ∃ (Z : C), IsZero Z ∧ IsIso (η.toNatTrans.app Z) := by
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := C)
  exact ⟨Z, hZ, Limits.IsZero.isIso (Functor.map_isZero F hZ)
    (Functor.map_isZero G hZ) _⟩

/-- The iso-locus is closed under cones: this is Lemma 2.3(2), triangulated part. -/
lemma isIso_app_of_distinguished (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsIso (η.toNatTrans.app T.obj₁)) (h₂ : IsIso (η.toNatTrans.app T.obj₂)) :
    IsIso (η.toNatTrans.app T.obj₃) := by
  obtain ⟨θ, hθ₁, hθ₂, hθ₃⟩ := η.triangle_lift T hT
  rw [← hθ₃]
  refine isIso₃_of_isIso₁₂ θ (F.map_distinguished T hT) (G.map_distinguished T hT) ?_ ?_
  · rwa [hθ₁]
  · rwa [hθ₂]

/-- The iso-locus is closed under isomorphisms. -/
instance isoLocus_isClosedUnderIsomorphisms : η.isoLocus.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    have h := η.toNatTrans.naturality e.hom
    have hY : η.toNatTrans.app Y =
        ((asIso (F.map e.hom)).inv ≫ (η.toNatTrans.app X ≫ G.map e.hom)) :=
      (Iso.eq_inv_comp (asIso (F.map e.hom))).2 h
    change IsIso (η.toNatTrans.app Y)
    rw [hY]
    have hX' : IsIso (η.toNatTrans.app X) := hX
    infer_instance

instance isoLocus_isStableUnderShift : η.isoLocus.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun X hX => η.isIso_app_shift X n hX⟩

instance isoLocus_containsZero : η.isoLocus.ContainsZero :=
  ⟨η.isIso_app_zero⟩

instance isoLocus_isTriangulatedClosed₃ : η.isoLocus.IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (fun T hT h₁ h₂ =>
    η.isIso_app_of_distinguished T hT h₁ h₂)

instance isoLocus_isTriangulatedClosed₂ : η.isoLocus.IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

/-- **Lemma 2.3(2)** (triangulated part): for a trinatural transformation `η`
between triangulated functors, the full subcategory of objects at which `η` is an
isomorphism is a triangulated subcategory. -/
instance isoLocus_isTriangulated : η.isoLocus.IsTriangulated := {}

end Trinatural

end RelativeFM
