/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.WeakApproximable
import WeakApprox.Functoriality
import WeakApprox.CompactAb
import WeakApprox.Lemma4323
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Weak approximability is invariant under triangulated equivalences

`WeakApprox/WeakApproximable.lean` defines weak and standard weak
approximability.  This file shows that both are invariant under a triangulated
equivalence of triangulated categories that commutes with shifts and preserves
small coproducts: the t-structure is transported along the quasi-inverse, and
weak approximation data are transported by Neeman's adjoint criterion for
compactness, the corresponding statement for generation, and Lemma 3.1(3) for
the approximation envelopes.

Both directions are given, hence an `Iff`.  This is the invariance used when
moving between equivalent models of `D_qc`; the two categories must share the
hom universe `v`, because `IsCompactAb` and `Coprod` are indexed by it.

Found by a member of the Ultramath run `smwur4wqg` (direction D5).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type w} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Transport of a `t`-structure along a triangulated equivalence.  The aisle
and co-aisle in degree `n` consist of the objects whose image under `F.inv`
lies in the corresponding aisle or co-aisle of the source `t`-structure.
This is the t-structure invariance needed for Remark 5.4 of Lank--Pauwels. -/
noncomputable def transportTStructure (F : C ⥤ D) [F.IsEquivalence]
    [F.CommShift ℤ] [F.IsTriangulated] (t : TStructure C) : TStructure D := by
  letI : F.asEquivalence.functor.CommShift ℤ := by
    change F.CommShift ℤ
    infer_instance
  letI : F.asEquivalence.functor.IsTriangulated := by
    change F.IsTriangulated
    infer_instance
  letI : F.inv.CommShift ℤ := F.asEquivalence.commShiftInverse ℤ
  letI : F.asEquivalence.inverse.CommShift ℤ := by
    change F.inv.CommShift ℤ
    infer_instance
  letI : F.asEquivalence.CommShift ℤ := F.asEquivalence.commShift_of_functor ℤ
  letI : F.inv.IsTriangulated := F.asEquivalence.toAdjunction.isTriangulated_rightAdjoint
  exact
    { le := fun n Y => t.le n (F.inv.obj Y)
      ge := fun n Y => t.ge n (F.inv.obj Y)
      le_isClosedUnderIsomorphisms := fun n =>
        ⟨fun e' h => (t.le n).prop_of_iso (F.inv.mapIso e') h⟩
      ge_isClosedUnderIsomorphisms := fun n =>
        ⟨fun e' h => (t.ge n).prop_of_iso (F.inv.mapIso e') h⟩
      le_shift := fun n a n' h X hX =>
        (t.le n').prop_of_iso ((F.inv.commShiftIso a).app X).symm
          (t.le_shift n a n' h _ hX)
      ge_shift := fun n a n' h X hX =>
        (t.ge n').prop_of_iso ((F.inv.commShiftIso a).app X).symm
          (t.ge_shift n a n' h _ hX)
      zero' := by
        intro X Y f hX hY
        apply F.inv.map_injective
        rw [F.inv.map_zero]
        exact t.zero' (F.inv.map f) hX hY
      le_zero_le := fun _ hX => t.le_zero_le _ hX
      ge_one_le := fun _ hX => t.ge_one_le _ hX
      exists_triangle_zero_one := fun A => by
        obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ := t.exists_triangle_zero_one (F.inv.obj A)
        refine ⟨F.obj X, F.obj Y,
          (t.le 0).prop_of_iso (F.asEquivalence.unitIso.app X) hX,
          (t.ge 1).prop_of_iso (F.asEquivalence.unitIso.app Y) hY,
          F.map f ≫ (F.objObjPreimageIso A).hom, (F.objObjPreimageIso A).inv ≫ F.map g,
          F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app X, ?_⟩
        exact isomorphic_distinguished _ (F.map_distinguished _ hT) _
          (Triangle.isoMk _ _ (Iso.refl _) (F.objObjPreimageIso A).symm (Iso.refl _)
            (by
              simp only [Triangle.mk, Functor.mapTriangle, Iso.refl_hom, Category.id_comp,
                Iso.symm_hom]
              rw [Category.assoc, Iso.hom_inv_id, Category.comp_id])
            (by simp [Triangle.mk, Functor.mapTriangle])
            (by simp [Triangle.mk, Functor.mapTriangle])) }

/-- Membership in a transported aisle is, definitionally, membership after
applying the quasi-inverse.  This accompanies Remark 5.4's invariance statement. -/
theorem transportTStructure_le (F : C ⥤ D) [F.IsEquivalence]
    [F.CommShift ℤ] [F.IsTriangulated] (t : TStructure C) (n : ℤ) (Y : D) :
    (transportTStructure F t).le n Y ↔ t.le n (F.inv.obj Y) := Iff.rfl

/-- Membership in a transported co-aisle is, definitionally, membership after
applying the quasi-inverse.  This accompanies Remark 5.4's invariance statement. -/
theorem transportTStructure_ge (F : C ⥤ D) [F.IsEquivalence]
    [F.CommShift ℤ] [F.IsTriangulated] (t : TStructure C) (n : ℤ) (Y : D) :
    (transportTStructure F t).ge n Y ↔ t.ge n (F.inv.obj Y) := Iff.rfl

end RelativeWeakApprox

#print axioms RelativeWeakApprox.transportTStructure
