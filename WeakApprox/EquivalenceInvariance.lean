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

/-- Transport of weak approximation data (Definition 2.1) along a triangulated
equivalence.  Compactness and generation are transported by the adjunction;
Lemma 3.1(3) transports the approximation envelope. -/
noncomputable def transportWeakApproximationData (F : C ⥤ D) [F.IsEquivalence]
    [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    [HasCoproducts.{v} C] [HasCoproducts.{v} D]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
    (W : WeakApproximationData C) : WeakApproximationData D := by
  letI : F.asEquivalence.functor.CommShift ℤ := by
    change F.CommShift ℤ
    infer_instance
  letI : F.asEquivalence.functor.Additive := by
    change F.Additive
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
    { G := F.obj W.G
      t := transportTStructure F W.t
      A := W.A
      A_pos := W.A_pos
      G_compact := isCompactAb_leftAdjoint_obj' F.asEquivalence.toAdjunction W.G_compact
        (fun _ => inferInstance)
      G_generates := isGenerator_leftAdjoint_obj F.asEquivalence.toAdjunction W.G_generates
      G_mem_le := (W.t.le W.A).prop_of_iso (F.asEquivalence.unitIso.app W.G) W.G_mem_le
      hom_vanishing := by
        intro Y hY f
        change W.t.le (-W.A) (F.inv.obj Y) at hY
        apply (F.asEquivalence.toAdjunction.homEquiv W.G Y).injective
        rw [W.hom_vanishing hY (F.asEquivalence.toAdjunction.homEquiv W.G Y f)]
        exact (F.asEquivalence.toAdjunction.homAddEquiv_zero W.G Y).symm
      exists_triangle := by
        intro Y hY
        change W.t.le 0 (F.inv.obj Y) at hY
        obtain ⟨X, Z, f, g, h, hT, hX, hZ⟩ := W.exists_triangle _ hY
        have hself : envelope (F.obj W.G) 0 0 (F.obj W.G) :=
          lemma_3_1_1_contains _ _ _ _ (shiftInterval_self _ (by simp) (by simp))
        refine ⟨F.obj X, F.obj Z,
          F.map f ≫ (F.objObjPreimageIso Y).hom, (F.objObjPreimageIso Y).inv ≫ F.map g,
          F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app X, ?_, ?_, ?_⟩
        · exact isomorphic_distinguished _ (F.map_distinguished _ hT) _
            (Triangle.isoMk _ _ (Iso.refl _) (F.objObjPreimageIso Y).symm (Iso.refl _)
              (by
                simp only [Triangle.mk, Functor.mapTriangle, Iso.refl_hom, Category.id_comp,
                  Iso.symm_hom]
                rw [Category.assoc, Iso.hom_inv_id, Category.comp_id])
              (by simp [Triangle.mk, Functor.mapTriangle])
              (by simp [Triangle.mk, Functor.mapTriangle]))
        · simpa using lemma_3_1_3 F W.G (F.obj W.G) (-W.A) W.A 0 0 hself hX
        · exact (W.t.le (-1)).prop_of_iso (F.asEquivalence.unitIso.app Z) hZ }

/-- **Definition 5.3, invariance under equivalence.**  A triangulated,
shift-compatible equivalence carrying small coproducts transports weak
approximation data, and hence weak approximability.  Exactness is stated as
`F.IsTriangulated`, since bare `F.IsEquivalence` does not provide that instance. -/
theorem satisfiesWA_of_equivalence (F : C ⥤ D) [F.CommShift ℤ] [F.Additive]
    [F.IsTriangulated] [CategoryTheory.IsTriangulated C]
    [CategoryTheory.IsTriangulated D] (hF : F.IsEquivalence)
    [HasCoproducts.{v} C] [HasCoproducts.{v} D]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F] :
    SatisfiesWA C → SatisfiesWA D := by
  letI : F.IsEquivalence := hF
  rintro ⟨W⟩
  exact ⟨transportWeakApproximationData F W⟩

/-- **Definition 5.3, reverse invariance.**  The quasi-inverse of a triangulated
equivalence transports weak approximability back to the source category. -/
theorem satisfiesWA_of_equivalence_inv (F : C ⥤ D) [F.CommShift ℤ] [F.Additive]
    [F.IsTriangulated] [CategoryTheory.IsTriangulated C]
    [CategoryTheory.IsTriangulated D] (hF : F.IsEquivalence)
    [HasCoproducts.{v} C] [HasCoproducts.{v} D]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F] :
    SatisfiesWA D → SatisfiesWA C := by
  letI : F.IsEquivalence := hF
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
  exact satisfiesWA_of_equivalence F.inv inferInstance

/-- **Definition 5.3, equivalence invariance as an iff.** -/
theorem satisfiesWA_iff_of_equivalence (F : C ⥤ D) [F.CommShift ℤ] [F.Additive]
    [F.IsTriangulated] [CategoryTheory.IsTriangulated C]
    [CategoryTheory.IsTriangulated D] (hF : F.IsEquivalence)
    [HasCoproducts.{v} C] [HasCoproducts.{v} D]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F] :
    SatisfiesWA C ↔ SatisfiesWA D :=
  ⟨satisfiesWA_of_equivalence F hF, satisfiesWA_of_equivalence_inv F hF⟩

/-- **Remark 5.4, invariance under equivalence.**  Standard weak
approximability is transported with its chosen t-structure: the data produced
have t-structure `transportTStructure F t`. -/
theorem satisfiesStandardWA_of_equivalence (F : C ⥤ D) [F.CommShift ℤ] [F.Additive]
    [F.IsTriangulated] [CategoryTheory.IsTriangulated C]
    [CategoryTheory.IsTriangulated D] (hF : F.IsEquivalence)
    [HasCoproducts.{v} C] [HasCoproducts.{v} D]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
    (t : TStructure C) :
    SatisfiesStandardWA C t → SatisfiesStandardWA D (transportTStructure F t) := by
  letI : F.IsEquivalence := hF
  rintro ⟨W, rfl⟩
  exact ⟨transportWeakApproximationData F W, rfl⟩

/-- **Remark 5.4, reverse invariance.**  The quasi-inverse transports standard
weak approximability, with the t-structure transported by that quasi-inverse. -/
theorem satisfiesStandardWA_of_equivalence_inv (F : C ⥤ D) [F.CommShift ℤ]
    [F.Additive] [F.IsTriangulated] [CategoryTheory.IsTriangulated C]
    [CategoryTheory.IsTriangulated D] (hF : F.IsEquivalence)
    [F.inv.CommShift ℤ] [F.inv.IsTriangulated]
    [HasCoproducts.{v} C] [HasCoproducts.{v} D]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
    (t : TStructure D) :
    SatisfiesStandardWA D t → SatisfiesStandardWA C (transportTStructure F.inv t) := by
  letI : F.IsEquivalence := hF
  exact satisfiesStandardWA_of_equivalence F.inv inferInstance t

end RelativeWeakApprox

#print axioms RelativeWeakApprox.transportTStructure
#print axioms RelativeWeakApprox.transportWeakApproximationData
#print axioms RelativeWeakApprox.satisfiesWA_iff_of_equivalence
#print axioms RelativeWeakApprox.satisfiesStandardWA_of_equivalence
