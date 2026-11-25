import FourierMukai.Scheme.DerivedCoproducts
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.BifunctorHomotopy

/-!
# Independence of K-projective representatives

Two K-projective complexes isomorphic in the derived category are homotopy
equivalent.  The equivalence is constructed directly from the given derived
isomorphism.  Consequently every additive functor carries such representatives
to isomorphic objects in the target derived category, without assuming that the
functor is exact.
-/

@[expose] public section

namespace RelativeFM.KProjectiveTensorHom

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The derived isomorphism between two K-projective complexes lifted to the
homotopy category. -/
noncomputable def homotopyIsoOfDerivedIso {K L : CochainComplex C ℤ}
    [K.IsKProjective] [L.IsKProjective]
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    (HomotopyCategory.quotient C (.up ℤ)).obj K ≅
      (HomotopyCategory.quotient C (.up ℤ)).obj L := by
  let E := DerivedCoproducts.derivedHomKProjectiveEquiv K L
  let E' := DerivedCoproducts.derivedHomKProjectiveEquiv L K
  let f := E.symm e.hom
  let g := E'.symm e.inv
  have hfg : f ≫ g = 𝟙 _ := by
    apply (DerivedCoproducts.derivedHomKProjectiveEquiv K K).injective
    rw [DerivedCoproducts.derivedHomKProjectiveEquiv_apply,
      DerivedCoproducts.derivedHomMap_comp]
    change DerivedCoproducts.derivedHomMap K L f ≫ DerivedCoproducts.derivedHomMap L K g =
      DerivedCoproducts.derivedHomMap K K (𝟙 _)
    rw [show DerivedCoproducts.derivedHomMap K L f = e.hom from by
      change E (E.symm e.hom) = e.hom
      exact E.apply_symm_apply e.hom]
    rw [show DerivedCoproducts.derivedHomMap L K g = e.inv from by
      change E' (E'.symm e.inv) = e.inv
      exact E'.apply_symm_apply e.inv]
    simp [DerivedCoproducts.derivedHomMap]
  have hgf : g ≫ f = 𝟙 _ := by
    apply (DerivedCoproducts.derivedHomKProjectiveEquiv L L).injective
    rw [DerivedCoproducts.derivedHomKProjectiveEquiv_apply,
      DerivedCoproducts.derivedHomMap_comp]
    change DerivedCoproducts.derivedHomMap L K g ≫ DerivedCoproducts.derivedHomMap K L f =
      DerivedCoproducts.derivedHomMap L L (𝟙 _)
    rw [show DerivedCoproducts.derivedHomMap K L f = e.hom from by
      change E (E.symm e.hom) = e.hom
      exact E.apply_symm_apply e.hom]
    rw [show DerivedCoproducts.derivedHomMap L K g = e.inv from by
      change E' (E'.symm e.inv) = e.inv
      exact E'.apply_symm_apply e.inv]
    simp [DerivedCoproducts.derivedHomMap]
  exact { hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }

/-- Two K-projective representatives of one derived object are homotopy
equivalent. -/
noncomputable def homotopyEquivOfDerivedIso {K L : CochainComplex C ℤ}
    [K.IsKProjective] [L.IsKProjective]
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) : HomotopyEquiv K L :=
  HomotopyCategory.homotopyEquivOfIso (homotopyIsoOfDerivedIso e)

/-- The homotopy lift really computes the supplied derived isomorphism. -/
lemma derivedHomMap_homotopyIsoOfDerivedIso_hom {K L : CochainComplex C ℤ}
    [K.IsKProjective] [L.IsKProjective]
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    DerivedCoproducts.derivedHomMap K L (homotopyIsoOfDerivedIso e).hom = e.hom := by
  exact (DerivedCoproducts.derivedHomKProjectiveEquiv K L).apply_symm_apply e.hom

/-- An additive functor carries K-projective complexes isomorphic in the
derived category to isomorphic complexes in its target derived category. -/
noncomputable def qObjMapHomologicalComplexIsoOfDerivedIso {D : Type*} [Category D]
    [Abelian D] (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ}
    [K.IsKProjective] [L.IsKProjective]
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj L) := by
  let e' := homotopyIsoOfDerivedIso e
  exact (DerivedCategory.quotientCompQhIso D).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategory (.up ℤ)).mapIso e') ≪≫
      (DerivedCategory.quotientCompQhIso D).app _

/-- The isomorphism induced on any K-projective resolution of a common derived
object. -/
noncomputable def DerivedCoproducts.KProjectiveResolution.homotopyEquiv
    {X : DerivedCategory C}
    (R S : DerivedCoproducts.KProjectiveResolution X) : HomotopyEquiv R.complex S.complex := by
  letI : R.complex.IsKProjective := R.isKProjective
  letI : S.complex.IsKProjective := S.isKProjective
  exact homotopyEquivOfDerivedIso (R.iso ≪≫ S.iso.symm)

/-- Tensor products preserve homotopy equivalences in both variables. -/
noncomputable def tensorHomotopyEquiv {R : Type u} [CommRing R]
    {K₁ K₂ L₁ L₂ : CochainComplex (ModuleCat.{u} R) ℤ}
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (K₁ ⊗ K₂) (L₁ ⊗ L₂) where
  hom := e₁.hom ⊗ₘ e₂.hom
  inv := e₁.inv ⊗ₘ e₂.inv
  homotopyHomInvId := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    exact (((HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyHomInvId
        (e₂.hom ≫ e₂.inv) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K₁) e₂.homotopyHomInvId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (MonoidalCategory.id_tensorHom_id K₁ K₂)))
  homotopyInvHomId := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    exact (((HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyInvHomId
        (e₂.inv ≫ e₂.hom) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 L₁) e₂.homotopyInvHomId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (MonoidalCategory.id_tensorHom_id L₁ L₂)))

/-- The derived isomorphism induced by two homotopy equivalences. -/
noncomputable def qObjTensorIsoOfHomotopyEquiv {R : Type u} [CommRing R]
    {K₁ K₂ L₁ L₂ : CochainComplex (ModuleCat.{u} R) ℤ}
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    DerivedCategory.Q.obj (K₁ ⊗ K₂) ≅ DerivedCategory.Q.obj (L₁ ⊗ L₂) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso
      (HomotopyCategory.isoOfHomotopyEquiv (tensorHomotopyEquiv e₁ e₂)) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app _

/-- Independence of the total tensor model on a pair of K-projective
representatives. -/
noncomputable def qObjTensorIsoOfDerivedIso {R : Type u} [CommRing R]
    {K₁ K₂ L₁ L₂ : CochainComplex (ModuleCat.{u} R) ℤ}
    [K₁.IsKProjective] [L₁.IsKProjective] [K₂.IsKProjective] [L₂.IsKProjective]
    (e₁ : DerivedCategory.Q.obj K₁ ≅ DerivedCategory.Q.obj L₁)
    (e₂ : DerivedCategory.Q.obj K₂ ≅ DerivedCategory.Q.obj L₂) :
    DerivedCategory.Q.obj (K₁ ⊗ K₂) ≅ DerivedCategory.Q.obj (L₁ ⊗ L₂) :=
  qObjTensorIsoOfHomotopyEquiv
    (homotopyEquivOfDerivedIso e₁) (homotopyEquivOfDerivedIso e₂)

end
end RelativeFM.KProjectiveTensorHom

#print axioms RelativeFM.KProjectiveTensorHom.homotopyIsoOfDerivedIso
#print axioms RelativeFM.KProjectiveTensorHom.homotopyEquivOfDerivedIso
#print axioms RelativeFM.KProjectiveTensorHom.qObjMapHomologicalComplexIsoOfDerivedIso
#print axioms RelativeFM.KProjectiveTensorHom.tensorHomotopyEquiv
#print axioms RelativeFM.KProjectiveTensorHom.qObjTensorIsoOfDerivedIso
