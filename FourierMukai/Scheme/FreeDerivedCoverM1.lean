import FourierMukai.Scheme.AffineSupportedBaseM1
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Derived lifts of maps out of a projective object in degree zero
-/

@[expose] public section

namespace RelativeFM.FreeDerivedCoverM1

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe w v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Lift a map out of a projective object to a derived morphism, after choosing
an ambient complex strictly bounded above by zero. -/
lemma exists_derived_from_single_projective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {P : C} [Projective P] (K : CochainComplex C ℤ) [K.IsStrictlyLE 0]
    {F : DerivedCategory C} (e : DerivedCategory.Q.obj K ≅ F)
    (ρ : P ⟶ (DerivedCategory.homologyFunctor C 0).obj F) :
    ∃ ψ : DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj P) ⟶ F,
      (DerivedCategory.homologyFunctorFactors C 0).hom.app
          ((HomologicalComplex.single C (.up ℤ) 0).obj P) ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 P).hom ≫ ρ =
          (DerivedCategory.homologyFunctor C 0).map ψ := by
  let H := DerivedCategory.homologyFunctor C 0
  let HF := DerivedCategory.homologyFunctorFactors C 0
  let eC := K.iCyclesIso 0 1 (by simp)
    ((K.isZero_of_isStrictlyLE 0 1 (by simp)).eq_of_tgt _ _)
  let q : P ⟶ K.homology 0 := ρ ≫ (H.mapIso e).inv ≫ HF.hom.app K
  let k : P ⟶ K.X 0 := Projective.factorThru q (eC.inv ≫ K.homologyπ 0)
  let h : (HomologicalComplex.single C (.up ℤ) 0).obj P ⟶ K :=
    HomologicalComplex.mkHomFromSingle k (fun j hj =>
      (K.isZero_of_isStrictlyLE 0 j (by
        change 0 + 1 = j at hj
        omega)).eq_of_tgt _ _)
  let ψ : DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj P) ⟶ F :=
    DerivedCategory.Q.map h ≫ e.hom
  have hk : k ≫ eC.inv ≫ K.homologyπ 0 = q := by
    exact Projective.factorThru_comp q (eC.inv ≫ K.homologyπ 0)
  let eH := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 P
  let eS := HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 P
  have hmap : eH.hom ≫ q = HomologicalComplex.homologyMap h 0 := by
    rw [← hk]
    apply (cancel_epi (((HomologicalComplex.single C (.up ℤ) 0).obj P).homologyπ 0)).mp
    rw [HomologicalComplex.homologyπ_naturality]
    have hs : ((HomologicalComplex.single C (.up ℤ) 0).obj P).homologyπ 0 ≫ eH.hom =
        eS.hom := HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom _ _ _
    rw [← Category.assoc, hs]
    have hc : HomologicalComplex.cyclesMap h 0 =
        ((HomologicalComplex.single C (.up ℤ) 0).obj P).iCycles 0 ≫ h.f 0 ≫ eC.inv := by
      rw [← cancel_mono eC.hom]
      change HomologicalComplex.cyclesMap h 0 ≫ K.iCycles 0 = _
      rw [HomologicalComplex.cyclesMap_i]
      simp
    rw [hc]
    have he : eS.hom = ((HomologicalComplex.single C (.up ℤ) 0).obj P).iCycles 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).hom :=
      HomologicalComplex.singleObjCyclesSelfIso_hom _ _ _
    rw [he]
    have hf : h.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).hom ≫ k :=
      HomologicalComplex.mkHomFromSingle_f _ _
    rw [hf]
    simp only [Category.assoc]
  refine ⟨ψ, ?_⟩
  dsimp [ψ]
  change HF.hom.app ((HomologicalComplex.single C (.up ℤ) 0).obj P) ≫ eH.hom ≫ ρ =
    (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map h ≫ e.hom)
  rw [Functor.map_comp]
  have he : (DerivedCategory.homologyFunctor C 0).map e.hom ≫
      (DerivedCategory.homologyFunctor C 0).map e.inv = 𝟙 _ := by
    rw [← Functor.map_comp, e.hom_inv_id]
    simp
  rw [← cancel_mono (H.map e.inv)]
  rw [← cancel_mono (HF.hom.app K)]
  simp only [H, Category.assoc, he, Category.comp_id]
  exact calc
    HF.hom.app ((HomologicalComplex.single C (.up ℤ) 0).obj P) ≫
        eH.hom ≫ ρ ≫ (DerivedCategory.homologyFunctor C 0).map e.inv ≫ HF.hom.app K =
      HF.hom.app ((HomologicalComplex.single C (.up ℤ) 0).obj P) ≫ eH.hom ≫ q := by
        simp only [q, H, Functor.mapIso_inv, Category.assoc]
    _ = HF.hom.app ((HomologicalComplex.single C (.up ℤ) 0).obj P) ≫
        HomologicalComplex.homologyMap h 0 := by rw [hmap]
    _ = (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map h) ≫
        HF.hom.app K := (HF.hom.naturality h).symm

end

end RelativeFM.FreeDerivedCoverM1

#print axioms RelativeFM.FreeDerivedCoverM1.exists_derived_from_single_projective
