import FourierMukai.Scheme.PrincipalChainM4
import FourierMukai.Scheme.DerivedCoproducts
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

@[expose] public section

namespace RelativeFM.NeemanFiniteSupportM4

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open CochainComplex.HomComplex
open RelativeFM

universe w v u

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- In the derived category, a map from a single projective complex is zero if
it induces zero on degree-zero homology. -/
lemma derived_from_single_eq_zero_of_homologyMap_eq_zero
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {P : C} [Projective P] (F : DerivedCategory C)
    (φ : (DerivedCategory.singleFunctor C 0).obj P ⟶ F)
    (hH : (DerivedCategory.homologyFunctor C 0).map φ = 0) : φ = 0 := by
  let _ (n : ℤ) : Projective (((CochainComplex.singleFunctor C 0).obj P).X n) := by
    change Projective (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj P).X n)
    infer_instance
  let _ : ((CochainComplex.singleFunctor C 0).obj P).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ 0
  let K := DerivedCategory.Q.objPreimage F
  let e : DerivedCategory.Q.obj K ≅ F := DerivedCategory.Q.objObjPreimageIso F
  let x := (DerivedCoproducts.derivedHomKProjectiveEquiv
    ((CochainComplex.singleFunctor C 0).obj P) K).symm (φ ≫ e.inv)
  obtain ⟨h, hh⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective x
  have hQ : DerivedCategory.Q.map h = φ ≫ e.inv := by
    let E := DerivedCoproducts.derivedHomKProjectiveEquiv
      ((CochainComplex.singleFunctor C 0).obj P) K
    have hx := E.apply_symm_apply (φ ≫ e.inv)
    change E x = φ ≫ e.inv at hx
    rw [← hh] at hx
    rw [DerivedCoproducts.derivedHomKProjectiveEquiv_apply,
      DerivedCoproducts.derivedHomMap_quotient_map] at hx
    exact hx
  have hQH : (DerivedCategory.homologyFunctor C 0).map
      (DerivedCategory.Q.map h) = 0 := by
    rw [hQ, Functor.map_comp, hH, Limits.zero_comp]
  have hchain : HomologicalComplex.homologyMap h 0 = 0 := by
    let eF := (DerivedCategory.homologyFunctorFactors C 0).hom.app
      ((CochainComplex.singleFunctor C 0).obj P)
    rw [← cancel_epi eF]
    have hn := (DerivedCategory.homologyFunctorFactors C 0).hom.naturality h
    dsimp [eF] at hn ⊢
    calc
      (DerivedCategory.homologyFunctorFactors C 0).hom.app
          ((CochainComplex.singleFunctor C 0).obj P) ≫ HomologicalComplex.homologyMap h 0 =
          (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map h) ≫
            (DerivedCategory.homologyFunctorFactors C 0).hom.app K := hn.symm
      _ = 0 := by rw [hQH, Limits.zero_comp]
      _ = (DerivedCategory.homologyFunctorFactors C 0).hom.app
          ((CochainComplex.singleFunctor C 0).obj P) ≫ 0 := (Limits.comp_zero).symm
  have hquot := quotient_map_from_single_eq_zero_of_homologyMap_eq_zero K h hchain
  have hzero : DerivedCategory.Q.map h = 0 := by
    rw [← DerivedCoproducts.derivedHomMap_quotient_map h, hquot]
    simp only [DerivedCoproducts.derivedHomMap, Functor.map_zero,
      Limits.zero_comp, Limits.comp_zero]
  rw [← cancel_mono e.inv]
  simp only [← hQ, hzero, Limits.zero_comp]

end
end RelativeFM.NeemanFiniteSupportM4

#print axioms RelativeFM.NeemanFiniteSupportM4.derived_from_single_eq_zero_of_homologyMap_eq_zero
