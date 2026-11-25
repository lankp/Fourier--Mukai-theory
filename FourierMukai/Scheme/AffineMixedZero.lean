import FourierMukai.Scheme.AffineLocalCohomologySupport

@[expose] public section

namespace RelativeFM.Recollement.MixedZero

open CategoryTheory CategoryTheory.Limits
open ZeroObject
open RelativeFM RelativeFM.AffineLocalCohomology

universe vC uC vD uD vE uE u

noncomputable section

/-- If two left adjoints have zero composite, then the corresponding right
adjoints have zero composite in the opposite order.  The proof evaluates the
two adjunction Hom-equivalences on the identity of the candidate zero object. -/
lemma isZero_rightAdjoint_comp_of_leftAdjoint_comp_isZero
    {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
    {E : Type uE} [Category.{vE} E]
    {jStar : C ⥤ E} {jUpper : E ⥤ C} (jStarAdj : jStar ⊣ jUpper)
    {iLower : D ⥤ C} {iShriek : C ⥤ D} (iLowerAdj : iLower ⊣ iShriek)
    (hzero : ∀ X : D, IsZero (jStar.obj (iLower.obj X))) (Y : E) :
    IsZero (iShriek.obj (jUpper.obj Y)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (iLowerAdj.homEquiv _ _).symm.injective
  apply (jStarAdj.homEquiv _ _).symm.injective
  exact (hzero _).eq_of_src _ _

/-- Functorial packaging of `isZero_rightAdjoint_comp_of_leftAdjoint_comp_isZero`. -/
noncomputable def rightAdjointCompIsoZero
    {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasZeroMorphisms D]
    {E : Type uE} [Category.{vE} E]
    {jStar : C ⥤ E} {jUpper : E ⥤ C} (jStarAdj : jStar ⊣ jUpper)
    {iLower : D ⥤ C} {iShriek : C ⥤ D} (iLowerAdj : iLower ⊣ iShriek)
    (hzero : ∀ X : D, IsZero (jStar.obj (iLower.obj X))) :
    jUpper ⋙ iShriek ≅ 0 :=
  NatIso.ofComponents
    (fun Y ↦ IsZero.iso
      (isZero_rightAdjoint_comp_of_leftAdjoint_comp_isZero
        jStarAdj iLowerAdj hzero Y) (Functor.zero_obj Y))
    (fun {Y _} _ ↦
      (isZero_rightAdjoint_comp_of_leftAdjoint_comp_isZero
        jStarAdj iLowerAdj hzero Y).eq_of_src _ _)

attribute [local instance] HasDerivedCategory.standard

/-- The supported local-cohomology object attached to a complex restricted from
the open localization is zero.  This descends the already proved ambient zero
statement through the fully faithful supported inclusion. -/
lemma isZero_jStar_derivedRestrictionScalars (A : Type u) [CommRing A] (f : A)
    (X : AffineD (Away A f)) :
    IsZero ((jStar A f).obj ((derivedRestrictionScalars A f).obj X)) := by
  apply IsZero.of_full_of_faithful_of_isZero (affineDZι A f)
  exact (isZero_derivedFunctor_restriction A f X).of_iso
    ((jStarFactors A f).app ((derivedRestrictionScalars A f).obj X))

/-- The supported form of the zero composite `RΓ_Z Rj_* ≅ 0`, proved directly
from the explicit cone description rather than through the kernel field. -/
noncomputable def jStarDerivedRestrictionScalarsIsoZero
    (A : Type u) [CommRing A] (f : A) :
    derivedRestrictionScalars A f ⋙ jStar A f ≅ 0 :=
  NatIso.ofComponents
    (fun X ↦ IsZero.iso (isZero_jStar_derivedRestrictionScalars A f X)
      (Functor.zero_obj X))
    (fun {X _} _ ↦ (isZero_jStar_derivedRestrictionScalars A f X).eq_of_src _ _)

/-- The mixed zero-composite field of the affine recollement.  It needs only the
two adjunctions supplied by the other fields; no formula for either right
adjoint is used. -/
noncomputable def iShriekJUpperIsoZero (A : Type u) [CommRing A] (f : A)
    (iShriek : AffineD A ⥤ AffineD (Away A f))
    (jUpper : AffineDZ A f ⥤ AffineD A)
    (iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek)
    (jStarAdj : jStar A f ⊣ jUpper) :
    jUpper ⋙ iShriek ≅ 0 :=
  rightAdjointCompIsoZero jStarAdj iLowerAdj
    (isZero_jStar_derivedRestrictionScalars A f)

#print axioms isZero_rightAdjoint_comp_of_leftAdjoint_comp_isZero
#print axioms rightAdjointCompIsoZero
#print axioms isZero_jStar_derivedRestrictionScalars
#print axioms jStarDerivedRestrictionScalarsIsoZero
#print axioms iShriekJUpperIsoZero

end
end RelativeFM.Recollement.MixedZero
