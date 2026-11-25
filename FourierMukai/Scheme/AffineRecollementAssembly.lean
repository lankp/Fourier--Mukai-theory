/-
Integration surface for the affine recollement, prepared by member m6.

This file does not construct either missing adjoint or the second triangle.
It fixes the fields already proved from ring data, including m3's mixed zero
composite, and derives all four right-adjoint shift/exactness fields from the
two adjunctions before assembling the remainder into the
existing `AffineRecollementInput` interface.
-/
import FourierMukai.Scheme.AffineSupportedAssembly
import FourierMukai.Scheme.AffineMixedZero
import FourierMukai.Scheme.AffineIShriek

@[expose] public section

namespace RelativeFM.Recollement.AssemblyM6

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

open RelativeFM
open RelativeFM.AffineLocalCohomology

/-- Exactly the part of `AffineRecollementInput` not supplied by
`AffineLocalCohomologySupport`, `AffineGluing`, and `MixedZero`.  The
local-cohomology functor is fixed to `AffineLocalCohomology.jStar A f`; it is
not a field here. -/
structure RemainingInput (A : Type u) [CommRing A] (f : A) where
  iShriek : AffineD A ⥤ AffineD (Away A f)
  iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek
  jUpper : AffineDZ A f ⥤ AffineD A
  jStarAdj : jStar A f ⊣ jUpper
  [jStarAdj_isIso_counit : IsIso jStarAdj.counit]
  secondConnecting :
    jStar A f ⋙ jUpper ⟶ iShriek ⋙ derivedRestrictionScalars A f ⋙
      shiftFunctor (AffineD A) (1 : ℤ)
  second_distinguished (X : AffineD A) :
    Triangle.mk (iLowerAdj.counit.app X) (jStarAdj.unit.app X)
      (secondConnecting.app X) ∈ distTriang (AffineD A)

attribute [instance] RemainingInput.jStarAdj_isIso_counit

namespace RemainingInput

variable {A : Type u} [CommRing A] {f : A} (I : RemainingInput A f)

include I

/-- Fill the existing affine recollement interface.  The local-cohomology
fields are previously proved declarations, and the mixed zero composite is
m3's formal consequence of the two adjunctions; neither is a new hypothesis. -/
noncomputable def toAffineRecollementInput : AffineRecollementInput A f where
  iShriek := I.iShriek
  iShriek_commShift := IShriek.commShiftOfILowerAdj f I.iLowerAdj
  iShriek_exact := IShriek.exactOfILowerAdj f I.iLowerAdj
  iLowerAdj := I.iLowerAdj
  jStar := jStar A f
  jStar_commShift := jStar_commShift A f
  jStar_exact := jStar_exact A f
  jShriekAdj := jShriekAdj A f
  jUpper := I.jUpper
  jUpper_commShift := I.jStarAdj.rightAdjointCommShift ℤ
  jUpper_exact := by
    let _ : I.jUpper.CommShift ℤ := I.jStarAdj.rightAdjointCommShift ℤ
    let _ : I.jStarAdj.CommShift ℤ := I.jStarAdj.commShift_of_leftAdjoint ℤ
    exact I.jStarAdj.isTriangulated_rightAdjoint
  jStarAdj := I.jStarAdj
  jStarAdj_isIso_counit := I.jStarAdj_isIso_counit
  kernel := supported_kernel A f (jStar A f) (jStarFactors A f)
  iShriek_jUpper := MixedZero.iShriekJUpperIsoZero A f I.iShriek I.jUpper
    I.iLowerAdj I.jStarAdj
  firstConnecting := supportedFirstConnecting A f (jStar A f) (jStarFactors A f)
  first_distinguished :=
    supportedFirstTriangle_distinguished A f (jStar A f) (jStarFactors A f)
  secondConnecting := I.secondConnecting
  second_distinguished := I.second_distinguished

/-- The resulting six-functor recollement. -/
noncomputable def toRecollement : AffineRecollement A f :=
  I.toAffineRecollementInput.toRecollement

@[simp] theorem toRecollement_eq :
    I.toRecollement = I.toAffineRecollementInput.toRecollement := rfl

@[simp] theorem toAffineRecollementInput_jStar :
    I.toAffineRecollementInput.jStar = jStar A f := rfl

@[simp] theorem toAffineRecollementInput_jShriekAdj :
    I.toAffineRecollementInput.jShriekAdj = jShriekAdj A f := rfl

end RemainingInput

end
end RelativeFM.Recollement.AssemblyM6

#print axioms RelativeFM.Recollement.AssemblyM6.RemainingInput.toAffineRecollementInput
#print axioms RelativeFM.Recollement.AssemblyM6.RemainingInput.toRecollement
