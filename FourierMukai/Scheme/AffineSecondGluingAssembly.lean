import FourierMukai.Scheme.AffineSecondGluing
import FourierMukai.Scheme.AffineIShriek
import FourierMukai.Scheme.AffineMixedZero
import FourierMukai.Scheme.AffineJUpperAdjoint

@[expose] public section

/-!
# Assembly of the affine recollement from its two remaining adjunctions

The second gluing triangle is constructed by `M4.AffineSecondGluing`.  This
module checks that, together with the mixed-zero and adjoint-triple results,
the entire affine recollement follows from two functors and their adjunctions.
-/

namespace RelativeFM.Recollement.SecondGluing.AssemblyM4

open RelativeFM RelativeFM.AffineLocalCohomology
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The irreducible residue of the affine recollement: the right adjoint of
restriction of scalars, the right adjoint of local cohomology, and their two
adjunctions. -/
structure AdjointInput (A : Type u) [CommRing A] (f : A) where
  iShriek : AffineD A ⥤ AffineD (Away A f)
  iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek
  jUpper : AffineDZ A f ⥤ AffineD A
  jStarAdj : jStar A f ⊣ jUpper

namespace AdjointInput

variable {A : Type u} [CommRing A] {f : A} (I : AdjointInput A f)

include I

/-- Assemble every field of `AffineRecollementInput`. -/
noncomputable def toAffineRecollementInput : AffineRecollementInput A f := by
  let _ : I.iShriek.CommShift ℤ := IShriek.commShiftOfILowerAdj f I.iLowerAdj
  let _ : I.iShriek.IsTriangulated := IShriek.exactOfILowerAdj f I.iLowerAdj
  exact {
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
  jStarAdj_isIso_counit := JUpperM1.jStarAdj_isIso_counit A f I.jUpper I.jStarAdj
  kernel := supported_kernel A f (jStar A f) (jStarFactors A f)
  iShriek_jUpper := MixedZero.iShriekJUpperIsoZero A f I.iShriek I.jUpper
    I.iLowerAdj I.jStarAdj
  firstConnecting := supportedFirstConnecting A f (jStar A f) (jStarFactors A f)
  first_distinguished :=
    supportedFirstTriangle_distinguished A f (jStar A f) (jStarFactors A f)
  secondConnecting := concreteAffineSecondConnecting A f I.iShriek I.iLowerAdj
    I.jUpper I.jStarAdj (JUpperM1.jUpperFullyFaithful A f I.jUpper I.jStarAdj)
    (MixedZero.iShriekJUpperIsoZero A f I.iShriek I.jUpper I.iLowerAdj I.jStarAdj)
  second_distinguished := concreteAffineSecondDistinguished A f I.iShriek I.iLowerAdj
    I.jUpper I.jStarAdj (JUpperM1.jUpperFullyFaithful A f I.jUpper I.jStarAdj)
    (MixedZero.iShriekJUpperIsoZero A f I.iShriek I.jUpper I.iLowerAdj I.jStarAdj)
  }

/-- The resulting recollement. -/
noncomputable def toRecollement : AffineRecollement A f :=
  I.toAffineRecollementInput.toRecollement

end AdjointInput

end
end RelativeFM.Recollement.SecondGluing.AssemblyM4

#print axioms RelativeFM.Recollement.SecondGluing.AssemblyM4.AdjointInput.toAffineRecollementInput
#print axioms RelativeFM.Recollement.SecondGluing.AssemblyM4.AdjointInput.toRecollement
