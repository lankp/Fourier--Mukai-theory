import FourierMukai.Scheme.DerivedTensorHomClosed
import FourierMukai.Scheme.AffineJUpperTensorHom
import FourierMukai.Scheme.AffineLocalCohomologyRingObject
import FourierMukai.Scheme.AffineSecondGluingAssembly

/-!
# The affine derived tensor--Hom package and its local-cohomology consequence

The tagged inputs are deliberately split.  `AffineDerivedClosedStacksInput`
contains the derived monoidal structure (Stacks 06YU) and a chosen derived
internal Hom with its adjunctions (Stacks 08J8; 0A63 in the affine module
case).  `AffineCechComparisonInput` contains only the part of Stacks 0A6R used
by `AffineJUpperTensorHom`: an isomorphism between the local-cohomology functor
and derived tensoring by the ring local-cohomology object.  The augmentation
normalization is not needed for the adjunction and is not guessed here.
-/

@[expose] public section

namespace RelativeFM.KProjectiveTensorHom

open CategoryTheory CategoryTheory.Limits
open RelativeFM RelativeFM.AffineLocalCohomology RelativeFM.TensorHom.ConcreteC

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The tagged derived closed structure on `D(A-Mod)`.  The existential
`MonoidalCategory` is the derived tensor construction of Stacks 06YU.  The
remaining package is its symmetric structure and a chosen `RHom` with all
tensor--Hom adjunctions, Stacks 08J8 (0A63 for modules over a ring). -/
structure AffineDerivedClosedStacksInput (A : Type u) [CommRing A] : Prop where
  derived_closed :
    ∃ (M : MonoidalCategory (AffineD A)),
      @MonoidalClosedAdapter.SymmetricMonoidalClosedInput (AffineD A) _ M

/-- Realize the explicitly tagged 06YU/08J8 input as the repository's complete
`DerivedTensorHomData`, including internal currying. -/
noncomputable def affineDerivedTensorHomData {A : Type u} [CommRing A]
    (I : AffineDerivedClosedStacksInput A) : DerivedTensorHomData (AffineD A) := by
  letI : MonoidalCategory (AffineD A) := I.derived_closed.choose
  exact MonoidalClosedAdapter.derivedTensorHomDataOfInput (AffineD A)
    I.derived_closed.choose_spec

namespace AffineCech

variable {A : Type u} [CommRing A] (f : A)

/-- The part of Stacks 0A6R consumed by the tensor--Hom construction of the
local-cohomology right adjoint.  It is an actual comparison isomorphism, not a
statement of the desired adjunction. -/
structure ComparisonInput (T : DerivedTensorHomData (AffineD A)) : Prop where
  /-- Stacks 0A6R: `RΓ_Z(A) ⊗^L (-)` computes the local-cohomology functor. -/
  tag_0A6R : Nonempty (derivedFunctor A f ≅
    T.tensorLeft (ringLocalCohomologyObject A f))

variable {T : DerivedTensorHomData (AffineD A)} (I : ComparisonInput f T)

/-- The comparison supplied by 0A6R. -/
noncomputable def cechIso : derivedFunctor A f ≅
    T.tensorLeft (ringLocalCohomologyObject A f) := Classical.choice I.tag_0A6R

/-- The same comparison read through the supported-category inclusion. -/
noncomputable def supportedCechIso :
    jStar A f ⋙ affineDZι A f ≅
      T.tensorLeft (ringLocalCohomologyObject A f) :=
  jStarFactors A f ≪≫ cechIso f I

/-- **The remaining local-cohomology adjunction**, conditional on the derived
closed structure and the tagged 0A6R comparison. -/
noncomputable def jStarAdj :
    jStar A f ⊣ affineDZι A f ⋙
      T.rhom.obj (Opposite.op (ringLocalCohomologyObject A f)) :=
  Recollement.JUpperM1.TensorHom.jStarAdj A f
    (T.tensorLeft (ringLocalCohomologyObject A f))
    (T.rhom.obj (Opposite.op (ringLocalCohomologyObject A f)))
    (T.tensorHomAdj (ringLocalCohomologyObject A f)) (supportedCechIso f I)

/-- Shift compatibility, exactness, the full-faithfulness statements and the
iso-counit condition for the constructed right adjoint. -/
noncomputable def jUpperConsequences :
    Recollement.JUpperM1.Consequences A f
      (Recollement.JUpperM1.TensorHom.jUpper A f
        (T.rhom.obj (Opposite.op (ringLocalCohomologyObject A f))))
      (jStarAdj f I) :=
  Recollement.JUpperM1.TensorHom.consequences A f
    (T.tensorLeft (ringLocalCohomologyObject A f))
    (T.rhom.obj (Opposite.op (ringLocalCohomologyObject A f)))
    (T.tensorHomAdj (ringLocalCohomologyObject A f)) (supportedCechIso f I)

end AffineCech

/-- The right adjoint to derived restriction of scalars along an affine open
localization, supplied by Stacks 0E55 and transported to modules through the
affine dictionary.  The functor is a parameter, so this proposition contains
no hidden choice and no assertion of the GL26 conclusions. -/
structure AffineOpenRightAdjointStacksInput {A : Type u} [CommRing A] (f : A)
    (iShriek : AffineD A ⥤ AffineD (Away A f)) : Prop where
  /-- Stacks 0E55, in the affine module model: `Rj_*` has a right adjoint. -/
  tag_0E55 : Nonempty (derivedRestrictionScalars A f ⊣ iShriek)

namespace RecollementAssembly

variable {A : Type u} [CommRing A] (f : A)

/-- Combine the 0E55 open adjoint and the 0A6R/tensor--Hom supported adjoint.
This is exactly the small residue consumed by `AffineSecondGluingAssembly`. -/
noncomputable def adjointInput (T : DerivedTensorHomData (AffineD A))
    (iShriek : AffineD A ⥤ AffineD (Away A f))
    (hOpen : AffineOpenRightAdjointStacksInput f iShriek)
    (hCech : AffineCech.ComparisonInput f T) :
    Recollement.SecondGluing.AssemblyM4.AdjointInput A f where
  iShriek := iShriek
  iLowerAdj := Classical.choice hOpen.tag_0E55
  jUpper := Recollement.JUpperM1.TensorHom.jUpper A f
    (T.rhom.obj (Opposite.op (ringLocalCohomologyObject A f)))
  jStarAdj := AffineCech.jStarAdj f hCech

/-- The full affine recollement input, with all remaining gluing fields proved
by the existing second-gluing and mixed-zero modules. -/
noncomputable def toAffineRecollementInput (T : DerivedTensorHomData (AffineD A))
    (iShriek : AffineD A ⥤ AffineD (Away A f))
    (hOpen : AffineOpenRightAdjointStacksInput f iShriek)
    (hCech : AffineCech.ComparisonInput f T) : AffineRecollementInput A f :=
  (adjointInput f T iShriek hOpen hCech).toAffineRecollementInput

/-- The full affine recollement from the three tagged geometric inputs. -/
noncomputable def toRecollement (T : DerivedTensorHomData (AffineD A))
    (iShriek : AffineD A ⥤ AffineD (Away A f))
    (hOpen : AffineOpenRightAdjointStacksInput f iShriek)
    (hCech : AffineCech.ComparisonInput f T) : AffineRecollement A f :=
  (adjointInput f T iShriek hOpen hCech).toRecollement

/-- Convenience form taking the derived closed structure directly from the
06YU/08J8 interface. -/
noncomputable def toRecollementOfStacks (hClosed : AffineDerivedClosedStacksInput A)
    (iShriek : AffineD A ⥤ AffineD (Away A f))
    (hOpen : AffineOpenRightAdjointStacksInput f iShriek)
    (hCech : AffineCech.ComparisonInput f (affineDerivedTensorHomData hClosed)) :
    AffineRecollement A f :=
  toRecollement f (affineDerivedTensorHomData hClosed) iShriek hOpen hCech

end RecollementAssembly
end
end RelativeFM.KProjectiveTensorHom

#print axioms RelativeFM.KProjectiveTensorHom.affineDerivedTensorHomData
#print axioms RelativeFM.KProjectiveTensorHom.AffineCech.supportedCechIso
#print axioms RelativeFM.KProjectiveTensorHom.AffineCech.jStarAdj
#print axioms RelativeFM.KProjectiveTensorHom.AffineCech.jUpperConsequences
#print axioms RelativeFM.KProjectiveTensorHom.RecollementAssembly.toAffineRecollementInput
#print axioms RelativeFM.KProjectiveTensorHom.RecollementAssembly.toRecollement
#print axioms RelativeFM.KProjectiveTensorHom.RecollementAssembly.toRecollementOfStacks
