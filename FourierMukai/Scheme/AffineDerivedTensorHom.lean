import FourierMukai.Scheme.DerivedTensorHomClosed
import FourierMukai.Scheme.AffineJUpperTensorHom
import FourierMukai.Scheme.AffineLocalCohomologyRingObject
import FourierMukai.Scheme.AffineSecondGluingAssembly

/-!
# The affine derived tensor--Hom package and its local-cohomology consequence

`AffineDerivedClosedStacksInput` contains the derived monoidal structure (Stacks
06YU) and a chosen derived internal Hom with its adjunctions (Stacks 08J8; 0A63 in
the affine module case).  `AffineOpenRightAdjointStacksInput` is Stacks 0E55 in the
affine module model.

The 0A6R route to the local-cohomology right adjoint (`AffineCech.ComparisonInput`
and the `RecollementAssembly` built on it) was deleted in wave 6
(`results/OPEN_INPUTS.md` row 1.10): it is superseded by
`Recollement.JUpperConstruction.affineRecollementInputOfIShriek`.
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

/-- The right adjoint to derived restriction of scalars along an affine open
localization, supplied by Stacks 0E55 and transported to modules through the
affine dictionary.  The functor is a parameter, so this proposition contains
no hidden choice and no assertion of the GL26 conclusions. -/
structure AffineOpenRightAdjointStacksInput {A : Type u} [CommRing A] (f : A)
    (iShriek : AffineD A ⥤ AffineD (Away A f)) : Prop where
  /-- Stacks 0E55, in the affine module model: `Rj_*` has a right adjoint. -/
  tag_0E55 : Nonempty (derivedRestrictionScalars A f ⊣ iShriek)

end
end RelativeFM.KProjectiveTensorHom

#print axioms RelativeFM.KProjectiveTensorHom.affineDerivedTensorHomData
