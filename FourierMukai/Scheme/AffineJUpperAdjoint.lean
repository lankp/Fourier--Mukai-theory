/-
Formal reductions for the right adjoint of affine local cohomology.

This file deliberately takes only `jUpper` and `jStarAdj` as parameters.  It
proves the three additional fields required by `AffineRecollementInput`:
shift compatibility, triangulatedness, and invertibility of the counit.
-/
import FourierMukai.Scheme.AffineLocalCohomologySupport
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Triangulated.Adjunction

@[expose] public section

namespace RelativeFM.Recollement.JUpperM1

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

open AffineLocalCohomology

variable (A : Type u) [CommRing A] (f : A)
variable (jUpper : AffineDZ A f ⥤ AffineD A)
variable (jStarAdj : jStar A f ⊣ jUpper)

/-- The supported inclusion, local cohomology, and its right adjoint form an
adjoint triple. -/
noncomputable def adjointTriple :
    Adjunction.Triple (affineDZι A f) (jStar A f) jUpper where
  adj₁ := jShriekAdj A f
  adj₂ := jStarAdj

/-- The unit of the first adjunction is invertible exactly when the counit of
the second adjunction is. -/
lemma isIso_unit_iff_isIso_counit :
    IsIso (jShriekAdj A f).unit ↔ IsIso jStarAdj.counit :=
  (adjointTriple A f jUpper jStarAdj).isIso_unit_iff_isIso_counit

/-- Full faithfulness of the supported inclusion makes the counit of the
second adjunction invertible.  No calculation of `jUpper` is needed. -/
noncomputable instance jStarAdj_isIso_counit : IsIso jStarAdj.counit := by
  rw [← isIso_unit_iff_isIso_counit A f jUpper jStarAdj]
  infer_instance

/-- The right adjoint in this adjoint triple is fully faithful. -/
noncomputable def jUpperFullyFaithful : jUpper.FullyFaithful :=
  (adjointTriple A f jUpper jStarAdj).fullyFaithfulEquiv
    (Functor.FullyFaithful.ofFullyFaithful (affineDZι A f))

/-- A negative test for the naive candidate `jUpper = affineDZι`: if that
inclusion were right adjoint to local cohomology, every map from the kernel of
local cohomology to a supported object would be zero. -/
lemma eq_zero_to_supported_of_isZero_jStar
    (badAdj : jStar A f ⊣ affineDZι A f)
    {X : AffineD A} (hX : IsZero ((jStar A f).obj X))
    (Y : AffineDZ A f) (g : X ⟶ Y.obj) : g = 0 := by
  apply (badAdj.homEquiv X Y).symm.injective
  exact hX.eq_of_src ((badAdj.homEquiv X Y).symm g)
    ((badAdj.homEquiv X Y).symm 0)

/-- Specializing the negative test to the essential image of restriction of
scalars, whose local cohomology is already known to vanish. -/
lemma eq_zero_from_open_of_supportedInclusion_right_adjoint
    (badAdj : jStar A f ⊣ affineDZι A f)
    (Z : AffineD (Away A f)) (Y : AffineDZ A f)
    (g : (derivedRestrictionScalars A f).obj Z ⟶ Y.obj) : g = 0 := by
  apply eq_zero_to_supported_of_isZero_jStar A f badAdj
  apply IsZero.of_full_of_faithful_of_isZero (affineDZι A f)
  exact (isZero_derivedFunctor_restriction A f Z).of_iso
    ((jStarFactors A f).app ((derivedRestrictionScalars A f).obj Z))

/-- A nonzero map from the open essential image to a supported object is a
complete obstruction to taking `jUpper` to be the supported inclusion. -/
lemma isEmpty_supportedInclusionAdj_of_nonzero_open_map
    {Z : AffineD (Away A f)} {Y : AffineDZ A f}
    (g : (derivedRestrictionScalars A f).obj Z ⟶ Y.obj) (hg : g ≠ 0) :
    IsEmpty (jStar A f ⊣ affineDZι A f) :=
  ⟨fun badAdj ↦ hg
    (eq_zero_from_open_of_supportedInclusion_right_adjoint A f badAdj Z Y g)⟩

/-- Shift compatibility of any right adjoint to local cohomology. -/
noncomputable def jUpper_commShift : jUpper.CommShift ℤ :=
  jStarAdj.rightAdjointCommShift ℤ

/-- The adjunction is compatible with these shift structures. -/
noncomputable def jStarAdj_commShift :
    letI := jStarAdj.rightAdjointCommShift ℤ
    jStarAdj.CommShift ℤ :=
  jStarAdj.commShift_of_leftAdjoint ℤ

/-- Any right adjoint to local cohomology is triangulated. -/
noncomputable def jUpper_exact :
    letI := jStarAdj.rightAdjointCommShift ℤ
    letI := jStarAdj.commShift_of_leftAdjoint ℤ
    jUpper.IsTriangulated := by
  letI := jStarAdj.rightAdjointCommShift ℤ
  letI := jStarAdj.commShift_of_leftAdjoint ℤ
  exact jStarAdj.isTriangulated_rightAdjoint

/-- Bundled form of all consequences, convenient when filling a recollement
structure whose fields are typeclass instances. -/
structure Consequences where
  [commShift : jUpper.CommShift ℤ]
  [adjCommShift : jStarAdj.CommShift ℤ]
  [exact : jUpper.IsTriangulated]
  [isIsoCounit : IsIso jStarAdj.counit]

/-- Construct all four consequences together. -/
noncomputable def consequences : Consequences A f jUpper jStarAdj := by
  letI := jStarAdj.rightAdjointCommShift ℤ
  letI := jStarAdj.commShift_of_leftAdjoint ℤ
  exact
    { commShift := inferInstance
      adjCommShift := inferInstance
      exact := jStarAdj.isTriangulated_rightAdjoint
      isIsoCounit := inferInstance }

#print axioms adjointTriple
#print axioms isIso_unit_iff_isIso_counit
#print axioms jStarAdj_isIso_counit
#print axioms jUpperFullyFaithful
#print axioms eq_zero_to_supported_of_isZero_jStar
#print axioms eq_zero_from_open_of_supportedInclusion_right_adjoint
#print axioms isEmpty_supportedInclusionAdj_of_nonzero_open_map
#print axioms jUpper_commShift
#print axioms jStarAdj_commShift
#print axioms jUpper_exact
#print axioms consequences

end
end RelativeFM.Recollement.JUpperM1
