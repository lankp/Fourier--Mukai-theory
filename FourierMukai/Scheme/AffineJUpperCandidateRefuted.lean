import FourierMukai.Scheme.AffineLocalCohomologySupport
import FourierMukai.Scheme.PerfectModel

/-!
# The localization-tensor candidate for `jUpper` is not fully faithful

If the proposed formula `K ↦ K ⊗^L_A A[1/f]` is to land in `AffineD A`,
it must be followed by derived restriction of scalars. Thus its derived
formula is `affineDZι ⋙ derivedExtensionScalars ⋙ derivedRestrictionScalars`.
The existing support vanishing theorem makes this functor zero. Over the
integers with `f = 2`, the supported category is nonzero (it contains `ZMod 2`
in degree zero), so this candidate is not faithful. Consequently it cannot be
the right member of any adjunction whose counit is an isomorphism.
-/

@[expose] public section

namespace RelativeFM.Recollement.TensorCandidate

open CategoryTheory CategoryTheory.Limits
open ZeroObject

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The localization-tensor candidate for the supported right adjoint, with
its output viewed again in `D(A)`. -/
noncomputable def tensorLocalizationCandidate (A : Type u) [CommRing A] (f : A) :
    AffineDZ A f ⥤ AffineD A :=
  (affineDZι A f ⋙ derivedExtensionScalars A f) ⋙ derivedRestrictionScalars A f

/-- The candidate is zero on every supported object. -/
lemma isZero_tensorLocalizationCandidate_obj (A : Type u) [CommRing A] (f : A)
    (X : AffineDZ A f) : IsZero ((tensorLocalizationCandidate A f).obj X) := by
  exact (derivedRestrictionScalars A f).map_isZero
    (isZero_derivedExtensionScalars_of_support A f X.property)

/-- The tensor-localization formula gives the zero functor on the whole
supported derived category. -/
noncomputable def tensorLocalizationCandidateIsoZero (A : Type u) [CommRing A]
    (f : A) : tensorLocalizationCandidate A f ≅ 0 :=
  NatIso.ofComponents
    (fun X ↦ IsZero.iso (isZero_tensorLocalizationCandidate_obj A f X)
      (Functor.zero_obj X))
    (fun {X _} _ ↦ (isZero_tensorLocalizationCandidate_obj A f X).eq_of_src _ _)

/-- The explicit `2`-power-torsion module used for the counterexample. -/
abbrev zmodTwoModule : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 2)

lemma zmodTwoModule_powerTorsion : PowerTorsion ℤ (2 : ℤ) zmodTwoModule := by
  rw [powerTorsion_iff]
  intro x
  refine ⟨1, ?_⟩
  change (2 : ℤ) • (x : ZMod 2) = 0
  exact CharTwo.two_zsmul x

lemma zmodTwoModule_not_isZero : ¬ IsZero zmodTwoModule := by
  intro h
  have hs := ModuleCat.subsingleton_of_isZero h
  have h10 := @Subsingleton.elim zmodTwoModule hs 1 0
  change (1 : ZMod 2) = 0 at h10
  exact one_ne_zero h10

/-- `ZMod 2` in degree zero is a nonzero supported derived object. -/
noncomputable def zmodTwoSupported : AffineDZ ℤ (2 : ℤ) :=
  ⟨(DerivedCategory.singleFunctor (ModuleCat.{0} ℤ) 0).obj zmodTwoModule,
    AffinePerfect.cohomologyWithin_single_zero (PowerTorsion ℤ (2 : ℤ)) zmodTwoModule
      zmodTwoModule_powerTorsion⟩

lemma zmodTwoSupported_not_isZero : ¬ IsZero zmodTwoSupported := by
  intro hX
  have hsingle : IsZero
      ((DerivedCategory.singleFunctor (ModuleCat.{0} ℤ) 0).obj zmodTwoModule) :=
    (affineDZι ℤ (2 : ℤ)).map_isZero hX
  have hhomology := (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) 0).map_isZero
    hsingle
  apply zmodTwoModule_not_isZero
  exact hhomology.of_iso
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app
      zmodTwoModule).symm

/-- In particular, the candidate is not faithful and hence not fully faithful. -/
lemma tensorLocalizationCandidate_not_faithful :
    ¬ (tensorLocalizationCandidate ℤ (2 : ℤ)).Faithful := by
  intro hfaithful
  letI : (tensorLocalizationCandidate ℤ (2 : ℤ)).Faithful := hfaithful
  have hzero := isZero_tensorLocalizationCandidate_obj ℤ (2 : ℤ) zmodTwoSupported
  have hid : 𝟙 zmodTwoSupported = 0 := by
    apply (tensorLocalizationCandidate ℤ (2 : ℤ)).map_injective
    exact hzero.eq_of_src _ _
  exact zmodTwoSupported_not_isZero ((IsZero.iff_id_eq_zero _).mpr hid)

/-- No left adjoint whatsoever can make this candidate fully faithful: the
counit of such an adjunction cannot be an isomorphism. -/
lemma no_adjunction_with_isIso_counit
    (F : AffineD ℤ ⥤ AffineDZ ℤ (2 : ℤ))
    (adj : F ⊣ tensorLocalizationCandidate ℤ (2 : ℤ)) : ¬ IsIso adj.counit := by
  intro hcounit
  letI : IsIso adj.counit := hcounit
  have hff : (tensorLocalizationCandidate ℤ (2 : ℤ)).FullyFaithful :=
    adj.fullyFaithfulROfIsIsoCounit
  exact tensorLocalizationCandidate_not_faithful hff.faithful

#print axioms tensorLocalizationCandidateIsoZero
#print axioms zmodTwoModule_powerTorsion
#print axioms zmodTwoSupported_not_isZero
#print axioms tensorLocalizationCandidate_not_faithful
#print axioms no_adjunction_with_isIso_counit

end

end RelativeFM.Recollement.TensorCandidate
