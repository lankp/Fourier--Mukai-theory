import FourierMukai.Scheme.AffineLocalCohomology
import FourierMukai.Scheme.AffineQCoh
import FourierMukai.Scheme.AffineGluing
import Mathlib.CategoryTheory.Triangulated.Adjunction

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open scoped ChangeOfRings

universe u

noncomputable section

set_option maxHeartbeats 1000000

attribute [local instance] HasDerivedCategory.standard

namespace AffineLocalCohomology

lemma exists_pow_smul_of_one_tmul_eq_zero (A : Type u) [CommRing A] (f : A)
    (M : ModuleCat.{u} A) (m : M)
    (h : (1 : Away A f) ⊗ₜ[A] m = 0) :
    ∃ n : ℕ, f ^ n • m = 0 := by
  have h' : (TensorProduct.mk A (Away A f) M 1) m = 0 := by
    simpa [TensorProduct.mk] using h
  letI : IsLocalizedModule (Submonoid.powers f)
    (TensorProduct.mk A (Away A f) M 1) :=
    IsLocalization.tensorProduct_isLocalizedModule (Submonoid.powers f) (Away A f)
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
    (S := Submonoid.powers f) (f := TensorProduct.mk A (Away A f) M 1)
    (x₁ := m) (x₂ := 0) (by simpa using h')
  obtain ⟨c, n, rfl⟩ := c
  exact ⟨n, by simpa [Submonoid.smul_def] using hc⟩

lemma exists_pow_smul_of_one_tmul_eq_zero_of_module_eq
    (A : Type u) [CommRing A] (f : A) (P : Module A (Away A f))
    (hP : P = Algebra.toModule) (M : ModuleCat.{u} A) (m : M)
    (h : @TensorProduct.tmul A _ (Away A f) M _ _ P _ 1 m = 0) :
    ∃ n : ℕ, f ^ n • m = 0 := by
  subst P
  have h' : (TensorProduct.mk A (Away A f) M 1) m = 0 := by
    simpa [TensorProduct.mk] using h
  letI : IsLocalizedModule (Submonoid.powers f)
    (TensorProduct.mk A (Away A f) M 1) :=
    IsLocalization.tensorProduct_isLocalizedModule (Submonoid.powers f) (Away A f)
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
    (S := Submonoid.powers f) (f := TensorProduct.mk A (Away A f) M 1)
    (x₁ := m) (x₂ := 0) (by simpa using h')
  obtain ⟨c, n, rfl⟩ := c
  exact ⟨n, by simpa [Submonoid.smul_def] using hc⟩

lemma exists_pow_smul_of_one_tmul_eq_zero_ringHom (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{u} A) (m : M)
    (h : (1 : Away A f) ⊗ₜ[A, (algebraMap A (Away A f))] m = 0) :
    ∃ n : ℕ, f ^ n • m = 0 := by
  let P : Module A (Away A f) := Module.compHom _ (algebraMap A (Away A f))
  have hP : P = Algebra.toModule := Module.ext' P _ fun a x ↦ by
    exact IsScalarTower.algebraMap_smul (Away A f) a x
  exact exists_pow_smul_of_one_tmul_eq_zero_of_module_eq A f P hP M m h

lemma powerTorsion_of_isZero_extendScalars (A : Type u) [CommRing A] (f : A)
    (M : ModuleCat.{u} A)
    (hM : IsZero ((ModuleCat.extendScalars (algebraMap A (Away A f))).obj M)) :
    PowerTorsion A f M := by
  rw [powerTorsion_iff]
  intro m
  apply exists_pow_smul_of_one_tmul_eq_zero_ringHom A f M m
  have hm : (((1 : Away A f) ⊗ₜ[A, (algebraMap A (Away A f))] m :
      (ModuleCat.extendScalars (algebraMap A (Away A f))).obj M)) = 0 := by
    let hs := ModuleCat.subsingleton_of_isZero hM
    dsimp [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] at hs
    exact @Subsingleton.elim _ hs _ _
  with_unfolding_all exact hm

lemma powerTorsion_homology_derivedFunctor (A : Type u) [CommRing A] (f : A)
    (X : AffineD A) (n : ℤ) : PowerTorsion A f
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((derivedFunctor A f).obj X)) := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))
  apply powerTorsion_of_isZero_extendScalars A f
  have hzero : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Away A f)) n).obj
        ((derivedExtensionScalars A f).obj ((derivedFunctor A f).obj X))) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (Away A f)) n).map_isZero
      (isZero_derivedExtensionScalars_derivedFunctor A f X)
  exact hzero.of_iso (mapDerivedCategoryHomologyIso F ((derivedFunctor A f).obj X) n).symm

lemma derivedFunctor_isSupported (A : Type u) [CommRing A] (f : A) (X : AffineD A) :
    AffineIsSupported A f ((derivedFunctor A f).obj X) := by
  intro n
  exact powerTorsion_homology_derivedFunctor A f X n

/-- Local cohomology as a functor into the supported full subcategory. -/
noncomputable def jStar (A : Type u) [CommRing A] (f : A) : AffineD A ⥤ AffineDZ A f :=
  supportedFunctorOf A f (derivedFunctor_isSupported A f)

/-- The inclusion of the supported category identifies `jStar` with the explicit
local-cohomology functor. -/
noncomputable def jStarFactors (A : Type u) [CommRing A] (f : A) :
    jStar A f ⋙ affineDZι A f ≅ derivedFunctor A f :=
  supportedFunctorOfFactors A f (derivedFunctor_isSupported A f)

/-- The supported inclusion is left adjoint to local cohomology. -/
noncomputable def jShriekAdj (A : Type u) [CommRing A] (f : A) :
    affineDZι A f ⊣ jStar A f :=
  supportedLocalCohomologyAdjunction A f (jStar A f) (jStarFactors A f)

/-- Shift compatibility of local cohomology, inherited from the supported
inclusion through the adjunction. -/
noncomputable instance jStar_commShift (A : Type u) [CommRing A] (f : A) :
    (jStar A f).CommShift ℤ :=
  (jShriekAdj A f).rightAdjointCommShift ℤ

/-- The adjunction is compatible with these shift structures. -/
noncomputable instance jShriekAdj_commShift (A : Type u) [CommRing A] (f : A) :
    (jShriekAdj A f).CommShift ℤ :=
  (jShriekAdj A f).commShift_of_leftAdjoint ℤ

/-- Triangulatedness of local cohomology, inherited from the triangulated
supported inclusion. -/
noncomputable instance jStar_exact (A : Type u) [CommRing A] (f : A) :
    (jStar A f).IsTriangulated :=
  (jShriekAdj A f).isTriangulated_rightAdjoint

/-- Shift compatibility of the ambient local-cohomology functor. -/
noncomputable instance derivedFunctor_commShift (A : Type u) [CommRing A] (f : A) :
    (derivedFunctor A f).CommShift ℤ :=
  Functor.CommShift.ofIso (jStarFactors A f) ℤ

/-- The comparison between `jStar` and `derivedFunctor` is shift compatible. -/
noncomputable instance jStarFactors_commShift (A : Type u) [CommRing A] (f : A) :
    NatTrans.CommShift (jStarFactors A f).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (jStarFactors A f) ℤ

/-- Triangulatedness of the ambient local-cohomology functor. -/
noncomputable instance derivedFunctor_exact (A : Type u) [CommRing A] (f : A) :
    (derivedFunctor A f).IsTriangulated :=
  Functor.isTriangulated_of_iso (jStarFactors A f)

#print axioms exists_pow_smul_of_one_tmul_eq_zero
#print axioms exists_pow_smul_of_one_tmul_eq_zero_ringHom
#print axioms powerTorsion_of_isZero_extendScalars
#print axioms powerTorsion_homology_derivedFunctor
#print axioms derivedFunctor_isSupported
#print axioms jStar
#print axioms jStarFactors
#print axioms jShriekAdj
#print axioms jStar_commShift
#print axioms jShriekAdj_commShift
#print axioms jStar_exact
#print axioms derivedFunctor_commShift
#print axioms jStarFactors_commShift
#print axioms derivedFunctor_exact

end AffineLocalCohomology
end
end RelativeFM
