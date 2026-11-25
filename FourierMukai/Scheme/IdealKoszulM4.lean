import FourierMukai.Scheme.PrincipalKoszulM4

@[expose] public section

namespace RelativeFM.NeemanFiniteSupportM4

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeFM
open RelativeFM.SupportedAisleM6.Koszul

universe u

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HasDerivedCategory.standard

/-- Ideal closed support implies derived scalar annihilation by every element
of the ideal, after taking a suitable power.  This is the algebraic input to
Neeman's finite Koszul factorization; it does not construct the tensor Koszul
object itself. -/
theorem exists_pow_derivedMultiplication_comp_eq_zero_of_ideal_support
    (A : Type u) [CommRing A] (I : Ideal A) {F : AffineD A}
    (hF : AffineIsSupportedIdeal A I F) (a : A) (ha : a ∈ I)
    (α : ringObject A ⟶ F) :
    ∃ n : ℕ, 0 < n ∧ derivedMultiplication A (a ^ n) ≫ α = 0 := by
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (ringObject A) ≅
    ModuleCat.of A A := E.app (ModuleCat.of A A)
  let x := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map α (e.inv (1 : A))
  obtain ⟨n, hn⟩ := hF 0 x a ha
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  let _ : Projective (ModuleCat.of A A) :=
    ModuleCat.projective_of_free (Module.Basis.singleton (Fin 1) A)
  apply derived_from_single_eq_zero_of_homologyMap_eq_zero
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (derivedMultiplication A (a ^ (n + 1)) ≫ α) = 0
  ext y
  have hy : y = e.hom y • e.inv (1 : A) := by
    apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
    simp
  rw [hy]
  simp only [map_smul]
  have heval : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (derivedMultiplication A (a ^ (n + 1)) ≫ α) (e.inv (1 : A)) = 0 := by
    rw [h0_derivedMultiplication_comp_eval]
    change (a ^ (n + 1)) •
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map α (e.inv (1 : A)) = 0
    dsimp [x] at hn
    rw [pow_succ', mul_smul, hn, smul_zero]
  change e.hom y • (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (derivedMultiplication A (a ^ (n + 1)) ≫ α) (e.inv (1 : A)) = e.hom y • 0
  rw [heval, smul_zero]

/-- The principal theorem recovered from the ideal form. -/
theorem exists_pow_derivedMultiplication_comp_eq_zero_of_support'
    (A : Type u) [CommRing A] (f : A) {F : AffineD A}
    (hF : AffineIsSupported A f F) (α : ringObject A ⟶ F) :
    ∃ n : ℕ, 0 < n ∧ derivedMultiplication A (f ^ n) ≫ α = 0 := by
  rw [← affineIsSupportedIdeal_span_singleton] at hF
  exact exists_pow_derivedMultiplication_comp_eq_zero_of_ideal_support
    A (Ideal.span {f}) hF f (Ideal.subset_span (Set.mem_singleton f)) α

end
end RelativeFM.NeemanFiniteSupportM4

#print axioms RelativeFM.NeemanFiniteSupportM4.exists_pow_derivedMultiplication_comp_eq_zero_of_ideal_support
#print axioms RelativeFM.NeemanFiniteSupportM4.exists_pow_derivedMultiplication_comp_eq_zero_of_support'
