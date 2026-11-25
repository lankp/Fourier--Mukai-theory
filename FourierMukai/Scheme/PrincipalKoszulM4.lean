import FourierMukai.Scheme.DerivedSingleM4
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.Basis.Basic

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

/-- Evaluate derived multiplication on the canonical generator of the degree-zero
homology of the regular module. -/
lemma h0_derivedMultiplication_eval (A : Type u) [CommRing A] (a : A) :
    let E := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0
    let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (ringObject A) ≅
    ModuleCat.of A A := E.app (ModuleCat.of A A)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (derivedMultiplication A a) (e.inv (1 : A)) = e.inv a := by
  dsimp only
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (ringObject A) ≅
    ModuleCat.of A A := E.app (ModuleCat.of A A)
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  change e.hom ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
      (regularMultiplication A a)) (e.inv (1 : A))) = e.hom (e.inv a)
  have hn := congrArg (fun q => q (e.inv (1 : A)))
    (E.hom.naturality (regularMultiplication A a))
  change e.hom ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
      (regularMultiplication A a)) (e.inv (1 : A))) =
        regularMultiplication A a (e.hom (e.inv (1 : A))) at hn
  simpa [regularMultiplication] using hn

/-- Derived multiplication acts by the expected scalar on the represented
degree-zero cohomology class. -/
lemma h0_derivedMultiplication_comp_eval (A : Type u) [CommRing A] (a : A)
    {F : AffineD A} (α : ringObject A ⟶ F) :
    let E := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0
    let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (ringObject A) ≅
    ModuleCat.of A A := E.app (ModuleCat.of A A)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (derivedMultiplication A a ≫ α) (e.inv (1 : A)) =
        a • (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map α (e.inv (1 : A)) := by
  dsimp only
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (ringObject A) ≅
    ModuleCat.of A A := E.app (ModuleCat.of A A)
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (derivedMultiplication A a ≫ α) (e.inv (1 : A)) =
      a • (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map α (e.inv (1 : A))
  have he : e.inv a = a • e.inv (1 : A) := by
    change e.inv.hom a = a • e.inv.hom (1 : A)
    simpa only [smul_eq_mul, mul_one] using (map_smul e.inv.hom a 1)
  calc
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (derivedMultiplication A a ≫ α) (e.inv (1 : A)) =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map α
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            (derivedMultiplication A a) (e.inv (1 : A))) := by
      simp only [Functor.map_comp, ConcreteCategory.comp_apply]
    _ = (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map α (e.inv a) :=
      congrArg (fun z => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map α z)
        (h0_derivedMultiplication_eval A a)
    _ = (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map α
        (a • e.inv (1 : A)) := congrArg _ he
    _ = a • (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map α
        (e.inv (1 : A)) := map_smul _ _ _

/-- Principal support implies derived scalar annihilation of every map from
the regular module, after replacing the power by its successor. -/
lemma exists_pow_derivedMultiplication_comp_eq_zero_of_support
    (A : Type u) [CommRing A] (f : A) {F : AffineD A}
    (hF : AffineIsSupported A f F) (α : ringObject A ⟶ F) :
    ∃ n : ℕ, 0 < n ∧ derivedMultiplication A (f ^ n) ≫ α = 0 := by
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (ringObject A) ≅
    ModuleCat.of A A := E.app (ModuleCat.of A A)
  let x := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map α (e.inv (1 : A))
  obtain ⟨n, hn⟩ := powerTorsion_iff.mp (hF 0) x
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  let _ : Projective (ModuleCat.of A A) :=
    ModuleCat.projective_of_free (Module.Basis.singleton (Fin 1) A)
  apply derived_from_single_eq_zero_of_homologyMap_eq_zero
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (derivedMultiplication A (f ^ (n + 1)) ≫ α) = 0
  ext y
  have hy : y = e.hom y • e.inv (1 : A) := by
    apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
    simp
  rw [hy]
  simp only [map_smul]
  have heval : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (derivedMultiplication A (f ^ (n + 1)) ≫ α) (e.inv (1 : A)) = 0 := by
    rw [h0_derivedMultiplication_comp_eval]
    change (f ^ (n + 1)) •
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map α (e.inv (1 : A)) = 0
    dsimp [x] at hn
    rw [pow_succ', mul_smul, hn, smul_zero]
  change e.hom y • (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (derivedMultiplication A (f ^ (n + 1)) ≫ α) (e.inv (1 : A)) = e.hom y • 0
  rw [heval, smul_zero]

/-- Neeman's principal Koszul factorization.  Every map from `A[0]` to a
complex with `f`-power-torsion cohomology factors through the cone of `f^n`
for some positive `n`. -/
theorem exists_principal_koszul_factorization
    (A : Type u) [CommRing A] (f : A) {F : AffineD A}
    (hF : AffineIsSupported A f F) (α : ringObject A ⟶ F) :
    ∃ (n : ℕ) (_ : 0 < n) (β : (coneData A (f ^ n)).obj ⟶ F),
      (coneData A (f ^ n)).second ≫ β = α := by
  obtain ⟨n, hn, hα⟩ := exists_pow_derivedMultiplication_comp_eq_zero_of_support A f hF α
  obtain ⟨β, hβ⟩ := exists_factor_through_triangle_obj₃
    (Triangle.mk (derivedMultiplication A (f ^ n))
      (coneData A (f ^ n)).second (coneData A (f ^ n)).third)
    (coneData A (f ^ n)).distinguished α hα
  exact ⟨n, hn, β, hβ⟩

end
end RelativeFM.NeemanFiniteSupportM4

#print axioms RelativeFM.NeemanFiniteSupportM4.h0_derivedMultiplication_eval
#print axioms RelativeFM.NeemanFiniteSupportM4.h0_derivedMultiplication_comp_eval
#print axioms RelativeFM.NeemanFiniteSupportM4.exists_pow_derivedMultiplication_comp_eq_zero_of_support
#print axioms RelativeFM.NeemanFiniteSupportM4.exists_principal_koszul_factorization
