import FourierMukai.Scheme.AffineSupportedBaseM1
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Power torsion of maps out of perfect objects
-/

@[expose] public section

namespace RelativeFM.PerfectPowerTorsionM1

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open RelativeFM.SupportedAisleM6.Koszul

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Derived scalar multiplication is scalar multiplication in the `A`-linear
derived category. -/
lemma derivedMultiplication_eq_smul (A : Type u) [CommRing A] (a : A) :
    derivedMultiplication A a = a • 𝟙 (ringObject A) := by
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  change F.map (regularMultiplication A a) = a • 𝟙 (F.obj (ModuleCat.of A A))
  have hr : regularMultiplication A a = a • 𝟙 (ModuleCat.of A A) :=
    ModuleCat.lsmul_eq_smul_id (ModuleCat.of A A) a
  rw [hr, F.map_smul, F.map_id]

/-- Objects `X` for which every map to an `a`-supported complex becomes zero
after multiplication by a suitable positive power of `a`. -/
def SourcePowerTorsion (A : Type u) [CommRing A] (a : A) :
    ObjectProperty (AffineD A) :=
  fun X => ∀ F : AffineD A, AffineIsSupported A a F → ∀ β : X ⟶ F,
    ∃ n : ℕ, 0 < n ∧ (a ^ n • 𝟙 X) ≫ β = 0

lemma ringObject_sourcePowerTorsion (A : Type u) [CommRing A] (a : A) :
    SourcePowerTorsion A a (ringObject A) := by
  intro F hF β
  obtain ⟨n, hn, hβ⟩ :=
    NeemanFiniteSupportM4.exists_pow_derivedMultiplication_comp_eq_zero_of_support A a hF β
  exact ⟨n, hn, by rwa [← derivedMultiplication_eq_smul]⟩

instance sourcePowerTorsion_containsZero (A : Type u) [CommRing A] (a : A) :
    (SourcePowerTorsion A a).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    intro F hF β
    exact ⟨1, Nat.one_pos, (isZero_zero _).eq_of_src _ _⟩⟩

instance sourcePowerTorsion_isClosedUnderIsomorphisms
    (A : Type u) [CommRing A] (a : A) :
    (SourcePowerTorsion A a).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    intro F hF β
    obtain ⟨n, hn, hz⟩ := hX F hF (e.hom ≫ β)
    refine ⟨n, hn, ?_⟩
    rw [← cancel_epi e.hom]
    simpa only [Linear.smul_comp, Linear.comp_smul, Category.assoc,
      Category.id_comp, Category.comp_id, Limits.comp_zero] using hz

instance sourcePowerTorsion_isStableUnderShiftBy
    (A : Type u) [CommRing A] (a : A) (s : ℤ) :
    (SourcePowerTorsion A a).IsStableUnderShiftBy s where
  le_shift X hX := by
    intro F hF β
    let β' : X ⟶ F⟦-s⟧ :=
      (shiftShiftNeg X s).inv ≫ (shiftFunctor (AffineD A) (-s)).map β
    have hF' : AffineIsSupported A a (F⟦-s⟧) :=
      (AffineIsSupported A a).le_shift (-s) F hF
    obtain ⟨n, hn, hz⟩ := hX (F⟦-s⟧) hF' β'
    refine ⟨n, hn, ?_⟩
    apply (shiftFunctor (AffineD A) (-s)).map_injective
    rw [Functor.map_zero]
    rw [← cancel_epi (shiftShiftNeg X s).inv]
    simpa only [β', Linear.smul_comp, Linear.comp_smul, Functor.map_comp,
      Functor.map_smul, Functor.map_id, Category.assoc, Category.id_comp,
      Category.comp_id, Functor.map_zero, Limits.comp_zero] using hz

instance sourcePowerTorsion_isTriangulatedClosed₂
    (A : Type u) [CommRing A] (a : A) :
    (SourcePowerTorsion A a).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ => by
    intro F hF β
    obtain ⟨n₁, hn₁, hz₁⟩ := h₁ F hF (T.mor₁ ≫ β)
    have hz₁' : T.mor₁ ≫ ((a ^ n₁ • 𝟙 T.obj₂) ≫ β) = 0 := by
      simpa only [Linear.smul_comp, Linear.comp_smul, Category.assoc,
        Category.id_comp, Category.comp_id] using hz₁
    obtain ⟨γ, hγ⟩ := NeemanFiniteSupportM4.exists_factor_through_triangle_obj₃
      T hT ((a ^ n₁ • 𝟙 T.obj₂) ≫ β) hz₁'
    obtain ⟨n₃, hn₃, hz₃⟩ := h₃ F hF γ
    refine ⟨n₁ + n₃, Nat.add_pos_left hn₁ _, ?_⟩
    calc
      (a ^ (n₁ + n₃) • 𝟙 T.obj₂) ≫ β =
          (a ^ n₃ • 𝟙 T.obj₂) ≫ ((a ^ n₁ • 𝟙 T.obj₂) ≫ β) := by
        simp [pow_add, mul_smul, Linear.smul_comp, Linear.comp_smul,
          mul_comm, Category.assoc]
      _ = (a ^ n₃ • 𝟙 T.obj₂) ≫ T.mor₂ ≫ γ := by rw [hγ]
      _ = T.mor₂ ≫ ((a ^ n₃ • 𝟙 T.obj₃) ≫ γ) := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc,
          Category.id_comp, Category.comp_id]
      _ = 0 := by rw [hz₃, Limits.comp_zero])

instance sourcePowerTorsion_isStableUnderRetracts
    (A : Type u) [CommRing A] (a : A) :
    (SourcePowerTorsion A a).IsStableUnderRetracts where
  of_retract r hY := by
    intro F hF β
    obtain ⟨n, hn, hz⟩ := hY F hF (r.r ≫ β)
    refine ⟨n, hn, ?_⟩
    rw [← cancel_epi r.r]
    simpa only [Linear.smul_comp, Linear.comp_smul, Category.assoc,
      Category.id_comp, Category.comp_id, Limits.comp_zero] using hz

instance sourcePowerTorsion_isTriangulated (A : Type u) [CommRing A] (a : A) :
    (SourcePowerTorsion A a).IsTriangulated where

/-- Every perfect source is power-torsion over every supported target. -/
theorem perf_sourcePowerTorsion (A : Type u) [CommRing A] (a : A)
    {X : AffineD A} (hX : Perf A X) : SourcePowerTorsion A a X := by
  apply (ObjectProperty.triangEnvelope_le_iff
    (ObjectProperty.singleton (ringObject A))).mpr ?_ X hX
  intro Y hY
  obtain rfl : ringObject A = Y := (ObjectProperty.singleton_iff _ _).mp hY
  exact ringObject_sourcePowerTorsion A a

end

end RelativeFM.PerfectPowerTorsionM1

#print axioms RelativeFM.PerfectPowerTorsionM1.derivedMultiplication_eq_smul
#print axioms RelativeFM.PerfectPowerTorsionM1.sourcePowerTorsion_isStableUnderShiftBy
#print axioms RelativeFM.PerfectPowerTorsionM1.sourcePowerTorsion_isTriangulatedClosed₂
#print axioms RelativeFM.PerfectPowerTorsionM1.perf_sourcePowerTorsion
