import FourierMukai.Scheme.ClosedSupportNeeman
import FourierMukai.Scheme.PerfectCompactThick

/-!
# Additions to the affine supported Neeman base

No Stacks input is used in this module.  We discharge the Koszul-power
thick-generation residue in `ClosedSupportNeeman`, hence principal supported
zero detection.  We also prove that compactness descends along a full,
faithful, additive inclusion which preserves coproducts.  Since the principal
supported inclusion is a left adjoint, this identifies its compact Koszul
object from compactness of the ambient perfect object.
-/

@[expose] public section

namespace RelativeFM.AffineSupportedBaseM1

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open RelativeFM.SupportedAisleM6.Koszul

universe v u uC uD

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Multiplication of scalars is functional as a derived endomorphism of the
regular module. -/
lemma derivedMultiplication_comp (A : Type u) [CommRing A] (a b : A) :
    derivedMultiplication A a ≫ derivedMultiplication A b =
      derivedMultiplication A (a * b) := by
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  change F.map (regularMultiplication A a) ≫ F.map (regularMultiplication A b) =
    F.map (regularMultiplication A (a * b))
  rw [← F.map_comp]
  congr 1
  ext x
  simp [regularMultiplication, mul_comm]

/-- The octahedron on `a^n`, `a`, and their composite exhibits the Koszul
cone of `a^(n+1)` as an extension of the cones of `a^n` and `a`. -/
theorem coneData_pow_mem_triangEnvelope (A : Type u) [CommRing A] (a : A)
    (n : ℕ) (hn : 0 < n) :
    (ObjectProperty.singleton (coneData A a).obj).triangEnvelope
      (coneData A (a ^ n)).obj := by
  let P := (ObjectProperty.singleton (coneData A a).obj).triangEnvelope
  have hbase : P (coneData A a).obj := by
    apply ObjectProperty.le_triangEnvelope
    exact ObjectProperty.ofObj_apply _ Unit.unit
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : n = 0
      · subst n
        change P (coneData A (a ^ 1)).obj
        rw [pow_one]
        exact hbase
      · have hprev : P (coneData A (a ^ n)).obj := ih (Nat.pos_of_ne_zero h)
        have hcomm : derivedMultiplication A (a ^ n) ≫ derivedMultiplication A a =
            derivedMultiplication A (a ^ (n + 1)) := by
          rw [derivedMultiplication_comp, pow_succ]
        let o := Triangulated.someOctahedron hcomm
          (coneData A (a ^ n)).distinguished
          (coneData A a).distinguished
          (coneData A (a ^ (n + 1))).distinguished
        exact P.ext_of_isTriangulatedClosed₂ o.triangle o.mem hprev hbase

/-- Every positive-power principal Koszul cone lies in the thick envelope of
the Koszul cone of the original element. -/
theorem koszulPower_thick (A : Type u) [CommRing A] (a : A) :
    ∀ n : ℕ, 0 < n →
      (ObjectProperty.singleton (supportedGenerator A a).obj).triangEnvelope
        (coneData A (a ^ n)).obj := by
  intro n hn
  exact coneData_pow_mem_triangEnvelope A a n hn

/-- The principal Koszul object detects zero, with no further input.  This
removes the separate `hpowers` argument from
`supportedGenerator_isPaperGenerator_of_koszulPower_thick`. -/
theorem supportedGenerator_isPaperGenerator (A : Type u) [CommRing A] (a : A) :
    IsPaperGenerator (supportedGenerator A a) :=
  ClosedSupportNeemanM4.supportedGenerator_isPaperGenerator_of_koszulPower_thick
    A a (koszulPower_thick A a)

section CompactDescent

variable {C : Type uC} [Category.{v} C] [Preadditive C]
  {D : Type uD} [Category.{v} D] [Preadditive D]

/-- The additive Hom-groups of a fully faithful additive functor are naturally
isomorphic to the ambient Hom-groups. -/
noncomputable def fullyFaithfulCoyonedaIso (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.Additive] (X : C) :
    preadditiveCoyoneda.obj (.op X) ≅
      F ⋙ preadditiveCoyoneda.obj (.op (F.obj X)) := by
  let hF := Functor.FullyFaithful.ofFullyFaithful F
  exact NatIso.ofComponents
    (fun Y =>
      let e : (X ⟶ Y) ≃+ (F.obj X ⟶ F.obj Y) :=
        { toEquiv := hF.homEquiv
          map_add' := fun f g => F.map_add }
      e.toAddCommGrpIso)
    (fun f => by
      ext g
      change F.map (g ≫ f) = F.map g ≫ F.map f
      exact F.map_comp g f)

/-- Compactness descends along a fully faithful additive functor preserving
coproducts.  This is the supported-subcategory argument: supported coproducts
are computed ambiently, so ambient compactness may be tested there. -/
theorem isCompactAb_of_fullyFaithful (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.Additive] (X : C) (hX : IsCompactAb (F.obj X))
    (hF : ∀ J : Type v, PreservesColimitsOfShape (Discrete J) F) :
    IsCompactAb X := by
  constructor
  intro J
  letI : PreservesColimitsOfShape (Discrete J) F := hF J
  letI : PreservesColimitsOfShape (Discrete J)
      (preadditiveCoyoneda.obj (.op (F.obj X))) := hX.preserves J
  exact preservesColimitsOfShape_of_natIso (fullyFaithfulCoyonedaIso F X).symm

end CompactDescent

/-- The principal supported Koszul cone is compact as soon as the ambient
regular module is compact.  Perfectness gives ambient compactness, and the
principal supported inclusion preserves all colimits because it is a left
adjoint. -/
theorem supportedGenerator_isCompactAb (A : Type u) [CommRing A] (a : A)
    (hAc : IsCompactAb (ringObject A)) :
    IsCompactAb (supportedGenerator A a) := by
  apply isCompactAb_of_fullyFaithful (affineDZι A a) (supportedGenerator A a)
  · exact RelativeFM.isCompactAb_of_perf A hAc (supportedGenerator_obj_perf A a)
  · intro J
    exact SupportedAisleM6.affineDZι_preservesColimitsOfShape A a (Discrete J)

/-- Principal supported paper weak approximation now needs only ambient
regular-module compactness and the supported `H⁰` cover: supported
compactness and zero detection are proved above. -/
noncomputable def koszulSupportedPaperDataOfH0Cover'
    (A : Type u) [CommRing A] (a : A)
    (hAc : IsCompactAb (ringObject A))
    (hcover : ClosedSupportNeemanM4.PrincipalSupportedH0Cover A a
      (supportedGenerator A a) 2) :
    PaperM2.PaperWeakApproximationData (AffineDZ A a) :=
  ClosedSupportNeemanM4.koszulSupportedPaperDataOfH0Cover A a
    (supportedGenerator_isCompactAb A a hAc)
    (supportedGenerator_isPaperGenerator A a) hcover

/-- Existence form of the sharpened principal supported reduction. -/
theorem koszulSupported_satisfiesPaperWA_of_h0Cover'
    (A : Type u) [CommRing A] (a : A)
    (hAc : IsCompactAb (ringObject A))
    (hcover : ClosedSupportNeemanM4.PrincipalSupportedH0Cover A a
      (supportedGenerator A a) 2) :
    PaperM2.SatisfiesPaperWA (AffineDZ A a) :=
  ⟨koszulSupportedPaperDataOfH0Cover' A a hAc hcover⟩

end

end RelativeFM.AffineSupportedBaseM1

#print axioms RelativeFM.AffineSupportedBaseM1.derivedMultiplication_comp
#print axioms RelativeFM.AffineSupportedBaseM1.coneData_pow_mem_triangEnvelope
#print axioms RelativeFM.AffineSupportedBaseM1.supportedGenerator_isPaperGenerator
#print axioms RelativeFM.AffineSupportedBaseM1.isCompactAb_of_fullyFaithful
#print axioms RelativeFM.AffineSupportedBaseM1.supportedGenerator_isCompactAb
#print axioms RelativeFM.AffineSupportedBaseM1.koszulSupported_satisfiesPaperWA_of_h0Cover'
