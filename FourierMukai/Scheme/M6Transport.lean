/-
Triangulated transport between the standard and small-Hom affine models.

The comparison is the localized functor of the identity localizer morphism.
This supplies the shift compatibility and exactness proofs needed for
thick-envelope transport.  Compactness itself quantifies over different index
universes on the two sides, so lifting compactness remains an explicit input
in the two final dependency lemmas.
-/
import FourierMukai.Scheme.AffineCompactness
import FourierMukai.Scheme.Affine066S

@[expose] public section

namespace RelativeFM.CapstoneM6

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u uZ uU

noncomputable section

private noncomputable abbrev quasiIsoH (A : Type u) [CommRing A] :=
  HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)

private noncomputable abbrev QhStandard (A : Type u) [CommRing A] :
    HomotopyCategory (ModuleCat.{u} A) (.up ℤ) ⥤ AffineD A :=
  @DerivedCategory.Qh (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _)

private noncomputable abbrev QhSmall (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    HomotopyCategory (ModuleCat.{u} A) (.up ℤ) ⥤ SmallAffineD A H :=
  @DerivedCategory.Qh (ModuleCat.{u} A) _ _
    (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)

private noncomputable abbrev idLocalizer (A : Type u) [CommRing A] :=
  LocalizerMorphism.id (quasiIsoH A)

/-- Shift additivity for the explicit small-Hom model, proved without a
competing standard derived-category instance. -/
noncomputable def smallAffineShiftAdditive (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    ∀ n : ℤ, (shiftFunctor (SmallAffineD A H) n).Additive := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  infer_instance

/-- The standard-to-small comparison as a localized functor. -/
noncomputable abbrev affineQhComparisonFunctor (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) : AffineD A ⥤ SmallAffineD A H := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact (idLocalizer A).localizedFunctor (QhStandard A) (QhSmall A H)

/-- The standard-to-small comparison as an equivalence. -/
noncomputable abbrev affineQhComparison (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) : AffineD A ≌ SmallAffineD A H :=
  (affineQhComparisonFunctor A H).asEquivalence

/-- Shift compatibility of the localized comparison functor. -/
@[instance_reducible] noncomputable def affineQhComparison_commShift
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (affineQhComparisonFunctor A H).CommShift ℤ := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  letI : (idLocalizer A).functor.CommShift ℤ := by
    change (𝟭 (HomotopyCategory (ModuleCat.{u} A) (.up ℤ))).CommShift ℤ
    infer_instance
  infer_instance

attribute [local instance] affineQhComparison_commShift

/-- The natural square exhibiting the comparison as a lift of small `Qh`. -/
noncomputable def affineQhComparisonFactors (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    (idLocalizer A).functor ⋙ QhSmall A H ≅
      QhStandard A ⋙ affineQhComparisonFunctor A H := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact CatCommSq.iso (idLocalizer A).functor (QhStandard A) (QhSmall A H)
    (affineQhComparisonFunctor A H)

/-- The comparison functor is triangulated. -/
@[instance_reducible] noncomputable def affineQhComparison_isTriangulated
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (affineQhComparisonFunctor A H).IsTriangulated := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _
  letI := smallAffineShiftAdditive A H
  letI : (idLocalizer A).functor.CommShift ℤ := by
    change (𝟭 (HomotopyCategory (ModuleCat.{u} A) (.up ℤ))).CommShift ℤ
    infer_instance
  let e := affineQhComparisonFactors A H
  letI : NatTrans.CommShift e.hom ℤ :=
    LocalizerMorphism.natTransCommShift_hom _ _ _ _ e
  letI : NatTrans.CommShift e.symm.hom ℤ := inferInstance
  letI : ((idLocalizer A).functor ⋙ QhSmall A H).CommShift ℤ :=
    Functor.CommShift.comp _ _
  letI : (idLocalizer A).functor.IsTriangulated := by
    change (𝟭 (HomotopyCategory (ModuleCat.{u} A) (.up ℤ))).IsTriangulated
    infer_instance
  letI : (QhSmall A H).IsTriangulated := by infer_instance
  letI : ((idLocalizer A).functor ⋙ QhSmall A H).IsTriangulated := by
    infer_instance
  exact Functor.isTriangulated_of_precomp_iso
    (F := QhStandard A) (G := affineQhComparisonFunctor A H)
    (H := (idLocalizer A).functor ⋙ QhSmall A H) e.symm

attribute [local instance] affineQhComparison_isTriangulated

/-- The comparison identifies the two regular-module objects. -/
noncomputable def affineQhComparison_ringObjectIso (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    (affineQhComparison A H).functor.obj (ringObject A) ≅ smallRingObject A H := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact (affineQhComparisonFactors A H).symm.app
    (((HomotopyCategory.singleFunctors (ModuleCat.{u} A)).functor 0).obj
      (ModuleCat.of A A))

/-- Perfect thick envelopes transport to the small-Hom model. -/
theorem smallPerf_affineQhComparison_iff (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (X : AffineD A) :
    SmallPerf A H ((affineQhComparison A H).functor.obj X) ↔ Perf A X := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _
  letI := smallAffineShiftAdditive A H
  letI : (affineQhComparison A H).functor.CommShift ℤ :=
    affineQhComparison_commShift A H
  letI : (affineQhComparison A H).functor.IsTriangulated :=
    affineQhComparison_isTriangulated A H
  change (ObjectProperty.singleton (smallRingObject A H)).triangEnvelope
    ((affineQhComparison A H).functor.obj X) ↔
      (ObjectProperty.singleton (ringObject A)).triangEnvelope X
  rw [← AffinePerfect.triangEnvelope_singleton_eq_of_iso
    (affineQhComparison_ringObjectIso A H)]
  exact AffinePerfect.mem_triangEnvelope_singleton_map_iff
    (affineQhComparison A H).functor (ringObject A) X

/-- Objectwise perfectness on either side of the comparison. -/
theorem smallPerf_iff_perf_affineQhComparison_inverse (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (X : SmallAffineD A H) :
    SmallPerf A H X ↔ Perf A ((affineQhComparison A H).inverse.obj X) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _
  letI := smallAffineShiftAdditive A H
  letI : (SmallPerf A H).IsClosedUnderIsomorphisms := by
    unfold SmallPerf
    infer_instance
  constructor
  · intro hX
    apply (smallPerf_affineQhComparison_iff A H
      ((affineQhComparison A H).inverse.obj X)).mp
    exact (SmallPerf A H).prop_of_iso
      ((affineQhComparison A H).counitIso.app X).symm hX
  · intro hX
    have h := (smallPerf_affineQhComparison_iff A H
      ((affineQhComparison A H).inverse.obj X)).mpr hX
    exact (SmallPerf A H).prop_of_iso
      ((affineQhComparison A H).counitIso.app X) h

/-- If small-universe compactness lifts across the comparison, then the large
compact-to-perfect theorem proves the small-Hom directed Neeman input.  The
parameter is intentional: categorical equivalence alone does not change the
coproduct-index universe in `IsCompactAb`. -/
theorem smallNeemanCompactToPerfectInput_of_large
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (I : CompactToPerfectInput A)
    (liftCompact : ∀ X : SmallAffineD A H, IsCompactAb X →
      IsCompactAb ((affineQhComparison A H).inverse.obj X)) :
    SmallNeemanCompactToPerfectInput A H where
  perfect_of_compact X hX :=
    (smallPerf_iff_perf_affineQhComparison_inverse A H X).mpr
      (I.perfect_of_compact _ (liftCompact X hX))

/-- The same lifting parameter gives large-Hom perfect-to-compact from the
proved small-Hom implication. -/
theorem perfectToCompactInput_of_small
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (liftCompact : ∀ X : SmallAffineD A H, IsCompactAb X →
      IsCompactAb ((affineQhComparison A H).inverse.obj X)) :
    PerfectToCompactInput A where
  compact_of_perfect X hX := by
    letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
      UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _
    have hsmall : SmallPerf A H ((affineQhComparison A H).functor.obj X) :=
      (smallPerf_affineQhComparison_iff A H X).mpr hX
    have hc := liftCompact _ (NeemanM1.isCompactAb_of_smallPerf A H hsmall)
    exact isCompactAb_of_iso ((affineQhComparison A H).unitIso.app X).symm hc

/-- The large-Hom compact/model biconditional from its two separate directions.
The bounded-free induction does not supply `J`. -/
theorem neemanAffineCompactModelInput_of_directions
    (A : Type u) [CommRing A]
    (I : Stacks07LTCompactModelInput A)
    (J : PerfectToCompactInput A) :
    AffinePerfect.NeemanAffineCompactModelInput A := by
  intro X
  constructor
  · exact I.model_of_compact X
  · intro hX
    exact J.compact_of_perfect X (AffinePerfect.model_mem_perf A X hX)

/-- The Stacks 07LT compact-to-model interface after bounded-free induction
and bounded-model retract closure.  No compactness of perfect objects is used. -/
theorem stacks07LTCompactModelInput_capstone
    (A : Type u) [CommRing A]
    (I : Stacks07LT.BoundedFreeInductionInput A)
    (hR : (AffinePerfect.HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts) :
    Stacks07LTCompactModelInput A :=
  Stacks07LT.stacks07LTCompactModelInput_of_freeInduction A I hR

/-- Large-Hom capstone of bounded-free induction and retract closure, with the
independent reverse compactness input kept explicit. -/
theorem neemanAffineCompactModelInput_of_freeInduction
    (A : Type u) [CommRing A]
    (I : Stacks07LT.BoundedFreeInductionInput A)
    (hR : (AffinePerfect.HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts)
    (J : PerfectToCompactInput A) :
    AffinePerfect.NeemanAffineCompactModelInput A :=
  neemanAffineCompactModelInput_of_directions A
    (stacks07LTCompactModelInput_capstone A I hR) J

/-- The full large-Hom capstone with the sole extra size-transport obligation
made explicit. -/
theorem neemanAffineCompactModelInput_of_freeInduction_of_small
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (I : Stacks07LT.BoundedFreeInductionInput A)
    (hR : (AffinePerfect.HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts)
    (liftCompact : ∀ X : SmallAffineD A H, IsCompactAb X →
      IsCompactAb ((affineQhComparison A H).inverse.obj X)) :
    AffinePerfect.NeemanAffineCompactModelInput A :=
  neemanAffineCompactModelInput_of_freeInduction A I hR
    (perfectToCompactInput_of_small A H liftCompact)

/-- The forward implication from the bounded-free induction needs neither
reverse compactness nor retract closure. -/
theorem compactToPerfectInput_of_freeInduction
    (A : Type u) [CommRing A]
    (I : Stacks07LT.BoundedFreeInductionInput A) :
    CompactToPerfectInput A :=
  Stacks07LT.compactToPerfectInput_of_freeInduction A I

/-- The small-Hom affine form of Neeman 3.2(i): the reverse implication is
already proved, so only the directed input `I` remains. -/
theorem smallAffine_neeman_3_2_i
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (I : SmallNeemanCompactToPerfectInput A H) :
    Neeman_3_2_i (SmallAffineD A H) (SmallPerf A H) := by
  intro X
  exact NeemanM1.isCompactAb_iff_smallPerf_of_neeman A H I X

/-- Standard-middle small affine gluing after supplying a compact-to-perfect
proof; there is no additional Neeman, Stacks or coproduct input. -/
theorem affine_theorem_1_1_small_standard_of_compactProof
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (DZ : Type uZ) (DU : Type uU)
    [Category.{u} DZ] [Category.{u} DU]
    [Preadditive DZ] [Preadditive DU]
    [HasZeroObject DZ] [HasZeroObject DU]
    [HasShift DZ ℤ] [HasShift DU ℤ]
    [∀ n : ℤ, (shiftFunctor DZ n).Additive]
    [∀ n : ℤ, (shiftFunctor DU n).Additive]
    [Pretriangulated DZ] [Pretriangulated DU]
    [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DU]
    (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hgen : (@DerivedCategory.TStructure.t (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)).le 0 =
        Coprod (shiftTail (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) 0))
    (I : SmallNeemanCompactToPerfectInput A H) :
    SatisfiesWA (SmallAffineD A H) ↔ EventuallyHomZero S.G' S.G' :=
  affine_theorem_1_1_small_standard_neeman_only A H DZ DU S hgen I

end

end RelativeFM.CapstoneM6

#print axioms RelativeFM.CapstoneM6.affineQhComparison_commShift
#print axioms RelativeFM.CapstoneM6.affineQhComparison_isTriangulated
#print axioms RelativeFM.CapstoneM6.affineQhComparison_ringObjectIso
#print axioms RelativeFM.CapstoneM6.smallPerf_affineQhComparison_iff
#print axioms RelativeFM.CapstoneM6.smallPerf_iff_perf_affineQhComparison_inverse
#print axioms RelativeFM.CapstoneM6.smallNeemanCompactToPerfectInput_of_large
#print axioms RelativeFM.CapstoneM6.perfectToCompactInput_of_small
#print axioms RelativeFM.CapstoneM6.neemanAffineCompactModelInput_of_directions
#print axioms RelativeFM.CapstoneM6.neemanAffineCompactModelInput_of_freeInduction
#print axioms RelativeFM.CapstoneM6.compactToPerfectInput_of_freeInduction
#print axioms RelativeFM.CapstoneM6.smallAffine_neeman_3_2_i
#print axioms RelativeFM.CapstoneM6.affine_theorem_1_1_small_standard_of_compactProof
#print axioms RelativeFM.CapstoneM6.neemanAffineCompactModelInput_of_freeInduction_of_small
#print axioms RelativeFM.CapstoneM6.stacks07LTCompactModelInput_capstone
