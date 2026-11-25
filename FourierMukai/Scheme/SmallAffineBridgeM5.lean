import FourierMukai.Scheme.SmallHomTransportM5
import FourierMukai.Scheme.AffineCompactness
import FourierMukai.Scheme.PerfectModel
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section

namespace RelativeFM.SmallHomM5

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox

universe u

noncomputable section

/-- The quotient from cochain complexes to the small-Hom affine derived
category, with its derived-category instance explicit. -/
noncomputable abbrev smallAffineQ (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ SmallAffineD A H :=
  @DerivedCategory.Q (ModuleCat.{u} A) _ _
    (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)

/-- The large/small localization comparison, presented using the triangulated
localization functor `Qh` rather than its complex-level variant `Q`. -/
noncomputable def affineDQhEquivSmallAffineD
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    AffineD A ≌ SmallAffineD A H := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact Localization.uniq
    (@DerivedCategory.Qh (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
    (@DerivedCategory.Qh (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H))
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))

/-- The compatibility of the `Qh` comparison with the two localization
functors. -/
noncomputable def affineDQhEquivSmallAffineDFactors
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (@DerivedCategory.Qh (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _)) ⋙
        (affineDQhEquivSmallAffineD A H).functor ≅
      @DerivedCategory.Qh (ModuleCat.{u} A) _ _
        (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact Localization.compUniqFunctor _ _ _

/-- The inverse comparison is compatible with localization as well. -/
noncomputable def affineDQhEquivSmallAffineDInverseFactors
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (@DerivedCategory.Qh (ModuleCat.{u} A) _ _
        (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)) ⋙
        (affineDQhEquivSmallAffineD A H).inverse ≅
      @DerivedCategory.Qh (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact Localization.compUniqInverse _ _ _

noncomputable instance affineDQhEquivSmallAffineD_functor_commShift
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (affineDQhEquivSmallAffineD A H).functor.CommShift ℤ := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  letI : Localization.Lifting
      (@DerivedCategory.Qh (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (@DerivedCategory.Qh (ModuleCat.{u} A) _ _
        (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H))
      (affineDQhEquivSmallAffineD A H).functor :=
    ⟨affineDQhEquivSmallAffineDFactors A H⟩
  exact Functor.commShiftOfLocalization
    (@DerivedCategory.Qh (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) ℤ
    (@DerivedCategory.Qh (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H))
    (affineDQhEquivSmallAffineD A H).functor

noncomputable instance affineDQhEquivSmallAffineD_functor_isTriangulated
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (affineDQhEquivSmallAffineD A H).functor.IsTriangulated := by
  letI : ∀ n : ℤ, (shiftFunctor (AffineD A) n).Additive := inferInstance
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  letI : Localization.Lifting
      (@DerivedCategory.Qh (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (@DerivedCategory.Qh (ModuleCat.{u} A) _ _
        (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H))
      (affineDQhEquivSmallAffineD A H).functor :=
    ⟨affineDQhEquivSmallAffineDFactors A H⟩
  letI : NatTrans.CommShift (affineDQhEquivSmallAffineDFactors A H).hom ℤ := by
    exact NatTrans.commShift_iso_hom_of_localization
      (@DerivedCategory.Qh (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) ℤ
      (@DerivedCategory.Qh (ModuleCat.{u} A) _ _
        (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H))
      (affineDQhEquivSmallAffineD A H).functor
  exact Functor.isTriangulated_of_precomp_iso (affineDQhEquivSmallAffineDFactors A H)

noncomputable instance affineDQhEquivSmallAffineD_functor_additive
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (affineDQhEquivSmallAffineD A H).functor.Additive := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  rw [Localization.functor_additive_iff
    (@DerivedCategory.Qh (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
  exact Functor.additive_of_iso (affineDQhEquivSmallAffineDFactors A H).symm

noncomputable instance affineDQhEquivSmallAffineD_inverse_additive
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (affineDQhEquivSmallAffineD A H).inverse.Additive := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  rw [Localization.functor_additive_iff
    (@DerivedCategory.Qh (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H))
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
  exact Functor.additive_of_iso (affineDQhEquivSmallAffineDInverseFactors A H).symm

end

end RelativeFM.SmallHomM5

namespace RelativeFM.SmallHomM5

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox

universe u

noncomputable section

/-- The `Qh` comparison sends the standard regular module to the small regular
module, by evaluation of the localization compatibility isomorphism. -/
noncomputable def affineDQhEquivSmallAffineDRingObjectIso
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (affineDQhEquivSmallAffineD A H).functor.obj (ringObject A) ≅ smallRingObject A H := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact (affineDQhEquivSmallAffineDFactors A H).app
    (((HomotopyCategory.singleFunctors (ModuleCat.{u} A)).functor 0).obj
      (ModuleCat.of A A))

/-- The comparison sends `Q.obj K` in the standard model to `Q.obj K` in the
small model. -/
noncomputable def affineDQhEquivSmallAffineDQObjIso
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (affineDQhEquivSmallAffineD A H).functor.obj
        ((@DerivedCategory.Q (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _)).obj K) ≅
      (@DerivedCategory.Q (ModuleCat.{u} A) _ _
        (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)).obj K := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact (affineDQhEquivSmallAffineD A H).functor.mapIso
      ((@DerivedCategory.quotientCompQhIso (ModuleCat.{u} A) _ _
        (HasDerivedCategory.standard _)).symm.app K) ≪≫
    (affineDQhEquivSmallAffineDFactors A H).app
      ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj K) ≪≫
    (@DerivedCategory.quotientCompQhIso (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)).app K

/-- Perfectness transports from the standard affine model to the small-Hom
model along the triangulated comparison. -/
theorem smallPerf_map_of_perf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X : AffineD A} (hX : Perf A X) :
    SmallPerf A H ((affineDQhEquivSmallAffineD A H).functor.obj X) := by
  have h := AffinePerfect.mem_triangEnvelope_singleton_map
    (affineDQhEquivSmallAffineD A H).functor (ringObject A) hX
  change (ObjectProperty.singleton (smallRingObject A H)).triangEnvelope
    ((affineDQhEquivSmallAffineD A H).functor.obj X)
  rw [← AffinePerfect.triangEnvelope_singleton_eq_of_iso
    (affineDQhEquivSmallAffineDRingObjectIso A H)]
  exact h

/-- Conversely, small perfectness pulls back to standard perfectness. -/
theorem perf_inverse_of_smallPerf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X : SmallAffineD A H} (hX : SmallPerf A H X) :
    Perf A ((affineDQhEquivSmallAffineD A H).inverse.obj X) := by
  let E := affineDQhEquivSmallAffineD A H
  have hgen : (ObjectProperty.singleton (E.functor.obj (ringObject A))).triangEnvelope X := by
    rw [AffinePerfect.triangEnvelope_singleton_eq_of_iso
      (affineDQhEquivSmallAffineDRingObjectIso A H)]
    exact hX
  have h := (AffinePerfect.mem_triangEnvelope_singleton_map_iff E.functor
    (ringObject A) (E.inverse.obj X)).mp
      ((ObjectProperty.singleton (E.functor.obj (ringObject A))).triangEnvelope.prop_of_iso
        (E.counitIso.app X).symm hgen)
  exact h

/-- A strictly bounded finite-projective representative in the small-Hom
localization. -/
structure SmallBoundedFiniteProjectiveModel (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (X : SmallAffineD A H) where
  complex : CochainComplex (ModuleCat.{u} A) ℤ
  lower : ℤ
  upper : ℤ
  isStrictlyGE : complex.IsStrictlyGE lower
  isStrictlyLE : complex.IsStrictlyLE upper
  finite : ∀ n, Module.Finite A (complex.X n)
  projective : ∀ n, Module.Projective A (complex.X n)
  iso : X ≅ (@DerivedCategory.Q (ModuleCat.{u} A) _ _
    (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)).obj complex

/-- Bounded finite-projective representatives are small-perfect.  The proof
uses the standard 066T filtration theorem and the triangulated comparison, not
an independent truncation argument and not a compactness assertion. -/
theorem smallPerf_of_smallBoundedFiniteProjectiveModel
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    {X : SmallAffineD A H} (M : SmallBoundedFiniteProjectiveModel A H X) :
    SmallPerf A H X := by
  letI : (SmallPerf A H).IsClosedUnderIsomorphisms := by
    unfold SmallPerf
    infer_instance
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  let Y : AffineD A :=
    (@DerivedCategory.Q (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _)).obj M.complex
  let N : BoundedFiniteProjectiveModel A Y :=
    { complex := M.complex
      lower := M.lower
      upper := M.upper
      isStrictlyGE := M.isStrictlyGE
      isStrictlyLE := M.isStrictlyLE
      finite := M.finite
      projective := M.projective
      iso := Iso.refl _ }
  have hY : Perf A Y := AffinePerfect.boundedFiniteProjectiveModel_mem_perf A Y N
  have h := smallPerf_map_of_perf A H hY
  exact (SmallPerf A H).prop_of_iso
    (affineDQhEquivSmallAffineDQObjIso A H M.complex ≪≫ M.iso.symm) h

/-- Nonempty form of bounded-model perfectness. -/
theorem smallPerf_of_nonempty_smallBoundedFiniteProjectiveModel
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    {X : SmallAffineD A H} (M : Nonempty (SmallBoundedFiniteProjectiveModel A H X)) :
    SmallPerf A H X := by
  obtain ⟨M⟩ := M
  exact smallPerf_of_smallBoundedFiniteProjectiveModel A H M

end

end RelativeFM.SmallHomM5

#print axioms RelativeFM.SmallHomM5.affineDQhEquivSmallAffineD
#print axioms RelativeFM.SmallHomM5.affineDQhEquivSmallAffineD_functor_commShift
#print axioms RelativeFM.SmallHomM5.affineDQhEquivSmallAffineD_functor_isTriangulated
#print axioms RelativeFM.SmallHomM5.affineDQhEquivSmallAffineDRingObjectIso
#print axioms RelativeFM.SmallHomM5.smallPerf_map_of_perf
#print axioms RelativeFM.SmallHomM5.perf_inverse_of_smallPerf
#print axioms RelativeFM.SmallHomM5.smallPerf_of_smallBoundedFiniteProjectiveModel

namespace RelativeFM.SmallHomM5

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox

universe u

noncomputable section

/-- The `Qh` comparison is also a lift of the complex-level quotient `Q`. -/
noncomputable def affineDQhEquivSmallAffineDQFactors
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (@DerivedCategory.Q (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _)) ⋙
        (affineDQhEquivSmallAffineD A H).functor ≅
      @DerivedCategory.Q (ModuleCat.{u} A) _ _
        (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact
    Functor.isoWhiskerRight
      ((@DerivedCategory.quotientCompQhIso (ModuleCat.{u} A) _ _
        (HasDerivedCategory.standard _)).symm)
      (affineDQhEquivSmallAffineD A H).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (affineDQhEquivSmallAffineDFactors A H) ≪≫
    @DerivedCategory.quotientCompQhIso (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)

/-- Abstract uniqueness of localization identifies the original `Q` comparison
with the triangulated `Qh` comparison. -/
noncomputable def affineDQhToAffineDEquivSmallFunctorIso
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (affineDQhEquivSmallAffineD A H).functor ≅
      (affineDEquivSmallAffineD A H).functor := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact Localization.isoUniqFunctor
    (@DerivedCategory.Q (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
    (@DerivedCategory.Q (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H))
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    (affineDQhEquivSmallAffineD A H).functor
    (affineDQhEquivSmallAffineDQFactors A H)

noncomputable instance affineDEquivSmallAffineD_functor_commShift
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (affineDEquivSmallAffineD A H).functor.CommShift ℤ :=
  Functor.CommShift.ofIso (affineDQhToAffineDEquivSmallFunctorIso A H) ℤ

noncomputable instance affineDEquivSmallAffineD_functor_isTriangulated
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (affineDEquivSmallAffineD A H).functor.IsTriangulated := by
  letI : NatTrans.CommShift (affineDQhToAffineDEquivSmallFunctorIso A H).hom ℤ :=
    Functor.CommShift.ofIso_compatibility (affineDQhToAffineDEquivSmallFunctorIso A H) ℤ
  exact Functor.isTriangulated_of_iso (affineDQhToAffineDEquivSmallFunctorIso A H)

/-- The repository's original comparison sends the regular module to the small
regular module. -/
noncomputable def affineDEquivSmallAffineDRingObjectIso
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    (affineDEquivSmallAffineD A H).functor.obj (ringObject A) ≅ smallRingObject A H := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact (Localization.compUniqFunctor
    (@DerivedCategory.Q (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
    (@DerivedCategory.Q (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H))
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))).app
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A))

/-- The original comparison sends `Q.obj K` to `Q.obj K`. -/
noncomputable def affineDEquivSmallAffineDQObjIso
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (affineDEquivSmallAffineD A H).functor.obj
        ((@DerivedCategory.Q (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _)).obj K) ≅
      (smallAffineQ A H).obj K := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact (Localization.compUniqFunctor
    (@DerivedCategory.Q (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
    (@DerivedCategory.Q (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H))
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))).app K

/-- Perfectness transport for the repository's original comparison. -/
theorem smallPerf_map_original_of_perf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X : AffineD A} (hX : Perf A X) :
    SmallPerf A H ((affineDEquivSmallAffineD A H).functor.obj X) := by
  have h := AffinePerfect.mem_triangEnvelope_singleton_map
    (affineDEquivSmallAffineD A H).functor (ringObject A) hX
  change (ObjectProperty.singleton (smallRingObject A H)).triangEnvelope
    ((affineDEquivSmallAffineD A H).functor.obj X)
  rw [← AffinePerfect.triangEnvelope_singleton_eq_of_iso
    (affineDEquivSmallAffineDRingObjectIso A H)]
  exact h

/-- Compactness transport for the original comparison, in the valid
large-to-small direction. -/
theorem isCompactAb_original_map_of_isCompactAb (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X : AffineD A} (hX : IsCompactAb X) :
    IsCompactAb ((affineDEquivSmallAffineD A H).functor.obj X) :=
  isCompactAb_of_equivalence_large_to_small (affineDEquivSmallAffineD A H).functor hX

end

end RelativeFM.SmallHomM5

#print axioms RelativeFM.SmallHomM5.affineDEquivSmallAffineD_functor_commShift
#print axioms RelativeFM.SmallHomM5.affineDEquivSmallAffineD_functor_isTriangulated
#print axioms RelativeFM.SmallHomM5.smallPerf_map_original_of_perf
#print axioms RelativeFM.SmallHomM5.isCompactAb_original_map_of_isCompactAb

namespace RelativeFM.SmallHomM5

open CategoryTheory CategoryTheory.Limits
open RelativeWeakApprox

universe u

noncomputable section

/-- Pullback of small perfectness along the repository's original comparison. -/
theorem perf_inverse_original_of_smallPerf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X : SmallAffineD A H} (hX : SmallPerf A H X) :
    Perf A ((affineDEquivSmallAffineD A H).inverse.obj X) := by
  let E := affineDEquivSmallAffineD A H
  have hgen : (ObjectProperty.singleton (E.functor.obj (ringObject A))).triangEnvelope X := by
    rw [AffinePerfect.triangEnvelope_singleton_eq_of_iso
      (affineDEquivSmallAffineDRingObjectIso A H)]
    exact hX
  exact (AffinePerfect.mem_triangEnvelope_singleton_map_iff E.functor
    (ringObject A) (E.inverse.obj X)).mp
      ((ObjectProperty.singleton (E.functor.obj (ringObject A))).triangEnvelope.prop_of_iso
        (E.counitIso.app X).symm hgen)

/-- Small perfectness is exactly standard perfectness of the inverse image
under the original comparison. -/
theorem smallPerf_iff_perf_inverse_original (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (X : SmallAffineD A H) :
    SmallPerf A H X ↔ Perf A ((affineDEquivSmallAffineD A H).inverse.obj X) := by
  constructor
  · exact perf_inverse_original_of_smallPerf A H
  · intro h
    letI : (SmallPerf A H).IsClosedUnderIsomorphisms := by
      unfold SmallPerf
      infer_instance
    exact (SmallPerf A H).prop_of_iso ((affineDEquivSmallAffineD A H).counitIso.app X)
      (smallPerf_map_original_of_perf A H h)

/-- Standard perfectness is exactly small perfectness of the image under the
original comparison. -/
theorem perf_iff_smallPerf_original_map (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (X : AffineD A) :
    Perf A X ↔ SmallPerf A H ((affineDEquivSmallAffineD A H).functor.obj X) := by
  constructor
  · exact smallPerf_map_original_of_perf A H
  · intro h
    exact (Perf A).prop_of_iso ((affineDEquivSmallAffineD A H).unitIso.app X).symm
      (perf_inverse_original_of_smallPerf A H h)

end

end RelativeFM.SmallHomM5

#print axioms RelativeFM.SmallHomM5.smallPerf_iff_perf_inverse_original
#print axioms RelativeFM.SmallHomM5.perf_iff_smallPerf_original_map
