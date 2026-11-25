/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.SchemeNeemanFiniteCoverAssembly

/-!
# Isomorphism transport for scheme-level Neeman weak approximability

This module is self-contained and uses no Stacks input.  An isomorphism of
schemes is an open immersion.  Its sheaf restriction functor is exact and is an
equivalence, so it induces a triangulated equivalence of unbounded derived
categories.  We restrict that equivalence to complexes with quasicoherent
cohomology supported on a closed set and transport paper weak approximation
data at the standard `t`-structure.
-/

@[expose] public section

namespace RelativeFM.SchemeNeemanIsoTransportM4

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry Set
open RelativeWeakApprox RelativeWeakApprox.PaperM2
open RelativeFM.SchemeWeakApproxStatementM1
open RelativeFM.SchemeNeemanFiniteCoverAssemblyM5

universe u

noncomputable section

/-- Inclusion of the open complement of a closed set. -/
abbrev complementInclusion {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    (Z.compl : Scheme.{u}) ⟶ X :=
  AlgebraicGeometry.Scheme.Opens.ι (X := X) Z.compl

instance isDQCohSupported_isClosedUnderIsomorphisms
    (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) :
    (IsDQCohSupported X Z).IsClosedUnderIsomorphisms := by
  unfold IsDQCohSupported
  infer_instance

/-- The restriction functors along the two directions of a scheme isomorphism
form an equivalence of module categories. -/
noncomputable def moduleRestrictionEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk
    (Scheme.Modules.restrictFunctor e.inv)
    (Scheme.Modules.restrictFunctor e.hom)
    (Scheme.Modules.restrictFunctorId.symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).symm ≪≫
      Scheme.Modules.restrictFunctorComp e.hom e.inv)
    ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫
      Scheme.Modules.restrictFunctorId)

noncomputable instance moduleRestrictionEquivalence_functor_additive
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (moduleRestrictionEquivalence e).functor.Additive := by
  change (Scheme.Modules.restrictFunctor e.inv).Additive
  infer_instance

noncomputable instance moduleRestrictionEquivalence_inverse_additive
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (moduleRestrictionEquivalence e).inverse.Additive := by
  change (Scheme.Modules.restrictFunctor e.hom).Additive
  infer_instance

/-- The exact derived equivalence induced by a scheme isomorphism. -/
noncomputable def derivedRestrictionEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    Derived X ≌ Derived Y :=
  derivedEquivalence (moduleRestrictionEquivalence e)


noncomputable instance derivedRestrictionEquivalence_functor_additive
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (derivedRestrictionEquivalence e).functor.Additive := by
  change (moduleRestrictionEquivalence e).functor.mapDerivedCategory.Additive
  infer_instance

noncomputable instance derivedRestrictionEquivalence_functor_commShift
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (derivedRestrictionEquivalence e).functor.CommShift ℤ := by
  change (moduleRestrictionEquivalence e).functor.mapDerivedCategory.CommShift ℤ
  infer_instance

noncomputable instance derivedRestrictionEquivalence_functor_isTriangulated
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (derivedRestrictionEquivalence e).functor.IsTriangulated := by
  change (moduleRestrictionEquivalence e).functor.mapDerivedCategory.IsTriangulated
  infer_instance

/-- The inclusion of the complement of the pulled-back support contains the
image of the target complement under `e.inv`. -/
lemma complement_lift_range {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y) :
    Set.range ((complementInclusion Z) ≫ e.inv) ⊆
      Set.range (complementInclusion (isoPreimageClosed e Z)) := by
  rintro _ ⟨y, rfl⟩
  let x : (isoPreimageClosed e Z).compl :=
    ⟨e.inv ((complementInclusion Z) y), by
      change e.inv ((complementInclusion Z) y) ∉ (isoPreimageClosed e Z : Set X)
      intro hy
      have hycomp := y.property
      change (complementInclusion Z) y ∈ (Z : Set Y)ᶜ at hycomp
      exact hycomp (by simpa [isoPreimageClosed] using hy)⟩
  exact ⟨x, rfl⟩

/-- The morphism induced by `e.inv` between the two open complements. -/
noncomputable def complementRestrict {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y) :
    (Z.compl : Scheme.{u}) ⟶ ((isoPreimageClosed e Z).compl : Scheme.{u}) :=
  IsOpenImmersion.lift (complementInclusion (isoPreimageClosed e Z))
    ((complementInclusion Z) ≫ e.inv) (complement_lift_range e Z)

@[simp] lemma complementRestrict_ι {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y) :
    complementRestrict e Z ≫ complementInclusion (isoPreimageClosed e Z) =
      (complementInclusion Z) ≫ e.inv :=
  IsOpenImmersion.lift_fac _ _ _

noncomputable instance complementRestrict_isOpenImmersion {X Y : Scheme.{u}}
    (e : X ≅ Y) (Z : TopologicalSpace.Closeds Y) :
    IsOpenImmersion (complementRestrict e Z) := by
  letI : IsOpenImmersion (complementRestrict e Z ≫
      complementInclusion (isoPreimageClosed e Z)) := by
    rw [complementRestrict_ι]
    infer_instance
  exact IsOpenImmersion.of_comp (complementRestrict e Z)
    (complementInclusion (isoPreimageClosed e Z))

/-- The induced morphism between open complements is an isomorphism. -/
noncomputable instance complementRestrict_isIso {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y) : IsIso (complementRestrict e Z) := by
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, ?_⟩
  rw [TopCat.epi_iff_surjective]
  intro x
  let y : Z.compl :=
    ⟨e.hom ((complementInclusion (isoPreimageClosed e Z)) x), by
      change e.hom ((complementInclusion (isoPreimageClosed e Z)) x) ∉ (Z : Set Y)
      intro hy
      exact x.property hy⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  have hk := congrArg (fun f : (Z.compl : Scheme.{u}) ⟶ X => f y)
    (complementRestrict_ι e Z)
  change (complementInclusion (isoPreimageClosed e Z)) (complementRestrict e Z y) =
    (complementInclusion (isoPreimageClosed e Z)) x
  calc
    _ = e.inv ((complementInclusion Z) y) := hk
    _ = e.inv (e.hom ((complementInclusion (isoPreimageClosed e Z)) x)) := rfl
    _ = _ := by simp

/-- Restriction of the pulled-back sheaf to `Y \ Z` is a further restriction
of the original sheaf restricted to `X \ e⁻¹(Z)`. -/
noncomputable def restrictComplementIso {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor (complementInclusion Z)).obj
        ((Scheme.Modules.restrictFunctor e.inv).obj M) ≅
      (Scheme.Modules.restrictFunctor (complementRestrict e Z)).obj
        ((Scheme.Modules.restrictFunctor
          (complementInclusion (isoPreimageClosed e Z))).obj M) :=
  ((Scheme.Modules.restrictFunctorComp (complementInclusion Z) e.inv).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (complementRestrict_ι e Z)).symm.app M ≪≫
    (Scheme.Modules.restrictFunctorComp (complementRestrict e Z)
      (complementInclusion (isoPreimageClosed e Z))).app M

/-- Sheaf support on a closed set is preserved by restriction along a scheme
isomorphism. -/
theorem isZero_restrictComplement_map {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y) (M : X.Modules)
    (hM : IsZero ((Scheme.Modules.restrictFunctor
      (complementInclusion (isoPreimageClosed e Z))).obj M)) :
    IsZero ((Scheme.Modules.restrictFunctor (complementInclusion Z)).obj
      ((Scheme.Modules.restrictFunctor e.inv).obj M)) :=
  ((Scheme.Modules.restrictFunctor (complementRestrict e Z)).map_isZero hM).of_iso
    (restrictComplementIso e Z M)

/-- Cohomology with quasicoherent support is preserved by the derived
restriction equivalence. -/
theorem isDQCohSupported_derivedRestriction {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y) {A : Derived X}
    (hA : IsDQCohSupported X (isoPreimageClosed e Z) A) :
    IsDQCohSupported Y Z ((derivedRestrictionEquivalence e).functor.obj A) := by
  refine ⟨?_, ?_⟩
  · intro n
    have hM : ((Scheme.Modules.restrictFunctor e.inv).obj
        (cohomologySheaf A n)).IsQuasicoherent := by
      letI := hA.1 n
      infer_instance
    exact (quasiCoherent Y).prop_of_iso
      (mapDerivedCategoryHomologyIso (moduleRestrictionEquivalence e).functor A n).symm hM
  · intro n
    exact (isZero_restrictComplement_map e Z (cohomologySheaf A n) (hA.2 n)).of_iso
      ((Scheme.Modules.restrictFunctor (complementInclusion Z)).mapIso
        (mapDerivedCategoryHomologyIso (moduleRestrictionEquivalence e).functor A n))

@[simp] lemma isoPreimageClosed_symm {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y) :
    isoPreimageClosed e.symm (isoPreimageClosed e Z) = Z := by
  ext y
  simp [isoPreimageClosed]

/-- Supported quasicoherent cohomology is also reflected. -/
lemma isDQCohSupported_inverseImage {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y) :
    (IsDQCohSupported Y Z).inverseImage (derivedRestrictionEquivalence e).functor =
      IsDQCohSupported X (isoPreimageClosed e Z) := by
  ext A
  constructor
  · intro hA
    refine ⟨?_, ?_⟩
    · intro n
      have hM : ((Scheme.Modules.restrictFunctor e.inv).obj
          (cohomologySheaf A n)).IsQuasicoherent :=
        (quasiCoherent Y).prop_of_iso
          (mapDerivedCategoryHomologyIso (moduleRestrictionEquivalence e).functor A n)
          (hA.1 n)
      exact (isQuasicoherent_restrict_iff_of_isIso (cohomologySheaf A n) e.inv).1 hM
    · intro n
      have ht : IsZero ((Scheme.Modules.restrictFunctor (complementInclusion Z)).obj
          ((Scheme.Modules.restrictFunctor e.inv).obj (cohomologySheaf A n))) :=
        (hA.2 n).of_iso ((Scheme.Modules.restrictFunctor (complementInclusion Z)).mapIso
          (mapDerivedCategoryHomologyIso (moduleRestrictionEquivalence e).functor A n).symm)
      have hk : IsZero ((Scheme.Modules.restrictFunctor (complementRestrict e Z)).obj
          ((Scheme.Modules.restrictFunctor
            (complementInclusion (isoPreimageClosed e Z))).obj (cohomologySheaf A n))) :=
        ht.of_iso (restrictComplementIso e Z (cohomologySheaf A n)).symm
      letI : (Scheme.Modules.restrictFunctor (complementRestrict e Z)).IsEquivalence := by
        change (moduleRestrictionEquivalence
          (asIso (complementRestrict e Z)).symm).functor.IsEquivalence
        infer_instance
      exact IsZero.of_full_of_faithful_of_isZero _ _ hk
  · exact isDQCohSupported_derivedRestriction e Z

/-- The triangulated equivalence between supported `D_qc` categories induced by
a scheme isomorphism. -/
noncomputable def supportedDerivedRestrictionEquivalence {X Y : Scheme.{u}}
    (e : X ≅ Y) (Z : TopologicalSpace.Closeds Y) :
    DqcSupported X (isoPreimageClosed e Z) ≌ DqcSupported Y Z :=
  (derivedRestrictionEquivalence e).congrFullSubcategory
    (isDQCohSupported_inverseImage e Z)


noncomputable instance supportedDerivedRestrictionEquivalence_functor_additive
    {X Y : Scheme.{u}} (e : X ≅ Y) (Z : TopologicalSpace.Closeds Y) :
    (supportedDerivedRestrictionEquivalence e Z).functor.Additive := by
  dsimp only [supportedDerivedRestrictionEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

noncomputable instance supportedDerivedRestrictionEquivalence_functor_commShift
    {X Y : Scheme.{u}} (e : X ≅ Y) (Z : TopologicalSpace.Closeds Y) :
    (supportedDerivedRestrictionEquivalence e Z).functor.CommShift ℤ := by
  dsimp only [supportedDerivedRestrictionEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

noncomputable instance supportedDerivedRestrictionEquivalence_functor_isTriangulated
    {X Y : Scheme.{u}} (e : X ≅ Y) (Z : TopologicalSpace.Closeds Y) :
    (supportedDerivedRestrictionEquivalence e Z).functor.IsTriangulated := by
  dsimp only [supportedDerivedRestrictionEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- Derived restriction along an isomorphism carries the restricted standard
`t`-structure to the restricted standard `t`-structure. -/
theorem transportTStructure_eq_dqcSupportedStandard {X Y : Scheme.{u}}
    (e : X ≅ Y) (Z : TopologicalSpace.Closeds Y) :
    transportTStructure (supportedDerivedRestrictionEquivalence e Z).functor
      (dqcSupportedStandardTStructure X (isoPreimageClosed e Z)) =
        dqcSupportedStandardTStructure Y Z := by
  let F := (supportedDerivedRestrictionEquivalence e Z).functor
  apply RelativeWeakApprox.TStructure.ext_le_zero
  ext B
  rw [transportTStructure_le]
  rw [dqcSupportedStandardTStructure_le, dqcSupportedStandardTStructure_le]
  rw [TStructure.le_iff_isLE, TStructure.le_iff_isLE]
  let eB := (IsDQCohSupported Y Z).ι.mapIso (F.objObjPreimageIso B)
  change DerivedCategory.IsLE (F.inv.obj B).obj 0 ↔ DerivedCategory.IsLE B.obj 0
  constructor
  · intro h
    have hf : DerivedCategory.IsLE
        ((derivedRestrictionEquivalence e).functor.obj (F.inv.obj B).obj) 0 :=
      (derivedEquivalence_isLE_iff (moduleRestrictionEquivalence e) (F.inv.obj B).obj 0).2 h
    exact ⟨(DerivedCategory.TStructure.t.le 0).prop_of_iso eB hf.le⟩
  · intro h
    have hf : DerivedCategory.IsLE
        ((derivedRestrictionEquivalence e).functor.obj (F.inv.obj B).obj) 0 :=
      ⟨(DerivedCategory.TStructure.t.le 0).prop_of_iso eB.symm h.le⟩
    exact (derivedEquivalence_isLE_iff (moduleRestrictionEquivalence e)
      (F.inv.obj B).obj 0).1 hf

/-- **Scheme-isomorphism transport of supported Neeman 3.2(iv).**  This is the
`of_iso` gluing input, with the paper's zero-detection generator condition. -/
theorem neemanSupportedWeakApproximability_of_iso {X Y : Scheme.{u}}
    (e : X ≅ Y) (Z : TopologicalSpace.Closeds Y)
    (h : NeemanSupportedWeakApproximability X (isoPreimageClosed e Z)) :
    NeemanSupportedWeakApproximability Y Z := by
  let F := (supportedDerivedRestrictionEquivalence e Z).functor
  obtain ⟨W, hW⟩ := h
  refine ⟨⟨transportPaperWeakApproximationData F W, ?_⟩⟩
  rw [transportPaperWeakApproximationData_t, hW]
  exact transportTStructure_eq_dqcSupportedStandard e Z

@[simp] lemma isoPreimageClosed_top {X Y : Scheme.{u}} (e : X ≅ Y) :
    isoPreimageClosed e (⊤ : TopologicalSpace.Closeds Y) = ⊤ := by
  ext x
  simp [isoPreimageClosed]

/-- Scheme-isomorphism transport of ordinary Neeman weak approximability. -/
theorem neemanWeakApproximability_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (h : NeemanWeakApproximability X) : NeemanWeakApproximability Y := by
  apply (neemanSupportedWeakApproximability_top Y).1
  apply neemanSupportedWeakApproximability_of_iso e ⊤
  rw [isoPreimageClosed_top]
  exact (neemanSupportedWeakApproximability_top X).2 h

/-- The compact-complement condition is invariant under a scheme
isomorphism. -/
theorem isCompactClosedComplement_isoPreimage {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y) (hcZ : IsCompactClosedComplement Z) :
    IsCompactClosedComplement (isoPreimageClosed e Z) := by
  have h := e.hom.homeomorph.isCompact_preimage (s := (Z : Set Y)ᶜ) |>.2 hcZ
  simpa only [IsCompactClosedComplement, isoPreimageClosed,
    TopologicalSpace.Closeds.coe_mk, Set.preimage_compl] using h

/-- An affine supported base proved on `Spec Γ(X)` supplies the base on an
abstract affine scheme, including the compact-complement side condition. -/
theorem neemanSupportedWeakApproximability_of_isAffine
    (X : Scheme.{u}) [IsAffine X] (Z : TopologicalSpace.Closeds X)
    (hcZ : IsCompactClosedComplement Z)
    (hbase : ∀ (Z' : TopologicalSpace.Closeds (Spec Γ(X, ⊤))),
      IsCompactClosedComplement Z' →
        NeemanSupportedWeakApproximability (Spec Γ(X, ⊤)) Z') :
    NeemanSupportedWeakApproximability X Z :=
  neemanSupportedWeakApproximability_of_iso X.isoSpec.symm Z
    (hbase _ (isCompactClosedComplement_isoPreimage X.isoSpec.symm Z hcZ))

end

end RelativeFM.SchemeNeemanIsoTransportM4

#print axioms RelativeFM.SchemeNeemanIsoTransportM4.isDQCohSupported_inverseImage
#print axioms RelativeFM.SchemeNeemanIsoTransportM4.supportedDerivedRestrictionEquivalence
#print axioms RelativeFM.SchemeNeemanIsoTransportM4.transportTStructure_eq_dqcSupportedStandard
#print axioms RelativeFM.SchemeNeemanIsoTransportM4.neemanSupportedWeakApproximability_of_iso
#print axioms RelativeFM.SchemeNeemanIsoTransportM4.neemanWeakApproximability_of_iso
#print axioms RelativeFM.SchemeNeemanIsoTransportM4.neemanSupportedWeakApproximability_of_isAffine
