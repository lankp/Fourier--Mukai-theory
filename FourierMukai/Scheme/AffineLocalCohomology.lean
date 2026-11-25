import FourierMukai.Scheme.AffineRecollement
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Explicit local cohomology for a principal affine open

This file is a candidate for `FourierMukai/Scheme/AffineLocalCohomology.lean`,
imported immediately after `AffineRecollement.lean`. It constructs the
degreewise mapping cone of the localization unit and its shift by `-1`.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe u

noncomputable section

set_option maxHeartbeats 1000000

attribute [local instance] HasDerivedCategory.standard

namespace AffineLocalCohomology

/-- The extension/restriction adjunction, degreewise on cochain complexes. -/
noncomputable def openComplexAdjunction (A : Type u) [CommRing A] (f : A) :
    (ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⊣
      (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ) := by
  letI : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).left_adjoint_additive
  exact Adjunction.mapComplex
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A (Away A f)))
    (ComplexShape.up ℤ)

/-- The degreewise localization map `K ⟶ K ⊗[A] A[1/f]`, with the target
regarded again as a complex of `A`-modules. -/
noncomputable abbrev localizationMap (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    K ⟶ ((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙
      (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K :=
  (openComplexAdjunction A f).unit.app K

/-- Flat extension of scalars followed by exact restriction of scalars
preserves quasi-isomorphisms degreewise. -/
lemma quasiIso_openComplexMap (A : Type u) [CommRing A] (f : A)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (a : K ⟶ L) [QuasiIso a] :
    QuasiIso (((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙
      (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a) := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  change QuasiIso
    (((ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
    (((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map a))
  infer_instance

/-- The functorial (unshifted) mapping cone of the localization unit. -/
noncomputable def coneFunctor (A : Type u) [CommRing A] (f : A) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ where
  obj K := CochainComplex.mappingCone (localizationMap A f K)
  map {K L} a := CochainComplex.mappingCone.map
    (localizationMap A f K) (localizationMap A f L) a
    (((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙
      (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a)
    ((openComplexAdjunction A f).unit.naturality a)
  map_id K := by
    convert CochainComplex.mappingCone.map_id (localizationMap A f K) using 1
    ext n
    simp [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.ext_from_iff _ (n + 1) n rfl]
  map_comp {K L M} a b := by
    convert CochainComplex.mappingCone.map_comp
        (localizationMap A f K) (localizationMap A f L) (localizationMap A f M)
        a (((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
          (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map a)
        ((openComplexAdjunction A f).unit.naturality a)
        b (((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
          (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map b)
        ((openComplexAdjunction A f).unit.naturality b) using 1 <;>
      simp only [Functor.map_comp]

/-- The localization unit is an isomorphism on modules coming from `A[1/f]`.
This is the underived form of idempotence of open localization. -/
lemma unit_isIso_restrictScalars (A : Type u) [CommRing A] (f : A)
    (N : ModuleCat.{u} (Away A f)) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).unit.app
        ((ModuleCat.restrictScalars (algebraMap A (Away A f))).obj N)) := by
  haveI : IsIso ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).unit.app
        ((ModuleCat.restrictScalars (algebraMap A (Away A f))).obj N) ≫
      (ModuleCat.restrictScalars (algebraMap A (Away A f))).map
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
          (algebraMap A (Away A f))).counit.app N)) := by
    rw [(ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).right_triangle_components]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((ModuleCat.restrictScalars (algebraMap A (Away A f))).map
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
        (algebraMap A (Away A f))).counit.app N))

/-- If the three cohomology localization maps in a distinguished triangle have
power-torsion kernels and are surjective after multiplication by powers of `f`,
then every cohomology module of the first object is power torsion. -/
lemma powerTorsion_homology_obj₁_of_triangle (A : Type u) [CommRing A] (f : A)
    (T : Triangle (AffineD A)) (hT : T ∈ distTriang (AffineD A))
    (hker : ∀ (n : ℤ)
      (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj T.obj₂),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map T.mor₂ y = 0 →
      ∃ r : ℕ, f ^ r • y = 0)
    (hsurj : ∀ (n : ℤ)
      (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj T.obj₃),
      ∃ (r : ℕ) (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj T.obj₂),
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map T.mor₂ y = f ^ r • z)
    (n : ℤ) : PowerTorsion A f
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj T.obj₁) := by
  rw [powerTorsion_iff]
  intro x
  let Hn := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  have hy : Hn.map T.mor₂ (Hn.map T.mor₁ x) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      comp_distTriang_mor_zero₁₂ _ hT]
    simp
  obtain ⟨r, hr⟩ := hker n (Hn.map T.mor₁ x) hy
  have hx : Hn.map T.mor₁ (f ^ r • x) = 0 := by
    rw [map_smul, hr]
  obtain ⟨z, hz⟩ := ((ShortComplex.moduleCat_exact_iff _).mp
    (DerivedCategory.HomologySequence.exact₁ T hT (n - 1) n (by omega)))
    (f ^ r • x) hx
  obtain ⟨s, y, hy'⟩ := hsurj (n - 1) z
  refine ⟨s + r, ?_⟩
  calc
    f ^ (s + r) • x = f ^ s • (f ^ r • x) := by rw [pow_add, mul_smul]
    _ = f ^ s • (DerivedCategory.HomologySequence.δ T (n - 1) n (by omega) z) := by
      rw [hz]
    _ = DerivedCategory.HomologySequence.δ T (n - 1) n (by omega) (f ^ s • z) := by
      rw [map_smul]
    _ = DerivedCategory.HomologySequence.δ T (n - 1) n (by omega)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n - 1)).map T.mor₂ y) := by
      rw [hy']
    _ = 0 := by
      rw [← ConcreteCategory.comp_apply]
      change (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n - 1)).map T.mor₂ ≫
        DerivedCategory.HomologySequence.δ T (n - 1) n (by omega)) y) = 0
      rw [DerivedCategory.HomologySequence.comp_δ T hT (n - 1) n (by omega)]
      rfl

/-- The cone functor preserves quasi-isomorphisms: apply the triangulated
five lemma after localization to the derived category. -/
lemma quasiIso_coneFunctor_map (A : Type u) [CommRing A] (f : A)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (a : K ⟶ L) [QuasiIso a] :
    QuasiIso ((coneFunctor A f).map a) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  let Φ := DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap
      (localizationMap A f K) (localizationMap A f L) a
      (((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
        (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map a)
      ((openComplexAdjunction A f).unit.naturality a))
  change IsIso Φ.hom₃
  haveI : IsIso Φ.hom₁ := by
    change IsIso (DerivedCategory.Q.map a)
    infer_instance
  haveI : IsIso Φ.hom₂ := by
    change IsIso (DerivedCategory.Q.map
      (((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
        (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map a))
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact quasiIso_openComplexMap A f a
  exact isIso₃_of_isIso₁₂ Φ
    (DerivedCategory.mappingCone_triangle_distinguished (localizationMap A f K))
    (DerivedCategory.mappingCone_triangle_distinguished (localizationMap A f L))
    inferInstance inferInstance

/-- The degreewise local-cohomology complex `cone(K ⟶ K[1/f])[-1]`. -/
noncomputable def complexFunctor (A : Type u) [CommRing A] (f : A) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  coneFunctor A f ⋙ shiftFunctor _ (-1 : ℤ)

/-- On objects, `complexFunctor` is literally the mapping cocone of the
localization unit. -/
noncomputable def complexFunctorObjIso (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (complexFunctor A f).obj K ≅
      CochainComplex.mappingCocone (localizationMap A f K) :=
  Iso.refl _

/-- Shifting the cone by `-1` preserves quasi-isomorphisms. -/
lemma quasiIso_complexFunctor_map (A : Type u) [CommRing A] (f : A)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (a : K ⟶ L) [QuasiIso a] :
    QuasiIso ((complexFunctor A f).map a) := by
  letI : QuasiIso ((coneFunctor A f).map a) := quasiIso_coneFunctor_map A f a
  change QuasiIso (((coneFunctor A f).map a)⟦(-1 : ℤ)⟧')
  infer_instance

/-- The shifted cone functor followed by `Q` inverts quasi-isomorphisms. -/
lemma complexFunctor_invertsQuasiIso (A : Type u) [CommRing A] (f : A) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A)
      (ComplexShape.up ℤ)).IsInvertedBy (complexFunctor A f ⋙ DerivedCategory.Q) := by
  intro K L a ha
  letI : QuasiIso a := ha
  change IsIso (DerivedCategory.Q.map ((complexFunctor A f).map a))
  exact Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) _
    (quasiIso_complexFunctor_map A f a)

/-- Local cohomology on the unbounded derived category, obtained without
resolutions from the degreewise localization fibre. -/
noncomputable def derivedFunctor (A : Type u) [CommRing A] (f : A) :
    AffineD A ⥤ AffineD A :=
  Localization.lift (complexFunctor A f ⋙ DerivedCategory.Q)
    (complexFunctor_invertsQuasiIso A f) DerivedCategory.Q

/-- The derived local-cohomology functor is computed by the explicit shifted
cone on cochain-complex representatives. -/
noncomputable def derivedFunctorFactors (A : Type u) [CommRing A] (f : A) :
    DerivedCategory.Q ⋙ derivedFunctor A f ≅ complexFunctor A f ⋙ DerivedCategory.Q :=
  Localization.fac (complexFunctor A f ⋙ DerivedCategory.Q)
    (complexFunctor_invertsQuasiIso A f) DerivedCategory.Q

/-- On a complex coming from `A[1/f]`, the degreewise localization map is
an isomorphism. -/
lemma isIso_localizationMap_restrictScalars (A : Type u) [CommRing A] (f : A)
    (Y : CochainComplex (ModuleCat.{u} (Away A f)) ℤ) :
    IsIso (localizationMap A f
      (((ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Y)) := by
  letI : ∀ n, IsIso ((localizationMap A f
      (((ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Y)).f n) := by
    intro n
    change IsIso ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).unit.app
        ((ModuleCat.restrictScalars (algebraMap A (Away A f))).obj (Y.X n)))
    exact unit_isIso_restrictScalars A f (Y.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The explicit local-cohomology complex is acyclic on any complex coming
from the open localization. -/
lemma isZero_Q_complexFunctor_restrictScalars (A : Type u) [CommRing A] (f : A)
    (Y : CochainComplex (ModuleCat.{u} (Away A f)) ℤ) :
    IsZero (DerivedCategory.Q.obj ((complexFunctor A f).obj
      (((ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Y))) := by
  letI := isIso_localizationMap_restrictScalars A f Y
  let φ := localizationMap A f
    (((ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Y)
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle φ)
  have hT : T ∈ distTriang (AffineD A) :=
    DerivedCategory.mappingCocone_triangle_distinguished φ
  change IsZero T.obj₁
  haveI : IsIso T.mor₂ := by
    change IsIso (DerivedCategory.Q.map φ)
    infer_instance
  exact T.isZero₁_of_isIso₂ hT inferInstance

/-- Derived local cohomology vanishes on a complex representative of an object
pulled back from the open localization. -/
lemma isZero_derivedFunctor_restriction_Q (A : Type u) [CommRing A] (f : A)
    (Y : CochainComplex (ModuleCat.{u} (Away A f)) ℤ) :
    IsZero ((derivedFunctor A f).obj
      ((derivedRestrictionScalars A f).obj (DerivedCategory.Q.obj Y))) := by
  exact (isZero_Q_complexFunctor_restrictScalars A f Y).of_iso
    ((derivedFunctor A f).mapIso
      ((derivedRestrictionScalarsFactors A f).app Y) ≪≫
      (derivedFunctorFactors A f).app
        (((ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Y))

/-- Derived local cohomology vanishes on every object coming from the open
localization. -/
lemma isZero_derivedFunctor_restriction (A : Type u) [CommRing A] (f : A)
    (X : AffineD (Away A f)) :
    IsZero ((derivedFunctor A f).obj ((derivedRestrictionScalars A f).obj X)) := by
  let Y := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  exact (isZero_derivedFunctor_restriction_Q A f Y).of_iso
    ((derivedFunctor A f).mapIso
      ((derivedRestrictionScalars A f).mapIso e.symm))

/-- If the shifted cone is zero, the original localization map is a
quasi-isomorphism. -/
lemma isIso_Q_localizationMap_of_isZero_Q_complexFunctor
    (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : IsZero (DerivedCategory.Q.obj ((complexFunctor A f).obj K))) :
    IsIso (DerivedCategory.Q.map (localizationMap A f K)) := by
  let φ := localizationMap A f K
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle φ)
  have hT : T ∈ distTriang (AffineD A) :=
    DerivedCategory.mappingCocone_triangle_distinguished φ
  change IsZero T.obj₁ at h
  have h₂ := (T.isZero₁_iff_isIso₂ hT).mp h
  change IsIso (DerivedCategory.Q.map φ) at h₂
  exact h₂

/-- The derived localization unit on a complex representative is an
isomorphism whenever derived local cohomology vanishes. -/
lemma isIso_derived_unit_Q_of_isZero (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : IsZero ((derivedFunctor A f).obj (DerivedCategory.Q.obj K))) :
    IsIso ((derivedExtensionRestrictionAdjunction A f).unit.app
      (DerivedCategory.Q.obj K)) := by
  have hcone : IsZero (DerivedCategory.Q.obj ((complexFunctor A f).obj K)) :=
    h.of_iso ((derivedFunctorFactors A f).app K).symm
  letI := isIso_Q_localizationMap_of_isZero_Q_complexFunctor A f K hcone
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : CatCommSq ((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      (derivedExtensionScalars A f) :=
    ⟨(derivedExtensionScalarsFactors A f).symm⟩
  letI : CatCommSq ((ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      (derivedRestrictionScalars A f) :=
    ⟨(derivedRestrictionScalarsFactors A f).symm⟩
  change IsIso (((Adjunction.mapComplex (ModuleCat.extendRestrictScalarsAdj
      (algebraMap A (Away A f))) (ComplexShape.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} (Away A f)) (ComplexShape.up ℤ))
      (derivedExtensionScalars A f) (derivedRestrictionScalars A f)).unit.app
        (DerivedCategory.Q.obj K))
  haveI : IsIso (DerivedCategory.Q.map
      ((Adjunction.mapComplex (ModuleCat.extendRestrictScalarsAdj
        (algebraMap A (Away A f))) (ComplexShape.up ℤ)).unit.app K)) := by
    change IsIso (DerivedCategory.Q.map (localizationMap A f K))
    infer_instance
  rw [Adjunction.localization_unit_app]
  infer_instance

/-- The derived localization unit is an isomorphism on any object whose local
cohomology vanishes. -/
lemma isIso_derived_unit_of_isZero (A : Type u) [CommRing A] (f : A)
    {X : AffineD A} (h : IsZero ((derivedFunctor A f).obj X)) :
    IsIso ((derivedExtensionRestrictionAdjunction A f).unit.app X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hQ : IsZero ((derivedFunctor A f).obj (DerivedCategory.Q.obj K)) :=
    h.of_iso ((derivedFunctor A f).mapIso e)
  haveI := isIso_derived_unit_Q_of_isZero A f K hQ
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  infer_instance

/-- The mixed open/local-cohomology composite is zero. -/
noncomputable def derivedRestrictionScalars_derivedFunctor_isoZero
    (A : Type u) [CommRing A] (f : A) :
    derivedRestrictionScalars A f ⋙ derivedFunctor A f ≅ 0 :=
  NatIso.ofComponents
    (fun X ↦ IsZero.iso (isZero_derivedFunctor_restriction A f X)
      (Functor.zero_obj X))
    (fun {X _ } _ ↦ (isZero_derivedFunctor_restriction A f X).eq_of_src _ _)

/-- Extension of scalars turns every localization unit into an isomorphism. -/
lemma isIso_extendScalars_localizationMap (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso (((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (localizationMap A f K)) := by
  letI : ∀ n, IsIso ((((ModuleCat.extendScalars
      (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (localizationMap A f K)).f n) := by
    intro n
    change IsIso ((ModuleCat.extendScalars (algebraMap A (Away A f))).map
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
        (algebraMap A (Away A f))).unit.app (K.X n)))
    exact IsIso.of_isIso_fac_right
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
        (algebraMap A (Away A f))).left_triangle_components (K.X n))
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Derived extension of scalars also turns the localization map into an
isomorphism. -/
lemma isIso_derivedExtensionScalars_localizationMap
    (A : Type u) [CommRing A] (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso ((derivedExtensionScalars A f).map
      (DerivedCategory.Q.map (localizationMap A f K))) := by
  letI := isIso_extendScalars_localizationMap A f K
  haveI : IsIso ((derivedExtensionScalarsFactors A f).hom.app K ≫
      ((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).map (localizationMap A f K)) := by
    change IsIso ((derivedExtensionScalarsFactors A f).hom.app K ≫
      DerivedCategory.Q.map
        (((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (localizationMap A f K)))
    infer_instance
  exact IsIso.of_isIso_fac_right
    ((derivedExtensionScalarsFactors A f).hom.naturality (localizationMap A f K))

/-- Applying derived extension of scalars to explicit local cohomology gives
zero on complex representatives. -/
lemma isZero_derivedExtensionScalars_derivedFunctor_Q
    (A : Type u) [CommRing A] (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsZero ((derivedExtensionScalars A f).obj
      ((derivedFunctor A f).obj (DerivedCategory.Q.obj K))) := by
  let φ := localizationMap A f K
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle φ)
  have hT : T ∈ distTriang (AffineD A) :=
    DerivedCategory.mappingCocone_triangle_distinguished φ
  let LT := (derivedExtensionScalars A f).mapTriangle.obj T
  have hLT : LT ∈ distTriang (AffineD (Away A f)) :=
    (derivedExtensionScalars A f).map_distinguished T hT
  have hzero : IsZero LT.obj₁ := by
    haveI : IsIso LT.mor₂ := by
      change IsIso ((derivedExtensionScalars A f).map (DerivedCategory.Q.map φ))
      exact isIso_derivedExtensionScalars_localizationMap A f K
    exact LT.isZero₁_of_isIso₂ hLT inferInstance
  exact hzero.of_iso ((derivedExtensionScalars A f).mapIso
    ((derivedFunctorFactors A f).app K))

/-- Derived extension of scalars kills explicit local cohomology on every
object. -/
lemma isZero_derivedExtensionScalars_derivedFunctor
    (A : Type u) [CommRing A] (f : A) (X : AffineD A) :
    IsZero ((derivedExtensionScalars A f).obj ((derivedFunctor A f).obj X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  exact (isZero_derivedExtensionScalars_derivedFunctor_Q A f K).of_iso
    ((derivedExtensionScalars A f).mapIso ((derivedFunctor A f).mapIso e)).symm

/-- The other mixed open/local-cohomology composite is zero. -/
noncomputable def derivedExtensionScalars_derivedFunctor_isoZero
    (A : Type u) [CommRing A] (f : A) :
    derivedFunctor A f ⋙ derivedExtensionScalars A f ≅ 0 :=
  NatIso.ofComponents
    (fun X ↦ IsZero.iso (isZero_derivedExtensionScalars_derivedFunctor A f X)
      (Functor.zero_obj X))
    (fun {X _ } _ ↦ (isZero_derivedExtensionScalars_derivedFunctor A f X).eq_of_src _ _)

/-- The kernel of explicit local cohomology is exactly the essential image of
restriction of scalars from the open localization. -/
lemma derivedFunctor_kernel (A : Type u) [CommRing A] (f : A) (X : AffineD A) :
    Nonempty ((derivedFunctor A f).obj X ≅ 0) ↔
      ∃ Y : AffineD (Away A f),
        Nonempty (X ≅ (derivedRestrictionScalars A f).obj Y) := by
  constructor
  · rintro ⟨e⟩
    have hX : IsZero ((derivedFunctor A f).obj X) := (isZero_zero _).of_iso e
    letI := isIso_derived_unit_of_isZero A f hX
    exact ⟨derivedExtensionScalars A f |>.obj X,
      ⟨asIso ((derivedExtensionRestrictionAdjunction A f).unit.app X)⟩⟩
  · rintro ⟨Y, ⟨e⟩⟩
    exact ⟨(derivedFunctor A f).mapIso e ≪≫
      IsZero.iso (isZero_derivedFunctor_restriction A f Y) (isZero_zero _)⟩

/-- The canonical componentwise map from the shifted cone to `K`.
Naturality is deliberately left for a later triangle-level proof. -/
noncomputable abbrev complexCounitApp (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (complexFunctor A f).obj K ⟶ K :=
  CochainComplex.mappingCocone.fst (localizationMap A f K)

#print axioms unit_isIso_restrictScalars
#print axioms powerTorsion_homology_obj₁_of_triangle
#print axioms quasiIso_openComplexMap
#print axioms quasiIso_coneFunctor_map
#print axioms isZero_derivedFunctor_restriction
#print axioms derivedRestrictionScalars_derivedFunctor_isoZero
#print axioms isIso_derived_unit_of_isZero
#print axioms derivedFunctor_kernel
#print axioms derivedExtensionScalars_derivedFunctor_isoZero
#print axioms quasiIso_complexFunctor_map
#print axioms coneFunctor
#print axioms complexFunctor
#print axioms complexFunctorObjIso
#print axioms derivedFunctor
#print axioms derivedFunctorFactors

end AffineLocalCohomology

end
end RelativeFM
