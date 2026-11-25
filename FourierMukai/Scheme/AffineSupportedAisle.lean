import FourierMukai.Scheme.AffineSupportedTStructure
import FourierMukai.Scheme.PerfectRing
import WeakApprox.Setup44
import WeakApprox.Lemma4323
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Tactic

@[expose] public section

namespace RelativeFM.SupportedAisleM6

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe w₁ w₂ v₁ v₂ u₁ u₂ u w v

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- An exact additive functor between abelian categories preserves the
standard cohomological upper bound. -/
lemma isLE_mapDerivedCategory
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C₁) (n : ℤ) (hX : X.IsLE n) :
    (F.mapDerivedCategory.obj X).IsLE n := by
  obtain ⟨K, e, hK⟩ := hX
  have hFK : CochainComplex.IsStrictlyLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact F.map_isZero (K.isZero_of_isStrictlyLE n i hi)
  exact ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K, hFK⟩

/-- Derived restriction of scalars along `A → A[1/f]` preserves the standard
upper cohomological bound. -/
lemma isLE_derivedRestrictionScalars (A : Type u) [CommRing A] (f : A)
    (X : AffineD (Away A f)) (n : ℤ) (hX : X.IsLE n) :
    ((derivedRestrictionScalars A f).obj X).IsLE n := by
  exact isLE_mapDerivedCategory
    (ModuleCat.restrictScalars (algebraMap A (Away A f))) X n hX

/-- Derived extension of scalars along `A → A[1/f]` preserves the standard
upper cohomological bound. Flatness supplies exactness. -/
lemma isLE_derivedExtensionScalars (A : Type u) [CommRing A] (f : A)
    (X : AffineD A) (n : ℤ) (hX : X.IsLE n) :
    ((derivedExtensionScalars A f).obj X).IsLE n := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact isLE_mapDerivedCategory
    (ModuleCat.extendScalars (algebraMap A (Away A f))) X n hX

/-- The regular module in degree zero has the expected standard bound. -/
lemma ringObject_isLE_zero (A : Type u) [CommRing A] :
    (ringObject A).IsLE 0 := by
  unfold ringObject
  infer_instance

/-- The regular module and its open localization are both in degree at most
zero. Consequently `RΓ_Z(A)[1]` is in degree at most zero: it is the middle
object of the twice-rotated first gluing triangle. -/
lemma isLE_localCohomology_ringObject_shift (A : Type u) [CommRing A] (f : A) :
    (((AffineLocalCohomology.derivedFunctor A f).obj (ringObject A))⟦(1 : ℤ)⟧).IsLE 0 := by
  let t : TStructure (AffineD A) := DerivedCategory.TStructure.t
  let T := AffineLocalCohomology.derivedFirstTriangle A f (ringObject A)
  have hT : T ∈ distTriang (AffineD A) :=
    AffineLocalCohomology.derivedFirstTriangle_distinguished A f (ringObject A)
  have hA : t.le 0 (ringObject A) := by
    change DerivedCategory.TStructure.t.le 0 (ringObject A)
    exact (ringObject_isLE_zero A).le
  have hOpen : t.le 0
      ((derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f).obj (ringObject A)) := by
    change DerivedCategory.TStructure.t.le 0
      ((derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f).obj (ringObject A))
    exact (isLE_derivedRestrictionScalars A f _ 0
      (isLE_derivedExtensionScalars A f _ 0 (ringObject_isLE_zero A))).le
  have hAshift : t.le 0 ((ringObject A)⟦(1 : ℤ)⟧) :=
    t.le_monotone (show (-1 : ℤ) ≤ 0 by omega) _
      (t.le_shift 0 1 (-1) (by omega) _ hA)
  have h := t.isLE₂ T.rotate.rotate
    (rot_of_distTriang _ (rot_of_distTriang _ hT)) 0 ⟨hOpen⟩ ⟨hAshift⟩
  exact ⟨h.le⟩

/-- Local cohomology shifted by one preserves every standard upper bound.
The open-localization term has the same bound by exact extension/restriction,
so the claim follows from the twice-rotated first gluing triangle. -/
lemma isLE_localCohomology_shift (A : Type u) [CommRing A] (f : A)
    (X : AffineD A) (n : ℤ) (hX : X.IsLE n) :
    (((AffineLocalCohomology.derivedFunctor A f).obj X)⟦(1 : ℤ)⟧).IsLE n := by
  let t : TStructure (AffineD A) := DerivedCategory.TStructure.t
  let T := AffineLocalCohomology.derivedFirstTriangle A f X
  have hT : T ∈ distTriang (AffineD A) :=
    AffineLocalCohomology.derivedFirstTriangle_distinguished A f X
  have hXle : t.le n X := by
    change DerivedCategory.TStructure.t.le n X
    exact hX.le
  have hOpen : t.le n
      ((derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f).obj X) := by
    change DerivedCategory.TStructure.t.le n
      ((derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f).obj X)
    exact (isLE_derivedRestrictionScalars A f _ n
      (isLE_derivedExtensionScalars A f X n hX)).le
  have hXshift : t.le n (X⟦(1 : ℤ)⟧) :=
    t.le_monotone (show n - 1 ≤ n by omega) _
      (t.le_shift n 1 (n - 1) (by omega) _ hXle)
  exact t.isLE₂ T.rotate.rotate
    (rot_of_distTriang _ (rot_of_distTriang _ hT)) n ⟨hOpen⟩ ⟨hXshift⟩

/-- A local-cohomology candidate for supported aisle generation, shifted
once so that its top cohomology is in degree zero.  This is not asserted to
be compact; `Koszul.supportedGenerator` supplies the perfect alternative. -/
noncomputable def supportedAisleGenerator (A : Type u) [CommRing A] (f : A) : AffineDZ A f :=
  ((AffineLocalCohomology.jStar A f).obj (ringObject A))⟦(1 : ℤ)⟧

/-- The candidate supported generator lies in the degree-zero aisle of the
induced standard `t`-structure. -/
lemma supportedAisleGenerator_mem_le_zero (A : Type u) [CommRing A] (f : A) :
    (Recollement.AssemblyM6.affineDZStandardTStructure A f).le 0
      (supportedAisleGenerator A f) := by
  change (AffineD.standardTStructure A).le 0 ((supportedAisleGenerator A f).obj)
  let e : (supportedAisleGenerator A f).obj ≅
      ((AffineLocalCohomology.derivedFunctor A f).obj (ringObject A))⟦(1 : ℤ)⟧ :=
    ((affineDZι A f).commShiftIso (1 : ℤ)).app
        ((AffineLocalCohomology.jStar A f).obj (ringObject A)) ≪≫
      (shiftFunctor (AffineD A) (1 : ℤ)).mapIso
        ((AffineLocalCohomology.jStarFactors A f).app (ringObject A))
  apply (AffineD.standardTStructure A).le 0 |>.prop_of_iso e.symm
  change DerivedCategory.TStructure.t.le 0
    (((AffineLocalCohomology.derivedFunctor A f).obj (ringObject A))⟦(1 : ℤ)⟧)
  exact (isLE_localCohomology_ringObject_shift A f).le

/-- The easy inclusion in compact generation of an aisle. No coproduct
existence hypothesis is needed: aisles are closed under every existent
colimit, by orthogonality. -/
lemma coprod_shiftTail_le {C : Type u} [Category.{v₁} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (t : TStructure C) (H : C) (hH : t.le 0 H) :
    Coprod (shiftTail H 0) ≤ t.le 0 := by
  letI (J : Type v₁) : (t.le 0).IsClosedUnderColimitsOfShape (Discrete J) :=
    TStructure.le_isClosedUnderColimitsOfShape t 0 (Discrete J)
  letI : (t.le 0).IsTriangulatedClosed₂ :=
    TStructure.le_isTriangulatedClosed₂ t 0
  apply Coprod.le
  rintro X ⟨n, hn, ⟨e⟩⟩
  apply (t.le 0).prop_of_iso e.symm
  exact t.le_monotone (show -n ≤ 0 by omega) _
    (t.le_shift 0 n (-n) (by omega) H hH)

/-- Specialization of the easy inclusion to the supported standard aisle. -/
lemma supported_coprod_shiftTail_le (A : Type u) [CommRing A] (f : A) :
    Coprod (shiftTail (supportedAisleGenerator A f) 0) ≤
      (Recollement.AssemblyM6.affineDZStandardTStructure A f).le 0 :=
  coprod_shiftTail_le _ _ (supportedAisleGenerator_mem_le_zero A f)

/-- The degree-n supported aisle is definitionally the restriction of the
ambient degree-n aisle to supported objects. -/
lemma mem_supported_le_iff (A : Type u) [CommRing A] (f : A)
    (X : AffineDZ A f) (n : ℤ) :
    (Recollement.AssemblyM6.affineDZStandardTStructure A f).le n X ↔
      (AffineD.standardTStructure A).le n X.obj := Iff.rfl

/-- The supported inclusion is coreflective: its right adjoint is the explicit
local-cohomology functor. -/
noncomputable instance affineDZι_coreflective (A : Type u) [CommRing A] (f : A) :
    Coreflective (affineDZι A f) where
  R := AffineLocalCohomology.jStar A f
  adj := AffineLocalCohomology.jShriekAdj A f

/-- A coreflective full subcategory has every colimit shape available in the
ambient category. -/
noncomputable def affineDZ_hasColimitsOfShape (A : Type u) [CommRing A] (f : A)
    (J : Type w) [Category.{v} J] [HasColimitsOfShape J (AffineD A)] :
    HasColimitsOfShape J (AffineDZ A f) :=
  hasColimitsOfShape_of_coreflective (affineDZι A f)

/-- In particular, ambient small coproducts give small coproducts in the
supported category. -/
noncomputable def affineDZ_hasCoproducts (A : Type u) [CommRing A] (f : A)
    [HasCoproducts.{w} (AffineD A)] : HasCoproducts.{w} (AffineDZ A f) :=
  fun J => affineDZ_hasColimitsOfShape A f (Discrete J)

/-- The supported inclusion preserves every colimit, since it is a left
adjoint. -/
noncomputable def affineDZι_preservesColimitsOfShape
    (A : Type u) [CommRing A] (f : A) (J : Type w) [Category.{v} J] :
    PreservesColimitsOfShape J (affineDZι A f) :=
  (AffineLocalCohomology.jShriekAdj A f).leftAdjoint_preservesColimits.preservesColimitsOfShape

/-- Consequently the supported object property is closed under every ambient
colimit shape for which the ambient category has colimits. -/
noncomputable def affineIsSupported_isClosedUnderColimitsOfShape
    (A : Type u) [CommRing A] (f : A) (J : Type w) [Category.{v} J]
    [HasColimitsOfShape J (AffineD A)] :
    (AffineIsSupported A f).IsClosedUnderColimitsOfShape J := by
  letI : HasColimitsOfShape J (AffineDZ A f) := affineDZ_hasColimitsOfShape A f J
  letI : PreservesColimitsOfShape J (affineDZι A f) :=
    affineDZι_preservesColimitsOfShape A f J
  letI : (AffineIsSupported A f).IsClosedUnderIsomorphisms := by
    unfold AffineIsSupported
    infer_instance
  exact ObjectProperty.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι
    (AffineIsSupported A f) J

/-- The supported `Coprod` construction maps into the ambient `Coprod`
construction on the underlying generator.  The proof is induction on the
inductive closure; the colimit step uses preservation by the left-adjoint
supported inclusion. -/
lemma map_supported_coprod {A : Type u} [CommRing A] {f : A}
    (GU : AffineDZ A f) {X : AffineDZ A f}
    (hX : Coprod (shiftTail GU 0) X) :
    Coprod (shiftTail GU.obj 0) X.obj := by
  refine coprod_map_le (affineDZι A f)
    (fun J => (AffineLocalCohomology.jShriekAdj A f).leftAdjoint_preservesColimits.preservesColimitsOfShape)
    (P := shiftTail GU 0) (Q := Coprod (shiftTail GU.obj 0)) (Y := X) ?_ hX
  intro Y hY
  obtain ⟨n, hn, ⟨e⟩⟩ := hY
  exact Coprod.of_mem _ ⟨n, hn,
    ⟨(affineDZι A f).mapIso e ≪≫ ((affineDZι A f).commShiftIso n).app GU⟩⟩

end
end RelativeFM.SupportedAisleM6

#print axioms RelativeFM.SupportedAisleM6.isLE_mapDerivedCategory
#print axioms RelativeFM.SupportedAisleM6.isLE_derivedRestrictionScalars
#print axioms RelativeFM.SupportedAisleM6.isLE_derivedExtensionScalars
#print axioms RelativeFM.SupportedAisleM6.isLE_localCohomology_ringObject_shift
#print axioms RelativeFM.SupportedAisleM6.supportedAisleGenerator_mem_le_zero
#print axioms RelativeFM.SupportedAisleM6.coprod_shiftTail_le
#print axioms RelativeFM.SupportedAisleM6.supported_coprod_shiftTail_le
#print axioms RelativeFM.SupportedAisleM6.affineDZ_hasColimitsOfShape
#print axioms RelativeFM.SupportedAisleM6.affineDZ_hasCoproducts
#print axioms RelativeFM.SupportedAisleM6.affineIsSupported_isClosedUnderColimitsOfShape
#print axioms RelativeFM.SupportedAisleM6.map_supported_coprod
#print axioms RelativeFM.SupportedAisleM6.isLE_localCohomology_shift
