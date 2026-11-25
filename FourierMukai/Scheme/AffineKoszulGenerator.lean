import FourierMukai.Scheme.AffineSupportedCoprodLift

@[expose] public section

namespace RelativeFM.SupportedAisleM6.Koszul

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open scoped ChangeOfRings

universe u₁ u₂ u v

noncomputable section

set_option maxHeartbeats 400000

attribute [local instance] HasDerivedCategory.standard

/-- Multiplication by a ring element on the regular module. -/
def regularMultiplication (A : Type u₁) [CommRing A] (f : A) :
    ModuleCat.of A A ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (LinearMap.lsmul A _ f)

/-- Extension of scalars turns regular multiplication by `f` into scalar
multiplication by the image of `f`. -/
lemma extendScalars_map_regularMultiplication
    {A : Type u₁} [CommRing A] {B : Type u₂} [CommRing B]
    (φ : A →+* B) (f : A) :
    (ModuleCat.extendScalars φ).map (regularMultiplication A f) =
      φ f • 𝟙 ((ModuleCat.extendScalars φ).obj (ModuleCat.of A A)) := by
  letI := φ.toAlgebra
  letI : Module B (TensorProduct A B (ModuleCat.of A A)) :=
    inferInstanceAs (Module B ((ModuleCat.extendScalars φ).obj (ModuleCat.of A A)))
  apply ModuleCat.ExtendScalars.hom_ext
  intro a
  change (1 : B) ⊗ₜ[A,φ] (f * a) =
    φ f • ((1 : B) ⊗ₜ[A,φ] a)
  rw [show f * a = f • a by rfl, TensorProduct.tmul_smul,
    ← IsScalarTower.algebraMap_smul B f]
  rfl

/-- Scalar multiplication on a module by a unit is an isomorphism. -/
lemma isIso_smul_id_of_isUnit {B : Type u₂} [CommRing B]
    (N : ModuleCat.{v} B) (b : B) (hb : IsUnit b) :
    IsIso (b • 𝟙 N) := by
  have hbij : Function.Bijective (fun x : N => b • x) := hb.smul_bijective
  letI : Mono (b • 𝟙 N) := (ModuleCat.mono_iff_injective _).mpr hbij.injective
  letI : Epi (b • 𝟙 N) := (ModuleCat.epi_iff_surjective _).mpr hbij.surjective
  exact isIso_of_mono_of_epi _

/-- In particular, regular multiplication becomes invertible after extension
of scalars whenever its defining element becomes a unit. -/
lemma isIso_extendScalars_map_regularMultiplication
    {A : Type u₁} [CommRing A] {B : Type u₂} [CommRing B]
    (φ : A →+* B) (f : A) (hf : IsUnit (φ f)) :
    IsIso ((ModuleCat.extendScalars φ).map (regularMultiplication A f)) := by
  rw [extendScalars_map_regularMultiplication]
  exact isIso_smul_id_of_isUnit _ _ hf

/-- Multiplication by `f` on the derived regular module in degree zero. -/
noncomputable def derivedMultiplication (A : Type u) [CommRing A] (f : A) :
    ringObject A ⟶ ringObject A :=
  (DerivedCategory.singleFunctor (ModuleCat A) 0).map (regularMultiplication A f)

/-- Derived extension to `A[1/f]` makes derived multiplication by `f` an
isomorphism. -/
lemma isIso_derivedExtensionScalars_derivedMultiplication
    (A : Type u) [CommRing A] (f : A) :
    IsIso ((derivedExtensionScalars A f).map (derivedMultiplication A f)) := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let F := ModuleCat.extendScalars (algebraMap A (Away A f))
  let e := F.mapDerivedCategorySingleFunctor 0
  letI : IsIso (e.hom.app (ModuleCat.of A A)) := NatIso.hom_app_isIso e _
  letI : IsIso (e.inv.app (ModuleCat.of A A)) := NatIso.inv_app_isIso e _
  haveI : IsIso ((DerivedCategory.singleFunctor (ModuleCat.{u} (Away A f)) 0).map
      (F.map (regularMultiplication A f))) := by
    letI : IsIso (F.map (regularMultiplication A f)) :=
      isIso_extendScalars_map_regularMultiplication (algebraMap A (Away A f)) f
        (IsLocalization.map_units (M := Submonoid.powers f)
          (Away A f) ⟨f, 1, by simp⟩)
    infer_instance
  haveI : IsIso (F.mapDerivedCategory.map (derivedMultiplication A f) ≫
      e.hom.app (ModuleCat.of A A)) := by
    change IsIso (((DerivedCategory.singleFunctor (ModuleCat A) 0) ⋙
      F.mapDerivedCategory).map (regularMultiplication A f) ≫
      e.hom.app (ModuleCat.of A A))
    rw [e.hom.naturality]
    change IsIso (e.hom.app (ModuleCat.of A A) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Away A f)) 0).map
        (F.map (regularMultiplication A f)))
    infer_instance
  have heq : F.mapDerivedCategory.map
      ((DerivedCategory.singleFunctor (ModuleCat A) 0).map (regularMultiplication A f)) =
      e.hom.app (ModuleCat.of A A) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} (Away A f)) 0).map
          (F.map (regularMultiplication A f)) ≫
        e.inv.app (ModuleCat.of A A) := by
    rw [← cancel_mono (e.hom.app (ModuleCat.of A A))]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact e.hom.naturality (regularMultiplication A f)
  change IsIso (F.mapDerivedCategory.map
    ((DerivedCategory.singleFunctor (ModuleCat A) 0).map (regularMultiplication A f)))
  rw [heq]
  infer_instance

/-- If derived extension to `A[1/f]` kills a complex, then all of its
cohomology modules are `f`-power torsion. -/
lemma affineIsSupported_of_isZero_derivedExtensionScalars
    (A : Type u) [CommRing A] (f : A) {X : AffineD A}
    (hX : IsZero ((derivedExtensionScalars A f).obj X)) :
    AffineIsSupported A f X := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  intro n
  apply AffineLocalCohomology.powerTorsion_of_isZero_extendScalars A f
  have hzero : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Away A f)) n).obj ((derivedExtensionScalars A f).obj X)) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (Away A f)) n).map_isZero hX
  exact hzero.of_iso
    (mapDerivedCategoryHomologyIso
      (ModuleCat.extendScalars (algebraMap A (Away A f))) X n).symm

/-- A chosen perfect cone of multiplication by `f` on the regular module.
This is the Koszul complex of `f`, in the convention
`A[0] --f--> A[0] --> K(f) --> A[0][1]`. -/
structure ConeData (A : Type u) [CommRing A] (f : A) where
  obj : AffineD A
  perfect : Perf A obj
  second : ringObject A ⟶ obj
  third : obj ⟶ ringObject A⟦(1 : ℤ)⟧
  distinguished : Triangle.mk (derivedMultiplication A f) second third ∈
    distTriang (AffineD A)

/-- The perfect cone exists by triangulated closure of perfect complexes. -/
noncomputable def coneData (A : Type u) [CommRing A] (f : A) : ConeData A f := by
  let h := perf_exists_cone (A := A) (derivedMultiplication A f)
    (ringObject_mem_perf A) (ringObject_mem_perf A)
  exact
    { obj := h.choose
      perfect := h.choose_spec.choose
      second := h.choose_spec.choose_spec.choose
      third := h.choose_spec.choose_spec.choose_spec.choose
      distinguished := h.choose_spec.choose_spec.choose_spec.choose_spec }

/-- The Koszul cone has `f`-power-torsion cohomology: multiplication by `f`
becomes an isomorphism after localization, so its cone localizes to zero. -/
lemma coneData_obj_isSupported (A : Type u) [CommRing A] (f : A) :
    AffineIsSupported A f (coneData A f).obj := by
  apply affineIsSupported_of_isZero_derivedExtensionScalars A f
  apply Triangle.isZero₃_of_isIso₁ ((derivedExtensionScalars A f).mapTriangle.obj
    (Triangle.mk (derivedMultiplication A f) (coneData A f).second (coneData A f).third))
    ((derivedExtensionScalars A f).map_distinguished _ (coneData A f).distinguished)
  exact isIso_derivedExtensionScalars_derivedMultiplication A f

/-- The Koszul cone lies in the standard degree-zero aisle. -/
lemma coneData_obj_mem_le_zero (A : Type u) [CommRing A] (f : A) :
    (AffineD.standardTStructure A).le 0 (coneData A f).obj := by
  let t : TStructure (AffineD A) := DerivedCategory.TStructure.t
  let T := Triangle.mk (derivedMultiplication A f) (coneData A f).second (coneData A f).third
  have hA : t.le 0 (ringObject A) := by
    change DerivedCategory.TStructure.t.le 0 (ringObject A)
    exact (ringObject_isLE_zero A).le
  have hAshift : t.le 0 ((ringObject A)⟦(1 : ℤ)⟧) :=
    t.le_monotone (show (-1 : ℤ) ≤ 0 by omega) _
      (t.le_shift 0 1 (-1) (by omega) _ hA)
  exact (t.isLE₂ T.rotate (rot_of_distTriang _ (coneData A f).distinguished) 0
    ⟨hA⟩ ⟨hAshift⟩).le

/-- The usual compact-generator candidate in the supported category: the
Koszul cone of `f`, not unshifted local cohomology. -/
noncomputable def supportedGenerator (A : Type u) [CommRing A] (f : A) : AffineDZ A f :=
  ⟨(coneData A f).obj, coneData_obj_isSupported A f⟩

lemma supportedGenerator_obj_perf (A : Type u) [CommRing A] (f : A) :
    Perf A (supportedGenerator A f).obj :=
  (coneData A f).perfect

lemma supportedGenerator_mem_le_zero (A : Type u) [CommRing A] (f : A) :
    (Recollement.AssemblyM6.affineDZStandardTStructure A f).le 0
      (supportedGenerator A f) :=
  coneData_obj_mem_le_zero A f

/-- The easy inclusion for the Koszul-generated supported aisle. -/
lemma supported_coprod_shiftTail_le (A : Type u) [CommRing A] (f : A) :
    Coprod (shiftTail (supportedGenerator A f) 0) ≤
      (Recollement.AssemblyM6.affineDZStandardTStructure A f).le 0 :=
  SupportedAisleM6.coprod_shiftTail_le _ _ (supportedGenerator_mem_le_zero A f)

/-- The Koszul compact-generation field is equivalent to ambient generation
by the Koszul cone on supported objects. -/
lemma supportedGenerator_aisle_eq_coprod_iff (A : Type u) [CommRing A] (f : A)
    [HasCoproducts.{u + 1} (AffineD A)] :
    (Recollement.AssemblyM6.affineDZStandardTStructure A f).le 0 =
        Coprod (shiftTail (supportedGenerator A f) 0) ↔
      ∀ X : AffineDZ A f, (AffineD.standardTStructure A).le 0 X.obj →
        Coprod (shiftTail (coneData A f).obj 0) X.obj := by
  exact SupportedAisleM6.supported_standard_aisle_eq_coprod_iff A f
    (supportedGenerator A f) (supportedGenerator_mem_le_zero A f)

end
end RelativeFM.SupportedAisleM6.Koszul

#print axioms RelativeFM.SupportedAisleM6.Koszul.extendScalars_map_regularMultiplication
#print axioms RelativeFM.SupportedAisleM6.Koszul.isIso_smul_id_of_isUnit
#print axioms RelativeFM.SupportedAisleM6.Koszul.isIso_derivedExtensionScalars_derivedMultiplication
#print axioms RelativeFM.SupportedAisleM6.Koszul.affineIsSupported_of_isZero_derivedExtensionScalars
#print axioms RelativeFM.SupportedAisleM6.Koszul.coneData_obj_isSupported
#print axioms RelativeFM.SupportedAisleM6.Koszul.coneData_obj_mem_le_zero
#print axioms RelativeFM.SupportedAisleM6.Koszul.supportedGenerator_obj_perf
#print axioms RelativeFM.SupportedAisleM6.Koszul.supportedGenerator_mem_le_zero
#print axioms RelativeFM.SupportedAisleM6.Koszul.supported_coprod_shiftTail_le
#print axioms RelativeFM.SupportedAisleM6.Koszul.supportedGenerator_aisle_eq_coprod_iff
