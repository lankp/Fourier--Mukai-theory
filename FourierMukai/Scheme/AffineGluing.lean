import FourierMukai.Scheme.AffineLocalCohomology
import Mathlib.CategoryTheory.Triangulated.Orthogonal

@[expose] public section

namespace RelativeFM.AffineLocalCohomology

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe u

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] HasDerivedCategory.standard

/-- The canonical map from explicit local cohomology to the identity, before
passing to the derived category. -/
noncomputable def complexCounit (A : Type u) [CommRing A] (f : A) :
    complexFunctor A f ⟶ 𝟭 (CochainComplex (ModuleCat.{u} A) ℤ) where
  app K := complexCounitApp A f K
  naturality := by
    intro K L a
    apply HomologicalComplex.Hom.ext
    funext n
    simp [complexFunctor, coneFunctor, complexCounitApp,
      CochainComplex.mappingCocone.fst, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.desc_f,
      CochainComplex.HomComplex.Cocycle.leftShift_coe]
    rw [CochainComplex.HomComplex.Cochain.leftShift_v
      (n := 1) _ (-1) 0 (by omega) n n (by omega) (n + -1) (by omega)]
    rw [CochainComplex.HomComplex.Cochain.leftShift_v
      (n := 1) _ (-1) 0 (by omega) n n (by omega) (n + -1) (by omega)]
    simp

/-- The canonical derived natural transformation `RΓ_Z → id`. -/
noncomputable def derivedCounit (A : Type u) [CommRing A] (f : A) :
    derivedFunctor A f ⟶ 𝟭 (AffineD A) := by
  letI := Localization.full_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) (AffineD A)
  exact ((Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q).preimage
    ((derivedFunctorFactors A f).hom ≫
      Functor.whiskerRight (complexCounit A f) DerivedCategory.Q ≫
      (Functor.leftUnitor DerivedCategory.Q).hom ≫
      (Functor.rightUnitor DerivedCategory.Q).inv)

@[simp] lemma derivedCounit_app_Q (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (derivedCounit A f).app (DerivedCategory.Q.obj K) =
      (derivedFunctorFactors A f).hom.app K ≫
        DerivedCategory.Q.map (complexCounitApp A f K) := by
  letI := Localization.full_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) (AffineD A)
  have h := NatTrans.congr_app
    (Functor.map_preimage ((Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q)
      ((derivedFunctorFactors A f).hom ≫
        Functor.whiskerRight (complexCounit A f) DerivedCategory.Q ≫
        (Functor.leftUnitor DerivedCategory.Q).hom ≫
        (Functor.rightUnitor DerivedCategory.Q).inv)) K
  simpa [derivedCounit, complexCounit] using h

/-- The connecting morphism of the explicit localization triangle, before
passing to the derived category. -/
noncomputable def complexConnecting (A : Type u) [CommRing A] (f : A) :
    ((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙
      (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⟶
      complexFunctor A f ⋙ shiftFunctor _ (1 : ℤ) where
  app K := (CochainComplex.mappingCocone.triangle (localizationMap A f K)).mor₃
  naturality := by
    intro K L a
    let φK := localizationMap A f K
    let φL := localizationMap A f L
    let b := ((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙
      (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a
    let comm : φK ≫ b = a ≫ φL := (openComplexAdjunction A f).unit.naturality a
    let m := CochainComplex.mappingCone.map φK φL a b comm
    have h : CochainComplex.mappingCone.inr φK ≫ m =
        b ≫ CochainComplex.mappingCone.inr φL :=
      (CochainComplex.mappingCone.triangleMap φK φL a b comm).comm₂
    change b ≫ (CochainComplex.mappingCocone.triangle φL).mor₃ =
      (CochainComplex.mappingCocone.triangle φK).mor₃ ≫ m⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧'
    dsimp only [CochainComplex.mappingCocone.triangle, Triangle.mk_mor₃,
      CochainComplex.mappingCone.triangle_mor₂]
    rw [← Category.assoc, ← h]
    simp only [Category.assoc]
    have hn := (shiftFunctorCompIsoId (CochainComplex (ModuleCat.{u} A) ℤ)
      (-1 : ℤ) 1 (by omega)).inv.naturality m
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [hn]

/-- Compatibility of derived extension followed by restriction with the
corresponding degreewise functor on complexes. -/
noncomputable def derivedOpenFactors (A : Type u) [CommRing A] (f : A) :
    DerivedCategory.Q ⋙ derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f ≅
      ((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
        (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight (derivedExtensionScalarsFactors A f)
      (derivedRestrictionScalars A f) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedRestrictionScalarsFactors A f) ≪≫
    (Functor.associator _ _ _).symm

/-- Compatibility of shifted derived local cohomology with its explicit complex
model. -/
noncomputable def derivedShiftFactors (A : Type u) [CommRing A] (f : A) :
    DerivedCategory.Q ⋙ derivedFunctor A f ⋙ shiftFunctor (AffineD A) (1 : ℤ) ≅
      (complexFunctor A f ⋙ shiftFunctor _ (1 : ℤ)) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight (derivedFunctorFactors A f) (shiftFunctor (AffineD A) (1 : ℤ)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.Q.commShiftIso (1 : ℤ)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The derived connecting transformation `Rj_*Lj^* → RΓ_Z[1]`. -/
noncomputable def derivedConnecting (A : Type u) [CommRing A] (f : A) :
    derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f ⟶
      derivedFunctor A f ⋙ shiftFunctor (AffineD A) (1 : ℤ) := by
  letI := Localization.full_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) (AffineD A)
  exact ((Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q).preimage
    ((derivedOpenFactors A f).hom ≫
      Functor.whiskerRight (complexConnecting A f) DerivedCategory.Q ≫
      (derivedShiftFactors A f).inv)

@[simp] lemma derivedConnecting_app_Q (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (derivedConnecting A f).app (DerivedCategory.Q.obj K) =
      (derivedOpenFactors A f).hom.app K ≫
        DerivedCategory.Q.map ((complexConnecting A f).app K) ≫
        (derivedShiftFactors A f).inv.app K := by
  letI := Localization.full_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) (AffineD A)
  have h := NatTrans.congr_app
    (Functor.map_preimage ((Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q)
      ((derivedOpenFactors A f).hom ≫
        Functor.whiskerRight (complexConnecting A f) DerivedCategory.Q ≫
        (derivedShiftFactors A f).inv)) K
  simpa [derivedConnecting] using h

@[simp] lemma derived_unit_comp_openFactors_hom (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (derivedExtensionRestrictionAdjunction A f).unit.app (DerivedCategory.Q.obj K) ≫
      (derivedOpenFactors A f).hom.app K =
        DerivedCategory.Q.map (localizationMap A f K) := by
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
  change ((((Adjunction.mapComplex (ModuleCat.extendRestrictScalarsAdj
      (algebraMap A (Away A f))) (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} (Away A f)) (ComplexShape.up ℤ))
    (derivedExtensionScalars A f) (derivedRestrictionScalars A f)).unit.app
      (DerivedCategory.Q.obj K)) ≫ (derivedOpenFactors A f).hom.app K = _)
  rw [Adjunction.localization_unit_app]
  simp [derivedOpenFactors]
  change _ ≫ (derivedRestrictionScalarsFactors A f).inv.app _ ≫
    (derivedRestrictionScalars A f).map ((derivedExtensionScalarsFactors A f).inv.app K) ≫
    (derivedRestrictionScalars A f).map ((derivedExtensionScalarsFactors A f).hom.app K) ≫
    (derivedRestrictionScalarsFactors A f).hom.app _ = _
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [(derivedRestrictionScalars A f).map_id
    (((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj K)]
  simp
  rfl

lemma derivedShiftFactors_inv_app (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (derivedShiftFactors A f).inv.app K =
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app ((complexFunctor A f).obj K) ≫
        ((derivedFunctorFactors A f).inv.app K)⟦(1 : ℤ)⟧' := by
  simp [derivedShiftFactors]

/-- The candidate first gluing triangle in the derived category. -/
noncomputable def derivedFirstTriangle (A : Type u) [CommRing A] (f : A)
    (X : AffineD A) : Triangle (AffineD A) :=
  Triangle.mk ((derivedCounit A f).app X)
    ((derivedExtensionRestrictionAdjunction A f).unit.app X)
    ((derivedConnecting A f).app X)

/-- On a complex representative, the first gluing triangle is isomorphic to the
mapping-cocone triangle of the localization unit. -/
noncomputable def derivedFirstTriangleIsoQ (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    derivedFirstTriangle A f (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCocone.triangle (localizationMap A f K)) := by
  refine Triangle.isoMk _ _ ((derivedFunctorFactors A f).app K) (Iso.refl _)
    ((derivedOpenFactors A f).app K) ?_ ?_ ?_
  · simp [derivedFirstTriangle]
  · simp [derivedFirstTriangle]
  · simp [derivedFirstTriangle, derivedShiftFactors]
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    rw [(shiftFunctor (AffineD A) (1 : ℤ)).map_id
      ((complexFunctor A f ⋙ DerivedCategory.Q).obj K)]
    simp [complexConnecting]
    rfl

/-- Naturality of the first gluing triangle. -/
def derivedFirstTriangleMap (A : Type u) [CommRing A] (f : A)
    {X Y : AffineD A} (a : X ⟶ Y) :
    derivedFirstTriangle A f X ⟶ derivedFirstTriangle A f Y where
  hom₁ := (derivedFunctor A f).map a
  hom₂ := a
  hom₃ := (derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f).map a
  comm₁ := by
    exact (derivedCounit A f).naturality a |>.symm
  comm₂ := by
    exact (derivedExtensionRestrictionAdjunction A f).unit.naturality a |>.symm
  comm₃ := by
    exact (derivedConnecting A f).naturality a |>.symm

/-- The first gluing triangle as a functor. -/
def derivedFirstTriangleFunctor (A : Type u) [CommRing A] (f : A) :
    AffineD A ⥤ Triangle (AffineD A) where
  obj := derivedFirstTriangle A f
  map := derivedFirstTriangleMap A f
  map_id X := by
    ext <;> simp [derivedFirstTriangleMap, derivedFirstTriangle]
  map_comp a b := by
    ext <;> simp [derivedFirstTriangleMap, derivedFirstTriangle]

/-- The first gluing triangle is distinguished on complex representatives. -/
lemma derivedFirstTriangle_distinguished_Q (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    derivedFirstTriangle A f (DerivedCategory.Q.obj K) ∈ distTriang (AffineD A) :=
  isomorphic_distinguished _
    (DerivedCategory.mappingCocone_triangle_distinguished (localizationMap A f K)) _
    (derivedFirstTriangleIsoQ A f K)

/-- The first gluing triangle `RΓ_Z X → X → Rj_*Lj^*X → RΓ_Z X[1]` is
distinguished for every object of the derived category. -/
lemma derivedFirstTriangle_distinguished (A : Type u) [CommRing A] (f : A)
    (X : AffineD A) : derivedFirstTriangle A f X ∈ distTriang (AffineD A) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  exact isomorphic_distinguished _ (derivedFirstTriangle_distinguished_Q A f K) _
    ((derivedFirstTriangleFunctor A f).mapIso e.symm)

/-- Objects supported on `V(f)` are left orthogonal to every object in the
essential image of `Rj_*Lj^*`. -/
lemma supported_rightOrthogonal_open (A : Type u) [CommRing A] (f : A)
    (X : AffineD A) :
    (AffineIsSupported A f).rightOrthogonal
      ((derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f).obj X) := by
  intro Y g hY
  let adj := derivedExtensionRestrictionAdjunction A f
  apply (adj.homEquiv _ _).symm.injective
  have hzero := isZero_derivedExtensionScalars_of_support A f hY
  have h := hzero.eq_of_src ((adj.homEquiv _ _).symm g) 0
  simpa [adj] using h

/-- For a supported source, postcomposition with `RΓ_Z X → X` is bijective.
Surjectivity uses the first gluing triangle; injectivity uses its inverse
rotation and the same orthogonality after a shift. -/
lemma derivedCounit_postcomp_bijective (A : Type u) [CommRing A] (f : A)
    {Y X : AffineD A} (hY : AffineIsSupported A f Y) :
    Function.Bijective (fun g : Y ⟶ (derivedFunctor A f).obj X ↦
      g ≫ (derivedCounit A f).app X) := by
  let T := derivedFirstTriangle A f X
  have hT : T ∈ distTriang (AffineD A) := derivedFirstTriangle_distinguished A f X
  have hopen := supported_rightOrthogonal_open A f X
  have hopenShift := (AffineIsSupported A f).rightOrthogonal.le_shift (-1 : ℤ) _ hopen
  constructor
  · intro g₁ g₂ h
    change g₁ ≫ (derivedCounit A f).app X = g₂ ≫ (derivedCounit A f).app X at h
    have hz : (g₁ - g₂) ≫ T.mor₁ = 0 := by
      dsimp [T, derivedFirstTriangle]
      rw [Preadditive.sub_comp, h, sub_self]
    obtain ⟨q, hq⟩ := T.invRotate.coyoneda_exact₂
      (inv_rot_of_distTriang _ hT) (g₁ - g₂) hz
    have hq0 : q = 0 := hopenShift q hY
    rw [hq0, zero_comp] at hq
    exact sub_eq_zero.mp hq
  · intro g
    obtain ⟨p, hp⟩ := T.coyoneda_exact₂ hT g (hopen (g ≫ T.mor₂) hY)
    exact ⟨p, hp.symm⟩

lemma affineDZι_preimage_hom (A : Type u) [CommRing A] (f : A)
    {Y Z : AffineDZ A f} (g : Y.obj ⟶ Z.obj) :
    ((affineDZι A f).preimage g).hom = g :=
  (affineDZι A f).map_preimage g

/-- Maps into the supported local-cohomology object identify with maps into
the explicit local-cohomology complex. -/
noncomputable def supportedToDerivedEquiv (A : Type u) [CommRing A] (f : A)
    (jStar : AffineD A ⥤ AffineDZ A f)
    (e : jStar ⋙ affineDZι A f ≅ derivedFunctor A f)
    (Y : AffineDZ A f) (X : AffineD A) :
    (Y ⟶ jStar.obj X) ≃ (Y.obj ⟶ (derivedFunctor A f).obj X) where
  toFun h := (affineDZι A f).map h ≫ e.hom.app X
  invFun k := (affineDZι A f).preimage (k ≫ e.inv.app X)
  left_inv h := by
    dsimp
    rw [Category.assoc, Iso.hom_inv_id_app]
    simpa using (affineDZι A f).preimage_map h
  right_inv k := by
    dsimp
    rw [affineDZι_preimage_hom]
    simp

/-- The natural transformation `i_*RΓ_Z → id` induced by a supported
factorization of the explicit local-cohomology functor. -/
noncomputable def supportedCounit (A : Type u) [CommRing A] (f : A)
    (jStar : AffineD A ⥤ AffineDZ A f)
    (e : jStar ⋙ affineDZι A f ≅ derivedFunctor A f) :
    jStar ⋙ affineDZι A f ⟶ 𝟭 (AffineD A) :=
  e.hom ≫ derivedCounit A f

/-- The Hom equivalence for the supported inclusion/local-cohomology
adjunction. -/
noncomputable def supportedHomEquiv (A : Type u) [CommRing A] (f : A)
    (jStar : AffineD A ⥤ AffineDZ A f)
    (e : jStar ⋙ affineDZι A f ≅ derivedFunctor A f)
    (Y : AffineDZ A f) (X : AffineD A) :
    (Y.obj ⟶ X) ≃ (Y ⟶ jStar.obj X) :=
  ((supportedToDerivedEquiv A f jStar e Y X).trans
    (Equiv.ofBijective _ (derivedCounit_postcomp_bijective A f Y.property))).symm

/-- The supported inclusion is left adjoint to any supported factorization of
the explicit local-cohomology functor. -/
noncomputable def supportedLocalCohomologyAdjunction (A : Type u) [CommRing A] (f : A)
    (jStar : AffineD A ⥤ AffineDZ A f)
    (e : jStar ⋙ affineDZι A f ≅ derivedFunctor A f) :
    affineDZι A f ⊣ jStar :=
  Adjunction.mkOfHomEquiv {
    homEquiv := supportedHomEquiv A f jStar e
    homEquiv_naturality_left_symm := by
      intro Y' Y X a b
      simp [supportedHomEquiv, supportedToDerivedEquiv]
    homEquiv_naturality_right := by
      intro Y X X' g h
      apply (supportedHomEquiv A f jStar e Y X').symm.injective
      simp [supportedHomEquiv, supportedToDerivedEquiv, affineDZι_preimage_hom]
      have he : (jStar.map h).hom ≫ e.hom.app X' =
          e.hom.app X ≫ (derivedFunctor A f).map h := e.hom.naturality h
      rw [reassoc_of% he]
      rw [(derivedCounit A f).naturality h]
      simp
      rw [← Category.assoc]
      have hg := (Equiv.ofBijective
        (fun g : Y.obj ⟶ (derivedFunctor A f).obj X ↦
          g ≫ (derivedCounit A f).app X)
        (derivedCounit_postcomp_bijective A f Y.property)).apply_symm_apply g
      exact (congrArg (fun t ↦ t ≫ h) hg).symm }

@[simp] lemma supportedLocalCohomologyAdjunction_counit (A : Type u) [CommRing A] (f : A)
    (jStar : AffineD A ⥤ AffineDZ A f)
    (e : jStar ⋙ affineDZι A f ≅ derivedFunctor A f) (X : AffineD A) :
    (supportedLocalCohomologyAdjunction A f jStar e).counit.app X =
      (supportedCounit A f jStar e).app X := by
  simp [supportedLocalCohomologyAdjunction, supportedHomEquiv,
    supportedToDerivedEquiv, supportedCounit]

/-- Factor explicit local cohomology through the supported full subcategory,
given the pointwise support theorem. -/
noncomputable def supportedFunctorOf (A : Type u) [CommRing A] (f : A)
    (h : ∀ X : AffineD A, AffineIsSupported A f ((derivedFunctor A f).obj X)) :
    AffineD A ⥤ AffineDZ A f where
  obj X := ⟨(derivedFunctor A f).obj X, h X⟩
  map a := ⟨(derivedFunctor A f).map a⟩
  map_id X := by
    ext
    exact (derivedFunctor A f).map_id X
  map_comp a b := by
    ext
    exact (derivedFunctor A f).map_comp a b

/-- The comparison of the pointwise supported factorization with the explicit
local-cohomology functor is definitional. -/
noncomputable def supportedFunctorOfFactors (A : Type u) [CommRing A] (f : A)
    (h : ∀ X : AffineD A, AffineIsSupported A f ((derivedFunctor A f).obj X)) :
    supportedFunctorOf A f h ⋙ affineDZι A f ≅ derivedFunctor A f :=
  NatIso.ofComponents
    (fun X ↦ by
      dsimp [supportedFunctorOf]
      exact Iso.refl _)
    (by
      intros X Y a
      dsimp [supportedFunctorOf]
      simp)

/-- The first gluing connecting transformation for a supported factorization
of local cohomology. -/
noncomputable def supportedFirstConnecting (A : Type u) [CommRing A] (f : A)
    (jStar : AffineD A ⥤ AffineDZ A f)
    (e : jStar ⋙ affineDZι A f ≅ derivedFunctor A f) :
    derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f ⟶
      jStar ⋙ affineDZι A f ⋙ shiftFunctor (AffineD A) (1 : ℤ) :=
  derivedConnecting A f ≫ Functor.whiskerRight e.inv (shiftFunctor (AffineD A) (1 : ℤ))

/-- The supported first gluing triangle identifies with the explicit derived
mapping-cocone triangle. -/
noncomputable def supportedFirstTriangleIso (A : Type u) [CommRing A] (f : A)
    (jStar : AffineD A ⥤ AffineDZ A f)
    (e : jStar ⋙ affineDZι A f ≅ derivedFunctor A f) (X : AffineD A) :
    Triangle.mk
      ((supportedLocalCohomologyAdjunction A f jStar e).counit.app X)
      ((derivedExtensionRestrictionAdjunction A f).unit.app X)
      ((supportedFirstConnecting A f jStar e).app X) ≅
      derivedFirstTriangle A f X := by
  refine Triangle.isoMk _ _ (e.app X) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [supportedCounit, derivedFirstTriangle]
  · simp [derivedFirstTriangle]
  · simp [supportedFirstConnecting, derivedFirstTriangle]

/-- The first gluing triangle for a supported factorization is distinguished. -/
lemma supportedFirstTriangle_distinguished (A : Type u) [CommRing A] (f : A)
    (jStar : AffineD A ⥤ AffineDZ A f)
    (e : jStar ⋙ affineDZι A f ≅ derivedFunctor A f) (X : AffineD A) :
    Triangle.mk
      ((supportedLocalCohomologyAdjunction A f jStar e).counit.app X)
      ((derivedExtensionRestrictionAdjunction A f).unit.app X)
      ((supportedFirstConnecting A f jStar e).app X) ∈ distTriang (AffineD A) :=
  isomorphic_distinguished _ (derivedFirstTriangle_distinguished A f X) _
    (supportedFirstTriangleIso A f jStar e X)

/-- The kernel characterization for a supported factorization of explicit
local cohomology. -/
lemma supported_kernel (A : Type u) [CommRing A] (f : A)
    (jStar : AffineD A ⥤ AffineDZ A f)
    (e : jStar ⋙ affineDZι A f ≅ derivedFunctor A f) (X : AffineD A) :
    Nonempty (jStar.obj X ≅ 0) ↔
      ∃ Y : AffineD (Away A f),
        Nonempty (X ≅ (derivedRestrictionScalars A f).obj Y) := by
  rw [← derivedFunctor_kernel A f X]
  constructor
  · rintro ⟨z⟩
    exact ⟨(e.app X).symm ≪≫ (affineDZι A f).mapIso z ≪≫
      (affineDZι A f).mapZeroObject⟩
  · rintro ⟨z⟩
    exact ⟨(affineDZι A f).preimageIso
      (e.app X ≪≫ z ≪≫ (affineDZι A f).mapZeroObject.symm)⟩

#print axioms complexCounit
#print axioms derivedCounit
#print axioms complexConnecting
#print axioms derivedConnecting
#print axioms derivedFirstTriangleIsoQ
#print axioms derivedFirstTriangle_distinguished
#print axioms supported_rightOrthogonal_open
#print axioms derivedCounit_postcomp_bijective
#print axioms supportedLocalCohomologyAdjunction
#print axioms supportedFirstTriangle_distinguished
#print axioms supported_kernel

end
end RelativeFM.AffineLocalCohomology
