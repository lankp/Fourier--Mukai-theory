import FourierMukai.Scheme.AffineSupportedAssembly
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

@[expose] public section

/-!
# The second gluing triangle of a recollement

This file gives a categorical construction of the second gluing triangle from
exactness, full faithfulness, the kernel description, and the two vanishing
composites. It does not use injective resolutions.
-/

namespace RelativeFM.Recollement.SecondGluing

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe vZ uZ vD uD vU uU

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{vZ} DZ] [Category.{vD} D] [Category.{vU} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A chosen distinguished triangle completing a morphism. -/
noncomputable def coneTriangle {X Y : D} (f : X ⟶ Y) : Triangle D :=
  let H := distinguished_cocone_triangle f
  Triangle.mk f H.choose_spec.choose H.choose_spec.choose_spec.choose

lemma coneTriangle_distinguished {X Y : D} (f : X ⟶ Y) :
    coneTriangle f ∈ distTriang D :=
  (distinguished_cocone_triangle f).choose_spec.choose_spec.choose_spec

lemma coneTriangle_obj₁ {X Y : D} (f : X ⟶ Y) :
    (coneTriangle f).obj₁ = X := rfl

lemma coneTriangle_obj₂ {X Y : D} (f : X ⟶ Y) :
    (coneTriangle f).obj₂ = Y := rfl

@[simp] lemma coneTriangle_mor₁ {X Y : D} (f : X ⟶ Y) :
    (coneTriangle f).mor₁ = f := rfl

variable (L : DZ ⥤ D) (R : D ⥤ DZ) (adjL : L ⊣ R)

include adjL in
/-- An object killed by the right adjoint of `L` is right orthogonal to the
essential image of `L`. -/
lemma rightOrthogonal_of_isZero_map {Y : D} (hY : IsZero (R.obj Y)) :
    L.essImage.rightOrthogonal Y := by
  intro X f hX
  obtain ⟨Z, ⟨e⟩⟩ := hX
  rw [← cancel_epi e.hom]
  apply (adjL.homEquiv Z Y).injective
  exact hY.eq_of_tgt _ _

variable [L.CommShift ℤ] [L.IsTriangulated] [L.Full] [L.Faithful]
variable [R.CommShift ℤ] [R.IsTriangulated]

/-- The third object in the cone of the counit is right orthogonal to the
essential image of the left adjoint. -/
lemma coneCounit_obj₃_rightOrthogonal (X : D) :
    L.essImage.rightOrthogonal (coneTriangle (adjL.counit.app X)).obj₃ := by
  apply rightOrthogonal_of_isZero_map L R adjL
  let T := coneTriangle (adjL.counit.app X)
  have hT : T ∈ distTriang D := coneTriangle_distinguished _
  exact Triangle.isZero₃_of_isIso₁ (R.mapTriangle.obj T) (R.map_distinguished T hT)
    (by
      change IsIso (R.map (adjL.counit.app X))
      infer_instance)

variable (J : D ⥤ DU) (U : DU ⥤ D) (adjJ : J ⊣ U)
variable [J.CommShift ℤ] [J.IsTriangulated]
variable [U.Full] [U.Faithful]

/-- Precomposition with the second map of the counit cone is injective on maps
to an object right orthogonal to the essential image of `L`. -/
lemma coneCounit_mor₂_precomp_injective {X Y : D}
    (hY : L.essImage.rightOrthogonal Y) :
    Function.Injective (fun k : (coneTriangle (adjL.counit.app X)).obj₃ ⟶ Y ↦
      (coneTriangle (adjL.counit.app X)).mor₂ ≫ k) := by
  intro k₁ k₂ hk
  let T := coneTriangle (adjL.counit.app X)
  have hT : T ∈ distTriang D := coneTriangle_distinguished _
  have hzero : T.mor₂ ≫ (k₁ - k₂) = 0 := by
    dsimp [T] at hk ⊢
    rw [Preadditive.comp_sub, hk, sub_self]
  obtain ⟨q, hq⟩ := T.yoneda_exact₃ hT (k₁ - k₂) hzero
  have hP : L.essImage T.obj₁ := ⟨R.obj X, ⟨Iso.refl _⟩⟩
  have hq0 : q = 0 := hY q (L.essImage.le_shift 1 _ hP)
  apply sub_eq_zero.mp
  rw [hq, hq0, comp_zero]

variable (zru : U ⋙ R ≅ 0)

include adjL zru in
lemma open_obj_rightOrthogonal (X : D) :
    L.essImage.rightOrthogonal (U.obj (J.obj X)) := by
  apply rightOrthogonal_of_isZero_map L R adjL
  exact (Functor.zero_obj (J.obj X)).of_iso (zru.app (J.obj X))

include adjJ zru in
/-- The comparison from the chosen counit cone to `UJX`, obtained by
factoring the unit of `J ⊣ U`. -/
noncomputable def comparison (X : D) :
    (coneTriangle (adjL.counit.app X)).obj₃ ⟶ U.obj (J.obj X) :=
  let T := coneTriangle (adjL.counit.app X)
  (T.yoneda_exact₂ (coneTriangle_distinguished _) (adjJ.unit.app X)
    ((open_obj_rightOrthogonal L R adjL J U zru X)
      (adjL.counit.app X ≫ adjJ.unit.app X)
      ⟨R.obj X, ⟨Iso.refl _⟩⟩)).choose

lemma unit_eq_coneCounit_mor₂_comp_comparison (X : D) :
    adjJ.unit.app X = (coneTriangle (adjL.counit.app X)).mor₂ ≫
      comparison L R adjL J U adjJ zru X :=
  (coneTriangle (adjL.counit.app X)).yoneda_exact₂
    (coneTriangle_distinguished _) (adjJ.unit.app X)
    ((open_obj_rightOrthogonal L R adjL J U zru X)
      (adjL.counit.app X ≫ adjJ.unit.app X)
      ⟨R.obj X, ⟨Iso.refl _⟩⟩) |>.choose_spec

section ComparisonIsIso

variable (zjl : L ⋙ J ≅ 0)
variable (ker : ∀ Y : D, Nonempty (J.obj Y ≅ 0) ↔
  ∃ Z : DZ, Nonempty (Y ≅ L.obj Z))

include adjJ zru zjl ker in
lemma comparison_isIso (X : D) :
    IsIso (comparison L R adjL J U adjJ zru X) := by
  let T := coneTriangle (adjL.counit.app X)
  let h := comparison L R adjL J U adjJ zru X
  have hT : T ∈ distTriang D := coneTriangle_distinguished _
  have hη : adjJ.unit.app X = T.mor₂ ≫ h :=
    unit_eq_coneCounit_mor₂_comp_comparison L R adjL J U adjJ zru X
  have hJT : J.mapTriangle.obj T ∈ distTriang DU := J.map_distinguished T hT
  have hzero₁ : IsZero ((J.mapTriangle.obj T).obj₁) :=
    (Functor.zero_obj (R.obj X)).of_iso (zjl.app (R.obj X))
  haveI : IsIso (J.map T.mor₂) :=
    (Triangle.isZero₁_iff_isIso₂ (J.mapTriangle.obj T) hJT).mp hzero₁
  letI : IsIso adjJ.counit := adjJ.counit_isIso_of_R_fully_faithful
  haveI : IsIso (adjJ.counit.app (J.obj X)) :=
    NatIso.isIso_app_of_isIso adjJ.counit (J.obj X)
  have hunit : IsIso (J.map (adjJ.unit.app X)) :=
    isIso_of_comp_hom_eq_id _ (adjJ.left_triangle_components X)
  haveI : IsIso (J.map T.mor₂ ≫ J.map h) := by
    rw [← J.map_comp, ← hη]
    exact hunit
  haveI : IsIso (J.map h) :=
    IsIso.of_isIso_comp_left (J.map T.mor₂) (J.map h)
  let S := coneTriangle h
  have hS : S ∈ distTriang D := coneTriangle_distinguished _
  have hJK : IsZero (J.obj S.obj₃) := by
    exact Triangle.isZero₃_of_isIso₁ (J.mapTriangle.obj S) (J.map_distinguished S hS)
      (by change IsIso (J.map h); infer_instance)
  obtain ⟨Z, ⟨e⟩⟩ := (ker S.obj₃).mp ⟨hJK.isoZero⟩
  have hKP : L.essImage S.obj₃ := ⟨Z, ⟨e.symm⟩⟩
  have hKperp : L.essImage.rightOrthogonal S.obj₃ :=
    L.essImage.rightOrthogonal.ext_of_isTriangulatedClosed₃ S hS
      (coneCounit_obj₃_rightOrthogonal L R adjL X)
      (open_obj_rightOrthogonal L R adjL J U zru X)
  have hKzero : IsZero S.obj₃ :=
    (IsZero.iff_id_eq_zero _).mpr (hKperp (𝟙 _) hKP)
  change IsIso h
  exact (Triangle.isZero₃_iff_isIso₁ S hS).mp hKzero

end ComparisonIsIso

section SecondTriangle

variable (zjl : L ⋙ J ≅ 0)
variable (ker : ∀ Y : D, Nonempty (J.obj Y ≅ 0) ↔
  ∃ Z : DZ, Nonempty (Y ≅ L.obj Z))

include adjL adjJ zru zjl ker in
/-- The comparison isomorphism, packaged once so that all later proofs use the
same inverse. -/
noncomputable def comparisonIso (X : D) :
    (coneTriangle (adjL.counit.app X)).obj₃ ≅ U.obj (J.obj X) := by
  letI := comparison_isIso L R adjL J U adjJ zru zjl ker X
  exact asIso (comparison L R adjL J U adjJ zru X)

@[simp] lemma comparisonIso_hom (X : D) :
    (comparisonIso L R adjL J U adjJ zru zjl ker X).hom =
      comparison L R adjL J U adjJ zru X := rfl

include adjL adjJ zru zjl ker in
/-- The connecting morphism from the chosen cone, transported along the
comparison isomorphism. -/
noncomputable def connectingApp (X : D) :
    U.obj (J.obj X) ⟶ (shiftFunctor D (1 : ℤ)).obj (L.obj (R.obj X)) :=
  (comparisonIso L R adjL J U adjJ zru zjl ker X).inv ≫
    (coneTriangle (adjL.counit.app X)).mor₃

lemma connectingApp_naturality {X Y : D} (a : X ⟶ Y) :
    U.map (J.map a) ≫ connectingApp L R adjL J U adjJ zru zjl ker Y =
      connectingApp L R adjL J U adjJ zru zjl ker X ≫
        (L.map (R.map a))⟦(1 : ℤ)⟧' := by
  let TX := coneTriangle (adjL.counit.app X)
  let TY := coneTriangle (adjL.counit.app Y)
  let eX := comparisonIso L R adjL J U adjJ zru zjl ker X
  let eY := comparisonIso L R adjL J U adjJ zru zjl ker Y
  have hTX : TX ∈ distTriang D := coneTriangle_distinguished _
  have hTY : TY ∈ distTriang D := coneTriangle_distinguished _
  let φ := completeDistinguishedTriangleMorphism TX TY hTX hTY
    (L.map (R.map a)) a (adjL.counit.naturality a).symm
  have hφ₃ : φ.hom₃ = eX.hom ≫ U.map (J.map a) ≫ eY.inv := by
    apply coneCounit_mor₂_precomp_injective L R adjL
      (X := X) (Y := TY.obj₃) (coneCounit_obj₃_rightOrthogonal L R adjL Y)
    rw [← cancel_mono eY.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [reassoc_of% φ.comm₂]
    change a ≫ TY.mor₂ ≫ eY.hom = TX.mor₂ ≫ eX.hom ≫ U.map (J.map a)
    dsimp only [TX, TY, eX, eY]
    rw [comparisonIso_hom]
    rw [comparisonIso_hom]
    rw [← unit_eq_coneCounit_mor₂_comp_comparison L R adjL J U adjJ zru Y,
      ← reassoc_of% (unit_eq_coneCounit_mor₂_comp_comparison L R adjL J U adjJ zru X)]
    exact adjJ.unit.naturality a
  have hφ₁ : φ.hom₁ = L.map (R.map a) := rfl
  change U.map (J.map a) ≫ (eY.inv ≫ TY.mor₃) =
    (eX.inv ≫ TX.mor₃) ≫ (L.map (R.map a))⟦(1 : ℤ)⟧'
  have H := congrArg (fun k ↦ eX.inv ≫ k) φ.comm₃.symm
  rw [hφ₁] at H
  simp only [hφ₃, Category.assoc, Iso.inv_hom_id_assoc] at H
  rw [Category.assoc]
  exact H

include adjL adjJ zru zjl ker in
/-- The second connecting transformation of a recollement, constructed from a
chosen completion of the counit. -/
noncomputable def secondConnecting :
    J ⋙ U ⟶ R ⋙ L ⋙ shiftFunctor D (1 : ℤ) where
  app X := connectingApp L R adjL J U adjJ zru zjl ker X
  naturality X Y a := connectingApp_naturality L R adjL J U adjJ zru zjl ker a

/-- The second gluing triangle is isomorphic to the chosen completion of the
counit. -/
noncomputable def secondTriangleIso (X : D) :
    Triangle.mk (adjL.counit.app X) (adjJ.unit.app X)
      ((secondConnecting L R adjL J U adjJ zru zjl ker).app X) ≅
      coneTriangle (adjL.counit.app X) := by
  let e := comparisonIso L R adjL J U adjJ zru zjl ker X
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp) ?_ ?_
  · change adjJ.unit.app X ≫ e.inv = (𝟙 X) ≫ (coneTriangle (adjL.counit.app X)).mor₂
    rw [Category.id_comp]
    rw [← cancel_mono e.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [e]
    rw [comparisonIso_hom]
    exact unit_eq_coneCounit_mor₂_comp_comparison L R adjL J U adjJ zru X
  · dsimp only [Triangle.mk_mor₃, Iso.refl_hom, Iso.symm_hom, Functor.map_id,
      Category.comp_id, secondConnecting, connectingApp, e]
    simp

/-- The second gluing triangle is distinguished. -/
lemma second_distinguished (X : D) :
    Triangle.mk (adjL.counit.app X) (adjJ.unit.app X)
      ((secondConnecting L R adjL J U adjJ zru zjl ker).app X) ∈ distTriang D :=
  isomorphic_distinguished _ (coneTriangle_distinguished (adjL.counit.app X)) _
    (secondTriangleIso L R adjL J U adjJ zru zjl ker X)

#print axioms comparison_isIso
#print axioms secondConnecting
#print axioms second_distinguished

end SecondTriangle

end
end RelativeFM.Recollement.SecondGluing


/-! ## Affine specialization -/

namespace RelativeFM.Recollement.SecondGluing

open RelativeFM
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The second connecting transformation for the affine recollement, with
precisely the missing-field data as its inputs. -/
noncomputable def affineSecondConnecting
    (A : Type u) [CommRing A] (f : A)
    (iShriek : AffineD A ⥤ AffineD (Away A f))
    [iShriek.CommShift ℤ] [iShriek.IsTriangulated]
    (iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek)
    (jStar : AffineD A ⥤ AffineDZ A f)
    [jStar.CommShift ℤ] [jStar.IsTriangulated]
    (jUpper : AffineDZ A f ⥤ AffineD A)
    (jStarAdj : jStar ⊣ jUpper)
    (jUpperFF : jUpper.FullyFaithful)
    (iShriek_jUpper : jUpper ⋙ iShriek ≅ 0)
    (jStar_iLower : derivedRestrictionScalars A f ⋙ jStar ≅ 0)
    (ker : ∀ X : AffineD A, Nonempty (jStar.obj X ≅ 0) ↔
      ∃ Y : AffineD (Away A f), Nonempty (X ≅ (derivedRestrictionScalars A f).obj Y)) :
    jStar ⋙ jUpper ⟶ iShriek ⋙ derivedRestrictionScalars A f ⋙
      shiftFunctor (AffineD A) (1 : ℤ) := by
  letI : jUpper.Full := jUpperFF.full
  letI : jUpper.Faithful := jUpperFF.faithful
  exact secondConnecting (derivedRestrictionScalars A f) iShriek iLowerAdj
    jStar jUpper jStarAdj iShriek_jUpper jStar_iLower ker

/-- The distinguished second gluing triangle for the affine recollement. -/
lemma affineSecondDistinguished
    (A : Type u) [CommRing A] (f : A)
    (iShriek : AffineD A ⥤ AffineD (Away A f))
    [iShriek.CommShift ℤ] [iShriek.IsTriangulated]
    (iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek)
    (jStar : AffineD A ⥤ AffineDZ A f)
    [jStar.CommShift ℤ] [jStar.IsTriangulated]
    (jUpper : AffineDZ A f ⥤ AffineD A)
    (jStarAdj : jStar ⊣ jUpper)
    (jUpperFF : jUpper.FullyFaithful)
    (iShriek_jUpper : jUpper ⋙ iShriek ≅ 0)
    (jStar_iLower : derivedRestrictionScalars A f ⋙ jStar ≅ 0)
    (ker : ∀ X : AffineD A, Nonempty (jStar.obj X ≅ 0) ↔
      ∃ Y : AffineD (Away A f), Nonempty (X ≅ (derivedRestrictionScalars A f).obj Y))
    (X : AffineD A) :
    Triangle.mk (iLowerAdj.counit.app X) (jStarAdj.unit.app X)
      ((affineSecondConnecting A f iShriek iLowerAdj jStar jUpper jStarAdj jUpperFF
        iShriek_jUpper jStar_iLower ker).app X) ∈ distTriang (AffineD A) := by
  letI : jUpper.Full := jUpperFF.full
  letI : jUpper.Faithful := jUpperFF.faithful
  exact second_distinguished (derivedRestrictionScalars A f) iShriek iLowerAdj
    jStar jUpper jStarAdj iShriek_jUpper jStar_iLower ker X

#print axioms affineSecondConnecting
#print axioms affineSecondDistinguished

end
end RelativeFM.Recollement.SecondGluing


namespace RelativeFM.Recollement.SecondGluing

open RelativeFM RelativeFM.AffineLocalCohomology
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Restriction kills any supported factorization of explicit local cohomology,
by the corresponding ambient vanishing theorem. -/
noncomputable def supportedRestrictionIsoZeroOfFactors
    (A : Type u) [CommRing A] (f : A)
    (jStar : AffineD A ⥤ AffineDZ A f)
    (e : jStar ⋙ affineDZι A f ≅ derivedFunctor A f) :
    derivedRestrictionScalars A f ⋙ jStar ≅ 0 :=
  NatIso.ofComponents
    (fun Y ↦ (affineDZι A f).preimageIso
      (e.app ((derivedRestrictionScalars A f).obj Y) ≪≫
        (derivedRestrictionScalars_derivedFunctor_isoZero A f).app Y ≪≫
        (Functor.zero_obj Y).isoZero ≪≫ (affineDZι A f).mapZeroObject.symm ≪≫
        (affineDZι A f).mapIso (Functor.zero_obj Y).isoZero.symm))
    (by
      intro Y Y' a
      apply (Functor.zero_obj Y').eq_of_tgt)

/-- The concrete affine second connecting transformation. All remaining inputs
are the d1/d2/d3 fields; the concrete local-cohomology side is supplied from
ring data. -/
noncomputable def concreteAffineSecondConnecting
    (A : Type u) [CommRing A] (f : A)
    (iShriek : AffineD A ⥤ AffineD (Away A f))
    [iShriek.CommShift ℤ] [iShriek.IsTriangulated]
    (iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek)
    (jUpper : AffineDZ A f ⥤ AffineD A)
    (jStarAdj : jStar A f ⊣ jUpper)
    (jUpperFF : jUpper.FullyFaithful)
    (iShriek_jUpper : jUpper ⋙ iShriek ≅ 0) :
    jStar A f ⋙ jUpper ⟶ iShriek ⋙ derivedRestrictionScalars A f ⋙
      shiftFunctor (AffineD A) (1 : ℤ) :=
  affineSecondConnecting A f iShriek iLowerAdj (jStar A f) jUpper jStarAdj jUpperFF
    iShriek_jUpper (supportedRestrictionIsoZeroOfFactors A f (jStar A f) (jStarFactors A f))
    (supported_kernel A f (jStar A f) (jStarFactors A f))

lemma concreteAffineSecondDistinguished
    (A : Type u) [CommRing A] (f : A)
    (iShriek : AffineD A ⥤ AffineD (Away A f))
    [iShriek.CommShift ℤ] [iShriek.IsTriangulated]
    (iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek)
    (jUpper : AffineDZ A f ⥤ AffineD A)
    (jStarAdj : jStar A f ⊣ jUpper)
    (jUpperFF : jUpper.FullyFaithful)
    (iShriek_jUpper : jUpper ⋙ iShriek ≅ 0)
    (X : AffineD A) :
    Triangle.mk (iLowerAdj.counit.app X) (jStarAdj.unit.app X)
      ((concreteAffineSecondConnecting A f iShriek iLowerAdj jUpper jStarAdj jUpperFF
        iShriek_jUpper).app X) ∈ distTriang (AffineD A) :=
  affineSecondDistinguished A f iShriek iLowerAdj (jStar A f) jUpper jStarAdj jUpperFF
    iShriek_jUpper (supportedRestrictionIsoZeroOfFactors A f (jStar A f) (jStarFactors A f))
    (supported_kernel A f (jStar A f) (jStarFactors A f)) X

#print axioms supportedRestrictionIsoZeroOfFactors
#print axioms concreteAffineSecondConnecting
#print axioms concreteAffineSecondDistinguished

end
end RelativeFM.Recollement.SecondGluing
