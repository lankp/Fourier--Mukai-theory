/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.PerfectModelConverse

/-!
# The Le--Chen two-out-of-three theorem for split idempotents

This file proves the matrix argument in Le--Chen, *Karoubianness of a
triangulated category*, J. Algebra 310 (2007), Proposition 2.3, in an arbitrary
pretriangulated category.  Remark 2.4 of that paper observes that the
octahedral axiom is not used.
-/

@[expose] public section
namespace RelativeFM.AffinePerfect

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Preadditive
open scoped ZeroObject Classical

universe u v
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A splitting of an idempotent whose image is required to lie in a given
class of objects.  This is the notion the Le--Chen argument is about; for
`T = HasBoundedFiniteProjectiveModel A` it is Stacks 066S's statement that a
direct summand of a strictly perfect complex is strictly perfect, applied to the
idempotent that the retract defines. -/
def SplitsWithin {C : Type u} [Category.{v} C] (T : ObjectProperty C)
    {Y : C} (e : Y ⟶ Y) : Prop :=
  ∃ (Z : C), T Z ∧ ∃ (i : Z ⟶ Y) (q : Y ⟶ Z), i ≫ q = 𝟙 Z ∧ q ≫ i = e

lemma SplitsWithin.of_iso {C : Type u} [Category.{v} C] {T : ObjectProperty C}
    {Y Y' : C} (φ : Y ≅ Y') (e : Y ⟶ Y) (e' : Y' ⟶ Y')
    (hcomm : e ≫ φ.hom = φ.hom ≫ e') (h : SplitsWithin T e) : SplitsWithin T e' := by
  obtain ⟨Z, hZ, i, q, hi, hq⟩ := h
  refine ⟨Z, hZ, i ≫ φ.hom, φ.inv ≫ q, by simp [Category.assoc, hi], ?_⟩
  simp only [Category.assoc, reassoc_of% hq, hcomm]
  exact φ.inv_hom_id_assoc e'

namespace LeChen

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A particularly convenient strong splitting: the source is identified with
the biproduct of the image and a complement, and the idempotent is the
projection onto the first summand. -/
structure StrongSplitting (T : ObjectProperty C) {X : C} (e : X ⟶ X) where
  image : C
  complement : C
  image_mem : T image
  decomposition : X ≅ image ⊞ complement
  comm : e ≫ decomposition.hom =
    decomposition.hom ≫ biprod.map (𝟙 image) 0

/-- Lemma 2.2 of Le--Chen, in the explicit biproduct form needed for
Proposition 2.3. -/
noncomputable def strongSplitting {T : ObjectProperty C} {X : C} (e : X ⟶ X)
    (s : SplitsWithin T e) : StrongSplitting T e := by
  let Z := s.choose
  have hZ : T Z := s.choose_spec.1
  let i : Z ⟶ X := s.choose_spec.2.choose
  let q : X ⟶ Z := s.choose_spec.2.choose_spec.choose
  have hiq : i ≫ q = 𝟙 Z := s.choose_spec.2.choose_spec.choose_spec.1
  have hqi : q ≫ i = e := s.choose_spec.2.choose_spec.choose_spec.2
  letI : IsSplitMono i := IsSplitMono.mk' { retraction := q, id := hiq }
  letI : IsSplitEpi q := IsSplitEpi.mk' { section_ := i, id := hiq }
  let W := (distinguished_cocone_triangle i).choose
  let p : X ⟶ W := (distinguished_cocone_triangle i).choose_spec.choose
  let w : W ⟶ Z⟦(1 : ℤ)⟧ :=
    (distinguished_cocone_triangle i).choose_spec.choose_spec.choose
  have hT : Triangle.mk i p w ∈ distTriang C :=
    (distinguished_cocone_triangle i).choose_spec.choose_spec.choose_spec
  let Tr := Triangle.mk i p w
  change Tr ∈ distTriang C at hT
  have hmono : Mono Tr.mor₁ := by change Mono i; infer_instance
  have hzero : Tr.mor₃ = 0 := Tr.mor₃_eq_zero_of_mono₁ hT hmono
  letI : Epi p := Tr.epi₂ hT hzero
  letI : IsSplitEpi p := isSplitEpi_of_epi p
  let j : W ⟶ X := section_ p - section_ p ≫ q ≫ i
  have hip : i ≫ p = 0 := comp_distTriang_mor_zero₁₂ Tr hT
  have hjp : j ≫ p = 𝟙 W := by
    dsimp [j]
    simp [Category.assoc, hip]
  have hjq : j ≫ q = 0 := by
    dsimp [j]
    simp [Category.assoc, hiq]
  have htotal : q ≫ i + p ≫ j = 𝟙 X := by
    have hp : (q ≫ i + p ≫ j - 𝟙 X) ≫ p = 0 := by
      simp [sub_comp, Category.assoc, hip, hjp]
    obtain ⟨g, hg⟩ := Tr.coyoneda_exact₂ hT _ hp
    change (X ⟶ Z) at g
    have hg' : q ≫ i + p ≫ j - 𝟙 X = g ≫ i := hg
    have hq : (q ≫ i + p ≫ j - 𝟙 X) ≫ q = 0 := by
      simp [sub_comp, Category.assoc, hiq, hjq]
    have hg0 : g = 0 := by
      rw [hg'] at hq
      rw [Category.assoc, hiq, Category.comp_id] at hq
      exact hq
    have hsub : q ≫ i + p ≫ j - 𝟙 X = 0 :=
      hg'.trans (by rw [hg0, zero_comp])
    exact sub_eq_zero.mp hsub
  let d := binaryBiproductData Tr hT hzero j hjp q htotal
  let E : X ≅ Z ⊞ W := biprod.uniqueUpToIso _ _ d.isBilimit
  exact
    { image := Z
      complement := W
      image_mem := hZ
      decomposition := E
      comm := by
        change e ≫ biprod.lift q p = biprod.lift q p ≫ biprod.map (𝟙 Z) 0
        rw [← hqi]
        ext <;> simp [Category.assoc, hiq, hip] }

/-- Conjugating by the decomposition turns the strong splitting into the
literal complementary idempotent as well. -/
lemma StrongSplitting.comm_complement {T : ObjectProperty C} {X : C} {e : X ⟶ X}
    (s : StrongSplitting T e) :
    (𝟙 X - e) ≫ s.decomposition.hom =
      s.decomposition.hom ≫ biprod.map 0 (𝟙 s.complement) := by
  rw [sub_comp, s.comm]
  ext <;> simp

/-- The projection-inclusion description of the first component. -/
lemma StrongSplitting.idem_eq {T : ObjectProperty C} {X : C} {e : X ⟶ X}
    (s : StrongSplitting T e) :
    (s.decomposition.hom ≫ biprod.fst) ≫
      (biprod.inl ≫ s.decomposition.inv) = e := by
  rw [← cancel_mono s.decomposition.hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id, s.comm]
  ext <;> simp

/-- A binary product is the product over `WalkingPair`, with the comparison
recorded without any definitional-equality assumptions on the diagram. -/
noncomputable def prodPairIso (F : WalkingPair → C) [HasProduct F] :
    (F WalkingPair.left ⨯ F WalkingPair.right) ≅ ∏ᶜ F :=
  IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
    ((IsLimit.postcomposeHomEquiv (diagramIsoPair (Discrete.functor F)) _).2
      (productIsProduct F))

@[simp] lemma prodPairIso_hom_left (F : WalkingPair → C) [HasProduct F] :
    (prodPairIso F).hom ≫ Pi.π F WalkingPair.left = prod.fst := by
  unfold prodPairIso
  simpa using IsLimit.conePointUniqueUpToIso_hom_comp
    (prodIsProd (F WalkingPair.left) (F WalkingPair.right))
    ((IsLimit.postcomposeHomEquiv (diagramIsoPair (Discrete.functor F)) _).2
      (productIsProduct F)) ⟨WalkingPair.left⟩

@[simp] lemma prodPairIso_hom_right (F : WalkingPair → C) [HasProduct F] :
    (prodPairIso F).hom ≫ Pi.π F WalkingPair.right = prod.snd := by
  unfold prodPairIso
  simpa using IsLimit.conePointUniqueUpToIso_hom_comp
    (prodIsProd (F WalkingPair.left) (F WalkingPair.right))
    ((IsLimit.postcomposeHomEquiv (diagramIsoPair (Discrete.functor F)) _).2
      (productIsProduct F)) ⟨WalkingPair.right⟩

lemma comp_map_inv_hom {D : Type*} [Category D] (F : C ⥤ D)
    {W : D} {X Y : C} (f : W ⟶ F.obj Y) (e : X ≅ Y) :
    (f ≫ F.map e.inv) ≫ F.map e.hom = f := by
  simp

@[simp] lemma biprod_prodPairIso_hom_left (F : WalkingPair → C) [HasProduct F] :
    (biprod.isoProd (F WalkingPair.left) (F WalkingPair.right) ≪≫ prodPairIso F).hom ≫
      Pi.π F WalkingPair.left = biprod.fst := by
  simp [Category.assoc, biprod.isoProd_hom, prod.lift_fst]

@[simp] lemma biprod_prodPairIso_hom_right (F : WalkingPair → C) [HasProduct F] :
    (biprod.isoProd (F WalkingPair.left) (F WalkingPair.right) ≪≫ prodPairIso F).hom ≫
      Pi.π F WalkingPair.right = biprod.snd := by
  simp [Category.assoc, biprod.isoProd_hom, prod.lift_snd]

/-- Comparison of the three objects of a biproduct triangle with those of the
corresponding product triangle. -/
noncomputable def biproductTriangleProdIso₁ (T₁ T₂ : Triangle C) :
    T₁.obj₁ ⊞ T₂.obj₁ ≅ (productTriangle (pairFunction T₁ T₂)).obj₁ :=
  biprod.isoProd _ _ ≪≫
    prodPairIso (fun j ↦ (pairFunction T₁ T₂ j).obj₁)

noncomputable def biproductTriangleProdIso₂ (T₁ T₂ : Triangle C) :
    T₁.obj₂ ⊞ T₂.obj₂ ≅ (productTriangle (pairFunction T₁ T₂)).obj₂ :=
  biprod.isoProd _ _ ≪≫
    prodPairIso (fun j ↦ (pairFunction T₁ T₂ j).obj₂)

noncomputable def biproductTriangleProdIso₃ (T₁ T₂ : Triangle C) :
    T₁.obj₃ ⊞ T₂.obj₃ ≅ (productTriangle (pairFunction T₁ T₂)).obj₃ :=
  biprod.isoProd _ _ ≪≫
    prodPairIso (fun j ↦ (pairFunction T₁ T₂ j).obj₃)

lemma biprodProdPairIso_natural (F G : WalkingPair → C) [HasProduct F] [HasProduct G]
    (p : ∀ j, F j ⟶ G j) :
    biprod.map (p WalkingPair.left) (p WalkingPair.right) ≫
      (biprod.isoProd (G WalkingPair.left) (G WalkingPair.right) ≪≫ prodPairIso G).hom =
    (biprod.isoProd (F WalkingPair.left) (F WalkingPair.right) ≪≫ prodPairIso F).hom ≫
      Limits.Pi.map p := by
  apply Pi.hom_ext
  intro j
  cases j
  · rw [Category.assoc, biprod_prodPairIso_hom_left,
      Category.assoc ((biprod.isoProd _ _ ≪≫ prodPairIso F).hom) (Limits.Pi.map p),
      Limits.Pi.map_π, ← Category.assoc, biprod_prodPairIso_hom_left, biprod.map_fst]
  · rw [Category.assoc, biprod_prodPairIso_hom_right,
      Category.assoc ((biprod.isoProd _ _ ≪≫ prodPairIso F).hom) (Limits.Pi.map p),
      Limits.Pi.map_π, ← Category.assoc, biprod_prodPairIso_hom_right, biprod.map_snd]

/-- The termwise biproduct of two triangles, with its connecting map chosen by
comparison with the product triangle. -/
noncomputable def biproductTriangle (T₁ T₂ : Triangle C) : Triangle C :=
  Triangle.mk (biprod.map T₁.mor₁ T₂.mor₁) (biprod.map T₁.mor₂ T₂.mor₂)
    ((biproductTriangleProdIso₃ T₁ T₂).hom ≫
      (productTriangle (pairFunction T₁ T₂)).mor₃ ≫
      (shiftFunctor C (1 : ℤ)).map (biproductTriangleProdIso₁ T₁ T₂).inv)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The comparison between a biproduct of triangles and the corresponding
product triangle. -/
noncomputable def biproductTriangleIsoProduct (T₁ T₂ : Triangle C) :
    biproductTriangle T₁ T₂ ≅ productTriangle (pairFunction T₁ T₂) := by
  refine Triangle.isoMk _ _ (biproductTriangleProdIso₁ T₁ T₂)
    (biproductTriangleProdIso₂ T₁ T₂) (biproductTriangleProdIso₃ T₁ T₂) ?_ ?_ ?_
  · change @Eq (T₁.obj₁ ⊞ T₂.obj₁ ⟶ ∏ᶜ fun j ↦ (pairFunction T₁ T₂ j).obj₂) _ _
    simp only [biproductTriangle, Triangle.mk, biproductTriangleProdIso₁,
      biproductTriangleProdIso₂, productTriangle_mor₁,
      pairFunction_left, pairFunction_right]
    convert biprodProdPairIso_natural (fun j ↦ (pairFunction T₁ T₂ j).obj₁)
      (fun j ↦ (pairFunction T₁ T₂ j).obj₂) (fun j ↦ (pairFunction T₁ T₂ j).mor₁) using 1 <;>
      simp
  · change @Eq (T₁.obj₂ ⊞ T₂.obj₂ ⟶ ∏ᶜ fun j ↦ (pairFunction T₁ T₂ j).obj₃) _ _
    simp only [biproductTriangle, Triangle.mk, biproductTriangleProdIso₂,
      biproductTriangleProdIso₃, productTriangle_mor₂,
      pairFunction_left, pairFunction_right]
    convert biprodProdPairIso_natural (fun j ↦ (pairFunction T₁ T₂ j).obj₂)
      (fun j ↦ (pairFunction T₁ T₂ j).obj₃) (fun j ↦ (pairFunction T₁ T₂ j).mor₂) using 1 <;>
      simp
  · simp only [biproductTriangle, Triangle.mk]
    simpa only [← Category.assoc] using comp_map_inv_hom (shiftFunctor C (1 : ℤ))
      ((biproductTriangleProdIso₃ T₁ T₂).hom ≫
        (productTriangle (pairFunction T₁ T₂)).mor₃)
      (biproductTriangleProdIso₁ T₁ T₂)

lemma biproductTriangle_distinguished (T₁ T₂ : Triangle C)
    (hT₁ : T₁ ∈ distTriang C) (hT₂ : T₂ ∈ distTriang C) :
    biproductTriangle T₁ T₂ ∈ distTriang C := by
  apply isomorphic_distinguished _ (productTriangle_distinguished (pairFunction T₁ T₂) ?_)
    _ (biproductTriangleIsoProduct T₁ T₂)
  intro j
  cases j
  · exact hT₁
  · exact hT₂

lemma prop_biprod_of_triangulated (T : ObjectProperty C) [T.IsTriangulated]
    [T.IsClosedUnderIsomorphisms] {X Y : C} (hX : T X) (hY : T Y) : T (X ⊞ Y) :=
  T.prop_of_iso (biprod.isoProd X Y).symm (T.prop_prod X Y hX hY)

lemma biproductTriangle_mor₃_map_fst (T₁ T₂ : Triangle C) :
    (biproductTriangle T₁ T₂).mor₃ ≫ (shiftFunctor C (1 : ℤ)).map
      (biprod.fst : T₁.obj₁ ⊞ T₂.obj₁ ⟶ T₁.obj₁) = biprod.fst ≫ T₁.mor₃ := by
  let φ := (biproductTriangleIsoProduct T₁ T₂).hom ≫
    productTriangle.π (pairFunction T₁ T₂) WalkingPair.left
  have h := φ.comm₃
  dsimp [φ, productTriangle.π,TriangleMorphism.comp] at h
  have h₁ : (biproductTriangleIsoProduct T₁ T₂).hom.hom₁ =
      (biproductTriangleProdIso₁ T₁ T₂).hom := rfl
  have h₃ : (biproductTriangleIsoProduct T₁ T₂).hom.hom₃ =
      (biproductTriangleProdIso₃ T₁ T₂).hom := rfl
  rw [h₁, h₃] at h
  have hp₁ : (biproductTriangleProdIso₁ T₁ T₂).hom ≫
      Pi.π (fun k ↦ (pairFunction T₁ T₂ k).obj₁) WalkingPair.left = biprod.fst := by
    unfold biproductTriangleProdIso₁ productTriangle Triangle.mk
    dsimp only
    exact biprod_prodPairIso_hom_left (fun k ↦ (pairFunction T₁ T₂ k).obj₁)
  have hp₃ : (biproductTriangleProdIso₃ T₁ T₂).hom ≫
      Pi.π (fun k ↦ (pairFunction T₁ T₂ k).obj₃) WalkingPair.left = biprod.fst := by
    unfold biproductTriangleProdIso₃ productTriangle Triangle.mk
    dsimp only
    exact biprod_prodPairIso_hom_left (fun k ↦ (pairFunction T₁ T₂ k).obj₃)
  rw [hp₁, hp₃] at h
  exact h

lemma biproductTriangle_mor₃_map_snd (T₁ T₂ : Triangle C) :
    (biproductTriangle T₁ T₂).mor₃ ≫ (shiftFunctor C (1 : ℤ)).map
      (biprod.snd : T₁.obj₁ ⊞ T₂.obj₁ ⟶ T₂.obj₁) = biprod.snd ≫ T₂.mor₃ := by
  let φ := (biproductTriangleIsoProduct T₁ T₂).hom ≫
    productTriangle.π (pairFunction T₁ T₂) WalkingPair.right
  have h := φ.comm₃
  dsimp [φ, productTriangle.π,TriangleMorphism.comp] at h
  have h₁ : (biproductTriangleIsoProduct T₁ T₂).hom.hom₁ =
      (biproductTriangleProdIso₁ T₁ T₂).hom := rfl
  have h₃ : (biproductTriangleIsoProduct T₁ T₂).hom.hom₃ =
      (biproductTriangleProdIso₃ T₁ T₂).hom := rfl
  rw [h₁, h₃] at h
  have hp₁ : (biproductTriangleProdIso₁ T₁ T₂).hom ≫
      Pi.π (fun k ↦ (pairFunction T₁ T₂ k).obj₁) WalkingPair.right = biprod.snd := by
    unfold biproductTriangleProdIso₁ productTriangle Triangle.mk
    dsimp only
    exact biprod_prodPairIso_hom_right (fun k ↦ (pairFunction T₁ T₂ k).obj₁)
  have hp₃ : (biproductTriangleProdIso₃ T₁ T₂).hom ≫
      Pi.π (fun k ↦ (pairFunction T₁ T₂ k).obj₃) WalkingPair.right = biprod.snd := by
    unfold biproductTriangleProdIso₃ productTriangle Triangle.mk
    dsimp only
    exact biprod_prodPairIso_hom_right (fun k ↦ (pairFunction T₁ T₂ k).obj₃)
  rw [hp₁, hp₃] at h
  exact h

/-- An intertwiner of two split idempotents is diagonal in the associated strong
splitting coordinates. -/
lemma exists_biprod_map_of_comm {T : ObjectProperty C} {X Y : C}
    {eX : X ⟶ X} {eY : Y ⟶ Y} (sX : StrongSplitting T eX) (sY : StrongSplitting T eY)
    (u : X ⟶ Y) (hu : u ≫ eY = eX ≫ u) :
    ∃ (f : sX.image ⟶ sY.image) (g : sX.complement ⟶ sY.complement),
      sX.decomposition.inv ≫ u ≫ sY.decomposition.hom = biprod.map f g := by
  let u' := sX.decomposition.inv ≫ u ≫ sY.decomposition.hom
  let PX := biprod.map (𝟙 sX.image) (0 : sX.complement ⟶ sX.complement)
  let PY := biprod.map (𝟙 sY.image) (0 : sY.complement ⟶ sY.complement)
  have hsX : sX.decomposition.inv ≫ eX = PX ≫ sX.decomposition.inv := by
    rw [← cancel_mono sX.decomposition.hom]
    simp [PX, Category.assoc, sX.comm]
  have hu' : u' ≫ PY = PX ≫ u' := by
    calc
      u' ≫ PY = sX.decomposition.inv ≫ u ≫ eY ≫ sY.decomposition.hom := by
        simpa only [u', Category.assoc] using
          congrArg (fun k ↦ sX.decomposition.inv ≫ u ≫ k) sY.comm.symm
      _ = sX.decomposition.inv ≫ eX ≫ u ≫ sY.decomposition.hom := by
        simpa only [Category.assoc] using
          congrArg (fun k ↦ sX.decomposition.inv ≫ k ≫ sY.decomposition.hom) hu
      _ = PX ≫ u' := by
        simpa only [u', Category.assoc] using
          congrArg (fun k ↦ k ≫ u ≫ sY.decomposition.hom) hsX
  let a := biprod.inl ≫ u' ≫ biprod.fst
  let b := biprod.inl ≫ u' ≫ biprod.snd
  let c := biprod.inr ≫ u' ≫ biprod.fst
  let d := biprod.inr ≫ u' ≫ biprod.snd
  have hb : b = 0 := by
    have h := congrArg (fun k ↦ biprod.inl ≫ k ≫ biprod.snd) hu'
    have h' := h.symm
    simpa [b, PX, PY, Category.assoc] using h'
  have hc : c = 0 := by
    have h := congrArg (fun k ↦ biprod.inr ≫ k ≫ biprod.fst) hu'
    simpa [c, PX, PY, Category.assoc] using h
  refine ⟨a, d, ?_⟩
  change u' = biprod.map a d
  rw [← Biprod.ofComponents_eq u']
  change Biprod.ofComponents a b c d = biprod.map a d
  rw [hb, hc]
  ext <;> simp

/-- The zero-product observation in Lemma 2.1(2) of Le--Chen. -/
lemma comp_eq_zero_of_distTriang (Tr : Triangle C) (hTr : Tr ∈ distTriang C)
    {W X : C} (x : Tr.obj₃ ⟶ X) (y : W ⟶ Tr.obj₃)
    (hx : Tr.mor₂ ≫ x = 0) (hy : y ≫ Tr.mor₃ = 0) : y ≫ x = 0 := by
  obtain ⟨g, hg⟩ := Tr.yoneda_exact₃ hTr x hx
  rw [hg, ← Category.assoc, hy, zero_comp]

/-- The extension, or third-object, form of Le--Chen Proposition 2.3, with
images constrained to lie in a triangulated object property. -/
lemma splitsWithin_third {T : ObjectProperty C} [T.IsTriangulated]
    [T.IsClosedUnderIsomorphisms] {Tr : Triangle C} (hTr : Tr ∈ distTriang C)
    (e : Tr ⟶ Tr)
    (he₁ : e.hom₁ ≫ e.hom₁ = e.hom₁) (he₂ : e.hom₂ ≫ e.hom₂ = e.hom₂)
    (he₃ : e.hom₃ ≫ e.hom₃ = e.hom₃) :
    SplitsWithin T e.hom₁ → SplitsWithin T e.hom₂ → SplitsWithin T e.hom₃ := by
  intro s₁ s₂
  let sX := strongSplitting e.hom₁ s₁
  let sY := strongSplitting e.hom₂ s₂
  obtain ⟨a, d, hu⟩ := exists_biprod_map_of_comm sX sY Tr.mor₁ e.comm₁
  obtain ⟨Z₁, hZ₁, v₁, w₁, hT₁⟩ :=
    T.distinguished_cocone_triangle a sX.image_mem sY.image_mem
  obtain ⟨Z₂, v₂, w₂, hT₂⟩ := distinguished_cocone_triangle d
  let T₁ := Triangle.mk a v₁ w₁
  let T₂ := Triangle.mk d v₂ w₂
  change T₁ ∈ distTriang C at hT₁
  change T₂ ∈ distTriang C at hT₂
  let S := biproductTriangle T₁ T₂
  have hS : S ∈ distTriang C := biproductTriangle_distinguished T₁ T₂ hT₁ hT₂
  let E : S ≅ Tr := isoTriangleOfIso₁₂ S Tr hS hTr
    sX.decomposition.symm sY.decomposition.symm (by
      dsimp [S, T₁, T₂, biproductTriangle, Triangle.mk]
      rw [← hu]
      simp [Category.assoc])
  let θ := Triangle.π₃.mapIso E
  let Φ : S ⟶ S := E.hom ≫ e ≫ E.inv
  let PX := biprod.map (𝟙 sX.image) (0 : sX.complement ⟶ sX.complement)
  let PY := biprod.map (𝟙 sY.image) (0 : sY.complement ⟶ sY.complement)
  have hsX : sX.decomposition.inv ≫ e.hom₁ = PX ≫ sX.decomposition.inv := by
    rw [← cancel_mono sX.decomposition.hom]
    simp [PX, Category.assoc, sX.comm]
  have hsY : sY.decomposition.inv ≫ e.hom₂ = PY ≫ sY.decomposition.inv := by
    rw [← cancel_mono sY.decomposition.hom]
    simp [PY, Category.assoc, sY.comm]
  have hΦ₁ : Φ.hom₁ = PX := by
    change sX.decomposition.inv ≫ (e.hom₁ ≫ sX.decomposition.hom) = PX
    rw [sX.comm]
    exact sX.decomposition.inv_hom_id_assoc PX
  have hΦ₂ : Φ.hom₂ = PY := by
    change sY.decomposition.inv ≫ (e.hom₂ ≫ sY.decomposition.hom) = PY
    rw [sY.comm]
    exact sY.decomposition.inv_hom_id_assoc PY
  have hΦ₃ : Φ.hom₃ = θ.hom ≫ e.hom₃ ≫ θ.inv := rfl
  have hΦ_idem : Φ.hom₃ ≫ Φ.hom₃ = Φ.hom₃ := by
    simpa only [hΦ₃, Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun k ↦ θ.hom ≫ k ≫ θ.inv) he₃
  let a₁₁ := biprod.inl ≫ Φ.hom₃ ≫ biprod.fst
  let a₁₂ := biprod.inl ≫ Φ.hom₃ ≫ biprod.snd
  let a₂₁ := biprod.inr ≫ Φ.hom₃ ≫ biprod.fst
  let a₂₂ := biprod.inr ≫ Φ.hom₃ ≫ biprod.snd
  have hc₂ := Φ.comm₂
  rw [hΦ₂] at hc₂
  have hv₁₁ : v₁ ≫ a₁₁ = v₁ := by
    have h := congrArg (fun k ↦ biprod.inl ≫ k ≫ biprod.fst) hc₂
    simpa [S, T₁, T₂, biproductTriangle, a₁₁, PY, Category.assoc] using h
  have hv₁₂ : v₁ ≫ a₁₂ = 0 := by
    have h := congrArg (fun k ↦ biprod.inl ≫ k ≫ biprod.snd) hc₂
    simpa [S, T₁, T₂, biproductTriangle, a₁₂, PY, Category.assoc] using h
  have hv₂₁ : v₂ ≫ a₂₁ = 0 := by
    have h := congrArg (fun k ↦ biprod.inr ≫ k ≫ biprod.fst) hc₂
    simpa [S, T₁, T₂, biproductTriangle, a₂₁, PY, Category.assoc] using h
  have hv₂₂ : v₂ ≫ a₂₂ = 0 := by
    have h := congrArg (fun k ↦ biprod.inr ≫ k ≫ biprod.snd) hc₂
    simpa [S, T₁, T₂, biproductTriangle, a₂₂, PY, Category.assoc] using h
  have hc₃ := Φ.comm₃
  rw [hΦ₁] at hc₃
  have hPX_fst : (shiftFunctor C (1 : ℤ)).map PX ≫
      (shiftFunctor C (1 : ℤ)).map biprod.fst =
      (shiftFunctor C (1 : ℤ)).map biprod.fst := by
    rw [← Functor.map_comp]
    simp [PX]
  have hPX_snd : (shiftFunctor C (1 : ℤ)).map PX ≫
      (shiftFunctor C (1 : ℤ)).map biprod.snd = 0 := by
    rw [← Functor.map_comp]
    simp [PX]
  have hw₁₁ : a₁₁ ≫ w₁ = w₁ := by
    have hpost := congrArg (fun k ↦ k ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst) hc₃
    have hdiag := congrArg (fun k ↦ S.mor₃ ≫ k) hPX_fst
    have hcomp : S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst =
        (Φ.hom₃ ≫ S.mor₃) ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst := by
      calc
        S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst =
            S.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map PX ≫
              (shiftFunctor C (1 : ℤ)).map biprod.fst) := hdiag.symm
        _ = (S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map PX) ≫
            (shiftFunctor C (1 : ℤ)).map biprod.fst := (Category.assoc _ _ _).symm
        _ = _ := hpost
    have hp := biproductTriangle_mor₃_map_fst T₁ T₂
    change S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst =
      biprod.fst ≫ T₁.mor₃ at hp
    have hmain := (hp.symm.trans hcomp).trans (by simpa only [Category.assoc] using congrArg (fun k ↦ Φ.hom₃ ≫ k) hp)
    have h' := congrArg (fun k ↦ biprod.inl ≫ k) hmain
    simpa [a₁₁, T₁, Category.assoc, biprod.inl_fst_assoc] using h'.symm
  have hw₁₂ : a₁₂ ≫ w₂ = 0 := by
    have hpost := congrArg (fun k ↦ k ≫ (shiftFunctor C (1 : ℤ)).map biprod.snd) hc₃
    have hdiag := congrArg (fun k ↦ S.mor₃ ≫ k) hPX_snd
    have hcomp : S.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map PX ≫
        (shiftFunctor C (1 : ℤ)).map biprod.snd) =
        (Φ.hom₃ ≫ S.mor₃) ≫ (shiftFunctor C (1 : ℤ)).map biprod.snd := by
      calc
        S.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map PX ≫
            (shiftFunctor C (1 : ℤ)).map biprod.snd) =
            (S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map PX) ≫
              (shiftFunctor C (1 : ℤ)).map biprod.snd := (Category.assoc _ _ _).symm
        _ = _ := hpost
    have hp := biproductTriangle_mor₃_map_snd T₁ T₂
    change S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.snd =
      biprod.snd ≫ T₂.mor₃ at hp
    have hmain := ((hdiag.trans comp_zero).symm.trans hcomp).trans (by simpa only [Category.assoc] using congrArg (fun k ↦ Φ.hom₃ ≫ k) hp)
    have h' := congrArg (fun k ↦ biprod.inl ≫ k) hmain
    simpa [a₁₂, T₂, Category.assoc] using h'.symm
  have hw₂₁ : a₂₁ ≫ w₁ = 0 := by
    have hpost := congrArg (fun k ↦ k ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst) hc₃
    have hdiag := congrArg (fun k ↦ S.mor₃ ≫ k) hPX_fst
    have hcomp : S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst =
        (Φ.hom₃ ≫ S.mor₃) ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst := by
      calc
        S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst =
            S.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map PX ≫
              (shiftFunctor C (1 : ℤ)).map biprod.fst) := hdiag.symm
        _ = (S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map PX) ≫
            (shiftFunctor C (1 : ℤ)).map biprod.fst := (Category.assoc _ _ _).symm
        _ = _ := hpost
    have hp := biproductTriangle_mor₃_map_fst T₁ T₂
    change S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst =
      biprod.fst ≫ T₁.mor₃ at hp
    have hmain := (hp.symm.trans hcomp).trans (by simpa only [Category.assoc] using congrArg (fun k ↦ Φ.hom₃ ≫ k) hp)
    have h' := congrArg (fun k ↦ biprod.inr ≫ k) hmain
    simpa [a₂₁, T₁, Category.assoc, biprod.inr_fst_assoc] using h'.symm
  have hw₂₂ : a₂₂ ≫ w₂ = 0 := by
    have hpost := congrArg (fun k ↦ k ≫ (shiftFunctor C (1 : ℤ)).map biprod.snd) hc₃
    have hdiag := congrArg (fun k ↦ S.mor₃ ≫ k) hPX_snd
    have hcomp : S.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map PX ≫
        (shiftFunctor C (1 : ℤ)).map biprod.snd) =
        (Φ.hom₃ ≫ S.mor₃) ≫ (shiftFunctor C (1 : ℤ)).map biprod.snd := by
      calc
        S.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map PX ≫
            (shiftFunctor C (1 : ℤ)).map biprod.snd) =
            (S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map PX) ≫
              (shiftFunctor C (1 : ℤ)).map biprod.snd := (Category.assoc _ _ _).symm
        _ = _ := hpost
    have hp := biproductTriangle_mor₃_map_snd T₁ T₂
    change S.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.snd =
      biprod.snd ≫ T₂.mor₃ at hp
    have hmain := ((hdiag.trans comp_zero).symm.trans hcomp).trans (by simpa only [Category.assoc] using congrArg (fun k ↦ Φ.hom₃ ≫ k) hp)
    have h' := congrArg (fun k ↦ biprod.inr ≫ k) hmain
    simpa [a₂₂, T₂, Category.assoc] using h'.symm
  have hz₂₁₁₂ : a₂₁ ≫ a₁₂ = 0 :=
    comp_eq_zero_of_distTriang T₁ hT₁ a₁₂ a₂₁ hv₁₂ hw₂₁
  have hz₁₂₂₁ : a₁₂ ≫ a₂₁ = 0 :=
    comp_eq_zero_of_distTriang T₂ hT₂ a₂₁ a₁₂ hv₂₁ hw₁₂
  have hz₁₂₂₂ : a₁₂ ≫ a₂₂ = 0 :=
    comp_eq_zero_of_distTriang T₂ hT₂ a₂₂ a₁₂ hv₂₂ hw₁₂
  have hz₂₂₂₂ : a₂₂ ≫ a₂₂ = 0 :=
    comp_eq_zero_of_distTriang T₂ hT₂ a₂₂ a₂₂ hv₂₂ hw₂₂
  have hsq := hΦ_idem
  rw [← Biprod.ofComponents_eq Φ.hom₃, Biprod.ofComponents_comp] at hsq
  have hsq₁₁ : a₁₁ ≫ a₁₁ + a₁₂ ≫ a₂₁ = a₁₁ := by
    have h := congrArg (fun k ↦ biprod.inl ≫ k ≫ biprod.fst) hsq
    simpa [a₁₁, a₁₂, a₂₁, Category.assoc] using h
  have hsq₂₂ : a₂₁ ≫ a₁₂ + a₂₂ ≫ a₂₂ = a₂₂ := by
    have h := congrArg (fun k ↦ biprod.inr ≫ k ≫ biprod.snd) hsq
    simpa [a₁₂, a₂₁, a₂₂, Category.assoc] using h
  have ha₁₁_idem : a₁₁ ≫ a₁₁ = a₁₁ := by simpa [hz₁₂₂₁] using hsq₁₁
  haveI : IsIso a₁₁ := by
    let ψ : T₁ ⟶ T₁ :=
      { hom₁ := 𝟙 _
        hom₂ := 𝟙 _
        hom₃ := a₁₁
        comm₁ := by simp
        comm₂ := by simpa only [T₁, Triangle.mk, Category.id_comp] using hv₁₁
        comm₃ := by simpa [T₁, Triangle.mk] using hw₁₁.symm }
    have h := isIso₃_of_isIso₁₂ ψ hT₁ hT₁
      (by dsimp [ψ]; infer_instance) (by dsimp [ψ]; infer_instance)
    exact h
  have ha₁₁ : a₁₁ = 𝟙 Z₁ := by
    apply (cancel_epi a₁₁).1
    exact ha₁₁_idem.trans (Category.comp_id a₁₁).symm
  have ha₂₂ : a₂₂ = 0 := by simpa [hz₂₁₁₂, hz₂₂₂₂] using hsq₂₂.symm
  have hsplit : SplitsWithin T Φ.hom₃ := by
    refine ⟨T₁.obj₃, hZ₁, biprod.lift (𝟙 T₁.obj₃) a₁₂,
      biprod.desc (𝟙 T₁.obj₃) a₂₁, ?_, ?_⟩
    · simp [biprod.lift_desc, hz₁₂₂₁]
    · rw [← Biprod.ofComponents_eq Φ.hom₃]
      change biprod.desc (𝟙 T₁.obj₃) a₂₁ ≫ biprod.lift (𝟙 T₁.obj₃) a₁₂ =
        Biprod.ofComponents a₁₁ a₁₂ a₂₁ a₂₂
      rw [show a₁₁ = 𝟙 T₁.obj₃ from ha₁₁, ha₂₂]
      simp only [Biprod.ofComponents, biprod.desc_eq, biprod.lift_eq, Category.assoc,
        Preadditive.add_comp, Preadditive.comp_add, reassoc_of% hz₂₁₁₂, comp_zero, zero_comp,
        add_zero, zero_add, Category.comp_id, Category.id_comp]
      abel
  rw [hΦ₃] at hsplit
  exact SplitsWithin.of_iso θ _ _ (by simp [Category.assoc]) hsplit

/-! ### Axiom audit -/

#print axioms SplitsWithin.of_iso
#print axioms LeChen.strongSplitting
#print axioms LeChen.biproductTriangle_distinguished
#print axioms LeChen.exists_biprod_map_of_comm
#print axioms LeChen.comp_eq_zero_of_distTriang
#print axioms LeChen.splitsWithin_third

end LeChen

end
end RelativeFM.AffinePerfect
