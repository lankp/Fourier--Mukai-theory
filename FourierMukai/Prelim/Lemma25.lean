/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Prelim.Generation
import FourierMukai.Prelim.Triangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeakApprox.CompactAb

/-!
# Lemma 2.5: equivalences of triangulated categories and their compact objects

Lemma 2.5 of

  E. Guisado Villalgordo, P. Lank, *Relative Fourier--Mukai theory for algebraic spaces*:
for an exact functor `F : T ⥤ S` between singly compactly generated
triangulated categories whose right adjoint preserves small coproducts, `F` is an
equivalence if and only if it restricts to an equivalence of compact objects.

**Compactness** is the paper's additive notion, `RelativeWeakApprox.IsCompactAb`: the
`AddCommGrpCat`-valued `Hom(X, -)` preserves `Type v₁`-small coproducts.  (Until
25 November 2026 this file used the `Type`-valued `IsCompact`, which no object of a
category with a zero object satisfies, so the lemma was vacuous; see
`Prelim/CompactnessAudit.lean`.  `IsCompact` is kept only as the refuted notion.)

**Rendering of the hypothesis.**  `SinglyCompactlyGenerated C G` is: `G` is compact and
`⟨G⟩‾ = C`, the latter by the universal property of generation under shifts, cones and
small coproducts (`ObjectProperty.IsLocalizingGenerator`).  The paper's definition ("`G`
compact and detects zero through its shifts") is equivalent to it under Stacks 09SN
(`RelativeFM.singlyCompactlyGenerated_iff`, `Prelim/Lemma24.lean`), and
`RelativeFM.lemma_2_5_of_tag09SN` states the lemma with the paper's definition; every
other hypothesis is the paper's.

**Proof** (the paper's): `F` preserves compacts by Neeman 1996 Thm 5.1
(`Adjunction.isCompactAb_leftAdjoint_obj`, the additive adjunction computation); an
equivalence restricts to compacts; conversely the unit and counit are trinatural
(`Trinatural.ofNatTrans`), isomorphisms on compacts, and their iso-loci are localizing
(`Trinatural.isoLocus_isClosedUnderColimitsOfShape`), hence everything.

Besides the main theorem the file provides, and these are used elsewhere in the
development: `Trinatural.ofNatTrans`, `NatTrans.isIso_app_of_isColimit`, and the criterion
`ObjectProperty.isIso_of_localizingGenerator_postcomp_bijective`.

Found by a member of the Ultramath run `smwufdjq4` (direction D8).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory Limits Pretriangulated

universe w v₁ v₂ u₁ u₂

namespace Trinatural

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]

/-- Every natural transformation compatible with shifts between triangulated
functors is trinatural.  On triangles, its three components are themselves a
morphism of triangles: the first two squares are naturality and the last one is
naturality together with compatibility with the shift. -/
def ofNatTrans (η : F ⟶ G) [NatTrans.CommShift η ℤ] : Trinatural F G where
  toNatTrans := η
  comm_shift X n := NatTrans.shift_app_comm η n X
  triangle_lift T _ := by
    let θ : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T :=
      { hom₁ := η.app T.obj₁
        hom₂ := η.app T.obj₂
        hom₃ := η.app T.obj₃
        comm₁ := η.naturality T.mor₁
        comm₂ := η.naturality T.mor₂
        comm₃ := by
          change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
              (η.app T.obj₁)⟦1⟧' =
            η.app T.obj₃ ≫ (G.map T.mor₃ ≫
              (G.commShiftIso (1 : ℤ)).hom.app T.obj₁)
          simp only [Category.assoc, NatTrans.shift_app_comm,
            ← η.naturality_assoc] }
    exact ⟨θ, rfl, rfl, rfl⟩

end Trinatural

namespace NatTrans

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {F G : C ⥤ D} (η : F ⟶ G)

/-- If a natural transformation is an isomorphism on every object of a diagram,
and both functors preserve a colimit of that diagram, then it is an isomorphism
at the colimit. -/
lemma isIso_app_of_isColimit {J : Type w} [Category.{w} J] {K : J ⥤ C}
    {c : Cocone K} (hcF : IsColimit (F.mapCocone c))
    (hcG : IsColimit (G.mapCocone c)) (hη : ∀ j, IsIso (η.app (K.obj j))) :
    IsIso (η.app c.pt) := by
  let t : Cocone (K ⋙ G) :=
    { pt := F.obj c.pt
      ι :=
        { app := fun j => inv (η.app (K.obj j)) ≫ F.map (c.ι.app j)
          naturality := by
            intro j j' f
            dsimp
            have hnat : G.map (K.map f) ≫ inv (η.app (K.obj j')) =
                inv (η.app (K.obj j)) ≫ F.map (K.map f) := by
              apply (IsIso.eq_inv_comp (η.app (K.obj j))).2
              rw [← Category.assoc, ← η.naturality, Category.assoc,
                IsIso.hom_inv_id, Category.comp_id]
            rw [← Category.assoc, hnat, Category.assoc, ← F.map_comp, c.w,
              Category.comp_id] } }
  let u : G.obj c.pt ⟶ F.obj c.pt := hcG.desc t
  have hu (j : J) : G.map (c.ι.app j) ≫ u =
      inv (η.app (K.obj j)) ≫ F.map (c.ι.app j) := hcG.fac t j
  have hn (j : J) : F.map (c.ι.app j) ≫ η.app c.pt =
      η.app (K.obj j) ≫ G.map (c.ι.app j) := by
    simpa using η.naturality (c.ι.app j)
  have h₁ : u ≫ η.app c.pt = 𝟙 _ := by
    apply hcG.hom_ext
    intro j
    simp only [Functor.mapCocone_ι_app]
    rw [← Category.assoc, hu, Category.assoc, hn]
    simp
  have h₂ : η.app c.pt ≫ u = 𝟙 _ := by
    apply hcF.hom_ext
    intro j
    simp only [Functor.mapCocone_ι_app]
    rw [← Category.assoc, hn, Category.assoc, hu]
    simp
  exact ⟨u, h₂, h₁⟩

end NatTrans

namespace ObjectProperty

variable {C : Type u₁} [Category.{v₁} C]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- `P` generates by shifts, cones and coproducts indexed by types in universe
`w`, expressed directly by the universal property of the localizing envelope.
This does not require constructing that envelope. -/
def IsLocalizingGenerator (P : ObjectProperty C) : Prop :=
  ∀ (Q : ObjectProperty C), Q.IsTriangulated → Q.IsClosedUnderIsomorphisms →
    (∀ (J : Type w), Q.IsClosedUnderColimitsOfShape (Discrete J)) →
    P ≤ Q → ∀ X, Q X

lemma IsLocalizingGenerator.mono {P Q : ObjectProperty C}
    (hP : IsLocalizingGenerator.{w} P) (hPQ : P ≤ Q) :
    IsLocalizingGenerator.{w} Q := by
  intro R hR hRiso hRcolim hQR X
  exact hP R hR hRiso hRcolim (hPQ.trans hQR) X

lemma leftOrthogonal_isClosedUnderColimitsOfShape (R : ObjectProperty C)
    (J : Type w) [Category.{w} J] :
    R.leftOrthogonal.IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  intro X hX
  obtain ⟨K, hK⟩ := hX
  intro Z f hZ
  apply (colimit.isColimit K).hom_ext
  intro j
  simp only [comp_zero]
  exact hK j _ hZ

/-- A localizing generating class detects zero objects. -/
lemma IsLocalizingGenerator.isZero_of_rightOrthogonal
    {P : ObjectProperty C} [P.IsStableUnderShift ℤ]
    (hP : IsLocalizingGenerator.{w} P) {Y : C}
    (hY : P.rightOrthogonal Y) : IsZero Y := by
  let R := (ObjectProperty.singleton Y).shiftClosure ℤ
  have hle : P ≤ R.leftOrthogonal := by
    intro X hX Z f hZ
    obtain ⟨Z₀, n, e, hZ₀⟩ := hZ
    have hZ₀' : Y = Z₀ := by
      simpa [R, ObjectProperty.singleton_iff] using hZ₀
    subst Z₀
    rw [← cancel_mono e.hom]
    simpa using (ObjectProperty.le_shift P.rightOrthogonal n Y hY) (f ≫ e.hom) hX
  rw [IsZero.iff_id_eq_zero]
  apply hP R.leftOrthogonal inferInstance inferInstance
    (fun J => leftOrthogonal_isClosedUnderColimitsOfShape R (Discrete J)) hle Y (𝟙 Y)
  change ∃ (Z : C) (n : ℤ) (_ : Y ≅ Z⟦n⟧), ObjectProperty.singleton Y Z
  exact ⟨Y, 0, (shiftFunctorZero C ℤ).symm.app Y, by simp⟩

lemma bijective_postcomp_shift {P : ObjectProperty C} [P.IsStableUnderShift ℤ]
    {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (A : C), P A → Function.Bijective (fun (a : A ⟶ X) => a ≫ f))
    (A : C) (hA : P A) (n : ℤ) :
    Function.Bijective (fun (a : A ⟶ X⟦n⟧) => a ≫ f⟦n⟧') := by
  let eX : (A⟦-n⟧ ⟶ X) ≃ (A ⟶ X⟦n⟧) :=
    (shiftEquiv C n).symm.toAdjunction.homEquiv A X
  let eY : (A⟦-n⟧ ⟶ Y) ≃ (A ⟶ Y⟦n⟧) :=
    (shiftEquiv C n).symm.toAdjunction.homEquiv A Y
  let φ := fun (a : A ⟶ X⟦n⟧) => a ≫ f⟦n⟧'
  apply (Function.Bijective.of_comp_iff φ eX.bijective).mp
  have hA' : P (A⟦-n⟧) := ObjectProperty.le_shift P (-n) A hA
  have hb : Function.Bijective (fun (a : A⟦-n⟧ ⟶ X) => eY (a ≫ f)) :=
    eY.bijective.comp (hf _ hA')
  have hs (a : A⟦-n⟧ ⟶ X) : eY (a ≫ f) = eX a ≫ f⟦n⟧' := by
    exact CategoryTheory.Adjunction.homEquiv_naturality_right
      (shiftEquiv C n).symm.toAdjunction a f
  convert hb using 1
  funext a
  simpa [φ] using (hs a).symm

/-- If `P` localizing generates, a morphism is an isomorphism whenever
postcomposition with it is bijective on maps out of every object of `P`. -/
theorem isIso_of_localizingGenerator_postcomp_bijective
    {P : ObjectProperty C} [P.IsStableUnderShift ℤ]
    (hP : IsLocalizingGenerator.{w} P) {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (A : C), P A → Function.Bijective (fun (a : A ⟶ X) => a ≫ f)) :
    IsIso f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  apply (Triangle.isZero₃_iff_isIso₁ _ hT).1
  apply hP.isZero_of_rightOrthogonal
  intro A a hA
  change A ⟶ Z at a
  have hf₁ := bijective_postcomp_shift f hf A hA (1 : ℤ)
  have ha : a ≫ h = 0 := by
    apply hf₁.1
    have hz : h ≫ f⟦1⟧' = 0 := comp_distTriang_mor_zero₃₁ (Triangle.mk f g h) hT
    dsimp
    rw [Category.assoc, hz, comp_zero, zero_comp]
  obtain ⟨b, rfl⟩ := Triangle.coyoneda_exact₃ _ hT a ha
  obtain ⟨c, rfl⟩ := (hf A hA).2 b
  have hz : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ (Triangle.mk f g h) hT
  change (c ≫ f) ≫ g = 0
  rw [Category.assoc, hz, comp_zero]

end ObjectProperty

namespace Trinatural

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]

/-- The iso-locus is closed under every colimit shape preserved by both
functors.  In particular, it is localizing when both functors preserve small
coproducts. -/
lemma isoLocus_isClosedUnderColimitsOfShape (η : Trinatural F G)
    (J : Type w) [Category.{w} J]
    [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G] :
    η.isoLocus.IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  intro X hX
  obtain ⟨K, hK⟩ := hX
  exact NatTrans.isIso_app_of_isColimit η.toNatTrans
    (isColimitOfPreserves F (colimit.isColimit K))
    (isColimitOfPreserves G (colimit.isColimit K)) hK

end Trinatural

namespace Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [F.IsTriangulated]
  (adj : F ⊣ G) {P : ObjectProperty C} {Q : ObjectProperty D}

/-- The generation step of **Lemma 2.5**.  Let `P` and `Q` generate by shifts,
cones and `w`-small coproducts.  If the unit is an isomorphism on `P`, the
counit is an isomorphism on `Q`, and the right adjoint preserves `w`-small
coproducts, then the adjunction is an adjoint equivalence.

The compactness step of the paper is deliberately separated from this theorem:
here `P` and `Q` may be arbitrary localizing generating classes. -/
theorem isEquivalence_of_unit_counit_on_localizingGenerators
    (hP : ObjectProperty.IsLocalizingGenerator.{w} P)
    (hQ : ObjectProperty.IsLocalizingGenerator.{w} Q)
    [∀ (J : Type w), PreservesColimitsOfShape (Discrete J) G]
    (hunit : ∀ X, P X → IsIso (adj.unit.app X))
    (hcounit : ∀ Y, Q Y → IsIso (adj.counit.app Y)) : F.IsEquivalence := by
  letI := adj.rightAdjointCommShift ℤ
  letI := adj.commShift_of_leftAdjoint ℤ
  letI : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  letI : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  letI := adj.isLeftAdjoint
  let η := Trinatural.ofNatTrans adj.unit
  let ε := Trinatural.ofNatTrans adj.counit
  have hη : ∀ X, IsIso (adj.unit.app X) := by
    intro X
    exact hP η.isoLocus inferInstance inferInstance
      (fun J => Trinatural.isoLocus_isClosedUnderColimitsOfShape η (Discrete J))
      hunit X
  have hε : ∀ Y, IsIso (adj.counit.app Y) := by
    intro Y
    exact hQ ε.isoLocus inferInstance inferInstance
      (fun J => Trinatural.isoLocus_isClosedUnderColimitsOfShape ε (Discrete J))
      hcounit Y
  letI : ∀ X, IsIso (adj.unit.app X) := hη
  letI : ∀ Y, IsIso (adj.counit.app Y) := hε
  exact adj.toEquivalence.isEquivalence_functor

end Adjunction

section TypeValuedCompactness

variable {C : Type u₁} [Category.{v₁} C]

/-- The `Type`-valued compactness: the covariant Hom functor `Hom(X, -) : C ⥤ Type v₁`
preserves coproducts indexed by types in universe `w`.

**This is not the paper's notion and it is not used for Lemma 2.4 or Lemma 2.5.**  A
coproduct in `Type` is a disjoint union, so in any category with a zero object no object
satisfies it (`RelativeFM.not_isCompact_of_hasZeroObject`, `Prelim/CompactnessAudit.lean`).
The definition is kept only for that refutation and for the comparison
`RelativeWeakApprox.isCoproductCompact_iff_relativeFM` (`WeakApprox/Lemma43.lean`).  The
paper's compactness is the additive one, `RelativeWeakApprox.IsCompactAb`, used below. -/
def IsCompact (X : C) : Prop :=
  ∀ (J : Type w) (K : Discrete J ⥤ C),
    PreservesColimit K (coyoneda.obj (Opposite.op X))

end TypeValuedCompactness

section CompactObjects

open RelativeWeakApprox

variable {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D] [Preadditive C] [Preadditive D]

/-- The object property of compact objects (GL26 §2.1, `T^c`): objects `X` whose additive
Hom functor `Hom(X, -) : C ⥤ AddCommGrpCat` preserves `Type v₁`-small coproducts
(`RelativeWeakApprox.IsCompactAb`), i.e. `⊕ᵢ Hom(X, Eᵢ) ≅ Hom(X, ∐ᵢ Eᵢ)`. -/
def compactObjects : ObjectProperty C := fun X => IsCompactAb X

instance : (compactObjects (C := C)).IsClosedUnderIsomorphisms where
  of_iso e hX := isCompactAb_of_iso e hX

namespace Adjunction

/-- A left adjoint preserves compact objects when its right adjoint preserves small
coproducts: Neeman, *The Grothendieck duality theorem via Bousfield's techniques and
Brown representability* (1996), Theorem 5.1, compactness part, as used in the paper's
proof of **Lemma 2.5** (`lem:equivalence_or_fully_faithful_via_compacts`).  With
additive compactness this is the computation
`Hom(FX, ∐ Y) ≅ Hom(X, G ∐ Y) ≅ Hom(X, ∐ GY) ≅ ⊕ Hom(X, GY) ≅ ⊕ Hom(FX, Y)`; it is
`RelativeWeakApprox.isCompactAb_leftAdjoint_obj'` (`WeakApprox/CompactAb.lean`), which
composes the additive adjunction isomorphism `preadditiveCompCoyonedaIso` with the
coproduct preservation of `G` and of `Hom(X, -)`. -/
theorem isCompactAb_leftAdjoint_obj {F : C ⥤ D} {G : D ⥤ C} [F.Additive] (adj : F ⊣ G)
    [∀ (J : Type v₁), PreservesColimitsOfShape (Discrete J) G]
    {X : C} (hX : IsCompactAb X) : IsCompactAb (F.obj X) :=
  isCompactAb_leftAdjoint_obj' adj hX (fun _ => inferInstance)

end Adjunction

instance [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] :
    (compactObjects (C := C)).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun X hX => isCompactAb_shift X n hX⟩

lemma isCompactAb_obj_of_isEquivalence {X : C} (F : C ⥤ D) [F.IsEquivalence] [F.Additive]
    (hX : IsCompactAb X) : IsCompactAb (F.obj X) :=
  have : F.asEquivalence.functor.Additive := ‹F.Additive›
  Adjunction.isCompactAb_leftAdjoint_obj F.asEquivalence.toAdjunction hX

lemma isCompactAb_obj_iff_of_isEquivalence (F : C ⥤ D) [F.IsEquivalence] [F.Additive]
    (X : C) : IsCompactAb (F.obj X) ↔ IsCompactAb X := by
  constructor
  · intro hX
    have : F.asEquivalence.functor.Additive := ‹F.Additive›
    have : F.inv.Additive := Equivalence.inverse_additive F.asEquivalence
    have h := isCompactAb_obj_of_isEquivalence F.inv hX
    exact isCompactAb_of_iso (F.asEquivalence.unitIso.symm.app X) h
  · exact isCompactAb_obj_of_isEquivalence F

lemma compactObjects_inverseImage_eq_of_isEquivalence (F : C ⥤ D) [F.IsEquivalence]
    [F.Additive] :
    (compactObjects (C := D)).inverseImage F = compactObjects (C := C) := by
  ext X
  exact isCompactAb_obj_iff_of_isEquivalence F X

/-- The forward implication in **Lemma 2.5**
(`lem:equivalence_or_fully_faithful_via_compacts`): an (additive) equivalence induces an
equivalence between the full subcategories of compact objects. -/
noncomputable def compactRestrictionEquivalence (F : C ⥤ D) [F.IsEquivalence] [F.Additive] :
    (compactObjects (C := C)).FullSubcategory ≌ (compactObjects (C := D)).FullSubcategory :=
  F.asEquivalence.congrFullSubcategory (compactObjects_inverseImage_eq_of_isEquivalence F)

end CompactObjects

section Lemma25

open RelativeWeakApprox

variable {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- "`C` is compactly generated by the single object `G`" (GL26 §2.1, the hypothesis of
**Lemma 2.5**, `lem:equivalence_or_fully_faithful_via_compacts`): `G` is compact in the
additive sense (`RelativeWeakApprox.IsCompactAb`) and `⟨G⟩‾ = C`, i.e. every
triangulated, isomorphism-closed property closed under small (`Type v₁`-indexed)
coproducts and containing `G` holds everywhere.

The paper's definition is "`G` is compact and `Hom(G⟦n⟧, E) = 0` for all `n` implies
`E ≅ 0`".  Under Stacks 09SN the two agree:
`RelativeFM.singlyCompactlyGenerated_iff` (`Prelim/Lemma24.lean`), and
`RelativeFM.lemma_2_5_of_tag09SN` states Lemma 2.5 with the paper's definition. -/
def SinglyCompactlyGenerated (C : Type u₁) [Category.{v₁} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (G : C) : Prop :=
  IsCompactAb G ∧ ObjectProperty.IsLocalizingGenerator.{v₁} (ObjectProperty.singleton G)

lemma compactObjects_isLocalizingGenerator {G : C} (hG : SinglyCompactlyGenerated C G) :
    ObjectProperty.IsLocalizingGenerator.{v₁} (compactObjects (C := C)) := by
  apply hG.2.mono
  intro X hX
  have hGX : G = X := by simpa [ObjectProperty.singleton_iff] using hX
  rw [← hGX]
  exact hG.1

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- The functor between the full subcategories of compact objects induced by an additive
left adjoint whose right adjoint preserves small coproducts. -/
def compactRestriction [F.Additive] [∀ (J : Type v₁), PreservesColimitsOfShape (Discrete J) G] :
    (compactObjects (C := C)).FullSubcategory ⥤ (compactObjects (C := D)).FullSubcategory :=
  (compactObjects (C := D)).lift ((compactObjects (C := C)).ι ⋙ F)
    (fun X => Adjunction.isCompactAb_leftAdjoint_obj adj X.property)

variable [F.Additive] [∀ (J : Type v₁), PreservesColimitsOfShape (Discrete J) G]
  [(compactRestriction adj).IsEquivalence]

include adj

/-- Full faithfulness on compact Hom-sets follows from equivalence of the
compact restriction. -/
lemma compact_map_bijective {X Y : C} (hX : IsCompactAb X) (hY : IsCompactAb Y) :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  let A : (compactObjects (C := C)).FullSubcategory := ⟨X, hX⟩
  let B : (compactObjects (C := C)).FullSubcategory := ⟨Y, hY⟩
  let K := compactRestriction adj
  have hb := K.asEquivalence.fullyFaithfulFunctor.map_bijective A B
  constructor
  · intro f g hfg
    have hp : K.map (ObjectProperty.homMk f : A ⟶ B) =
        K.map (ObjectProperty.homMk g : A ⟶ B) := by
      apply ObjectProperty.hom_ext
      exact hfg
    have heq := hb.1 hp
    exact congrArg InducedCategory.Hom.hom heq
  · intro g
    obtain ⟨f, hf⟩ := hb.2 (ObjectProperty.homMk g : K.obj A ⟶ K.obj B)
    have hf' : K.map f = ObjectProperty.homMk g := hf
    refine ⟨f.hom, ?_⟩
    have hf'' := congrArg (fun k : K.obj A ⟶ K.obj B => k.hom) hf'
    simpa [K, compactRestriction, A, B, ObjectProperty.lift, ObjectProperty.ι] using hf''

/-- Essential surjectivity of the compact restriction, stated with ambient
objects and ambient isomorphisms. -/
lemma exists_compact_iso (Y : D) (hY : IsCompactAb Y) :
    ∃ (X : C), IsCompactAb X ∧ Nonempty (F.obj X ≅ Y) := by
  let K := compactRestriction adj
  obtain ⟨X, ⟨e⟩⟩ := K.asEquivalence.essSurj_functor.mem_essImage
    (⟨Y, hY⟩ : (compactObjects (C := D)).FullSubcategory)
  exact ⟨X.obj, X.property, ⟨(compactObjects (C := D)).ι.mapIso e⟩⟩

/-- The unit is an isomorphism at each compact object when the adjunction's
left adjoint is an equivalence on compact objects and the compact objects
localizing generate. -/
lemma isIso_unit_app_of_compactRestriction
    (hP : ObjectProperty.IsLocalizingGenerator.{v₁} (compactObjects (C := C)))
    {X : C} (hX : IsCompactAb X) : IsIso (adj.unit.app X) := by
  apply ObjectProperty.isIso_of_localizingGenerator_postcomp_bijective hP
  intro A hA
  have heq : (fun (a : A ⟶ X) => a ≫ adj.unit.app X) =
      (fun a => adj.homEquiv A (F.obj X) (F.map a)) := by
    funext a
    simpa only [CategoryTheory.Adjunction.homEquiv_unit, Functor.id_map,
      Functor.comp_map] using (adj.unit.naturality a)
  refine heq.symm ▸ ?_
  exact (adj.homEquiv A (F.obj X)).bijective.comp (compact_map_bijective (adj := adj) hA hX)

/-- The converse implication in **Lemma 2.5**, using the localizing-envelope
formulation of compact generation. -/
theorem isEquivalence_of_compactRestriction
    (hP : ObjectProperty.IsLocalizingGenerator.{v₁} (compactObjects (C := C)))
    (hQ : ObjectProperty.IsLocalizingGenerator.{v₁} (compactObjects (C := D)))
    [F.CommShift ℤ] [F.IsTriangulated] : F.IsEquivalence := by
  have hunitCompact : ∀ X, IsCompactAb X → IsIso (adj.unit.app X) :=
    fun X hX => isIso_unit_app_of_compactRestriction adj hP hX
  have hunit : ∀ X, IsIso (adj.unit.app X) := by
    letI := adj.rightAdjointCommShift ℤ
    letI := adj.commShift_of_leftAdjoint ℤ
    letI : G.IsTriangulated := adj.isTriangulated_rightAdjoint
    letI : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
    letI := adj.isLeftAdjoint
    let η := Trinatural.ofNatTrans adj.unit
    intro X
    exact hP η.isoLocus inferInstance inferInstance
      (fun J => Trinatural.isoLocus_isClosedUnderColimitsOfShape η (Discrete J))
      hunitCompact X
  letI : ∀ X, IsIso (adj.unit.app X) := hunit
  letI : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  letI : F.Faithful := adj.fullyFaithfulLOfIsIsoUnit.faithful
  letI : F.Full := adj.fullyFaithfulLOfIsIsoUnit.full
  have hcounitCompact : ∀ Y, IsCompactAb Y → IsIso (adj.counit.app Y) := by
    intro Y hY
    obtain ⟨X, hX, ⟨e⟩⟩ := exists_compact_iso (adj := adj) Y hY
    exact adj.isIso_counit_app_of_iso e.symm
  exact Adjunction.isEquivalence_of_unit_counit_on_localizingGenerators (adj := adj)
    hP hQ hunitCompact hcounitCompact

end Adjunction

/-- **Lemma 2.5** (`lem:equivalence_or_fully_faithful_via_compacts`).  Let `F ⊣ G` be an
adjunction between triangulated categories `C`, `D`, each compactly generated by a single
object (`SinglyCompactlyGenerated`), with `F` exact and `G` preserving small coproducts.
Then `F` is an equivalence if and only if its restriction `C^c ⥤ D^c` to compact objects
is an equivalence.

Compactness is the paper's additive one (`RelativeWeakApprox.IsCompactAb`), with
`Type v₁`-small coproducts.  "Compactly generated by `G`" is rendered as `G` compact and
`⟨G⟩‾ = C` (`SinglyCompactlyGenerated`); the paper's zero-detection form is equivalent to
it under Stacks 09SN (`RelativeFM.singlyCompactlyGenerated_iff`), and
`RelativeFM.lemma_2_5_of_tag09SN` (`Prelim/Lemma24.lean`) states the lemma in that form.
The paper's restriction to compacts lands in `D^c` by Neeman's Theorem 5.1
(`Adjunction.isCompactAb_leftAdjoint_obj`), which is how `compactRestriction` is built. -/
theorem lemma_2_5 {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (GT : C) (hT : SinglyCompactlyGenerated C GT)
    (GS : D) (hS : SinglyCompactlyGenerated D GS)
    [∀ (J : Type v₁), PreservesColimitsOfShape (Discrete J) G]
    [F.CommShift ℤ] [F.IsTriangulated] :
    F.IsEquivalence ↔ (Adjunction.compactRestriction adj).IsEquivalence := by
  let hP := compactObjects_isLocalizingGenerator hT
  let hQ := compactObjects_isLocalizingGenerator hS
  constructor
  · intro hF
    letI : F.IsEquivalence := hF
    exact (compactRestrictionEquivalence F).isEquivalence_functor
  · intro h
    letI : (Adjunction.compactRestriction adj).IsEquivalence := h
    exact Adjunction.isEquivalence_of_compactRestriction (adj := adj) hP hQ

end Lemma25

end RelativeFM
