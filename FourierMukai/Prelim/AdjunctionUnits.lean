/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as
described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.TFAE

/-!
# Units and counits of an adjunction; adjoint equivalences

This file formalizes two categorical statements of
E. Guisado Villalgordo and P. Lank, *Relative Fourier--Mukai theory for algebraic spaces*
(GL26):

* **Lemma C.1** (`cmp:lem:units`) and the torsor remark after it;
* **Lemma-Definition 7.10** (`def:adj_equiv`), the equivalence of the four conditions
  defining an adjoint equivalence.

## What is proved

For Lemma C.1, with `adj : F ⊣ G` (in `Cat`, except where stated):

* (1) `Adjunction.twist adj β`: for `β : G ≅ G` the pair
  `(adj.unit ≫ whiskerLeft F β.hom, whiskerRight β.inv F ≫ adj.counit)`, i.e. the
  paper's `((βF) ∘ η, ε ∘ (Fβ⁻¹))`, is again an adjunction `F ⊣ G`
  (`Adjunction.twist_unit`, `Adjunction.twist_counit`); the same in an arbitrary
  bicategory is `Bicategorical.twist`;
* (2) `Adjunction.unitsComparison adj adj'` is the paper's `β = (Gε) ∘ (η'G)`; it is
  Mathlib's conjugate `conjugateEquiv adj adj' (𝟙 F)` of `id_F`
  (`unitsComparison_eq_conjugateEquiv`), hence invertible
  (`unitsComparisonIso`); for every `γ : G ≅ G` the two formulas
  `η' = (γF) ∘ η` and `ε' = ε ∘ (Fγ⁻¹)` are each equivalent to `γ = β`
  (`unit_eq_iff`, `counit_eq_iff`), so they are equivalent to each other
  and `β` is the unique automorphism satisfying them.  The headline statement is
  `RelativeFM.lemma_C_1`.
* The torsor remark (only the `Aut(G)` half): `twist` is an action of `Aut(G)`
  (`twist_refl`, `twist_trans`), and it is simply transitive
  (`existsUnique_twist_eq`).  The dual `Aut(F)`-torsor and the non-commutation of the
  two actions are not formalized.

For Lemma-Definition 7.10:

* `RepresentablyFullyFaithful F` is the footnote's notion in `Cat`: postcomposition
  `(D ⥤ C) ⥤ (D ⥤ C')` is full and faithful for every category `D` (in fixed universes
  `w, w'`).  `representablyFullyFaithful_iff` proves the footnote's claim that this is
  equivalent to `F` being full and faithful (in every pair of universes), rather than
  assuming it.
* `representablyFullyFaithful_left_iff_isIso_unit`,
  `representablyFullyFaithful_right_iff_isIso_counit`: the key step of the paper's proof.
* `RelativeFM.lemmaDef_7_10`: for `adj : F ⊣ G` the four conditions
  `F.IsEquivalence`, `G.IsEquivalence`,
  `RepresentablyFullyFaithful F ∧ RepresentablyFullyFaithful G`,
  `IsIso adj.unit ∧ IsIso adj.counit` are equivalent (`List.TFAE`).

## Deviations from the paper

* **Ambient 2-category.**  The paper states both results in an arbitrary 2-category `𝒯`.
  Part (1) of Lemma C.1 is proved in that generality, for an arbitrary Mathlib bicategory
  (`RelativeFM.Bicategorical.twist`; a strict 2-category is a special case).  Part (2) of
  Lemma C.1, the torsor remark and Lemma-Definition 7.10 are proved for `𝒯 = Cat` only, with
  Mathlib functors and natural transformations: Mathlib's `Bicategory.Adjunction` lacks
  the conjugate calculus used for (2) and the representable 2-functors `𝒯(D, -)` and
  2-Yoneda argument the paper uses for 7.10 (3) ⇔ (4).
* **Triang.**  Lemma C.1 says "in particular this holds in `Triang`".  The `Cat` version
  applies verbatim to the underlying functors of a triangulated adjunction.  It
  transfers to `Triang` once `β` is compatible with the shift data
  (`NatTrans.CommShift`); then the twisted unit and counit are composites of
  shift-compatible transformations.  That compatibility, and the fact that the comparison
  `β` of two triangulated adjunction structures is shift-compatible, are **not** proved
  here.
* In 7.10 "representably fully faithful" quantifies over categories `D` in one pair of
  universes `(w, w')`; the equivalence with full faithfulness holds for every choice.

## Mathlib

`Adjunction.ext` (an adjunction is determined by its unit),
`conjugateEquiv`/`conjugateEquiv_apply_app`/`conjugateEquiv_iso`,
`Functor.FullyFaithful.whiskeringRight`, `Adjunction.fullyFaithfulLOfIsIsoUnit`,
`Adjunction.fullyFaithfulROfIsIsoCounit`, `Adjunction.unit_isIso_of_L_fully_faithful`,
`Adjunction.counit_isIso_of_R_fully_faithful`, `Adjunction.toEquivalence`,
`Adjunction.isEquivalence_left_of_isEquivalence_right` and its dual.  No assumption is made.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Functor

universe w w' v₁ v₂ u₁ u₂

variable {C : Type u₁} {C' : Type u₂} [Category.{v₁} C] [Category.{v₂} C']

/-! ### Lemma C.1 (1): twisting by an automorphism of the right adjoint -/

namespace Adjunction

variable {F : C ⥤ C'} {G : C' ⥤ C}

/-- **Lemma C.1 (1)** (`cmp:lem:units`).  If `F ⊣ G` with unit `η` and counit `ε`, and
`β : G ≅ G`, then `F ⊣ G` with unit `(βF) ∘ η` and counit `ε ∘ (Fβ⁻¹)`.  In Mathlib's
diagrammatic notation the unit is `η ≫ whiskerLeft F β.hom` and the counit is
`whiskerRight β.inv F ≫ ε`. -/
@[simps]
def twist (adj : F ⊣ G) (β : G ≅ G) : F ⊣ G where
  unit := adj.unit ≫ whiskerLeft F β.hom
  counit := whiskerRight β.inv F ≫ adj.counit
  left_triangle_components X := by
    simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, whiskerLeft_app,
      whiskerRight_app]
    rw [F.map_comp, Category.assoc, ← F.map_comp_assoc (β.hom.app _), Iso.hom_inv_id_app,
      F.map_id, Category.id_comp, adj.left_triangle_components]
  right_triangle_components Y := by
    simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, whiskerLeft_app,
      whiskerRight_app]
    have h := β.hom.naturality (adj.counit.app Y)
    have hβ := β.hom.naturality (F.map (β.inv.app Y))
    have h' := adj.unit.naturality (β.inv.app Y)
    simp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, Functor.comp_map] at h hβ h'
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% hβ, ← h, ← reassoc_of% h', adj.right_triangle_components_assoc,
      Iso.inv_hom_id_app]

/-! ### Lemma C.1 (2): comparison of two unit/counit pairs -/

/-- The paper's `β = (Gε) ∘ (η'G) : G ⇒ G` for two adjunction structures `adj = (η, ε)` and
`adj' = (η', ε')` on `F ⊣ G` (Lemma C.1 (2), `cmp:lem:units`). -/
@[simps]
def unitsComparison (adj adj' : F ⊣ G) : G ⟶ G where
  app Y := adj'.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y)
  naturality Y Y' f := by
    have h₁ := adj'.unit.naturality (G.map f)
    have h₂ := adj.counit.naturality f
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h₁ h₂
    rw [reassoc_of% h₁, ← G.map_comp, Category.assoc, ← G.map_comp, h₂]

/-- `unitsComparison adj adj'` is the conjugate of `𝟙 F` with respect to `adj` and `adj'`
(the definition of `β` in the paper's proof of Lemma C.1 (2)). -/
theorem unitsComparison_eq_conjugateEquiv (adj adj' : F ⊣ G) :
    unitsComparison adj adj' = conjugateEquiv adj adj' (𝟙 F) := by
  ext Y
  simp [conjugateEquiv_apply_app]

instance (adj adj' : F ⊣ G) : IsIso (unitsComparison adj adj') := by
  rw [unitsComparison_eq_conjugateEquiv]; infer_instance

/-- The comparison `β` of Lemma C.1 (2) as an automorphism of `G`. -/
noncomputable def unitsComparisonIso (adj adj' : F ⊣ G) : G ≅ G :=
  asIso (unitsComparison adj adj')

@[simp]
theorem unitsComparisonIso_hom (adj adj' : F ⊣ G) :
    (unitsComparisonIso adj adj').hom = unitsComparison adj adj' := rfl

/-- Lemma C.1 (2), the unit formula: for `γ : G ≅ G`, `η' = (γF) ∘ η` iff `γ = β`. -/
theorem unit_eq_iff (adj adj' : F ⊣ G) (γ : G ≅ G) :
    adj'.unit = adj.unit ≫ whiskerLeft F γ.hom ↔ γ.hom = unitsComparison adj adj' := by
  constructor
  · intro h
    ext Y
    have hY := congr_arg (fun t => t.app (G.obj Y)) h
    simp only [NatTrans.comp_app, whiskerLeft_app, Functor.comp_obj, Functor.id_obj] at hY
    have hγ := γ.hom.naturality (adj.counit.app Y)
    simp only [Functor.comp_obj, Functor.id_obj] at hγ
    rw [unitsComparison_app, hY, Category.assoc, ← hγ, adj.right_triangle_components_assoc]
  · intro h
    ext X
    simp only [NatTrans.comp_app, whiskerLeft_app, Functor.comp_obj, Functor.id_obj, h,
      unitsComparison_app]
    have h₁ := adj'.unit.naturality (adj.unit.app X)
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h₁
    rw [reassoc_of% h₁, ← G.map_comp, adj.left_triangle_components, G.map_id,
      Category.comp_id]

/-- Lemma C.1 (2), the counit formula: for `γ : G ≅ G`, `ε' = ε ∘ (Fγ⁻¹)` iff `γ = β`. -/
theorem counit_eq_iff (adj adj' : F ⊣ G) (γ : G ≅ G) :
    adj'.counit = whiskerRight γ.inv F ≫ adj.counit ↔ γ.hom = unitsComparison adj adj' := by
  have key : adj'.counit = whiskerRight γ.inv F ≫ adj.counit ↔
      whiskerRight γ.hom F ≫ adj'.counit = adj.counit := by
    constructor
    · intro h
      rw [h, ← Category.assoc, ← whiskerRight_comp, γ.hom_inv_id, whiskerRight_id',
        Category.id_comp]
    · intro h
      rw [← h, ← Category.assoc, ← whiskerRight_comp, γ.inv_hom_id, whiskerRight_id',
        Category.id_comp]
  rw [key]
  constructor
  · intro h
    ext Y
    rw [unitsComparison_app, ← h]
    simp only [NatTrans.comp_app, whiskerRight_app, Functor.comp_obj, Functor.id_obj,
      Functor.map_comp]
    have h₁ := adj'.unit.naturality (γ.hom.app Y)
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h₁
    rw [← reassoc_of% h₁, adj'.right_triangle_components, Category.comp_id]
  · intro h
    ext Y
    simp only [NatTrans.comp_app, whiskerRight_app, Functor.comp_obj, Functor.id_obj, h,
      unitsComparison_app, Functor.map_comp, Category.assoc]
    have h₂ := adj'.counit.naturality (adj.counit.app Y)
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h₂
    rw [h₂, adj'.left_triangle_components_assoc]

/-- The comparison of an adjunction structure with itself is the identity. -/
theorem unitsComparison_self (adj : F ⊣ G) : unitsComparison adj adj = 𝟙 G := by
  ext Y; simp

/-- `twist adj (unitsComparisonIso adj adj') = adj'`. -/
theorem twist_unitsComparisonIso (adj adj' : F ⊣ G) :
    twist adj (unitsComparisonIso adj adj') = adj' := by
  apply Adjunction.ext
  rw [twist_unit, eq_comm, unit_eq_iff]
  rfl

/-! ### The torsor remark after Lemma C.1 (the `Aut(G)` half) -/

/-- Twisting by the identity does nothing. -/
theorem twist_refl (adj : F ⊣ G) : twist adj (Iso.refl G) = adj := by
  apply Adjunction.ext
  ext X; simp

/-- Twisting is an action of `Aut(G)`: twisting by `γ` and then by `δ` is twisting by the
composite `γ ≫ δ`. -/
theorem twist_trans (adj : F ⊣ G) (γ δ : G ≅ G) :
    twist (twist adj γ) δ = twist adj (γ ≪≫ δ) := by
  apply Adjunction.ext
  ext X; simp

/-- **Remark after Lemma C.1** (`cmp:lem:units`), `Aut(G)` half: the adjunction structures
on `F ⊣ G` form a torsor under `Aut(G)`; given `adj` and `adj'`, exactly one `γ : G ≅ G`
twists `adj` into `adj'`. -/
theorem existsUnique_twist_eq (adj adj' : F ⊣ G) :
    ∃! γ : G ≅ G, twist adj γ = adj' := by
  refine ⟨unitsComparisonIso adj adj', twist_unitsComparisonIso adj adj', ?_⟩
  intro γ hγ
  ext1
  rw [unitsComparisonIso_hom, ← unit_eq_iff, ← hγ, twist_unit]

end Adjunction

/-! ### Lemma C.1 (1) in an arbitrary bicategory -/

namespace Bicategorical

open CategoryTheory.Bicategory

variable {B : Type*} [CategoryTheory.Bicategory B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}

/-- **Lemma C.1 (1)** (`cmp:lem:units`), in an arbitrary bicategory `B` (in particular in a
strict 2-category).  If `f ⊣ g` with unit `η : 𝟙 a ⟶ f ≫ g` and counit `ε : g ≫ f ⟶ 𝟙 b`
(Mathlib writes `f ≫ g` for the paper's `G ∘ F`), and `β : g ≅ g`, then `f ⊣ g` with unit
`η ≫ f ◁ β.hom` (the paper's `(βF) ∘ η`) and counit `β.inv ▷ f ≫ ε` (the paper's
`ε ∘ (Fβ⁻¹)`).  The proof is the paper's whiskering computation, with the interchange law
`whisker_exchange` and the coherence tactic `bicategory`. -/
@[simps]
def twist (adj : CategoryTheory.Bicategory.Adjunction f g) (β : g ≅ g) :
    CategoryTheory.Bicategory.Adjunction f g where
  unit := adj.unit ≫ f ◁ β.hom
  counit := β.inv ▷ f ≫ adj.counit
  left_triangle := by
    calc leftZigzag (adj.unit ≫ f ◁ β.hom) (β.inv ▷ f ≫ adj.counit)
        = adj.unit ▷ f ⊗≫ f ◁ ((β.hom ≫ β.inv) ▷ f) ⊗≫ f ◁ adj.counit := by
          simp only [Bicategory.comp_whiskerRight, Bicategory.whiskerLeft_comp]; bicategory
      _ = leftZigzag adj.unit adj.counit := by
          rw [Iso.hom_inv_id, Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id]; bicategory
      _ = _ := adj.left_triangle
  right_triangle := by
    calc rightZigzag (adj.unit ≫ f ◁ β.hom) (β.inv ▷ f ≫ adj.counit)
        = g ◁ adj.unit ⊗≫ (g ◁ (f ◁ β.hom) ≫ β.inv ▷ (f ≫ g)) ⊗≫ adj.counit ▷ g := by
          bicategory
      _ = g ◁ adj.unit ⊗≫ (β.inv ▷ (f ≫ g) ≫ g ◁ (f ◁ β.hom)) ⊗≫ adj.counit ▷ g := by
          rw [whisker_exchange]
      _ = (g ◁ adj.unit ≫ β.inv ▷ (f ≫ g)) ⊗≫ ((g ≫ f) ◁ β.hom ≫ adj.counit ▷ g) := by
          bicategory
      _ = (β.inv ▷ 𝟙 a ≫ g ◁ adj.unit) ⊗≫ (adj.counit ▷ g ≫ 𝟙 b ◁ β.hom) := by
          rw [whisker_exchange, whisker_exchange]
      _ = β.inv ▷ 𝟙 a ⊗≫ rightZigzag adj.unit adj.counit ⊗≫ 𝟙 b ◁ β.hom := by
          bicategory
      _ = (ρ_ g).hom ≫ (β.inv ≫ β.hom) ≫ (λ_ g).inv := by
          rw [adj.right_triangle]; bicategory
      _ = (ρ_ g).hom ≫ (λ_ g).inv := by simp

end Bicategorical

open Adjunction in
/-- **Lemma C.1** (`cmp:lem:units`), in `Cat`.  Let `adj = (η, ε)` and `adj' = (η', ε')` be two
adjunction structures on `F ⊣ G`, and `β = (Gε) ∘ (η'G)` (`unitsComparison adj adj'`).
Then `β` is invertible, and an automorphism `γ` of `G` satisfies `η' = (γF) ∘ η` iff it
satisfies `ε' = ε ∘ (Fγ⁻¹)` iff `γ = β`; `β` satisfies both.  Part (1) of the lemma is
`RelativeFM.Adjunction.twist`. -/
theorem lemma_C_1 {F : C ⥤ C'} {G : C' ⥤ C} (adj adj' : F ⊣ G) :
    IsIso (unitsComparison adj adj') ∧
    adj'.unit = adj.unit ≫ whiskerLeft F (unitsComparisonIso adj adj').hom ∧
    adj'.counit = whiskerRight (unitsComparisonIso adj adj').inv F ≫ adj.counit ∧
    ∀ γ : G ≅ G,
      (adj'.unit = adj.unit ≫ whiskerLeft F γ.hom ↔ γ.hom = unitsComparison adj adj') ∧
      (adj'.counit = whiskerRight γ.inv F ≫ adj.counit ↔
        γ.hom = unitsComparison adj adj') :=
  ⟨inferInstance, (unit_eq_iff adj adj' _).2 rfl, (counit_eq_iff adj adj' _).2 rfl,
    fun γ => ⟨unit_eq_iff adj adj' γ, counit_eq_iff adj adj' γ⟩⟩

/-! ### Lemma-Definition 7.10 -/

/-- A functor `F : C ⥤ C'` is **representably fully faithful** (footnote to
Lemma-Definition 7.10, `def:adj_equiv`, in `𝒯 = Cat`) if postcomposition with `F`,
`(D ⥤ C) ⥤ (D ⥤ C')`, is full and faithful for every category `D : Type w` with
`Category.{w'} D`. -/
def RepresentablyFullyFaithful (F : C ⥤ C') : Prop :=
  ∀ (D : Type w) [Category.{w'} D],
    ((whiskeringRight D C C').obj F).Full ∧ ((whiskeringRight D C C').obj F).Faithful

/-- The underlying type of a category with one object and one morphism. -/
structure PointCat : Type w where
  /-- The unique object. -/
  mk ::

/-- The category with one object and one morphism, with morphisms in `Type w'`. -/
instance PointCat.category : Category.{w'} PointCat.{w} where
  Hom _ _ := PUnit.{w' + 1}
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- If postcomposition with `F` is full and faithful on functors out of a category `D` with an
object, then `F` is full and faithful (evaluate at constant functors). -/
theorem full_faithful_of_whiskeringRight (F : C ⥤ C') {D : Type*} [Category* D] (d : D)
    [((whiskeringRight D C C').obj F).Full] [((whiskeringRight D C C').obj F).Faithful] :
    F.Full ∧ F.Faithful := by
  refine ⟨⟨fun {X Y} f => ?_⟩, ⟨fun {X Y} f g hfg => ?_⟩⟩
  · obtain ⟨a, ha⟩ := ((whiskeringRight D C C').obj F).map_surjective
      (X := (Functor.const D).obj X) (Y := (Functor.const D).obj Y)
      ((Functor.constComp D X F).hom ≫ (Functor.const D).map f ≫ (Functor.constComp D Y F).inv)
    refine ⟨a.app d, ?_⟩
    simpa using congr_arg (fun t => t.app d) ha
  · have := ((whiskeringRight D C C').obj F).map_injective
      (X := (Functor.const D).obj X) (Y := (Functor.const D).obj Y)
      (a₁ := (Functor.const D).map f) (a₂ := (Functor.const D).map g) (by ext; simpa using hfg)
    exact congr_arg (fun t => t.app d) this

/-- The footnote to Lemma-Definition 7.10 (`def:adj_equiv`): in `Cat`, representable full
faithfulness is ordinary full faithfulness (for every choice of universes). -/
theorem representablyFullyFaithful_iff (F : C ⥤ C') :
    RepresentablyFullyFaithful.{w, w'} F ↔ F.Full ∧ F.Faithful := by
  constructor
  · intro h
    obtain ⟨_, _⟩ := h PointCat.{w}
    exact full_faithful_of_whiskeringRight F (D := PointCat.{w}) PointCat.mk
  · rintro ⟨_, _⟩ D _
    let hF : F.FullyFaithful := .ofFullyFaithful F
    exact ⟨(hF.whiskeringRight D).full, (hF.whiskeringRight D).faithful⟩

variable {F : C ⥤ C'} {G : C' ⥤ C}

/-- Step of the proof of Lemma-Definition 7.10 (`def:adj_equiv`): a left adjoint is
representably fully faithful iff the unit is an isomorphism. -/
theorem representablyFullyFaithful_left_iff_isIso_unit (adj : F ⊣ G) :
    RepresentablyFullyFaithful.{w, w'} F ↔ IsIso adj.unit := by
  rw [representablyFullyFaithful_iff]
  constructor
  · rintro ⟨_, _⟩; infer_instance
  · intro _
    exact ⟨adj.fullyFaithfulLOfIsIsoUnit.full, adj.fullyFaithfulLOfIsIsoUnit.faithful⟩

/-- Step of the proof of Lemma-Definition 7.10 (`def:adj_equiv`): a right adjoint is
representably fully faithful iff the counit is an isomorphism. -/
theorem representablyFullyFaithful_right_iff_isIso_counit (adj : F ⊣ G) :
    RepresentablyFullyFaithful.{w, w'} G ↔ IsIso adj.counit := by
  rw [representablyFullyFaithful_iff]
  constructor
  · rintro ⟨_, _⟩; infer_instance
  · intro _
    exact ⟨adj.fullyFaithfulROfIsIsoCounit.full, adj.fullyFaithfulROfIsIsoCounit.faithful⟩

/-- **Lemma-Definition 7.10** (`def:adj_equiv`), in `Cat`.  For an adjunction `F ⊣ G` with unit
`η` and counit `ε`, the following are equivalent:
(1) `F` is an equivalence; (2) `G` is an equivalence; (3) `F` and `G` are representably
fully faithful; (4) `η` and `ε` are isomorphisms. -/
theorem lemmaDef_7_10 (adj : F ⊣ G) :
    List.TFAE [F.IsEquivalence, G.IsEquivalence,
      RepresentablyFullyFaithful.{w, w'} F ∧ RepresentablyFullyFaithful.{w, w'} G,
      IsIso adj.unit ∧ IsIso adj.counit] := by
  tfae_have 1 → 4 := fun _ => ⟨inferInstance, inferInstance⟩
  tfae_have 2 → 4 := fun _ => ⟨inferInstance, inferInstance⟩
  tfae_have 4 → 1 := fun ⟨_, _⟩ => adj.toEquivalence.isEquivalence_functor
  tfae_have 4 → 2 := fun ⟨_, _⟩ => adj.toEquivalence.isEquivalence_inverse
  tfae_have 3 ↔ 4 := by
    rw [representablyFullyFaithful_left_iff_isIso_unit adj,
      representablyFullyFaithful_right_iff_isIso_counit adj]
  tfae_finish

end RelativeFM
