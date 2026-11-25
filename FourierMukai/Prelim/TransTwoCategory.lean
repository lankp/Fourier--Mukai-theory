/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as
described in the file LICENSE. -/
import FourierMukai.Prelim.AppendixB
import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat

/-!
# The 2-category `Trans` of categories with translation

This file formalizes, from

  E. Guisado Villalgordo, P. Lank, *Relative Fourier--Mukai theory for algebraic spaces*
  (GL26), Appendix B:

* **Lemma B.2** (`lem:trans_is_2-cat`): categories with translation, their 1-morphisms
  `(F, ξ)` and transnatural transformations (Definition B.1, `def:cat_with_trans`) form a
  2-category `Trans`, uniquely, such that the forgetful assignment `Trans → Cat` is a
  2-functor.
  - `Trans.TransCat` is the type of objects; `Trans.instBicategory` the bicategory structure;
    `Trans.instStrict` says that it is a *strict* bicategory (Mathlib's
    `Bicategory.Strict`: 1-cell composition is associative and unital on the nose, and the
    associators and unitors are identities);
  - `Trans.forget : StrictPseudofunctor TransCat Cat` is the forgetful 2-functor (a strict
    pseudofunctor in Mathlib's terms);
  - `Trans.lemma_B2_faithful`: it is faithful on 2-morphisms;
  - `Trans.lemma_B2_unique`: any choice of identity 2-cells, vertical composition,
    whiskerings, associators and unitors on these 1- and 2-cells which the forgetful map
    sends to those of `Cat` is the one of `Trans.instBicategory`.
  The horizontal composite of two transnatural transformations, computed in `Cat`, is
  transnatural (`Trans.IsTransnatural.hcomp`), as in the paper's proof.
* **Lemma B.4(5)** (`lem:equiv_transadj`), in the paper's form: `Trans.lemma_B4` is the TFAE
  of Lemma B.4 with condition (5) stated as "`(F, ξ) ⊣ (G, ζ)` is an adjunction in the
  bicategory `Trans` (Mathlib's `Bicategory.Adjunction`) whose unit and counit are `η` and
  `ε`" (`Trans.IsAdjunctionInTrans`).  `Trans.isTransAdjunction_iff` shows that the
  unit/counit rendering `Trans.IsTransAdjunction` of `Prelim/AppendixB.lean` is equivalent
  to it.
* Lemma B.5(1) restated with adjunctions in `Trans`: `Trans.lemma_B5_existsUnique_bicategory`.

Nothing is assumed: no Stacks field, no hypothesis beyond the paper's.

## Deviations

* The paper asks the translation `T` of a category with translation to be an
  autoequivalence.  Here an object of `Trans` is a category with an arbitrary endofunctor
  `T`: none of the 2-categorical structure uses invertibility of `T`, and Lemma B.4 holds
  for arbitrary endofunctors.  The full sub-bicategory on the objects with `T` an
  equivalence is the paper's `Trans`; Lemma B.2 for it is the restriction of the statement
  here (all structure is computed in the same way).
* Objects are bundled at fixed universe levels: `TransCat.{v, u}` has underlying category in
  `Cat.{v, u}`.  Accordingly `Trans.lemma_B4` is stated for categories `C C' : Type u` with
  morphisms in `Type v`; the universe-polymorphic form of conditions (1)–(4) and of the
  unit/counit rendering of (5) is `Trans.lemma_B4_unitCounit` (`Prelim/AppendixB.lean`).
* "Uniquely" is stated as `Trans.lemma_B2_unique`: the 1-cells, their composition and
  identities, and the 2-cells are fixed by Definition B.1; we show that the remaining data
  of a bicategory (identity 2-cells, vertical composition, whiskerings, associators,
  unitors) is determined by asking the forgetful map to send it to the corresponding data
  of `Cat`, which is the paper's argument (faithfulness on 2-morphisms).
-/

@[expose] public section

universe v u

namespace RelativeFM

namespace Trans

open CategoryTheory Category Functor Bicategory

set_option linter.checkUnivs false in
/-- An object of the 2-category `Trans` (GL26, Definition B.1(1), `def:cat_with_trans`): a
category `base` with a translation endofunctor `T`.  The paper asks `T` to be an
autoequivalence; see the module docstring. -/
structure TransCat where
  /-- The underlying category. -/
  base : Cat.{v, u}
  /-- The translation. -/
  T : base ⥤ base

/-- A 1-morphism `(F, ξ) : (C, T) → (C', T')` of categories with translation (GL26,
Definition B.1(2)): a functor `F` with `ξ : T ⋙ F ≅ F ⋙ T'` (the paper's `ξ : FT ≅ T'F`). -/
@[ext]
structure Hom (X Y : TransCat.{v, u}) : Type (max u v) where
  /-- The underlying functor. -/
  F : X.base ⥤ Y.base
  /-- The translation compatibility isomorphism. -/
  ξ : X.T ⋙ F ≅ F ⋙ Y.T

/-- A 2-morphism of `Trans` (GL26, Definition B.1(5)): a transnatural transformation. -/
@[ext]
structure Hom₂ {X Y : TransCat.{v, u}} (f g : Hom X Y) : Type (max u v) where
  /-- The underlying natural transformation. -/
  τ : f.F ⟶ g.F
  transnat : IsTransnatural f.ξ g.ξ τ

/-! ### Transnaturality of the operations of `Cat` -/

section transnat

variable {C C' C'' : Type*} [Category* C] [Category* C'] [Category* C'']
  {T : C ⥤ C} {T' : C' ⥤ C'} {T'' : C'' ⥤ C''}

lemma IsTransnatural.id {F : C ⥤ C'} (ξ : T ⋙ F ≅ F ⋙ T') : IsTransnatural ξ ξ (𝟙 F) := by
  intro c; simp

lemma IsTransnatural.comp {F G H : C ⥤ C'} {ξ : T ⋙ F ≅ F ⋙ T'} {ζ : T ⋙ G ≅ G ⋙ T'}
    {θ : T ⋙ H ≅ H ⋙ T'} {α : F ⟶ G} {β : G ⟶ H} (hα : IsTransnatural ξ ζ α)
    (hβ : IsTransnatural ζ θ β) : IsTransnatural ξ θ (α ≫ β) := by
  intro c
  simp only [NatTrans.comp_app, assoc, T'.map_comp]
  rw [hβ c, reassoc_of% (hα c)]

lemma IsTransnatural.whiskerLeft {F : C ⥤ C'} (ξ : T ⋙ F ≅ F ⋙ T') {G H : C' ⥤ C''}
    {ζ : T' ⋙ G ≅ G ⋙ T''} {θ : T' ⋙ H ≅ H ⋙ T''} {β : G ⟶ H} (hβ : IsTransnatural ζ θ β) :
    IsTransnatural (compIso ξ ζ) (compIso ξ θ) (Functor.whiskerLeft F β) := by
  intro c
  simp only [Functor.whiskerLeft_app, compIso_hom_app]
  rw [← β.naturality_assoc]
  dsimp only [Functor.comp_obj]
  rw [hβ (F.obj c)]
  simp

lemma IsTransnatural.whiskerRight {F G : C ⥤ C'} {ξ : T ⋙ F ≅ F ⋙ T'}
    {ζ : T ⋙ G ≅ G ⋙ T'} {α : F ⟶ G} (hα : IsTransnatural ξ ζ α) {H : C' ⥤ C''}
    (θ : T' ⋙ H ≅ H ⋙ T'') :
    IsTransnatural (compIso ξ θ) (compIso ζ θ) (Functor.whiskerRight α H) := by
  intro c
  have hn := θ.hom.naturality (α.app c)
  dsimp at hn
  simp only [Functor.whiskerRight_app, compIso_hom_app, assoc]
  rw [← H.map_comp_assoc, hα c, H.map_comp, assoc, hn]

/-- The horizontal composite (computed in `Cat`) of two transnatural transformations is
transnatural: the key step of the proof of **Lemma B.2** (`lem:trans_is_2-cat`), done in
the manuscript by pasting the two transnaturality squares and the interchange law. -/
lemma IsTransnatural.hcomp {F F' : C ⥤ C'} {ξ : T ⋙ F ≅ F ⋙ T'} {ξ' : T ⋙ F' ≅ F' ⋙ T'}
    {G G' : C' ⥤ C''} {ζ : T' ⋙ G ≅ G ⋙ T''} {ζ' : T' ⋙ G' ≅ G' ⋙ T''}
    {α : F ⟶ F'} {β : G ⟶ G'} (hα : IsTransnatural ξ ξ' α) (hβ : IsTransnatural ζ ζ' β) :
    IsTransnatural (compIso ξ ζ) (compIso ξ' ζ') (NatTrans.hcomp α β) := by
  have h : NatTrans.hcomp α β = Functor.whiskerRight α G ≫ Functor.whiskerLeft F' β := by
    ext c
    exact (β.naturality (α.app c)).symm
  rw [h]
  exact (hα.whiskerRight ζ).comp (IsTransnatural.whiskerLeft ξ' hβ)

end transnat

/-! ### The bicategory -/

/-- The identity 1-morphism `1_{(C,T)} = (1_C, 1_T)` (GL26, Definition B.1(3)). -/
def Hom.id (X : TransCat.{v, u}) : Hom X X := ⟨𝟭 _, idIso X.T⟩

/-- The composite `(G, ζ)(F, ξ) = (GF, ζ_F · Gξ)` (GL26, Definition B.1(4)). -/
def Hom.comp {X Y Z : TransCat.{v, u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨f.F ⋙ g.F, compIso f.ξ g.ξ⟩

instance : CategoryStruct.{max u v} TransCat.{v, u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp] lemma id_F (X : TransCat.{v, u}) : (𝟙 X : X ⟶ X).F = 𝟭 _ := rfl
@[simp] lemma id_ξ (X : TransCat.{v, u}) : (𝟙 X : X ⟶ X).ξ = idIso X.T := rfl
@[simp] lemma comp_F {X Y Z : TransCat.{v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).F = f.F ⋙ g.F := rfl
@[simp] lemma comp_ξ {X Y Z : TransCat.{v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).ξ = compIso f.ξ g.ξ := rfl

/-- 2-morphisms compose vertically as in `Cat`. -/
instance homCategory (X Y : TransCat.{v, u}) : Category.{max u v} (X ⟶ Y) where
  Hom f g := Hom₂ f g
  id f := ⟨𝟙 f.F, IsTransnatural.id f.ξ⟩
  comp α β := ⟨α.τ ≫ β.τ, α.transnat.comp β.transnat⟩

@[ext]
lemma hom₂_ext {X Y : TransCat.{v, u}} {f g : X ⟶ Y} {α β : f ⟶ g} (h : α.τ = β.τ) :
    α = β :=
  Hom₂.ext h

@[simp] lemma id_τ {X Y : TransCat.{v, u}} (f : X ⟶ Y) : (𝟙 f : f ⟶ f).τ = 𝟙 f.F := rfl
@[simp] lemma comp_τ {X Y : TransCat.{v, u}} {f g h : X ⟶ Y} (α : f ⟶ g) (β : g ⟶ h) :
    (α ≫ β).τ = α.τ ≫ β.τ := rfl

/-- Build an isomorphism of 1-morphisms of `Trans` from a natural isomorphism with
transnatural `hom`. -/
def isoMk {X Y : TransCat.{v, u}} {f g : X ⟶ Y} (e : f.F ≅ g.F)
    (he : IsTransnatural f.ξ g.ξ e.hom) : f ≅ g where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, he.inv⟩

@[simp] lemma isoMk_hom_τ {X Y : TransCat.{v, u}} {f g : X ⟶ Y} (e : f.F ≅ g.F)
    (he : IsTransnatural f.ξ g.ξ e.hom) : (isoMk e he).hom.τ = e.hom := rfl
@[simp] lemma isoMk_inv_τ {X Y : TransCat.{v, u}} {f g : X ⟶ Y} (e : f.F ≅ g.F)
    (he : IsTransnatural f.ξ g.ξ e.hom) : (isoMk e he).inv.τ = e.inv := rfl

lemma associator_transnat {W X Y Z : TransCat.{v, u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    IsTransnatural ((f ≫ g) ≫ h).ξ (f ≫ (g ≫ h)).ξ
      (Functor.associator f.F g.F h.F).hom := by
  intro c; simp

lemma leftUnitor_transnat {X Y : TransCat.{v, u}} (f : X ⟶ Y) :
    IsTransnatural (𝟙 X ≫ f).ξ f.ξ (Functor.leftUnitor f.F).hom := by
  intro c; simp

lemma rightUnitor_transnat {X Y : TransCat.{v, u}} (f : X ⟶ Y) :
    IsTransnatural (f ≫ 𝟙 Y).ξ f.ξ (Functor.rightUnitor f.F).hom := by
  intro c; simp

/-- **Lemma B.2** (`lem:trans_is_2-cat`), existence: the bicategory `Trans`.  1-cells and
their composition are those of Definition B.1; 2-cells are transnatural transformations,
and all 2-cell operations (identities, vertical composition, whiskerings, associators,
unitors) are computed in `Cat`. -/
instance instBicategory : Bicategory.{max u v, max u v} TransCat.{v, u} where
  homCategory := homCategory
  whiskerLeft f _ _ η := ⟨Functor.whiskerLeft f.F η.τ, IsTransnatural.whiskerLeft f.ξ η.transnat⟩
  whiskerRight η h := ⟨Functor.whiskerRight η.τ h.F, η.transnat.whiskerRight h.ξ⟩
  associator f g h := isoMk (Functor.associator f.F g.F h.F) (associator_transnat f g h)
  leftUnitor f := isoMk (Functor.leftUnitor f.F) (leftUnitor_transnat f)
  rightUnitor f := isoMk (Functor.rightUnitor f.F) (rightUnitor_transnat f)
  whiskerLeft_id := by intros; apply Hom₂.ext; ext; simp
  whiskerLeft_comp := by intros; apply Hom₂.ext; ext; simp
  id_whiskerLeft := by intros; apply Hom₂.ext; ext; simp [isoMk]
  comp_whiskerLeft := by intros; apply Hom₂.ext; ext; simp [isoMk]
  id_whiskerRight := by intros; apply Hom₂.ext; ext; simp
  comp_whiskerRight := by intros; apply Hom₂.ext; ext; simp
  whiskerRight_id := by intros; apply Hom₂.ext; ext; simp [isoMk]
  whiskerRight_comp := by intros; apply Hom₂.ext; ext; simp [isoMk]
  whisker_assoc := by intros; apply Hom₂.ext; ext; simp [isoMk]
  whisker_exchange := by intros; apply Hom₂.ext; ext; simp
  pentagon := by intros; apply Hom₂.ext; ext; simp [isoMk]
  triangle := by intros; apply Hom₂.ext; ext; simp [isoMk]

@[simp] lemma whiskerLeft_τ {X Y Z : TransCat.{v, u}} (f : X ⟶ Y) {g h : Y ⟶ Z} (η : g ⟶ h) :
    (f ◁ η).τ = Functor.whiskerLeft f.F η.τ := rfl
@[simp] lemma whiskerRight_τ {X Y Z : TransCat.{v, u}} {f g : X ⟶ Y} (η : f ⟶ g) (h : Y ⟶ Z) :
    (η ▷ h).τ = Functor.whiskerRight η.τ h.F := rfl
@[simp] lemma associator_hom_τ {W X Y Z : TransCat.{v, u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) : (α_ f g h).hom.τ = (Functor.associator f.F g.F h.F).hom := rfl
@[simp] lemma associator_inv_τ {W X Y Z : TransCat.{v, u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) : (α_ f g h).inv.τ = (Functor.associator f.F g.F h.F).inv := rfl
@[simp] lemma leftUnitor_hom_τ {X Y : TransCat.{v, u}} (f : X ⟶ Y) :
    (λ_ f).hom.τ = (Functor.leftUnitor f.F).hom := rfl
@[simp] lemma leftUnitor_inv_τ {X Y : TransCat.{v, u}} (f : X ⟶ Y) :
    (λ_ f).inv.τ = (Functor.leftUnitor f.F).inv := rfl
@[simp] lemma rightUnitor_hom_τ {X Y : TransCat.{v, u}} (f : X ⟶ Y) :
    (ρ_ f).hom.τ = (Functor.rightUnitor f.F).hom := rfl
@[simp] lemma rightUnitor_inv_τ {X Y : TransCat.{v, u}} (f : X ⟶ Y) :
    (ρ_ f).inv.τ = (Functor.rightUnitor f.F).inv := rfl

/-! ### Strictness -/

lemma Hom.ext_of_eq {X Y : TransCat.{v, u}} {f g : X ⟶ Y} (hF : f.F = g.F)
    (hξ : ∀ c, f.ξ.hom.app c = eqToHom (by rw [hF]) ≫ g.ξ.hom.app c ≫ eqToHom (by rw [hF])) :
    f = g := by
  obtain ⟨F, ξ⟩ := f
  obtain ⟨G, ζ⟩ := g
  dsimp at hF
  subst hF
  simp only [eqToHom_refl, id_comp, comp_id] at hξ
  have : ξ = ζ := by ext c; exact hξ c
  subst this
  rfl

@[simp] lemma eqToHom_τ {X Y : TransCat.{v, u}} {f g : X ⟶ Y} (h : f = g) :
    (eqToHom h).τ = eqToHom (congrArg Hom.F h) := by
  subst h; rfl

/-- **Lemma B.2** (`lem:trans_is_2-cat`): `Trans` is a *strict* 2-category: composition of
1-morphisms is associative and unital on the nose, and the associators and unitors are
identities. -/
instance instStrict : Bicategory.Strict TransCat.{v, u} where
  id_comp f := Hom.ext rfl (heq_of_eq (by ext c; simp))
  comp_id f := Hom.ext rfl (heq_of_eq (by ext c; simp))
  assoc f g h := Hom.ext rfl (heq_of_eq (by ext c; simp))
  leftUnitor_eqToIso f := by ext : 2; rw [eqToIso.hom, eqToHom_τ]; rfl
  rightUnitor_eqToIso f := by ext : 2; rw [eqToIso.hom, eqToHom_τ]; rfl
  associator_eqToIso f g h := by ext : 2; rw [eqToIso.hom, eqToHom_τ]; rfl

/-! ### The forgetful 2-functor `Trans → Cat` -/

/-- The forgetful 2-functor `Trans → Cat` (GL26, before Lemma B.2): it forgets the
translation, forgets `ξ`, and is the identity on 2-morphisms.  It is a strict pseudofunctor
(Mathlib's `StrictPseudofunctor`): it preserves identities and composition of 1-morphisms
on the nose, and all 2-cell operations. -/
def forget : StrictPseudofunctor TransCat.{v, u} Cat.{v, u} :=
  StrictPseudofunctor.mk'
    { obj X := X.base
      map f := Cat.Hom.ofFunctor f.F
      map₂ η := Cat.Hom₂.ofNatTrans η.τ
      map₂_id f := rfl
      map₂_comp η θ := rfl
      map_id X := rfl
      map_comp f g := rfl
      map₂_whisker_left f g g' η := by
        ext x; simp only [Cat.Hom₂.comp_app]; exact ((id_comp _).trans (comp_id _)).symm
      map₂_whisker_right η g := by
        ext x; simp only [Cat.Hom₂.comp_app]; exact ((id_comp _).trans (comp_id _)).symm
      map₂_left_unitor f := by ext x; exact (comp_id _).symm
      map₂_right_unitor f := by ext x; exact (comp_id _).symm
      map₂_associator f g h := by
        ext x; exact ((id_comp _).trans (comp_id _)).symm }

@[simp] lemma forget_obj (X : TransCat.{v, u}) : forget.obj X = X.base := rfl
@[simp] lemma forget_map {X Y : TransCat.{v, u}} (f : X ⟶ Y) :
    forget.map f = Cat.Hom.ofFunctor f.F := rfl
@[simp] lemma forget_map₂ {X Y : TransCat.{v, u}} {f g : X ⟶ Y} (η : f ⟶ g) :
    forget.map₂ η = Cat.Hom₂.ofNatTrans η.τ := rfl

/-- **Lemma B.2** (`lem:trans_is_2-cat`): the forgetful 2-functor is faithful on
2-morphisms (a transnatural transformation is a natural transformation with a property). -/
theorem lemma_B2_faithful {X Y : TransCat.{v, u}} (f g : X ⟶ Y) :
    Function.Injective (fun η : f ⟶ g => forget.map₂ η) := by
  intro η θ h
  ext1
  exact congrArg Cat.Hom₂.toNatTrans h

/-! ### Uniqueness -/

set_option linter.checkUnivs false in
/-- The data of a bicategory on `TransCat` beyond its 1-cells (with their composition and
identities, Definition B.1(2)–(4)) and its 2-cells (transnatural transformations,
Definition B.1(5)): identity 2-cells, vertical composition, whiskerings, associators and
unitors (with their inverses). -/
@[ext]
structure TwoCellData where
  /-- identity 2-cells -/
  id₂ : ∀ {X Y : TransCat.{v, u}} (f : X ⟶ Y), Hom₂ f f
  /-- vertical composition -/
  vcomp : ∀ {X Y : TransCat.{v, u}} {f g h : X ⟶ Y}, Hom₂ f g → Hom₂ g h → Hom₂ f h
  /-- left whiskering -/
  whiskerLeft : ∀ {X Y Z : TransCat.{v, u}} (f : X ⟶ Y) {g h : Y ⟶ Z},
    Hom₂ g h → Hom₂ (f ≫ g) (f ≫ h)
  /-- right whiskering -/
  whiskerRight : ∀ {X Y Z : TransCat.{v, u}} {f g : X ⟶ Y}, Hom₂ f g → ∀ h : Y ⟶ Z,
    Hom₂ (f ≫ h) (g ≫ h)
  /-- associator -/
  assocHom : ∀ {W X Y Z : TransCat.{v, u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
    Hom₂ ((f ≫ g) ≫ h) (f ≫ g ≫ h)
  /-- inverse associator -/
  assocInv : ∀ {W X Y Z : TransCat.{v, u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
    Hom₂ (f ≫ g ≫ h) ((f ≫ g) ≫ h)
  /-- left unitor -/
  leftUnitorHom : ∀ {X Y : TransCat.{v, u}} (f : X ⟶ Y), Hom₂ (𝟙 X ≫ f) f
  /-- inverse left unitor -/
  leftUnitorInv : ∀ {X Y : TransCat.{v, u}} (f : X ⟶ Y), Hom₂ f (𝟙 X ≫ f)
  /-- right unitor -/
  rightUnitorHom : ∀ {X Y : TransCat.{v, u}} (f : X ⟶ Y), Hom₂ (f ≫ 𝟙 Y) f
  /-- inverse right unitor -/
  rightUnitorInv : ∀ {X Y : TransCat.{v, u}} (f : X ⟶ Y), Hom₂ f (f ≫ 𝟙 Y)

/-- The 2-cell data of `TwoCellData` is sent by the forgetful assignment to the
corresponding data of `Cat` (`Cat.bicategory`: identities, vertical composition and
whiskerings of natural transformations, and `Functor.associator`, `Functor.leftUnitor`,
`Functor.rightUnitor`). -/
def TwoCellData.IsOverCat (D : TwoCellData.{v, u}) : Prop :=
  (∀ {X Y : TransCat.{v, u}} (f : X ⟶ Y), (D.id₂ f).τ = 𝟙 f.F) ∧
  (∀ {X Y : TransCat.{v, u}} {f g h : X ⟶ Y} (α : Hom₂ f g) (β : Hom₂ g h),
    (D.vcomp α β).τ = α.τ ≫ β.τ) ∧
  (∀ {X Y Z : TransCat.{v, u}} (f : X ⟶ Y) {g h : Y ⟶ Z} (β : Hom₂ g h),
    (D.whiskerLeft f β).τ = Functor.whiskerLeft f.F β.τ) ∧
  (∀ {X Y Z : TransCat.{v, u}} {f g : X ⟶ Y} (α : Hom₂ f g) (h : Y ⟶ Z),
    (D.whiskerRight α h).τ = Functor.whiskerRight α.τ h.F) ∧
  (∀ {W X Y Z : TransCat.{v, u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
    (D.assocHom f g h).τ = (Functor.associator f.F g.F h.F).hom ∧
      (D.assocInv f g h).τ = (Functor.associator f.F g.F h.F).inv) ∧
  (∀ {X Y : TransCat.{v, u}} (f : X ⟶ Y),
    (D.leftUnitorHom f).τ = (Functor.leftUnitor f.F).hom ∧
      (D.leftUnitorInv f).τ = (Functor.leftUnitor f.F).inv ∧
      (D.rightUnitorHom f).τ = (Functor.rightUnitor f.F).hom ∧
      (D.rightUnitorInv f).τ = (Functor.rightUnitor f.F).inv)

/-- The 2-cell data of the bicategory `Trans.instBicategory`. -/
def TwoCellData.ofBicategory : TwoCellData.{v, u} where
  id₂ f := 𝟙 f
  vcomp {_ _ f g h} α β := ((α : f ⟶ g) ≫ (β : g ⟶ h) : f ⟶ h)
  whiskerLeft f _ _ β := f ◁ β
  whiskerRight α h := α ▷ h
  assocHom f g h := (α_ f g h).hom
  assocInv f g h := (α_ f g h).inv
  leftUnitorHom f := (λ_ f).hom
  leftUnitorInv f := (λ_ f).inv
  rightUnitorHom f := (ρ_ f).hom
  rightUnitorInv f := (ρ_ f).inv

lemma TwoCellData.ofBicategory_isOverCat : TwoCellData.ofBicategory.{v, u}.IsOverCat := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_, ?_, ?_⟩) <;>
    (try refine ⟨?_, ?_⟩) <;> rfl

/-- **Lemma B.2** (`lem:trans_is_2-cat`), uniqueness: the 1-cells, their composition and
identities, and the 2-cells being those of Definition B.1, there is exactly one choice of
the remaining data of a 2-category (identity 2-cells, vertical composition, whiskerings,
associators, unitors) which the forgetful assignment `Trans → Cat` sends to the data of
`Cat`, namely that of `Trans.instBicategory`.  As in the paper, this is faithfulness of the
forgetful assignment on 2-morphisms. -/
theorem lemma_B2_unique (D : TwoCellData.{v, u}) (hD : D.IsOverCat) :
    D = TwoCellData.ofBicategory := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hD
  ext1
  · funext X Y f; exact Hom₂.ext (h1 f)
  · funext X Y f g h α β; exact Hom₂.ext (h2 α β)
  · funext X Y Z f g h β; exact Hom₂.ext (h3 f β)
  · funext X Y Z f g α h; exact Hom₂.ext (h4 α h)
  · funext W X Y Z f g h; exact Hom₂.ext (h5 f g h).1
  · funext W X Y Z f g h; exact Hom₂.ext (h5 f g h).2
  · funext X Y f; exact Hom₂.ext (h6 f).1
  · funext X Y f; exact Hom₂.ext (h6 f).2.1
  · funext X Y f; exact Hom₂.ext (h6 f).2.2.1
  · funext X Y f; exact Hom₂.ext (h6 f).2.2.2

/-! ### Adjunctions in `Trans` and Lemma B.4(5) -/

variable {X Y : TransCat.{v, u}}

/-- Condition (5) of **Lemma B.4** (`lem:equiv_transadj`) in the paper's form:
`(F, ξ) ⊣ (G, ζ)` is an adjunction in the 2-category `Trans` (Mathlib's
`Bicategory.Adjunction` in `Trans.instBicategory`) whose unit and counit are the unit `η`
and counit `ε` of the given adjunction `adj : F ⊣ G` in `Cat`. -/
def IsAdjunctionInTrans (f : X ⟶ Y) (g : Y ⟶ X) (adj : f.F ⊣ g.F) : Prop :=
  ∃ A : Bicategory.Adjunction f g, A.unit.τ = adj.unit ∧ A.counit.τ = adj.counit

/-- The unit/counit rendering `IsTransAdjunction` (`Prelim/AppendixB.lean`) of an adjunction
in `Trans` is equivalent to being an adjunction in the bicategory `Trans`. -/
theorem isTransAdjunction_iff (f : X ⟶ Y) (g : Y ⟶ X) (adj : f.F ⊣ g.F) :
    IsTransAdjunction adj f.ξ g.ξ ↔ IsAdjunctionInTrans f g adj := by
  constructor
  · rintro ⟨hu, hc⟩
    let A : Bicategory.Adjunction f g :=
      { unit := ⟨adj.unit, hu⟩
        counit := ⟨adj.counit, hc⟩
        left_triangle := by
          ext c
          simp [leftZigzag, bicategoricalComp]
        right_triangle := by
          ext c
          simp [rightZigzag, bicategoricalComp] }
    exact ⟨A, rfl, rfl⟩
  · rintro ⟨A, hu, hc⟩
    refine ⟨?_, ?_⟩
    · have := A.unit.transnat
      rw [hu] at this
      exact this
    · have := A.counit.transnat
      rw [hc] at this
      exact this


/-- The category with translation `(C, T)` as an object of `Trans`. -/
abbrev TransCat.of (C : Type u) [Category.{v} C] (T : C ⥤ C) : TransCat.{v, u} :=
  ⟨Cat.of C, T⟩

/-- The 1-morphism `(F, ξ) : (C, T) → (C', T')` of `Trans`. -/
abbrev Hom.of {C C' : Type u} [Category.{v} C] [Category.{v} C'] {T : C ⥤ C} {T' : C' ⥤ C'}
    (F : C ⥤ C') (ξ : T ⋙ F ≅ F ⋙ T') : TransCat.of C T ⟶ TransCat.of C' T' :=
  ⟨F, ξ⟩

section B4

variable {C C' : Type u} [Category.{v} C] [Category.{v} C'] {T : C ⥤ C} {T' : C' ⥤ C'}
  {F : C ⥤ C'} {G : C' ⥤ C} (adj : F ⊣ G) (ξ : T ⋙ F ≅ F ⋙ T') (ζ : T' ⋙ G ≅ G ⋙ T)

/-- **Lemma B.4** (`lem:equiv_transadj`).  Let `(F, ξ) : (C, T) → (C', T')` and
`(G, ζ) : (C', T') → (C, T)` be 1-morphisms of categories with translation and `adj : F ⊣ G`
an adjunction in `Cat`, with unit `η` and counit `ε`.  The following are equivalent:
(1) `(ξ, ζ⁻¹)` are mates; (2) `ε` is transnatural; (3) `η` is transnatural; (4) the Hom-set
square commutes; (5) `(F, ξ) ⊣ (G, ζ)` is an adjunction in the 2-category `Trans`
(Lemma B.2; Mathlib's `Bicategory.Adjunction` in `Trans.instBicategory`) with unit `η` and
counit `ε`.

`T`, `T'` are arbitrary endofunctors; `C`, `C'` live in the universes of `TransCat.{v, u}`.
The universe-polymorphic form, with (5) in unit/counit form, is
`Trans.lemma_B4_unitCounit`. -/
theorem lemma_B4 :
    List.TFAE [AreMates adj ξ ζ, CounitTransnatural adj ξ ζ, UnitTransnatural adj ξ ζ,
      HomSquare adj ξ ζ, IsAdjunctionInTrans (Hom.of F ξ) (Hom.of G ζ) adj] := by
  have h := lemma_B4_unitCounit adj ξ ζ
  have h5 : IsTransAdjunction adj ξ ζ ↔ IsAdjunctionInTrans (Hom.of F ξ) (Hom.of G ζ) adj :=
    isTransAdjunction_iff (Hom.of F ξ) (Hom.of G ζ) adj
  tfae_have 1 ↔ 2 := h.out 0 1
  tfae_have 1 ↔ 3 := h.out 0 2
  tfae_have 1 ↔ 4 := h.out 0 3
  tfae_have 1 ↔ 5 := (h.out 0 4).trans h5
  tfae_finish

/-- **Lemma B.5(1)** (`lem:adj_and_equiv_in_trans`) with adjunctions in the 2-category
`Trans`: if `T`, `T'` are autoequivalences, there is a unique `ζ` such that
`(F, ξ) ⊣ (G, ζ)` is an adjunction in `Trans` with unit and counit those of `adj`. -/
theorem lemma_B5_existsUnique_bicategory [T.IsEquivalence] [T'.IsEquivalence] :
    ∃! ζ : T' ⋙ G ≅ G ⋙ T, IsAdjunctionInTrans (Hom.of F ξ) (Hom.of G ζ) adj := by
  obtain ⟨ζ, hζ, huniq⟩ := lemma_B5_existsUnique adj ξ
  refine ⟨ζ, (isTransAdjunction_iff (Hom.of F ξ) (Hom.of G ζ) adj).1 hζ, fun ζ' h => ?_⟩
  exact huniq ζ' ((isTransAdjunction_iff (Hom.of F ξ) (Hom.of G ζ') adj).2 h)

end B4

/-! ### Non-vacuity -/

/-- Every category, with the identity as translation, is an object of `Trans`. -/
abbrev TransCat.ofId (C : Cat.{v, u}) : TransCat.{v, u} := ⟨C, 𝟭 C⟩

/-- Non-vacuity of `IsAdjunctionInTrans` (condition (5) of Lemma B.4): the identity
1-morphism of any object of `Trans` is adjoint to itself in `Trans`, with unit and counit
those of `Adjunction.id`. -/
theorem isAdjunctionInTrans_id (X : TransCat.{v, u}) :
    IsAdjunctionInTrans (𝟙 X) (𝟙 X) Adjunction.id :=
  ⟨Bicategory.Adjunction.id X, rfl, rfl⟩

/-- Non-vacuity of the hypotheses of Lemma B.4 in a non-trivial case: any adjunction
between categories with the identity translation, with the trivial `ξ`, `ζ`, is an
adjunction in `Trans`. -/
theorem isAdjunctionInTrans_ofId {C C' : Type u} [Category.{v} C] [Category.{v} C']
    {F : C ⥤ C'} {G : C' ⥤ C} (adj : F ⊣ G) :
    IsAdjunctionInTrans (Hom.of (T := 𝟭 C) (T' := 𝟭 C') F (Iso.refl F))
      (Hom.of (T := 𝟭 C') (T' := 𝟭 C) G (Iso.refl G)) adj := by
  refine ((lemma_B4 adj (T := 𝟭 C) (T' := 𝟭 C') (Iso.refl F) (Iso.refl G)).out 2 4).1 ?_
  intro c
  simp

end Trans

end RelativeFM
