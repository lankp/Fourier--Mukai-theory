/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Prelim.BaseChangeMates

/-!
# `PullPushData` from a pullback pseudofunctor and adjunctions

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), §7.2.
The abstract setting `RelativeFM.BaseChangeMates.PullPushData` of GL26 §7.2 asks for two
pseudofunctors `L(-)^*`, `R(-)_*`, adjunctions `Lf^* ⊣ Rf_*`, and the conjugacy of their structure
isomorphisms (Lipman (3.6.2); GL26 Lemma 2.13, `lem:spacey_Lipman_Hashimoto`).  This file builds
one from less: a pseudofunctor `L(-)^*` (values, composition and unit isomorphisms, associativity
and the two unit laws) and adjunctions `Lf^* ⊣ Rf_*`.  The structure isomorphisms of `R(-)_*` are
*defined* as the conjugates of those of `L(-)^*` (`R(f ≫ g)_* ≅ Rg_* Rf_*` is the conjugate of
`L(f ≫ g)^* ≅ Lf^* Lg^*`, which is how the Stacks Project defines it, Stacks 0D6E, and how
AxiomMath defines `AlgebraicGeometry.Space.smallEtaleDerivedPushforwardCompIso`, by uniqueness of
adjoints); the pseudofunctor axioms of `R(-)_*` are then *proved* from those of `L(-)^*` by
conjugation (Mathlib `conjugateEquiv_comp`, `conjugateEquiv_whiskerLeft`,
`conjugateEquiv_whiskerRight`, `conjugateEquiv_associator_hom`, `conjugateEquiv_leftUnitor_hom`,
`conjugateEquiv_rightUnitor_hom`), and the conjugacy fields `conj_comp`, `conj_id` hold by
definition.

So GL26 Lemma 2.13 (Lipman (3.6.2)) is not an input here: once `R(-)_*`'s composition law is the
conjugate one, the two pseudofunctors are conjugate by construction, and the content of
Lemma 2.13 that remains — that the conjugate composition law is coherent — is proved.

Nothing is assumed; Mathlib and `FourierMukai/Prelim/BaseChangeMates.lean` only.

## Main definitions

* `PullPseudofunctor S`: the input data.
* `PullPseudofunctor.toPullPushData`: the resulting `PullPushData S`.
* `PullPseudofunctor.push_assoc`, `push_id_comp`, `push_comp_id`: the pseudofunctor axioms of
  the conjugate composition law of `R(-)_*`.
-/

noncomputable section

namespace RelativeFM.Spaces.BaseChange

open CategoryTheory CategoryTheory.Functor RelativeFM.BaseChangeMates

universe v u v₁ u₁

set_option linter.checkUnivs false in
/-- A contravariant pseudofunctor `L(-)^*` on a category of spaces `S` (values `obj X`, unit and
composition isomorphisms, associativity and unit laws, written exactly as the corresponding fields
of `PullPushData`), together with functors `Rf_*` and adjunctions `Lf^* ⊣ Rf_*`.  No structure on
`R(-)_*` is given: it is induced by conjugation (`toPullPushData`). -/
structure PullPseudofunctor (S : Type u) [Category.{v} S] where
  /-- The category attached to a space. -/
  obj : S → Type u₁
  /-- The categories `obj X`. -/
  [cat : ∀ X, Category.{v₁} (obj X)]
  /-- Derived pullback `Lf^*`. -/
  pull {X Y : S} (f : X ⟶ Y) : obj Y ⥤ obj X
  /-- Derived pushforward `Rf_*`. -/
  push {X Y : S} (f : X ⟶ Y) : obj X ⥤ obj Y
  /-- `Lf^* ⊣ Rf_*`. -/
  adj {X Y : S} (f : X ⟶ Y) : pull f ⊣ push f
  /-- Unit isomorphism `L(id)^* ≅ id`. -/
  pullId (X : S) : pull (𝟙 X) ≅ 𝟭 (obj X)
  /-- Composition isomorphism `L(f ≫ g)^* ≅ Lf^* Lg^*`. -/
  pullComp {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) : pull (f ≫ g) ≅ pull g ⋙ pull f
  /-- Associativity of the composition isomorphisms of `pull`. -/
  pull_assoc {W X Y Z : S} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    (pullComp (a ≫ b) c).hom ≫ whiskerLeft (pull c) (pullComp a b).hom =
      eqToHom (by rw [Category.assoc]) ≫ (pullComp a (b ≫ c)).hom ≫
        whiskerRight (pullComp b c).hom (pull a) ≫
          (Functor.associator (pull c) (pull b) (pull a)).hom
  /-- Left unitality of `pull`. -/
  pull_id_comp {X Y : S} (f : X ⟶ Y) :
    (pullComp (𝟙 X) f).hom ≫ whiskerLeft (pull f) (pullId X).hom =
      eqToHom (by rw [Category.id_comp]) ≫ (Functor.rightUnitor (pull f)).inv
  /-- Right unitality of `pull`. -/
  pull_comp_id {X Y : S} (f : X ⟶ Y) :
    (pullComp f (𝟙 Y)).hom ≫ whiskerRight (pullId Y).hom (pull f) =
      eqToHom (by rw [Category.comp_id]) ≫ (Functor.leftUnitor (pull f)).inv

attribute [instance] PullPseudofunctor.cat

namespace PullPseudofunctor

variable {S : Type u} [Category.{v} S] (P : PullPseudofunctor.{v, u, v₁, u₁} S)

/-- `R(f ≫ g)_* ≅ Rg_* Rf_*` (Mathlib order `push f ⋙ push g`), *defined* as the conjugate of
`(pullComp f g)⁻¹`, i.e. the composition law of `R(-)_*` induced by uniqueness of adjoints
(Stacks 0D6E). -/
def pushComp {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) : P.push (f ≫ g) ≅ P.push f ⋙ P.push g :=
  ((conjugateIsoEquiv ((P.adj g).comp (P.adj f)) (P.adj (f ≫ g))) (P.pullComp f g)).symm

/-- `R(id)_* ≅ id`, the conjugate of `(pullId X)⁻¹`. -/
def pushId (X : S) : P.push (𝟙 X) ≅ 𝟭 (P.obj X) :=
  ((conjugateIsoEquiv Adjunction.id (P.adj (𝟙 X))) (P.pullId X)).symm

lemma pushComp_hom {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (P.pushComp f g).hom =
      conjugateEquiv (P.adj (f ≫ g)) ((P.adj g).comp (P.adj f)) (P.pullComp f g).inv := rfl

lemma pushComp_inv {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (P.pushComp f g).inv =
      conjugateEquiv ((P.adj g).comp (P.adj f)) (P.adj (f ≫ g)) (P.pullComp f g).hom := rfl

lemma pushId_hom (X : S) :
    (P.pushId X).hom = conjugateEquiv (P.adj (𝟙 X)) Adjunction.id (P.pullId X).inv := rfl

/-- An `eqToHom` between pullbacks along equal morphisms is conjugate to the `eqToHom` between
the pushforwards. -/
lemma conj_eqToHom {X Y : S} {k₁ k₂ : X ⟶ Y} (e : k₁ = k₂) :
    conjugateEquiv (P.adj k₁) (P.adj k₂) (eqToHom (by rw [e])) = eqToHom (by rw [e]) := by
  subst e
  simp [conjugateEquiv_id]

/-- Associativity of the conjugate composition law of `push`. -/
lemma push_assoc {W X Y Z : S} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    (P.pushComp (a ≫ b) c).hom ≫ whiskerRight (P.pushComp a b).hom (P.push c) ≫
        (Functor.associator (P.push a) (P.push b) (P.push c)).hom =
      eqToHom (by rw [Category.assoc]) ≫ (P.pushComp a (b ≫ c)).hom ≫
        whiskerLeft (P.push a) (P.pushComp b c).hom := by
  -- the pullback identity, in inverse form
  have key : (Functor.associator (P.pull c) (P.pull b) (P.pull a)).hom ≫
      whiskerLeft (P.pull c) (P.pullComp a b).inv ≫ (P.pullComp (a ≫ b) c).inv =
      whiskerRight (P.pullComp b c).inv (P.pull a) ≫ (P.pullComp a (b ≫ c)).inv ≫
        eqToHom (by rw [Category.assoc]) := by
    have h := P.pull_assoc a b c
    ext x
    have hx := congr_app h x
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_hom_app,
      eqToHom_app, Category.comp_id] at hx
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_hom_app,
      eqToHom_app, Category.id_comp]
    rw [← cancel_epi ((P.pullComp (a ≫ b) c).hom.app x ≫
      (P.pullComp a b).hom.app ((P.pull c).obj x))]
    conv_rhs => rw [← Category.assoc, hx]
    simp
  rw [P.pushComp_hom, P.pushComp_hom, P.pushComp_hom, P.pushComp_hom,
    ← conjugateEquiv_whiskerLeft (P.adj (a ≫ b)) ((P.adj b).comp (P.adj a)) (P.adj c),
    ← conjugateEquiv_whiskerRight (P.adj (b ≫ c)) ((P.adj c).comp (P.adj b)) (P.adj a),
    ← conjugateEquiv_associator_hom (P.adj c) (P.adj b) (P.adj a),
    conjugateEquiv_comp, conjugateEquiv_comp, ← P.conj_eqToHom (Category.assoc a b c),
    conjugateEquiv_comp, conjugateEquiv_comp]
  congr 1
  simp only [Category.assoc]
  exact key

/-- Left unitality of the conjugate composition law of `push`. -/
lemma push_id_comp {X Y : S} (f : X ⟶ Y) :
    (P.pushComp (𝟙 X) f).hom ≫ whiskerRight (P.pushId X).hom (P.push f) =
      eqToHom (by rw [Category.id_comp]) ≫ (Functor.leftUnitor (P.push f)).inv := by
  have key : whiskerLeft (P.pull f) (P.pullId X).inv ≫ (P.pullComp (𝟙 X) f).inv =
      (Functor.rightUnitor (P.pull f)).hom ≫ eqToHom (by rw [Category.id_comp]) := by
    have h := P.pull_id_comp f
    ext x
    have hx := congr_app h x
    simp only [NatTrans.comp_app, whiskerLeft_app, rightUnitor_inv_app, eqToHom_app,
      Category.comp_id] at hx
    simp only [NatTrans.comp_app, whiskerLeft_app, rightUnitor_hom_app, eqToHom_app]
    rw [← cancel_epi ((P.pullComp (𝟙 X) f).hom.app x ≫
      (P.pullId X).hom.app ((P.pull f).obj x))]
    conv_rhs => rw [hx]
    simp
  rw [P.pushComp_hom, P.pushId_hom,
    ← conjugateEquiv_whiskerLeft (P.adj (𝟙 X)) Adjunction.id (P.adj f),
    ← conjugateEquiv_rightUnitor_hom (P.adj f), ← P.conj_eqToHom (Category.id_comp f),
    conjugateEquiv_comp, conjugateEquiv_comp, key]

/-- Right unitality of the conjugate composition law of `push`. -/
lemma push_comp_id {X Y : S} (f : X ⟶ Y) :
    (P.pushComp f (𝟙 Y)).hom ≫ whiskerLeft (P.push f) (P.pushId Y).hom =
      eqToHom (by rw [Category.comp_id]) ≫ (Functor.rightUnitor (P.push f)).inv := by
  have key : whiskerRight (P.pullId Y).inv (P.pull f) ≫ (P.pullComp f (𝟙 Y)).inv =
      (Functor.leftUnitor (P.pull f)).hom ≫ eqToHom (by rw [Category.comp_id]) := by
    have h := P.pull_comp_id f
    ext x
    have hx := congr_app h x
    simp only [NatTrans.comp_app, whiskerRight_app, leftUnitor_inv_app, eqToHom_app,
      Category.comp_id] at hx
    simp only [NatTrans.comp_app, whiskerRight_app, leftUnitor_hom_app, eqToHom_app]
    rw [← cancel_epi ((P.pullComp f (𝟙 Y)).hom.app x ≫
      (P.pull f).map ((P.pullId Y).hom.app x))]
    conv_rhs => rw [hx]
    simp [← Functor.map_comp_assoc]
  rw [P.pushComp_hom, P.pushId_hom,
    ← conjugateEquiv_whiskerRight (P.adj (𝟙 Y)) Adjunction.id (P.adj f),
    ← conjugateEquiv_leftUnitor_hom (P.adj f), ← P.conj_eqToHom (Category.comp_id f),
    conjugateEquiv_comp, conjugateEquiv_comp, key]

set_option linter.checkUnivs false in
/-- **The `PullPushData` of a pullback pseudofunctor with adjunctions**: `pull`, `push`, `adj`,
`pullId`, `pullComp` are the given ones, `pushComp`, `pushId` the conjugate ones; the axioms of
`pull` are the given ones, those of `push` are `push_assoc`, `push_id_comp`, `push_comp_id`, and
the conjugacy axioms `conj_comp`, `conj_id` hold by definition. -/
abbrev toPullPushData : PullPushData.{v, u, v₁, u₁} S where
  obj := P.obj
  pull := P.pull
  push := P.push
  adj := P.adj
  pullId := P.pullId
  pullComp := P.pullComp
  pushId := P.pushId
  pushComp := P.pushComp
  pull_assoc := P.pull_assoc
  pull_id_comp := P.pull_id_comp
  pull_comp_id := P.pull_comp_id
  push_assoc := P.push_assoc
  push_id_comp := P.push_id_comp
  push_comp_id := P.push_comp_id
  conj_comp _ _ := rfl
  conj_id _ := rfl

@[simp] lemma toPullPushData_pull {X Y : S} (f : X ⟶ Y) : P.toPullPushData.pull f = P.pull f := rfl
@[simp] lemma toPullPushData_push {X Y : S} (f : X ⟶ Y) : P.toPullPushData.push f = P.push f := rfl
lemma toPullPushData_adj {X Y : S} (f : X ⟶ Y) : P.toPullPushData.adj f = P.adj f := rfl
lemma toPullPushData_pullComp {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.toPullPushData.pullComp f g = P.pullComp f g := rfl
lemma toPullPushData_pushComp {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.toPullPushData.pushComp f g = P.pushComp f g := rfl

end PullPseudofunctor

end RelativeFM.Spaces.BaseChange
