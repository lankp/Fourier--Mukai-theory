/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as
described in the file LICENSE. -/
import FourierMukai.Prelim.MatesCalculus
import Mathlib.CategoryTheory.CommSq

/-!
# Base-change morphisms as mates (GL26 §7.2)

E. Guisado Villalgordo and P. Lank, *Relative Fourier--Mukai theory for algebraic spaces* (GL26),
§7.2, in abstract form.

## Setting

`PullPushData S`: a category of spaces `S`, a category `obj X` for every space, a contravariant
pseudofunctor `pull` (`L(-)^*`) and a covariant pseudofunctor `push` (`R(-)_*`) given by values,
composition and unit isomorphisms with the pseudofunctor axioms, adjunctions `Lf^* ⊣ Rf_*`, and
the conjugacy of the structure isomorphisms of `pull` and `push` (Lipman (3.6.2); in GL26 this is
Lemma 2.13, `lem:spacey_Lipman_Hashimoto`).  A commutative square of GL26 (diagram
`diag:abstract_base_change`: `p : X ⟶ Z`, `q : Z' ⟶ Z`, `p' : X' ⟶ Z'`, `q' : X' ⟶ X`,
`p ∘ q' = q ∘ p'`) is Mathlib's `CommSq p' q' q p`, i.e. `p' ≫ q = q' ≫ p`, the orientation of
`SchemePullbackSquare` in `Scheme/Duality.lean`.

## Results

* **Lemma 7.12** (`lem:pseudofunctoriality_isos_are_conjugate`): `lemma_7_12`, the isomorphisms
  `λ_□` (`lam`) and `ρ_□` (`rho`) are conjugate.
* **Lemma-Definition 7.13** (`def:upper_star_lower_star_bc`): `theta` (right mate of `λ_□`),
  `thetaLeftMate` (left mate of `ρ_□`), and `lemma_7_13`: they agree.
* **Definition 7.14** (`def:lower_star_upper_cross_bc`): `xi`, the right conjugate of `θ_□` for
  given right adjoints `Rp_* ⊣ p^×`, `Rp'_* ⊣ (p')^×`; `isIso_xi`, `isIso_theta_of_isIso_xi`.
* **Lemma-Definition 7.15** (`def:upper_star_upper_cross_bc`): `beta` (right mate of `θ_□⁻¹`),
  `betaLeftMate` (left mate of `ξ_□⁻¹`), and `lemma_7_15`: they agree.
* **Lemma 7.17** (`lem:base_change_mates_pasting`): `lemma_7_17_theta` (item (1), the `^*`-`_*`
  maps) and `lemma_7_17_xi` (item (2), the `_*`-`^×` maps): compatibility with horizontal pasting.
* Lemma 7.11(1), inverse formula: `conjugateEquiv_inv_eq_inv`.

Non-vacuity: `constPullPushData S C` (every space ↦ a fixed category `C`, `pull = push = 𝟭`,
identity adjunctions) satisfies all axioms, for an arbitrary `S`, and has invertible `θ_□` for every
square (`constPullPushData_isIso_theta`); `Adjunction.id` supplies the right adjoints `f^×`.

Nothing is assumed: everything is proved from Mathlib and `Prelim/Mates.lean`,
`Prelim/MatesCalculus.lean`.

## Deviations from the paper

* Abstract setting: the derived categories, the functors and Lemma 2.13 are replaced by the data
  and the axiom `conj_comp` of `PullPushData`; the results are the categorical content of §7.2.
  Mathlib's `Pseudofunctor (LocallyDiscrete S) Cat` is not used (see `PullPushData`).
* The right adjoints `f^×` exist only for some `f` in the paper (proper ones); here they are
  arguments of `xi`, `beta` and `lemma_7_17_xi` rather than part of `PullPushData`.
* Mathlib composes functors diagrammatically and writes the associators of `Cat` explicitly: the
  paper's `L(p')^*Lq^*` is `pull q ⋙ pull p'`, etc.  "Under the canonical pseudofunctorial
  identifications" in 7.17 is made explicit by whiskering with `pullComp`/`pushComp`.
* Lemma 7.8 (mates form an isomorphism of double categories) is not formalized; 7.17 uses its
  consequences in Mathlib (`mateEquiv_vcomp`, `conjugateEquiv_comp`, `conjugateEquiv_whiskerLeft`,
  `conjugateEquiv_whiskerRight`, `conjugateEquiv_associator_hom`).  7.17(1) is proved from
  description 7.13(2) (the paper uses 7.13(1); they agree by `lemma_7_13`).

## Relation to `Scheme/Duality.lean`

The formulas match that file's definitions literally: `theta` is `BaseChangeSquare.theta` (the right
mate of `BaseChangeSquare.pullComp`, which plays the role of `(lam sq).hom`), `xi` is
`BaseChangeSquare.lowerStarUpperCross`, and `beta` is `BaseChangeSquare.beta`.  Once
`Scheme/Duality.lean` is given a `PullPushData` (wave 3), `lemma_7_13` discharges the coherence field
`BaseChangeCoherenceData.pushConjugate` (with `pushComp := (rho sq)`), which records Lemma 7.12
there; `lemma_7_15` shows that `BaseChangeSquare.beta` also has the second description of 7.15;
and `lemma_7_17_theta`/`lemma_7_17_xi` are the pasting facts.  `DerivedMorphismData` in that file
has no composition data, so it does not yet determine a `PullPushData`; `CompositeDualityData`
(`pullComp`, `pushComp`) carries the composition isomorphisms but not their conjugacy or coherence.
-/

@[expose] public section

namespace RelativeFM

namespace BaseChangeMates

open CategoryTheory CategoryTheory.Functor

universe v u v₁ u₁

/-- **Lemma 7.11(1)** (`lem:when_mate_correspondence_preserves_isos`), the formula
`\overline{α⁻¹} = \overline{α}⁻¹`: the conjugate of the inverse of an isomorphism is the inverse of
its conjugate.  (`Prelim/Mates.lean` has the invertibility statements of 7.11; this is the
inverse formula, deduced from Mathlib's `conjugateEquiv_comp` and `conjugateEquiv_id`.) -/
lemma conjugateEquiv_inv_eq_inv {C : Type*} {D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) [IsIso α] :
    conjugateEquiv adj₂ adj₁ (inv α) = inv (conjugateEquiv adj₁ adj₂ α) := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [conjugateEquiv_comp, IsIso.inv_hom_id, conjugateEquiv_id]

/-- Naturality of the right mate in the two vertical functors: whiskering the left 2-cell by
`a : G' ⟶ G` on top and `b : H ⟶ H'` at the bottom whiskers its right mate by `a` and `b`.
(A special case of Mathlib's `mateEquiv_vcomp` with identity adjunctions; proved directly from the
componentwise formula `mate_app` of `Prelim/Mates.lean`.) -/
lemma mateEquiv_whisker {A : Type*} {B : Type*} {C : Type*} {D : Type*} [Category A]
    [Category B] [Category C] [Category D] {G G' : A ⥤ C} {H H' : B ⥤ D}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (a : G' ⟶ G) (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (b : H ⟶ H') :
    (mateEquiv adj₁ adj₂ (whiskerRight a L₂ ≫ α ≫ whiskerLeft L₁ b) : R₁ ⋙ G' ⟶ H' ⋙ R₂) =
      whiskerLeft R₁ a ≫ (mateEquiv adj₁ adj₂ α : R₁ ⋙ G ⟶ H ⋙ R₂) ≫ whiskerRight b R₂ := by
  change mate adj₁ adj₂ _ = whiskerLeft R₁ a ≫ mate adj₁ adj₂ α ≫ whiskerRight b R₂
  ext d
  simp only [mate_app, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.map_comp, Category.assoc, Functor.comp_obj]
  rw [← adj₂.unit_naturality_assoc]
  congr 3
  simp only [← Functor.map_comp]
  congr 1
  exact (b.naturality _).symm

/-- The conjugate of the inverse associator is the inverse associator; the companion of
Mathlib's `conjugateEquiv_associator_hom`, from which it is deduced. -/
lemma conjugateEquiv_associator_inv {A : Type*} {B : Type*} {C : Type*} {D : Type*} [Category A]
    [Category B] [Category C] [Category D]
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      (Functor.associator _ _ _).inv = (Functor.associator _ _ _).inv := by
  have h := conjugateEquiv_comm (adj₀₁.comp (adj₁₂.comp adj₂₃)) ((adj₀₁.comp adj₁₂).comp adj₂₃)
    (α := (Functor.associator L₀₁ L₁₂ L₂₃).hom) (β := (Functor.associator L₀₁ L₁₂ L₂₃).inv)
    (by simp)
  rw [conjugateEquiv_associator_hom] at h
  rw [← cancel_epi (Functor.associator _ _ _).hom, h]
  simp

set_option linter.checkUnivs false in
/-- **Abstract setting of GL26 §7.2.**  A category of spaces `S`; for each `X : S` a category
`obj X` (in the paper `D_qc(X)`); a contravariant pseudofunctor `pull` (`L(-)^*`) and a covariant
pseudofunctor `push` (`R(-)_*`), each given by its values, composition isomorphisms
`pullComp f g : L(f ≫ g)^* ≅ Lf^* ∘ Lg^*` (Mathlib: `pull g ⋙ pull f`), `pushComp f g :
R(f ≫ g)_* ≅ Rg_* ∘ Rf_*` (Mathlib: `push f ⋙ push g`) and unit isomorphisms, subject to the
associativity and unitality axioms of a pseudofunctor (with the associators and unitors of `Cat`
written out); adjunctions `adj f : Lf^* ⊣ Rf_*`; and the compatibility `conj_comp`, `conj_id`
that the structure isomorphisms of `pull` and `push` are conjugate (Lipman (3.6.2); in GL26 this is
supplied by Lemma 2.13, `lem:spacey_Lipman_Hashimoto`).

Mathlib's `Pseudofunctor (LocallyDiscrete S) Cat` is not used because the morphisms and
2-morphisms of Mathlib's `Cat` are now wrapped in structures (`Cat.Hom`, `Cat.Hom₂`), which would
put a coercion between every statement here and the functors of `Scheme/Duality.lean`. -/
structure PullPushData (S : Type u) [Category.{v} S] where
  /-- The category attached to a space (in GL26, `D_qc(X)`). -/
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
  /-- Unit isomorphism `R(id)_* ≅ id`. -/
  pushId (X : S) : push (𝟙 X) ≅ 𝟭 (obj X)
  /-- Composition isomorphism `R(f ≫ g)_* ≅ Rg_* Rf_*`. -/
  pushComp {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) : push (f ≫ g) ≅ push f ⋙ push g
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
  /-- Associativity of the composition isomorphisms of `push` (Lipman (3.6.5.1)). -/
  push_assoc {W X Y Z : S} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    (pushComp (a ≫ b) c).hom ≫ whiskerRight (pushComp a b).hom (push c) ≫
        (Functor.associator (push a) (push b) (push c)).hom =
      eqToHom (by rw [Category.assoc]) ≫ (pushComp a (b ≫ c)).hom ≫
        whiskerLeft (push a) (pushComp b c).hom
  /-- Left unitality of `push`. -/
  push_id_comp {X Y : S} (f : X ⟶ Y) :
    (pushComp (𝟙 X) f).hom ≫ whiskerRight (pushId X).hom (push f) =
      eqToHom (by rw [Category.id_comp]) ≫ (Functor.leftUnitor (push f)).inv
  /-- Right unitality of `push`. -/
  push_comp_id {X Y : S} (f : X ⟶ Y) :
    (pushComp f (𝟙 Y)).hom ≫ whiskerLeft (push f) (pushId Y).hom =
      eqToHom (by rw [Category.comp_id]) ≫ (Functor.rightUnitor (push f)).inv
  /-- The composition isomorphisms of `pull` and `push` are conjugate (Lipman (3.6.2), GL26
  Lemma 2.13 `lem:spacey_Lipman_Hashimoto`): `pullComp f g` is conjugate to `(pushComp f g)⁻¹`
  with respect to `L(f ≫ g)^* ⊣ R(f ≫ g)_*` and the composite adjunction. -/
  conj_comp {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((adj g).comp (adj f)) (adj (f ≫ g)) (pullComp f g).hom = (pushComp f g).inv
  /-- The unit isomorphisms of `pull` and `push` are conjugate. -/
  conj_id (X : S) :
    conjugateEquiv Adjunction.id (adj (𝟙 X)) (pullId X).hom = (pushId X).inv

attribute [instance] PullPushData.cat

namespace PullPushData

variable {S : Type u} [Category.{v} S] (P : PullPushData.{v, u, v₁, u₁} S)

/-- An `eqToHom` between pullbacks along equal morphisms is conjugate to the `eqToHom` between
the pushforwards. -/
lemma conj_eqToHom {X Y : S} {k₁ k₂ : X ⟶ Y} (e : k₁ = k₂) :
    conjugateEquiv (P.adj k₂) (P.adj k₁) (eqToHom (by rw [e])) = eqToHom (by rw [e]) := by
  subst e
  simp [conjugateEquiv_id]

/-- The conjugacy of the composition isomorphisms in inverse form (Lemma 7.11(1) applied to
`conj_comp`): `(pullComp f g)⁻¹` is conjugate to `pushComp f g`. -/
lemma conj_comp_inv {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (P.adj (f ≫ g)) ((P.adj g).comp (P.adj f)) (P.pullComp f g).inv =
      (P.pushComp f g).hom := by
  rw [← cancel_epi (P.pushComp f g).inv, Iso.inv_hom_id, ← P.conj_comp, conjugateEquiv_comp,
    Iso.inv_hom_id, conjugateEquiv_id]

section Square

variable {X' X Z' Z : S} {p : X ⟶ Z} {q : Z' ⟶ Z} {p' : X' ⟶ Z'} {q' : X' ⟶ X}

/-- The pseudofunctoriality isomorphism `λ_□ : L(p')^* Lq^* ≅ L(q')^* Lp^*` of the commutative
square `p' ≫ q = q' ≫ p` (GL26 Lemma 7.12; Mathlib order `pull q ⋙ pull p' ≅ pull p ⋙ pull q'`,
the orientation of `BaseChangeSquare.pullComp` in `Scheme/Duality.lean`). -/
def lam (sq : CommSq p' q' q p) : P.pull q ⋙ P.pull p' ≅ P.pull p ⋙ P.pull q' :=
  (P.pullComp p' q).symm ≪≫ eqToIso (by rw [sq.w]) ≪≫ P.pullComp q' p

/-- The pseudofunctoriality isomorphism `ρ_□ : Rp_* Rq'_* ≅ Rq_* Rp'_*` of the commutative square
(Mathlib order `push q' ⋙ push p ≅ push p' ⋙ push q`, the orientation of
`BaseChangeCoherenceData.pushComp` in `Scheme/Duality.lean`). -/
def rho (sq : CommSq p' q' q p) : P.push q' ⋙ P.push p ≅ P.push p' ⋙ P.push q :=
  (P.pushComp q' p).symm ≪≫ eqToIso (by rw [sq.w]) ≪≫ P.pushComp p' q

/-- **Lemma 7.12** (`lem:pseudofunctoriality_isos_are_conjugate`).  `λ_□` and `ρ_□` are conjugate
with respect to the composite adjunctions `L(q')^*Lp^* ⊣ Rp_*Rq'_*` and `L(p')^*Lq^* ⊣ Rq_*Rp'_*`.

Proof as in the paper: `λ_□` is the composite `L(p')^*Lq^* ≅ L(p' ≫ q)^* = L(q' ≫ p)^* ≅
L(q')^*Lp^*`; the outer factors are conjugate to the corresponding factors of `ρ_□` by `conj_comp`
(Lipman (3.6.2)) and its inverse form (Lemma 7.11(1)), the middle `eqToHom` is self-conjugate, and
conjugates of composites compose (Lemma 7.9, Mathlib `conjugateEquiv_comp`). -/
theorem lemma_7_12 (sq : CommSq p' q' q p) :
    conjugateEquiv ((P.adj p).comp (P.adj q')) ((P.adj q).comp (P.adj p')) (P.lam sq).hom =
      (P.rho sq).hom := by
  simp only [lam, rho, Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  rw [← P.conj_comp q' p, ← P.conj_comp_inv p' q, ← P.conj_eqToHom sq.w]
  simp only [conjugateEquiv_comp, Category.assoc]

/-- **Lemma-Definition 7.13** (`def:upper_star_lower_star_bc`), description (2): the `^*`-`_*` base
change morphism `θ_□ : Lq^* Rp_* ⟶ Rp'_* L(q')^*` as the right mate of `λ_□` with respect to
`Lp^* ⊣ Rp_*` and `L(p')^* ⊣ Rp'_*`.  This is literally the formula of
`BaseChangeSquare.theta` in `Scheme/Duality.lean`. -/
def theta (sq : CommSq p' q' q p) : P.push p ⋙ P.pull q ⟶ P.pull q' ⋙ P.push p' :=
  mateEquiv (P.adj p) (P.adj p') (P.lam sq).hom

/-- **Lemma-Definition 7.13** (`def:upper_star_lower_star_bc`), description (1): the left mate of
`ρ_□` with respect to `L(q')^* ⊣ Rq'_*` and `Lq^* ⊣ Rq_*`. -/
def thetaLeftMate (sq : CommSq p' q' q p) : P.push p ⋙ P.pull q ⟶ P.pull q' ⋙ P.push p' :=
  (mateEquiv (P.adj q') (P.adj q)).symm (P.rho sq).hom

/-- **Lemma-Definition 7.13** (`def:upper_star_lower_star_bc`): the two descriptions of `θ_□` agree.
Proof as in the paper: Lemma 7.12 and Lemma 7.6 (Mathlib `iterated_mateEquiv_conjugateEquiv`).

This is exactly the field `BaseChangeCoherenceData.pushConjugate` of `Scheme/Duality.lean` for
`pushComp := ρ_□`. -/
theorem lemma_7_13 (sq : CommSq p' q' q p) : P.thetaLeftMate sq = P.theta sq := by
  have h := iterated_mateEquiv_conjugateEquiv (P.adj p) (P.adj p') (P.adj q) (P.adj q')
    (P.lam sq).hom
  rw [P.lemma_7_12 sq] at h
  unfold thetaLeftMate theta
  rw [← h]
  exact (mateEquiv (P.adj q') (P.adj q)).symm_apply_apply _

end Square

section Cross

variable {X' X Z' Z : S} {p : X ⟶ Z} {q : Z' ⟶ Z} {p' : X' ⟶ Z'} {q' : X' ⟶ X}
  {Cp : P.obj Z ⥤ P.obj X} {Cp' : P.obj Z' ⥤ P.obj X'}

/-- **Definition 7.14** (`def:lower_star_upper_cross_bc`): given right adjoints `Rp_* ⊣ p^×` and
`Rp'_* ⊣ (p')^×`, the `_*`-`^×` base change morphism `ξ_□ : Rq'_*(p')^× ⟶ p^× Rq_*` is the right
conjugate of `θ_□`.  Same formula as `BaseChangeSquare.lowerStarUpperCross` in
`Scheme/Duality.lean`. -/
def xi (sq : CommSq p' q' q p) (cp : P.push p ⊣ Cp) (cp' : P.push p' ⊣ Cp') :
    Cp' ⋙ P.push q' ⟶ P.push q ⋙ Cp :=
  conjugateEquiv ((P.adj q').comp cp') (cp.comp (P.adj q)) (P.theta sq)

/-- `ξ_□` is invertible when `θ_□` is (Lemma 7.11(1)). -/
instance isIso_xi (sq : CommSq p' q' q p) (cp : P.push p ⊣ Cp) (cp' : P.push p' ⊣ Cp')
    [IsIso (P.theta sq)] : IsIso (P.xi sq cp cp') := by
  unfold xi; infer_instance

/-- `θ_□` is invertible when `ξ_□` is (Lemma 7.11(1)); with `isIso_xi`, the "equivalently" of
Lemma-Definition 7.15. -/
lemma isIso_theta_of_isIso_xi (sq : CommSq p' q' q p) (cp : P.push p ⊣ Cp)
    (cp' : P.push p' ⊣ Cp') [IsIso (P.xi sq cp cp')] : IsIso (P.theta sq) := by
  have : IsIso (conjugateEquiv ((P.adj q').comp cp') (cp.comp (P.adj q)) (P.theta sq)) :=
    inferInstanceAs (IsIso (P.xi sq cp cp'))
  exact conjugateEquiv_of_iso ((P.adj q').comp cp') (cp.comp (P.adj q)) _

/-- **Lemma-Definition 7.15** (`def:upper_star_upper_cross_bc`), description (1): for invertible
`θ_□`, the `^*`-`^×` base change morphism `β_□ : L(q')^* p^× ⟶ (p')^× Lq^*` is the right mate of
`θ_□⁻¹` with respect to `Rp_* ⊣ p^×` and `Rp'_* ⊣ (p')^×`.  Same formula as
`BaseChangeSquare.beta` in `Scheme/Duality.lean`. -/
noncomputable def beta (sq : CommSq p' q' q p) (cp : P.push p ⊣ Cp) (cp' : P.push p' ⊣ Cp')
    [IsIso (P.theta sq)] : Cp ⋙ P.pull q' ⟶ P.pull q ⋙ Cp' :=
  mateEquiv cp cp' (inv (P.theta sq))

/-- **Lemma-Definition 7.15** (`def:upper_star_upper_cross_bc`), description (2): the left mate of
`ξ_□⁻¹` with respect to `Lq^* ⊣ Rq_*` and `L(q')^* ⊣ Rq'_*`. -/
noncomputable def betaLeftMate (sq : CommSq p' q' q p) (cp : P.push p ⊣ Cp)
    (cp' : P.push p' ⊣ Cp') [IsIso (P.theta sq)] : Cp ⋙ P.pull q' ⟶ P.pull q ⋙ Cp' :=
  (mateEquiv (P.adj q) (P.adj q')).symm (inv (P.xi sq cp cp'))

/-- **Lemma-Definition 7.15** (`def:upper_star_upper_cross_bc`): the two descriptions of `β_□` agree.
Proof as in the paper: Lemma 7.11(1) (`conjugateEquiv_inv_eq_inv`) and Lemma 7.6 (Mathlib
`iterated_mateEquiv_conjugateEquiv`) for the square with sides `Rq_*`, `(p')^×`, `p^×`, `Rq'_*`. -/
theorem lemma_7_15 (sq : CommSq p' q' q p) (cp : P.push p ⊣ Cp) (cp' : P.push p' ⊣ Cp')
    [IsIso (P.theta sq)] : P.betaLeftMate sq cp cp' = P.beta sq cp cp' := by
  have h := iterated_mateEquiv_conjugateEquiv cp cp' (P.adj q') (P.adj q) (inv (P.theta sq))
  rw [conjugateEquiv_inv_eq_inv] at h
  unfold betaLeftMate beta xi
  rw [← h]
  exact (mateEquiv (P.adj q) (P.adj q')).symm_apply_apply _

end Cross

section Pasting

/-- The composition isomorphism of `pull` along a chosen composite `ab = a ≫ b` (an auxiliary
device to avoid transport along equalities of composites, as Mathlib's `Pseudofunctor.mapComp'`). -/
def pullComp' {X Y Z : S} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z) (w : a ≫ b = ab) :
    P.pull ab ≅ P.pull b ⋙ P.pull a :=
  eqToIso (by rw [w]) ≪≫ P.pullComp a b

@[simp]
lemma pullComp'_rfl {X Y Z : S} (a : X ⟶ Y) (b : Y ⟶ Z) :
    P.pullComp' a b (a ≫ b) rfl = P.pullComp a b := by
  ext; simp [pullComp']

/-- Associativity of `pull` along chosen composites (componentwise). -/
lemma pullComp'_assoc_app {W X Y Z : S} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (ab : W ⟶ Y)
    (bc : X ⟶ Z) (abc : W ⟶ Z) (hab : a ≫ b = ab) (hbc : b ≫ c = bc) (h₁ : ab ≫ c = abc)
    (h₂ : a ≫ bc = abc) (x : P.obj Z) :
    (P.pullComp' ab c abc h₁).hom.app x ≫ (P.pullComp' a b ab hab).hom.app ((P.pull c).obj x) =
      (P.pullComp' a bc abc h₂).hom.app x ≫
        (P.pull a).map ((P.pullComp' b c bc hbc).hom.app x) := by
  subst hab hbc h₁
  have := congr_app (P.pull_assoc a b c) x
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
    eqToHom_app, Category.comp_id] at this
  simp only [this, pullComp', Iso.trans_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_app, Category.assoc, eqToHom_refl, Category.id_comp]

variable {X' X Z' Z : S} {p : X ⟶ Z} {q : Z' ⟶ Z} {p' : X' ⟶ Z'} {q' : X' ⟶ X}

/-- `λ_□` through an arbitrary choice of diagonal `d`. -/
lemma lam_hom_app (sq : CommSq p' q' q p) (d : X' ⟶ Z) (h₁ : p' ≫ q = d) (h₂ : q' ≫ p = d)
    (x : P.obj Z) :
    (P.lam sq).hom.app x =
      (P.pullComp' p' q d h₁).inv.app x ≫ (P.pullComp' q' p d h₂).hom.app x := by
  subst h₁
  simp [lam, pullComp']

variable {X'' X' X Y'' Y' Y : S} {g' : X'' ⟶ X'} {g : X' ⟶ X} {h' : Y'' ⟶ Y'} {h : Y' ⟶ Y}
  {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y}

/-- The pseudofunctoriality isomorphism `λ` of the outer rectangle is the pasting of those
of the two squares, under the identifications `pullComp`. -/
lemma lam_vert_comp_app (sl : CommSq f'' g' h' f') (sr : CommSq f' g h f) (x : P.obj Y) :
    (P.lam (sl.vert_comp sr)).hom.app x =
      (P.pull f'').map ((P.pullComp h' h).hom.app x) ≫ (P.lam sl).hom.app ((P.pull h).obj x) ≫
        (P.pull g').map ((P.lam sr).hom.app x) ≫ (P.pullComp g' g).inv.app ((P.pull f).obj x) := by
  have wδ₁ : (g' ≫ g) ≫ f = f'' ≫ h' ≫ h := by
    rw [Category.assoc, ← sr.w, ← Category.assoc, ← sl.w, Category.assoc]
  have wδ₂ : g' ≫ f' ≫ h = f'' ≫ h' ≫ h := by
    rw [← Category.assoc, ← sl.w, Category.assoc]
  have wa : (f'' ≫ h') ≫ h = f'' ≫ h' ≫ h := Category.assoc _ _ _
  rw [P.lam_hom_app (sl.vert_comp sr) (f'' ≫ h' ≫ h) rfl wδ₁,
    P.lam_hom_app sl (f'' ≫ h') rfl sl.w.symm, P.lam_hom_app sr (f' ≫ h) rfl sr.w.symm]
  have F1 := P.pullComp'_assoc_app f'' h' h (f'' ≫ h') (h' ≫ h) (f'' ≫ h' ≫ h) rfl rfl wa rfl x
  have F2 := P.pullComp'_assoc_app g' f' h (f'' ≫ h') (f' ≫ h) (f'' ≫ h' ≫ h) sl.w.symm rfl wa
    wδ₂ x
  have F3 := P.pullComp'_assoc_app g' g f (g' ≫ g) (f' ≫ h) (f'' ≫ h' ≫ h) rfl sr.w.symm wδ₁
    wδ₂ x
  simp only [pullComp'_rfl] at F1 F2 F3 ⊢
  -- `F1` expresses `(pull f'').map (pullComp h' h)` through the other comparison maps.
  have F1' : (P.pull f'').map ((P.pullComp h' h).hom.app x) =
      (P.pullComp f'' (h' ≫ h)).inv.app x ≫ (P.pullComp' (f'' ≫ h') h _ wa).hom.app x ≫
        (P.pullComp f'' h').hom.app ((P.pull h).obj x) := by
    rw [F1, Iso.inv_hom_id_app_assoc]
  rw [F1']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [reassoc_of% F2, ← Functor.map_comp_assoc (P.pull g'), Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, ← reassoc_of% F3, Iso.hom_inv_id_app, Category.comp_id]

/-- **Lemma 7.17(1)** (`lem:base_change_mates_pasting`), the `^*`-`_*` maps.  For the diagram with
top row `g' : X'' ⟶ X'`, `g : X' ⟶ X`, bottom row `h' : Y'' ⟶ Y'`, `h : Y' ⟶ Y` and vertical maps
`f'', f', f` (left square `sl : f'' ≫ h' = g' ≫ f'`, right square `sr : f' ≫ h = g ≫ f`; the
outer rectangle is Mathlib's `CommSq.vert_comp`, Mathlib's `CommSq` being drawn transposed), the
base change morphism of the rectangle is, under `L(h' ≫ h)^* ≅ L(h')^*Lh^*` and
`L(g' ≫ g)^* ≅ L(g')^*Lg^*`, the composite `(θ_l Lg^*) ∘ (L(h')^* θ_r)`.

Proof: by description 7.13(2), Mathlib's `mateEquiv_vcomp` (mates respect pasting, the part of
Lemma 7.8 used), naturality of mates in the vertical functors (`mateEquiv_whisker`), and the
identification of `λ` of the rectangle with the pasting of the `λ`s of the squares, which uses the
associativity of `pull` three times (`lam_vert_comp_app`).  The paper uses 7.13(1) and the
associativity of `push` instead; the two routes are equivalent by Lemma 7.13. -/
theorem lemma_7_17_theta (sl : CommSq f'' g' h' f') (sr : CommSq f' g h f) :
    P.theta (sl.vert_comp sr) =
      whiskerLeft (P.push f) (P.pullComp h' h).hom ≫ (Functor.associator _ _ _).inv ≫
        whiskerRight (P.theta sr) (P.pull h') ≫ (Functor.associator _ _ _).hom ≫
          whiskerLeft (P.pull g) (P.theta sl) ≫ (Functor.associator _ _ _).inv ≫
            whiskerRight (P.pullComp g' g).inv (P.push f'') := by
  have hA : (P.lam (sl.vert_comp sr)).hom =
      whiskerRight (P.pullComp h' h).hom (P.pull f'') ≫
        (TwoSquare.hComp (P.lam sr).hom (P.lam sl).hom).natTrans ≫
          whiskerLeft (P.pull f) (P.pullComp g' g).inv := by
    ext x
    rw [P.lam_vert_comp_app sl sr x]
    simp [TwoSquare.hComp]
  have hV := mateEquiv_vcomp (P.adj f) (P.adj f') (P.adj f'') (P.lam sr).hom (P.lam sl).hom
  unfold theta
  rw [hA, mateEquiv_whisker]
  change _ ≫ (mateEquiv (P.adj f) (P.adj f'')
    (TwoSquare.hComp (P.lam sr).hom (P.lam sl).hom)).natTrans ≫ _ = _
  rw [hV]
  ext x
  simp [TwoSquare.vComp]
  rfl

/-- **Lemma 7.17(2)** (`lem:base_change_mates_pasting`), the `_*`-`^×` maps.  With right adjoints
`Rf_* ⊣ f^×`, `Rf'_* ⊣ (f')^×`, `Rf''_* ⊣ (f'')^×`, the base change morphism of the outer rectangle
is, under `R(g' ≫ g)_* ≅ Rg_*Rg'_*` and `R(h' ≫ h)_* ≅ Rh_*Rh'_*`, the composite
`(ξ_r Rh'_*) ∘ (Rg_* ξ_l)`.

Proof: `ξ` is the conjugate of `θ` (Definition 7.14); conjugate the formula of 7.17(1) factor by
factor (Mathlib `conjugateEquiv_comp`, `conjugateEquiv_whiskerLeft`, `conjugateEquiv_whiskerRight`,
`conjugateEquiv_associator_hom`), using `conj_comp` for the two pseudofunctoriality factors.  The
triangle-identity computation of the paper's proof is contained in Mathlib's whiskering lemmas. -/
theorem lemma_7_17_xi (sl : CommSq f'' g' h' f') (sr : CommSq f' g h f)
    {Cf : P.obj Y ⥤ P.obj X} {Cf' : P.obj Y' ⥤ P.obj X'} {Cf'' : P.obj Y'' ⥤ P.obj X''}
    (cf : P.push f ⊣ Cf) (cf' : P.push f' ⊣ Cf') (cf'' : P.push f'' ⊣ Cf'') :
    P.xi (sl.vert_comp sr) cf cf'' =
      whiskerLeft Cf'' (P.pushComp g' g).hom ≫ (Functor.associator _ _ _).inv ≫
        whiskerRight (P.xi sl cf' cf'') (P.push g) ≫ (Functor.associator _ _ _).hom ≫
          whiskerLeft (P.push h') (P.xi sr cf cf') ≫ (Functor.associator _ _ _).inv ≫
            whiskerRight (P.pushComp h' h).inv Cf := by
  unfold xi
  rw [P.lemma_7_17_theta sl sr,
    ← conjugateEquiv_comp _ (cf.comp ((P.adj h).comp (P.adj h'))) _,
    ← conjugateEquiv_comp _ ((cf.comp (P.adj h)).comp (P.adj h')) _,
    ← conjugateEquiv_comp _ (((P.adj g).comp cf').comp (P.adj h')) _,
    ← conjugateEquiv_comp _ ((P.adj g).comp (cf'.comp (P.adj h'))) _,
    ← conjugateEquiv_comp _ ((P.adj g).comp ((P.adj g').comp cf'')) _,
    ← conjugateEquiv_comp _ (((P.adj g).comp (P.adj g')).comp cf'') _]
  simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom, conjugateEquiv_associator_inv, P.conj_comp, P.conj_comp_inv,
    Category.assoc]

end Pasting

end PullPushData

/-! ### Non-vacuity

The constant data on an arbitrary category of spaces `S`: every space is sent to a fixed category
`C`, `pull` and `push` are identities, all adjunctions are `Adjunction.id`, and all structure
isomorphisms are unitors.  All axioms of `PullPushData` hold, every commutative square has an
invertible `θ_□`, and `Rf_* = 𝟭 ⊣ 𝟭` supplies the right adjoints of 7.14/7.15, so every hypothesis
of Lemmas 7.12, 7.13, 7.15 and 7.17 is satisfiable. -/

section Example

variable (S : Type u) [Category.{v} S] (C : Type u₁) [Category.{v₁} C]

/-- The constant `PullPushData` with value `C`. -/
@[simps]
def constPullPushData : PullPushData.{v, u, v₁, u₁} S where
  obj _ := C
  cat _ := inferInstance
  pull _ := 𝟭 C
  push _ := 𝟭 C
  adj _ := Adjunction.id
  pullId _ := Iso.refl _
  pullComp _ _ := (Functor.leftUnitor (𝟭 C)).symm
  pushId _ := Iso.refl _
  pushComp _ _ := (Functor.leftUnitor (𝟭 C)).symm
  pull_assoc _ _ _ := by ext; simp
  pull_id_comp _ := by ext; simp
  pull_comp_id _ := by ext; simp
  push_assoc _ _ _ := by ext; simp
  push_id_comp _ := by ext; simp
  push_comp_id _ := by ext; simp
  conj_comp _ _ := by ext; simp
  conj_id _ := by ext; simp

/-- In the constant example, `θ_□` is invertible for every commutative square, so the
hypothesis of Lemma-Definition 7.15 is satisfiable. -/
instance constPullPushData_isIso_theta {X' X Z' Z : S} {p : X ⟶ Z} {q : Z' ⟶ Z} {p' : X' ⟶ Z'}
    {q' : X' ⟶ X} (sq : CommSq p' q' q p) : IsIso ((constPullPushData S C).theta sq) := by
  have hu : IsIso (Adjunction.id (C := C)).unit := by
    rw [Adjunction.id_unit]; infer_instance
  have hc : IsIso (Adjunction.id (C := C)).counit := by
    rw [Adjunction.id_counit]; infer_instance
  have : IsIso ((constPullPushData S C).adj p').unit := hu
  have : IsIso ((constPullPushData S C).adj p).counit := hc
  exact isIso_mate ((constPullPushData S C).adj p) ((constPullPushData S C).adj p')
    ((constPullPushData S C).lam sq).hom

/-- A commutative square in the constant example whose `θ_□` is invertible: all hypotheses of
Lemma-Definition 7.15 (and, with `Adjunction.id` as `Rf_* ⊣ f^×`, of Definition 7.14 and
Lemma 7.17(2)) hold simultaneously. -/
example (X : S) :
    IsIso ((constPullPushData S C).theta (CommSq.mk rfl : CommSq (𝟙 X) (𝟙 X) (𝟙 X) (𝟙 X))) :=
  inferInstance

end Example

end BaseChangeMates

end RelativeFM
