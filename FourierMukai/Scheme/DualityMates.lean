/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as
described in the file LICENSE. -/
import FourierMukai.Scheme.Duality
import FourierMukai.Prelim.BaseChangeMates

/-!
# Wiring GL26 §7.2 (base-change mates) into the six-functor interface

E. Guisado Villalgordo and P. Lank, *Relative Fourier--Mukai theory for algebraic spaces* (GL26),
§7.2: Lemma 7.12 (`lem:pseudofunctoriality_isos_are_conjugate`), Lemma-Definitions 7.13
(`def:upper_star_lower_star_bc`), 7.15 (`def:upper_star_upper_cross_bc`), Definition 7.14
(`def:lower_star_upper_cross_bc`) and Lemma 7.17 (`lem:base_change_mates_pasting`), for the
base-change maps `BaseChangeSquare.theta`, `BaseChangeSquare.lowerStarUpperCross` and
`BaseChangeSquare.beta` of `Scheme/Duality.lean`.

## The input

`DerivedPseudofunctorInput S`: a category of spaces `S`, for every `X : S` a category `D X` with
`DerivedTensorHomData`, for every `f : X ⟶ Y` a `DerivedMorphismData (T Y) (T X)` (the package
`Lf^*`, `Rf_*`, `f^×`, `f^!`, ... of `Duality.lean`), and the composition and unit isomorphisms of
`Lf^*` and `Rf_*` with

* the pseudofunctor axioms for both (associativity and unitality), and
* the conjugacy of the structure isomorphisms of `L(-)^*` and `R(-)_*` with respect to the
  adjunctions `Lf^* ⊣ Rf_*` of the packages: Lipman, *Notes on derived functors and Grothendieck
  duality*, (3.6.2); in GL26 this is Lemma 2.13 (`lem:spacey_Lipman_Hashimoto`).

This is the smallest data from which a `BaseChangeMates.PullPushData` is built
(`DerivedPseudofunctorInput.toPullPushData`): no field beyond those of `PullPushData` is added
except the tensor/Hom and morphism packages themselves.  It is **carried as a named hypothesis**
(a structure argument), not proved: `Duality.lean` does not construct the derived functors
`Lf^*`, `Rf_*` on `D_qc` as a family indexed by morphisms, so there is nothing concrete to prove it
from.  It is not a Stacks field and not Neeman's theorem; it is the Lipman (3.6.2) /
GL26 Lemma 2.13 input, named as such.

## What is proved

For a commutative square `sq : CommSq p' q' q p` in `S` (`p' ≫ q = q' ≫ p`, the orientation of
`SchemePullbackSquare`):

* `square sq : BaseChangeSquare (mor p) (mor p') (mor q) (mor q')`, with `pullComp := λ_□`;
  `square_theta`, `square_lowerStarUpperCross`, `square_beta`: the three base-change maps of
  `Duality.lean` are, definitionally, `θ_□`, `ξ_□`, `β_□` of `BaseChangeMates`.
* **Lemma 7.12** `lemma_7_12`: `λ_□` and `ρ_□` are conjugate.
* **Lemma-Definition 7.13** `coherence sq : BaseChangeCoherenceData (square sq)`: the field
  `pushConjugate` of `Duality.lean` is proved (from `BaseChangeMates.PullPushData.lemma_7_13`),
  with `pushComp := ρ_□`.  Moreover, for an *arbitrary* square, `BaseChangeCoherenceData` has at
  most one element (`BaseChangeCoherenceData.pushComp_hom_eq`, `subsingleton`): `pushConjugate`
  forces `pushComp.hom` to be the right mate of `theta`.  So the field is not a free choice of an
  unrelated isomorphism; for squares from a `DerivedPseudofunctorInput` it is inhabited and
  unique (`coherence_eq`).
* **Lemma-Definition 7.15** `lemma_7_15`: `BaseChangeSquare.beta` equals the left mate of
  `lowerStarUpperCross⁻¹`.
* **Lemma 7.17** `lemma_7_17_theta`, `lemma_7_17_lowerStarUpperCross`: the pasting laws for
  `BaseChangeSquare.theta` and `BaseChangeSquare.lowerStarUpperCross`.

## Decisions on the fields of `Duality.lean`

`BaseChangeCoherenceData.pushConjugate` is kept: `BaseChangeSquare` and `BaseChangeCoherenceData`
are also used for squares that are not produced by a `DerivedPseudofunctorInput`
(e.g. `Scheme/AffineConvolution.lean`), where it remains a hypothesis.  It now has a proved
instance (`coherence`) and is shown to determine `pushComp` (`pushComp_hom_eq`).  No other field of
`Duality.lean` has the type of a 7.12–7.17 statement: the fields of `BaseChangeIsomorphismData`
and `UpperShriekBaseChangeData` are geometric invertibility statements (Stacks 08IR, 0E5D,
GL26 `lem:neeman188`), and `CompositeDualityData` carries the composition data of `f^×`, `f^!`
and invertibility of `ρ(f,g)`, which `PullPushData` does not involve.

## Non-vacuity

`trivialInput S`: for an arbitrary category of spaces `S`, every space is sent to the one-object
category `Discrete PUnit` with the (unique) closed symmetric monoidal structure, every morphism to
the package with all four functors the identity.  All axioms hold; every square has invertible
`θ_□` (`trivialInput_isIso_theta`), so every hypothesis of 7.15 is satisfiable too.  In this
example the `Prop`-valued fields `IsProper`, `IsFlat`, `HasFiniteTorDimension` and `Perf` of the
morphism package are `True`/`⊤`; these are values of an example, not hypotheses of a theorem.

Nothing else is assumed.
-/

@[expose] public section

namespace RelativeFM

namespace DualityMates

open CategoryTheory CategoryTheory.Functor BaseChangeMates

universe v u v₁ u₁

/-! ### `BaseChangeCoherenceData` is determined by the square -/

section Coherence

variable {DX DX' DZ DZ' : Type u₁}
  [Category.{v₁} DX] [Category.{v₁} DX'] [Category.{v₁} DZ] [Category.{v₁} DZ']
  {TX : DerivedTensorHomData DX} {TX' : DerivedTensorHomData DX'}
  {TZ : DerivedTensorHomData DZ} {TZ' : DerivedTensorHomData DZ'}
  {p : DerivedMorphismData TZ TX} {p' : DerivedMorphismData TZ' TX'}
  {q : DerivedMorphismData TZ TZ'} {q' : DerivedMorphismData TX TX'}

/-- The coherence field `pushConjugate` of `BaseChangeCoherenceData` (GL26 Lemma 7.13,
`def:upper_star_lower_star_bc`, description (1) = description (2)) determines the push
comparison: `pushComp.hom` is the right mate of `theta`. -/
theorem BaseChangeCoherenceData.pushComp_hom_eq {sq : BaseChangeSquare p p' q q'}
    (C : BaseChangeCoherenceData sq) :
    C.pushComp.hom = mateEquiv q'.pullPushAdj q.pullPushAdj sq.theta := by
  rw [← C.pushConjugate]
  exact ((mateEquiv q'.pullPushAdj q.pullPushAdj).apply_symm_apply _).symm

/-- `BaseChangeCoherenceData` has at most one element: the conjugacy axiom leaves no freedom in
`pushComp`. -/
instance BaseChangeCoherenceData.subsingleton (sq : BaseChangeSquare p p' q q') :
    Subsingleton (BaseChangeCoherenceData sq) := by
  constructor
  rintro ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
  have e : c₁ = c₂ := by
    ext1
    rw [BaseChangeCoherenceData.pushComp_hom_eq ⟨c₁, h₁⟩,
      BaseChangeCoherenceData.pushComp_hom_eq ⟨c₂, h₂⟩]
  subst e
  rfl

end Coherence

set_option linter.checkUnivs false in
/-- **Input: Lipman (3.6.2) / GL26 Lemma 2.13 (`lem:spacey_Lipman_Hashimoto`), with the
pseudofunctoriality of `L(-)^*` and `R(-)_*`.**  A family of six-functor packages
`mor f : DerivedMorphismData (T Y) (T X)` indexed by the morphisms `f : X ⟶ Y` of a category of
spaces, together with composition and unit isomorphisms for the pullbacks and pushforwards, the
pseudofunctor axioms for both, and the conjugacy of the structure isomorphisms of pull and push
with respect to the adjunctions `(mor f).pullPushAdj`.

This is exactly the data of `BaseChangeMates.PullPushData` with `pull`, `push`, `adj` read off from
the packages (`toPullPushData`).  It is carried as a hypothesis: `Duality.lean` does not construct
these functors as a family. -/
structure DerivedPseudofunctorInput (S : Type u) [Category.{v} S] where
  /-- The category attached to a space (in GL26, `D_qc(X)`). -/
  D : S → Type u₁
  /-- The categories `D X`. -/
  [cat : ∀ X, Category.{v₁} (D X)]
  /-- Derived tensor and `RHom` on each `D X`. -/
  T : ∀ X, DerivedTensorHomData (D X)
  /-- The six-functor package of a morphism `f : X ⟶ Y`: `Lf^* : D Y ⥤ D X`, etc. -/
  mor {X Y : S} (f : X ⟶ Y) : DerivedMorphismData (T Y) (T X)
  /-- Unit isomorphism `L(id)^* ≅ id`. -/
  pullId (X : S) : (mor (𝟙 X)).pull ≅ 𝟭 (D X)
  /-- Composition isomorphism `L(f ≫ g)^* ≅ Lf^* Lg^*`. -/
  pullComp {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mor (f ≫ g)).pull ≅ (mor g).pull ⋙ (mor f).pull
  /-- Unit isomorphism `R(id)_* ≅ id`. -/
  pushId (X : S) : (mor (𝟙 X)).push ≅ 𝟭 (D X)
  /-- Composition isomorphism `R(f ≫ g)_* ≅ Rg_* Rf_*`. -/
  pushComp {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mor (f ≫ g)).push ≅ (mor f).push ⋙ (mor g).push
  /-- Associativity of the composition isomorphisms of `L(-)^*`. -/
  pull_assoc {W X Y Z : S} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    (pullComp (a ≫ b) c).hom ≫ whiskerLeft (mor c).pull (pullComp a b).hom =
      eqToHom (by rw [Category.assoc]) ≫ (pullComp a (b ≫ c)).hom ≫
        whiskerRight (pullComp b c).hom (mor a).pull ≫
          (Functor.associator (mor c).pull (mor b).pull (mor a).pull).hom
  /-- Left unitality of `L(-)^*`. -/
  pull_id_comp {X Y : S} (f : X ⟶ Y) :
    (pullComp (𝟙 X) f).hom ≫ whiskerLeft (mor f).pull (pullId X).hom =
      eqToHom (by rw [Category.id_comp]) ≫ (Functor.rightUnitor (mor f).pull).inv
  /-- Right unitality of `L(-)^*`. -/
  pull_comp_id {X Y : S} (f : X ⟶ Y) :
    (pullComp f (𝟙 Y)).hom ≫ whiskerRight (pullId Y).hom (mor f).pull =
      eqToHom (by rw [Category.comp_id]) ≫ (Functor.leftUnitor (mor f).pull).inv
  /-- Associativity of the composition isomorphisms of `R(-)_*` (Lipman (3.6.5.1)). -/
  push_assoc {W X Y Z : S} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    (pushComp (a ≫ b) c).hom ≫ whiskerRight (pushComp a b).hom (mor c).push ≫
        (Functor.associator (mor a).push (mor b).push (mor c).push).hom =
      eqToHom (by rw [Category.assoc]) ≫ (pushComp a (b ≫ c)).hom ≫
        whiskerLeft (mor a).push (pushComp b c).hom
  /-- Left unitality of `R(-)_*`. -/
  push_id_comp {X Y : S} (f : X ⟶ Y) :
    (pushComp (𝟙 X) f).hom ≫ whiskerRight (pushId X).hom (mor f).push =
      eqToHom (by rw [Category.id_comp]) ≫ (Functor.leftUnitor (mor f).push).inv
  /-- Right unitality of `R(-)_*`. -/
  push_comp_id {X Y : S} (f : X ⟶ Y) :
    (pushComp f (𝟙 Y)).hom ≫ whiskerLeft (mor f).push (pushId Y).hom =
      eqToHom (by rw [Category.comp_id]) ≫ (Functor.rightUnitor (mor f).push).inv
  /-- Lipman (3.6.2), GL26 Lemma 2.13 (`lem:spacey_Lipman_Hashimoto`): `pullComp f g` is
  conjugate to `(pushComp f g)⁻¹`. -/
  conj_comp {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((mor g).pullPushAdj.comp (mor f).pullPushAdj) (mor (f ≫ g)).pullPushAdj
      (pullComp f g).hom = (pushComp f g).inv
  /-- The unit isomorphisms of `L(-)^*` and `R(-)_*` are conjugate. -/
  conj_id (X : S) :
    conjugateEquiv Adjunction.id (mor (𝟙 X)).pullPushAdj (pullId X).hom = (pushId X).inv

attribute [instance] DerivedPseudofunctorInput.cat

namespace DerivedPseudofunctorInput

variable {S : Type u} [Category.{v} S] (I : DerivedPseudofunctorInput.{v, u, v₁, u₁} S)

/-- The abstract pull/push data of GL26 §7.2 underlying the input. -/
def toPullPushData : PullPushData.{v, u, v₁, u₁} S where
  obj := I.D
  pull f := (I.mor f).pull
  push f := (I.mor f).push
  adj f := (I.mor f).pullPushAdj
  pullId := I.pullId
  pullComp := I.pullComp
  pushId := I.pushId
  pushComp := I.pushComp
  pull_assoc := I.pull_assoc
  pull_id_comp := I.pull_id_comp
  pull_comp_id := I.pull_comp_id
  push_assoc := I.push_assoc
  push_id_comp := I.push_id_comp
  push_comp_id := I.push_comp_id
  conj_comp := I.conj_comp
  conj_id := I.conj_id

variable {X' X Z' Z : S} {p : X ⟶ Z} {q : Z' ⟶ Z} {p' : X' ⟶ Z'} {q' : X' ⟶ X}

/-- The `BaseChangeSquare` of `Duality.lean` attached to a commutative square `p' ≫ q = q' ≫ p`
of spaces: its pullback comparison is the pseudofunctoriality isomorphism `λ_□`. -/
def square (sq : CommSq p' q' q p) :
    BaseChangeSquare (I.mor p) (I.mor p') (I.mor q) (I.mor q') where
  pullComp := I.toPullPushData.lam sq

/-- **Lemma-Definition 7.13** (`def:upper_star_lower_star_bc`): `BaseChangeSquare.theta` of
`Duality.lean` is `θ_□` of `BaseChangeMates` (the same formula). -/
theorem square_theta (sq : CommSq p' q' q p) :
    (I.square sq).theta = I.toPullPushData.theta sq := rfl

/-- **Definition 7.14** (`def:lower_star_upper_cross_bc`): `BaseChangeSquare.lowerStarUpperCross`
is `ξ_□` for the right adjoints `Rf_* ⊣ f^×` of the packages. -/
theorem square_lowerStarUpperCross (sq : CommSq p' q' q p) :
    (I.square sq).lowerStarUpperCross =
      I.toPullPushData.xi sq (I.mor p).pushCrossAdj (I.mor p').pushCrossAdj := rfl

/-- **Lemma-Definition 7.15** (`def:upper_star_upper_cross_bc`): `BaseChangeSquare.beta` is `β_□`
of `BaseChangeMates`. -/
theorem square_beta (sq : CommSq p' q' q p) [IsIso (I.square sq).theta] :
    haveI : IsIso (I.toPullPushData.theta sq) := ‹IsIso (I.square sq).theta›
    (I.square sq).beta =
      I.toPullPushData.beta sq (I.mor p).pushCrossAdj (I.mor p').pushCrossAdj := rfl

/-- **Lemma 7.12** (`lem:pseudofunctoriality_isos_are_conjugate`), for `Duality.lean`'s squares:
the pullback comparison `(square sq).pullComp` (`λ_□`) is conjugate to `ρ_□`. -/
theorem lemma_7_12 (sq : CommSq p' q' q p) :
    conjugateEquiv ((I.mor p).pullPushAdj.comp (I.mor q').pullPushAdj)
        ((I.mor q).pullPushAdj.comp (I.mor p').pullPushAdj) (I.square sq).pullComp.hom =
      (I.toPullPushData.rho sq).hom :=
  I.toPullPushData.lemma_7_12 sq

/-- **Lemma-Definition 7.13** (`def:upper_star_lower_star_bc`) as the coherence data of
`Duality.lean`: `pushComp := ρ_□`, and the field `pushConjugate` (the two descriptions of `θ_□`
agree) is `BaseChangeMates.PullPushData.lemma_7_13`. -/
def coherence (sq : CommSq p' q' q p) : BaseChangeCoherenceData (I.square sq) where
  pushComp := I.toPullPushData.rho sq
  pushConjugate := I.toPullPushData.lemma_7_13 sq

/-- Any coherence data on `square sq` is `coherence sq`. -/
theorem coherence_eq (sq : CommSq p' q' q p) (C : BaseChangeCoherenceData (I.square sq)) :
    C = I.coherence sq :=
  Subsingleton.elim _ _

/-- **Lemma-Definition 7.15** (`def:upper_star_upper_cross_bc`): when `θ_□` is invertible,
`BaseChangeSquare.beta` (the right mate of `θ_□⁻¹`) equals the left mate of
`lowerStarUpperCross⁻¹` with respect to `Lq^* ⊣ Rq_*` and `L(q')^* ⊣ R(q')_*`. -/
theorem lemma_7_15 (sq : CommSq p' q' q p) [IsIso (I.square sq).theta] :
    (I.square sq).beta =
      (mateEquiv (I.mor q).pullPushAdj (I.mor q').pullPushAdj).symm
        (inv (I.square sq).lowerStarUpperCross) := by
  have : IsIso (I.toPullPushData.theta sq) := ‹IsIso (I.square sq).theta›
  exact (I.toPullPushData.lemma_7_15 sq (I.mor p).pushCrossAdj (I.mor p').pushCrossAdj).symm

variable {X'' X' X Y'' Y' Y : S} {g' : X'' ⟶ X'} {g : X' ⟶ X} {h' : Y'' ⟶ Y'} {h : Y' ⟶ Y}
  {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y}

/-- **Lemma 7.17(1)** (`lem:base_change_mates_pasting`) for `BaseChangeSquare.theta`.  Top row
`g' : X'' ⟶ X'`, `g : X' ⟶ X`, bottom row `h' : Y'' ⟶ Y'`, `h : Y' ⟶ Y`, vertical maps
`f'', f', f`; the base-change map of the outer rectangle is, under `L(h' ≫ h)^* ≅ L(h')^*Lh^*` and
`L(g' ≫ g)^* ≅ L(g')^*Lg^*`, the pasting of those of the two squares. -/
theorem lemma_7_17_theta (sl : CommSq f'' g' h' f') (sr : CommSq f' g h f) :
    (I.square (sl.vert_comp sr)).theta =
      whiskerLeft (I.mor f).push (I.pullComp h' h).hom ≫ (Functor.associator _ _ _).inv ≫
        whiskerRight (I.square sr).theta (I.mor h').pull ≫ (Functor.associator _ _ _).hom ≫
          whiskerLeft (I.mor g).pull (I.square sl).theta ≫ (Functor.associator _ _ _).inv ≫
            whiskerRight (I.pullComp g' g).inv (I.mor f'').push :=
  I.toPullPushData.lemma_7_17_theta sl sr

/-- **Lemma 7.17(2)** (`lem:base_change_mates_pasting`) for
`BaseChangeSquare.lowerStarUpperCross`: the `_*`-`^×` base-change map of the outer rectangle is,
under `R(g' ≫ g)_* ≅ Rg_*Rg'_*` and `R(h' ≫ h)_* ≅ Rh_*Rh'_*`, the pasting of those of the two
squares. -/
theorem lemma_7_17_lowerStarUpperCross (sl : CommSq f'' g' h' f') (sr : CommSq f' g h f) :
    (I.square (sl.vert_comp sr)).lowerStarUpperCross =
      whiskerLeft (I.mor f'').upperCross (I.pushComp g' g).hom ≫ (Functor.associator _ _ _).inv ≫
        whiskerRight (I.square sl).lowerStarUpperCross (I.mor g).push ≫
          (Functor.associator _ _ _).hom ≫
            whiskerLeft (I.mor h').push (I.square sr).lowerStarUpperCross ≫
              (Functor.associator _ _ _).inv ≫
                whiskerRight (I.pushComp h' h).inv (I.mor f).upperCross :=
  I.toPullPushData.lemma_7_17_xi sl sr (I.mor f).pushCrossAdj (I.mor f').pushCrossAdj
    (I.mor f'').pushCrossAdj

end DerivedPseudofunctorInput

/-! ### Non-vacuity: the one-object example -/

section Trivial

/-- The one-object category used in the example. -/
abbrev Pt : Type := Discrete PUnit.{1}

/-- The unique isomorphism between two objects of `Pt`. -/
def ptIso (A B : Pt) : A ≅ B := Discrete.eqToIso (Subsingleton.elim _ _)

/-- Any two functors to `Pt` are isomorphic. -/
def ptNatIso {C : Type*} [Category C] (F G : C ⥤ Pt) : F ≅ G :=
  NatIso.ofComponents (fun _ => ptIso _ _) (fun _ => Subsingleton.elim _ _)

/-- Any two endofunctors of `Pt` are adjoint. -/
def ptAdj (F G : Pt ⥤ Pt) : F ⊣ G :=
  Adjunction.mkOfUnitCounit
    { unit := (ptNatIso _ _).hom
      counit := (ptNatIso _ _).hom
      left_triangle := by ext; exact Subsingleton.elim _ _
      right_triangle := by ext; exact Subsingleton.elim _ _ }

/-- Every natural transformation between functors to `Pt` is invertible. -/
lemma ptIsIso {C : Type*} [Category C] {F G : C ⥤ Pt} (α : F ⟶ G) : IsIso α :=
  NatIso.isIso_of_isIso_app α

/-- The (unique) symmetric structure on the monoidal category `Pt`. -/
instance ptSymmetric : SymmetricCategory Pt where
  braiding _ _ := ptIso _ _
  braiding_naturality_right _ _ _ _ := Subsingleton.elim _ _
  braiding_naturality_left _ _ := Subsingleton.elim _ _
  hexagon_forward _ _ _ := Subsingleton.elim _ _
  hexagon_reverse _ _ _ := Subsingleton.elim _ _
  symmetry _ _ := Subsingleton.elim _ _

/-- The closed symmetric monoidal structure on `Pt`. -/
def ptTensorHom : DerivedTensorHomData Pt where
  rhom := (Functor.const _).obj (𝟭 Pt)
  tensorHomAdj _ := ptAdj _ _
  internalCurrying _ _ := ptNatIso _ _

/-- The six-functor package on `Pt` with all four functors the identity.  The `Prop`-valued
fields are example values (`True`, `⊤`), not hypotheses. -/
def ptMorphism : DerivedMorphismData ptTensorHom ptTensorHom where
  pull := 𝟭 Pt
  push := 𝟭 Pt
  pullPushAdj := Adjunction.id
  upperCross := 𝟭 Pt
  pushCrossAdj := Adjunction.id
  upperShriek := 𝟭 Pt
  pullUnit := ptIso _ _
  pullTensor := ptNatIso _ _
  projectionFormula := ptNatIso _ _
  chi := (ptNatIso _ _).hom
  sigma := (ptNatIso _ _).hom
  Perf := ⊤
  chi_isIso_of_perfect _ _ _ := inferInstance
  sigma_isIso_of_perfect _ _ _ := inferInstance
  IsProper := True
  IsFlat := True
  HasFiniteTorDimension := True
  sigma_isIso_of_flat _ _ _ := inferInstance
  properCrossShriek _ := Iso.refl _
  pullRHom _ := (ptNatIso _ _).hom
  pullRHom_isIso_of_perfect _ _ := inferInstance

variable (S : Type u) [Category.{v} S]

/-- **Non-vacuity of `DerivedPseudofunctorInput`**: the constant input with value `Pt` on an
arbitrary category of spaces. -/
def trivialInput : DerivedPseudofunctorInput.{v, u, 0, 0} S where
  D _ := Pt
  T _ := ptTensorHom
  mor _ := ptMorphism
  pullId _ := ptNatIso _ _
  pullComp _ _ := ptNatIso _ _
  pushId _ := ptNatIso _ _
  pushComp _ _ := ptNatIso _ _
  pull_assoc _ _ _ := by ext; exact Subsingleton.elim _ _
  pull_id_comp _ := by ext; exact Subsingleton.elim _ _
  pull_comp_id _ := by ext; exact Subsingleton.elim _ _
  push_assoc _ _ _ := by ext; exact Subsingleton.elim _ _
  push_id_comp _ := by ext; exact Subsingleton.elim _ _
  push_comp_id _ := by ext; exact Subsingleton.elim _ _
  conj_comp _ _ := by ext; exact Subsingleton.elim _ _
  conj_id _ := by ext; exact Subsingleton.elim _ _

/-- In the example every square has invertible `θ_□`, so the hypothesis of 7.15 is satisfiable. -/
instance trivialInput_isIso_theta {X' X Z' Z : S} {p : X ⟶ Z} {q : Z' ⟶ Z} {p' : X' ⟶ Z'}
    {q' : X' ⟶ X} (sq : CommSq p' q' q p) : IsIso ((trivialInput S).square sq).theta :=
  ptIsIso (C := Pt) _

/-- All hypotheses of Lemmas 7.12–7.17 hold simultaneously in the example, with coherence data. -/
example (X : S) :
    Nonempty (BaseChangeCoherenceData
      ((trivialInput S).square (CommSq.mk rfl : CommSq (𝟙 X) (𝟙 X) (𝟙 X) (𝟙 X)))) ∧
    IsIso ((trivialInput S).square (CommSq.mk rfl : CommSq (𝟙 X) (𝟙 X) (𝟙 X) (𝟙 X))).theta :=
  ⟨⟨(trivialInput S).coherence _⟩, inferInstance⟩

end Trivial

end DualityMates

end RelativeFM
