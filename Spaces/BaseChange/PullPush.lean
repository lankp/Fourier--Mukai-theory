/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Functors
import Spaces.BaseChange.OfPull

/-!
# GL26 Lemmas 7.12 and 7.17 for algebraic spaces

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), §7.2:

* **Lemma 7.12** (`lem:pseudofunctoriality_isos_are_conjugate`): `lemma_7_12`;
* **Lemma-Definition 7.13** (`def:upper_star_lower_star_bc`), the agreement of its two
  descriptions: `lemma_7_13`;
* **Lemma 7.17** (`lem:base_change_mates_pasting`): `lemma_7_17_theta` (item (1)) and
  `lemma_7_17_xi` (item (2));

for the derived categories, derived pullbacks and derived direct images of algebraic spaces
(GL26 §2.2, `Spaces/Categories.lean`, `Spaces/Functors.lean`).

## The data

`pullPushData B S hS : PullPushData (AlgebraicSpaces B S hS)` (the abstract setting of GL26 §7.2,
`FourierMukai/Prelim/BaseChangeMates.lean`) has

* `obj X = D(𝒪_X)` (`Spaces.D`), `pull f = Lf^*` (`Spaces.pull`), `push f = Rf_*` (`Spaces.push`),
  `adj f = (Lf^* ⊣ Rf_*)` (`Spaces.pullPushAdj`, Stacks 07A6);
* `pullComp f g : L(f ≫ g)^* ≅ Lf^* Lg^*` and `pullId X : L(𝟙)^* ≅ 𝟭`: AxiomMath's canonical
  pseudofunctoriality datum of derived pullback on small étale topoi,
  `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` (Stacks 0D6D), whose associativity
  and left unit law AxiomMath proves (`iso_assoc`, `iso_id`; `Spaces/.../
  DerivedPullbackCompositionCanonical.lean`, inside the import closure of `Spaces`, so not a tagged
  input).  The right unit law is not a field of AxiomMath's structure; it is derived here from the
  other two (`canonical_iso_comp_id`);
* `pushComp f g : R(f ≫ g)_* ≅ Rg_* Rf_*` and `pushId`: the conjugates (Stacks 0D6E, uniqueness of
  adjoints), with their pseudofunctor axioms proved by conjugation (`Spaces/BaseChange/OfPull.lean`).

So **no input** is used, Stacks or otherwise: in particular `DerivedPseudofunctorInput`
(Lipman (3.6.2), GL26 Lemma 2.13 `lem:spacey_Lipman_Hashimoto`, `results/ASSUMPTIONS.md` §1b) is
not needed for algebraic spaces.

## Deviations from GL26

* GL26 states 7.12–7.17 for `D_qc`; here they are stated on all of `D(𝒪_X)`.  This is more
  general: the functors restrict to `D_qc` (Stacks 08F4; for `Rf_*`, 08FA for `f` qcqs) and
  the restrictions of the natural transformations are the whiskerings by the inclusions, so the
  `D_qc` statements are the whiskered ones.  `R(-)_*` does not preserve `D_qc` for every morphism,
  which is why `PullPushData`, which wants `push f` for every `f`, is built on `D(𝒪_X)`.
* `pushComp` is the conjugate of AxiomMath's canonical 0D6D isomorphism, built exactly as AxiomMath
  builds `AlgebraicGeometry.Space.smallEtaleDerivedPushforwardCompIso`; the latter is built from
  a second spelling of 0D6D (`smallEtaleDerivedPullbackCompIso`, `SmallEtaleDerivedBaseChange.lean`)
  for which AxiomMath proves no coherence and no comparison with the canonical one.  The two
  pushforward isomorphisms are therefore not identified here.
* Mathlib conventions as in `Prelim/BaseChangeMates.lean` (diagrammatic composition, `CommSq`
  orientation, explicit associators).

## Non-vacuity

The statements carry no hypothesis besides a commutative square (and, for 7.17(2), right
adjoints of the three `Rf_*`); `CommSq.mk rfl` on identities and `pushIdAdj` (the right adjoint
of `R(𝟙)_*`) give instances (`lemma_7_17_xi_id`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Space
  RelativeFM.BaseChangeMates

namespace RelativeFM.Spaces.BaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- AxiomMath's canonical pseudofunctoriality datum of `L(-)^*` on algebraic spaces
(`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`, Stacks 0D6D). -/
abbrev canon : DerivedPullbackComposition B S hS := DerivedPullbackComposition.canonical B S hS

variable {B S hS}

/-- The identification attached to a factorisation `f ≫ g = k` is the one attached to `f ≫ g`
followed by transport along `f ≫ g = k`.  (True for every family of isomorphisms indexed by
factorisations.) -/
lemma canon_iso_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k) :
    (canon B S hS).iso f g k h =
      (canon B S hS).iso f g (f ≫ g) rfl ≪≫ eqToIso (congrArg (fun m => pull m) h) := by
  subst h
  ext
  simp

/-- `(pull 𝟙).map` of a component of `ι : L(𝟙)^* ≅ 𝟭` is the component at the image. -/
lemma pull_id_map_idIso (Y : AlgebraicSpaces B S hS) (N : D B S hS Y) :
    (pull (𝟙 Y)).map (((canon B S hS).idIso Y).hom.app N) =
      ((canon B S hS).idIso Y).hom.app ((pull (𝟙 Y)).obj N) := by
  have h := ((canon B S hS).idIso Y).hom.naturality (((canon B S hS).idIso Y).hom.app N)
  simp only [Functor.id_map] at h
  exact (cancel_mono (((canon B S hS).idIso Y).hom.app N)).1 h

/-- **The right unit law** of AxiomMath's canonical datum, derived from its associativity and
left unit law: the identification `L(𝟙)^* ⋙ Lf^* ≅ Lf^*` of the factorisation `f ≫ 𝟙 = f` is
`Lf^*` applied to `L(𝟙)^* ≅ 𝟭`. -/
lemma canonical_iso_comp_id {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (N : D B S hS Y) :
    ((canon B S hS).iso f (𝟙 Y) f (Category.comp_id f)).hom.app N =
      (pull f).map (((canon B S hS).idIso Y).hom.app N) := by
  set φ := (canon B S hS).iso f (𝟙 Y) f (Category.comp_id f)
  set ι := (canon B S hS).idIso Y
  -- at objects of the form `L(𝟙)^* M`
  have h₁ : ∀ M : D B S hS Y, φ.hom.app ((pull (𝟙 Y)).obj M) =
      (pull f).map (ι.hom.app ((pull (𝟙 Y)).obj M)) := by
    intro M
    have hA := congrArg Iso.hom ((canon B S hS).iso_assoc f (𝟙 Y) (𝟙 Y) (𝟙 Y) f f
      (Category.id_comp _) (Category.comp_id f) (Category.comp_id f) (Category.comp_id f) M)
    have hI := (canon B S hS).iso_id (𝟙 Y) (Category.id_comp _)
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hA
    rw [hI] at hA
    simp only [Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app,
      rightUnitor_hom_app] at hA
    exact (Iso.cancel_iso_hom_right _ _ (φ.app M)).1 (by simpa using hA)
  have h₂ := φ.hom.naturality (ι.hom.app N)
  simp only [Functor.comp_map] at h₂
  rw [pull_id_map_idIso, h₁, ← Functor.map_comp] at h₂
  rw [← cancel_epi ((pull f).map (ι.hom.app ((pull (𝟙 Y)).obj N)))]
  exact h₂.trans (Functor.map_comp _ _ _)

variable (B S hS)

/-- `L(f ≫ g)^* ≅ Lf^* Lg^*` (Mathlib order `pull g ⋙ pull f`): the inverse of AxiomMath's
canonical identification `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` (Stacks 0D6D). -/
def pullComp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull (f ≫ g) ≅ pull g ⋙ pull f :=
  ((canon B S hS).iso f g (f ≫ g) rfl).symm

/-- **The pullback pseudofunctor of algebraic spaces**: `D(𝒪_X)`, `Lf^*`, `Rf_*`,
`Lf^* ⊣ Rf_*` (Stacks 07A6), and AxiomMath's canonical composition and unit isomorphisms of
`L(-)^*` (Stacks 0D6D) with their coherences. -/
abbrev pullPseudofunctor : PullPseudofunctor (AlgebraicSpaces B S hS) where
  obj X := D B S hS X
  pull f := pull f
  push f := push f
  adj f := pullPushAdj f
  pullId X := (canon B S hS).idIso X
  pullComp f g := pullComp B S hS f g
  pull_assoc a b c := by
    ext x
    have h := congrArg Iso.inv ((canon B S hS).iso_assoc a b c (b ≫ c) (a ≫ b) (a ≫ b ≫ c)
      rfl rfl (Category.assoc a b c) rfl x)
    rw [canon_iso_eq (a ≫ b) c (a ≫ b ≫ c) (Category.assoc a b c)] at h
    simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, eqToIso.inv, eqToHom_app,
      NatTrans.comp_app, Category.assoc] at h
    simp only [pullComp, Iso.symm_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, eqToHom_app, Category.comp_id]
    rw [← h]
    simp
  pull_id_comp f := by
    ext x
    have h := (canon B S hS).iso_id f (Category.id_comp f)
    rw [canon_iso_eq (𝟙 _) f f (Category.id_comp f)] at h
    have hx := congr_app (congrArg Iso.hom h) x
    simp only [Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app, isoWhiskerLeft_hom,
      whiskerLeft_app, rightUnitor_hom_app] at hx
    simp only [pullComp, Iso.symm_hom, NatTrans.comp_app, whiskerLeft_app, rightUnitor_inv_app,
      eqToHom_app, Category.comp_id]
    rw [← cancel_epi (((canon B S hS).iso (𝟙 _) f (𝟙 _ ≫ f) rfl).hom.app x),
      Iso.hom_inv_id_app_assoc]
    simpa using hx.symm
  pull_comp_id f := by
    ext x
    have h := canonical_iso_comp_id f x
    rw [canon_iso_eq f (𝟙 _) f (Category.comp_id f)] at h
    simp only [Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app] at h
    simp only [pullComp, Iso.symm_hom, NatTrans.comp_app, whiskerRight_app, leftUnitor_inv_app,
      eqToHom_app, Category.comp_id]
    rw [← h]
    simp

/-- **The `PullPushData` of algebraic spaces** (GL26 §7.2 for `D(𝒪_X)`, `Lf^*`, `Rf_*`): built
from `pullPseudofunctor` by `PullPseudofunctor.toPullPushData`, so `R(-)_*`'s structure
isomorphisms are the conjugates of `L(-)^*`'s.  No input. -/
abbrev pullPushData : PullPushData (AlgebraicSpaces B S hS) :=
  (pullPseudofunctor B S hS).toPullPushData

variable {B S hS}

section Square

variable {X' X Z' Z : AlgebraicSpaces B S hS} {p : X ⟶ Z} {q : Z' ⟶ Z} {p' : X' ⟶ Z'}
  {q' : X' ⟶ X}

/-- The base change map `θ_□ : Lq^* Rp_* ⟶ Rp'_* L(q')^*` of a commutative square of algebraic
spaces (GL26 Lemma-Definition 7.13, `def:upper_star_lower_star_bc`, description (2)): the right
mate, under `Lp^* ⊣ Rp_*` and `L(p')^* ⊣ Rp'_*`, of `λ_□ : L(p')^* Lq^* ≅ L(q')^* Lp^*`. -/
lemma theta_eq (sq : CommSq p' q' q p) :
    (pullPushData B S hS).theta sq =
      mateEquiv (pullPushAdj p) (pullPushAdj p') ((pullPushData B S hS).lam sq).hom := rfl

/-- **Lemma 7.12** (`lem:pseudofunctoriality_isos_are_conjugate`) for algebraic spaces: for a
commutative square `p' ≫ q = q' ≫ p` of algebraic spaces, the pseudofunctoriality isomorphisms
`λ_□ : L(p')^* Lq^* ≅ L(q')^* Lp^*` and `ρ_□ : Rp_* R(q')_* ≅ Rq_* R(p')_*` are conjugate with
respect to the composite adjunctions `L(q')^*Lp^* ⊣ Rp_*R(q')_*` and `L(p')^*Lq^* ⊣ Rq_*R(p')_*`
(Stacks 07A6).  No input (`pullPushData`). -/
theorem lemma_7_12 (sq : CommSq p' q' q p) :
    conjugateEquiv ((pullPushAdj p).comp (pullPushAdj q'))
        ((pullPushAdj q).comp (pullPushAdj p')) ((pullPushData B S hS).lam sq).hom =
      ((pullPushData B S hS).rho sq).hom :=
  (pullPushData B S hS).lemma_7_12 sq

/-- **Lemma-Definition 7.13** (`def:upper_star_lower_star_bc`) for algebraic spaces: the two
descriptions of `θ_□` agree (the left mate of `ρ_□` is the right mate of `λ_□`). -/
theorem lemma_7_13 (sq : CommSq p' q' q p) :
    (pullPushData B S hS).thetaLeftMate sq = (pullPushData B S hS).theta sq :=
  (pullPushData B S hS).lemma_7_13 sq

end Square

section Pasting

variable {X'' X' X Y'' Y' Y : AlgebraicSpaces B S hS} {g' : X'' ⟶ X'} {g : X' ⟶ X}
  {h' : Y'' ⟶ Y'} {h : Y' ⟶ Y} {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y}

/-- **Lemma 7.17(1)** (`lem:base_change_mates_pasting`) for algebraic spaces: the `^*`-`_*` base
change map of a horizontal pasting of two commutative squares of algebraic spaces is, under
`L(h' ≫ h)^* ≅ L(h')^* Lh^*` and `L(g' ≫ g)^* ≅ L(g')^* Lg^*`, the pasting of the base change maps
of the two squares.  No input. -/
theorem lemma_7_17_theta (sl : CommSq f'' g' h' f') (sr : CommSq f' g h f) :
    (pullPushData B S hS).theta (sl.vert_comp sr) =
      whiskerLeft (push f) (pullComp B S hS h' h).hom ≫ (Functor.associator _ _ _).inv ≫
        whiskerRight ((pullPushData B S hS).theta sr) (pull h') ≫
          (Functor.associator _ _ _).hom ≫
            whiskerLeft (pull g) ((pullPushData B S hS).theta sl) ≫
              (Functor.associator _ _ _).inv ≫
                whiskerRight (pullComp B S hS g' g).inv (push f'') :=
  (pullPushData B S hS).lemma_7_17_theta sl sr

/-- **Lemma 7.17(2)** (`lem:base_change_mates_pasting`) for algebraic spaces: given right
adjoints `Rf_* ⊣ f^×`, `Rf'_* ⊣ (f')^×`, `Rf''_* ⊣ (f'')^×`, the `_*`-`^×` base change map of the
pasting is, under the conjugate identifications `R(g' ≫ g)_* ≅ Rg_* R(g')_*`,
`R(h' ≫ h)_* ≅ Rh_* R(h')_*`, the pasting of those of the two squares.  No input. -/
theorem lemma_7_17_xi (sl : CommSq f'' g' h' f') (sr : CommSq f' g h f)
    {Cf : D B S hS Y ⥤ D B S hS X} {Cf' : D B S hS Y' ⥤ D B S hS X'}
    {Cf'' : D B S hS Y'' ⥤ D B S hS X''}
    (cf : push f ⊣ Cf) (cf' : push f' ⊣ Cf') (cf'' : push f'' ⊣ Cf'') :
    (pullPushData B S hS).xi (sl.vert_comp sr) cf cf'' =
      whiskerLeft Cf'' ((pullPushData B S hS).pushComp g' g).hom ≫
        (Functor.associator _ _ _).inv ≫
          whiskerRight ((pullPushData B S hS).xi sl cf' cf'') (push g) ≫
            (Functor.associator _ _ _).hom ≫
              whiskerLeft (push h') ((pullPushData B S hS).xi sr cf cf') ≫
                (Functor.associator _ _ _).inv ≫
                  whiskerRight ((pullPushData B S hS).pushComp h' h).inv Cf :=
  (pullPushData B S hS).lemma_7_17_xi sl sr cf cf' cf''

end Pasting

/-! ### Non-vacuity -/

/-- `R(𝟙)_*` has a right adjoint (it is isomorphic to the identity): an instance of the right
adjoints `f^×` of Lemma 7.17(2). -/
def pushIdAdj (X : AlgebraicSpaces B S hS) : push (𝟙 X) ⊣ 𝟭 (D B S hS X) :=
  Adjunction.id.ofNatIsoLeft ((pullPushData B S hS).pushId X).symm

/-- Lemma 7.17(2) applies: the pasting of two identity squares on any algebraic space, with the
right adjoints `pushIdAdj`. -/
theorem lemma_7_17_xi_id (X : AlgebraicSpaces B S hS) :
    (pullPushData B S hS).xi ((CommSq.mk rfl : CommSq (𝟙 X) (𝟙 X) (𝟙 X) (𝟙 X)).vert_comp
        (CommSq.mk rfl : CommSq (𝟙 X) (𝟙 X) (𝟙 X) (𝟙 X))) (pushIdAdj X) (pushIdAdj X) =
      whiskerLeft (𝟭 _) ((pullPushData B S hS).pushComp (𝟙 X) (𝟙 X)).hom ≫
        (Functor.associator _ _ _).inv ≫
          whiskerRight ((pullPushData B S hS).xi (CommSq.mk rfl) (pushIdAdj X) (pushIdAdj X))
            (push (𝟙 X)) ≫
            (Functor.associator _ _ _).hom ≫
              whiskerLeft (push (𝟙 X)) ((pullPushData B S hS).xi (CommSq.mk rfl) (pushIdAdj X)
                (pushIdAdj X)) ≫
                (Functor.associator _ _ _).inv ≫
                  whiskerRight ((pullPushData B S hS).pushComp (𝟙 X) (𝟙 X)).inv (𝟭 _) :=
  lemma_7_17_xi _ _ (pushIdAdj X) (pushIdAdj X) (pushIdAdj X)

end RelativeFM.Spaces.BaseChange
