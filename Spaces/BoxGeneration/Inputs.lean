/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.BaseChange.Inputs

/-!
# Tagged AxiomMath input for GL26 Lemma 5.4: étale base change

The one AxiomMath theorem outside the `Spaces` import closure that
`Spaces/BoxGeneration/Lemma54.lean` (GL26 Lemma 5.4, `lem:neeman2023cor5_10`) uses and that no
earlier `Inputs.lean` provides.  Conventions of `Spaces/AxiomMathInputs.lean` (CLAUDE.md rule 2,
`results/STACKS_POLICY.md`): the statement is AxiomMath's verbatim, and `SpacesVerified`
discharges it by the AxiomMath declaration named in its docstring.

* `EtaleBaseChangeInput` (Stacks 08GE): AxiomMath's
  `AlgebraicGeometry.Space.isIso_smallEtaleDerivedModuleBaseChangeMap`, in
  `Spaces/Pushouts/DerivedPushoutEtaleBaseChange.lean`.

(path relative to `StacksFrontier/AlgebraicGeometry/`, AxiomMath commit `f56a316`.)

## Spelling

AxiomMath states the theorem for its base change map
`smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w K`
(`Spaces/SmallEtaleDerivedModuleAdjunction.lean`, outside the import closure).  As in
`BaseChange.FlatBaseChangeInput` (`Spaces/BaseChange/Inputs.lean`), the map is written out by its
body `Stacks.CategoryTheory.BaseChange.map (smallEtaleDerivedModuleAdjunction B S hS f)
(smallEtaleDerivedModuleAdjunction B S hS f') (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
(smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w) K`, with the four AxiomMath
definitions in it written out by their bodies: `pullPushAdj` (= `smallEtaleDerivedAdjunction`,
whose body is that of `smallEtaleDerivedModuleAdjunction`), `BaseChange.moduleCompIso`
(= `smallEtaleDerivedModulePullbackCompIso`) and
`moduleCompIso g' f ≪≫ eqToIso (congrArg (fun f ↦ pull f) sq.w)`
(= `smallEtaleDerivedModulePullbackSquareIso`, whose body is
`smallEtaleDerivedModulePullbackCompIso B S hS g' f ≪≫
smallEtaleDerivedModulePullbackCongr B S hS w`).
This is the spelling of `BaseChange.FlatBaseChangeInput`, which wave 7 checked to be AxiomMath's
map by `rfl`.

AxiomMath binds `f g f' g'` explicitly (section variables) and `B S hS X Y X' Y'` implicitly; the
statement below binds `X Y X' Y' f g f' g'` implicitly, which does not change the proposition.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.BoxGeneration

open RelativeFM.Spaces RelativeFM.Spaces.BaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 08GE** (étale base change for `Rf_*`), in the form of the base change map: for a
cartesian square `g' ≫ f = f' ≫ g` of algebraic spaces with `g` étale, the base change map
`Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` is an isomorphism for every `K ∈ D(𝒪_X)`.  AxiomMath:
`AlgebraicGeometry.Space.isIso_smallEtaleDerivedModuleBaseChangeMap f g f' g' sq hg`
(`Spaces/Pushouts/DerivedPushoutEtaleBaseChange.lean`), verbatim, with
`smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w K` written out by its body as in
`BaseChange.FlatBaseChangeInput` (module docstring). -/
def EtaleBaseChangeInput : Prop :=
  ∀ {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (_hg : IsEtale B S hS g.hom),
    ∀ K : D B S hS X,
      IsIso (Stacks.CategoryTheory.BaseChange.map (pullPushAdj f) (pullPushAdj f')
        (moduleCompIso f' g) (moduleCompIso g' f ≪≫ eqToIso (congrArg (fun f ↦ pull f) sq.w)) K)

end RelativeFM.Spaces.BoxGeneration
