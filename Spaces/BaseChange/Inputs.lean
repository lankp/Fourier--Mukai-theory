/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Functors

/-!
# Tagged AxiomMath inputs for base change over algebraic spaces

Conventions of `Spaces/AxiomMathInputs.lean` (CLAUDE.md rule 2, `results/STACKS_POLICY.md`): each
input is a `Prop` whose statement is the AxiomMath statement verbatim, discharged in
`SpacesVerified` by the AxiomMath declaration named in its docstring.  Here the AxiomMath
statements mention four AxiomMath *definitions* whose modules are outside the `Spaces` import list
(and outside its import closure); each is written out by its body, as a local definition below
whose docstring names the AxiomMath definition it copies.  Each local definition is, by
construction, definitionally equal to the AxiomMath one.  Checked (wave 7, in a scratch file
importing in addition the cheap AxiomMath modules
`Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionAgree` and
`Spaces.SmallEtaleDerivedProjectionFormula`, 13 modules beyond the closure): `moduleCompIso f g =
smallEtaleDerivedModulePullbackCompIso B S hS f g`, `projectionFormulaMap f E K =
smallEtaleProjectionFormulaMap B S hS f E K` and the `BaseChange.map …` of `FlatBaseChangeInput` `=
smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w E` all hold by `rfl`, and
`CompIsoAgreeInput B S hS` is `fun f g => smallEtaleDerivedModulePullbackCompIso_eq B S hS f g`.

| local definition | AxiomMath definition (body copied) | AxiomMath file |
|---|---|---|
| `modulesCompTransport` | `AlgebraicGeometry.Space.pullbackModulesCompTransport` | `Spaces/SmallEtaleDerivedModuleAdjunction.lean` |
| `derivedPullbackIsoOfModulesIso` | `Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackIsoOfPullbackModulesIso` (at small étale topoi) | `CategoryTheory/Sites/Cohomology/DerivedPullback/PullbackModulesIsoDerivedPullback.lean` |
| `moduleCompIso` | `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso` | `Spaces/SmallEtaleDerivedModuleAdjunction.lean` |
| `projectionFormulaMap` | `AlgebraicGeometry.Space.smallEtaleProjectionFormulaMap` (= `CategoryTheory.adjunctionTensorMap` at Stacks 07A4) | `Spaces/SmallEtaleDerivedProjectionFormula.lean`, `CategoryTheory/Adjunction/ProjectionFormulaMap.lean` |

**Spelling.**  All statements here are elaborated, like `Spaces/AxiomMathInputs.lean`, in the
instance environment of `Spaces` (`SheafOfModules.instAbelian`), and use the `Spaces` names
`Spaces.D`, `Spaces.pull` (`= smallEtaleDerivedModulePullback`), `Spaces.push`
(`= smallEtaleDerivedModulePushforward`), `Spaces.tensor`, `Spaces.tensorObj` and
`Spaces.pullPushAdj` (`= smallEtaleDerivedAdjunction`), each an abbreviation or definition whose
body is the AxiomMath declaration.  (Mixing the two instance environments inside a `mateEquiv`
makes the kernel unfold AxiomMath's derived categories; see `Spaces/BaseChange/Cube.lean`.)

Also written by their bodies, inline: `smallEtaleDerivedModuleAdjunction B S hS f` (body
`derivedAdjunction … (smallEtaleRingedToposHom B S hS f)`, which is also the body of
`smallEtaleDerivedAdjunction B S hS f` = `Spaces.pullPushAdj f`, used here),
`smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w` (body
`smallEtaleDerivedModulePullbackCompIso B S hS g' f ≪≫ smallEtaleDerivedModulePullbackCongr B S hS w`),
`smallEtaleDerivedModulePullbackCongr B S hS h` (body `eqToIso (congrArg (fun f ↦ …) h)`),
`smallEtaleDerivedModuleBaseChangeMap` (body `Stacks.CategoryTheory.BaseChange.map …`) and
`QcohDerived B S hS X` (= `Spaces.Dqc X`, as in `Spaces/AxiomMathInputs.lean`).

| input | Stacks | AxiomMath declaration | AxiomMath file |
|---|---|---|---|
| `CompIsoAgreeInput` | 0D6D (two spellings agree) | `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_eq` | `Spaces/Morphisms/PseudoCoherent/DerivedPullbackCompositionAgree.lean` |
| `FlatBaseChangeInput` | 0A1K at `𝒪_X` (flat base change, `f` flat) | `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isFlat` | `Spaces/Perfect/CohomologyBaseChangeIso.lean` |
| `Tag08INInput` | 08IN (projection formula) | `AlgebraicGeometry.Space.isIso_smallEtaleProjectionFormulaMap` | `Spaces/SmallEtaleProjectionFormulaIso.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/` or `StacksFrontier/`, AxiomMath commit
`f56a316`.)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy)
open scoped CategoryTheory.Prod

namespace RelativeFM.Spaces.BaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Bodies

variable {B S hS} {X Y Z : AlgebraicSpaces B S hS}

/-- The body of AxiomMath's `AlgebraicGeometry.Space.pullbackModulesCompTransport B S hS f g`
(`Spaces/SmallEtaleDerivedModuleAdjunction.lean`), with AxiomMath's abbreviation
`smallEtaleRingedToposHomComp B S hS f g` written out by its body `RingedToposHom.comp … g f`. -/
def modulesCompTransport (f : X ⟶ Y) (g : Y ⟶ Z) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Z)
        (RingedToposHom.comp (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f)).toModulesHom ≅
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS (f ≫ g)).toModulesHom :=
  (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Z)
      (RingedToposHom.comp (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f))).leftAdjointUniq
    ((RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS (f ≫ g))).ofNatIsoRight
        (pushforwardModulesCompTransport B S hS f g).symm)

/-- The body of AxiomMath's
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackIsoOfPullbackModulesIso`
(`CategoryTheory/Sites/Cohomology/DerivedPullback/PullbackModulesIsoDerivedPullback.lean`), at the
small étale ringed topoi of two algebraic spaces. -/
def derivedPullbackIsoOfModulesIso
    {φ ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
    [(pullbackOnHomotopy φ).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := smallEtaleRingedTopos B S hS Y))]
    [(pullbackOnHomotopy ψ).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := smallEtaleRingedTopos B S hS Y))]
    (e : φ.toModulesHom.pullbackModules ≅ ψ.toModulesHom.pullbackModules) :
    derivedPullback (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y) φ ≅
      derivedPullback (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        ψ :=
  Functor.leftDerivedNatIso
    (derivedPullback (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y) φ)
    (derivedPullback (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y) ψ)
    (derivedPullbackComparison φ) (derivedPullbackComparison ψ)
    (quasiIsoTarget (Y := smallEtaleRingedTopos B S hS Y))
    (Functor.isoWhiskerRight
      (@Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
        (RingedToposHom.pullbackModules_additive φ) (RingedToposHom.pullbackModules_additive ψ)
        e (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- The body of AxiomMath's `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso B S hS
f g` (Stacks 0D6D; `Spaces/SmallEtaleDerivedModuleAdjunction.lean`), with
`derivedPullbackIsoOfPullbackModulesIso` and `pullbackModulesCompTransport` written out by their
bodies (`derivedPullbackIsoOfModulesIso`, `modulesCompTransport`). -/
def moduleCompIso (f : X ⟶ Y) (g : Y ⟶ Z) : pull g ⋙ pull f ≅ pull (f ≫ g) :=
  derivedPullbackCompIso (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (Z := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g) ≪≫
    derivedPullbackIsoOfModulesIso
      (φ := RingedToposHom.comp (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f))
      (ψ := smallEtaleRingedToposHom B S hS (f ≫ g)) (modulesCompTransport f g)

/-- The body of AxiomMath's `AlgebraicGeometry.Space.smallEtaleProjectionFormulaMap B S hS f E K`
(`Spaces/SmallEtaleDerivedProjectionFormula.lean`): AxiomMath's
`CategoryTheory.adjunctionTensorMap (smallEtaleDerivedModuleAdjunction B S hS f)
(Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
(Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X)) (smallEtaleDerivedPullbackTensorIso f).hom
E K`, with `adjunctionTensorMap` (`CategoryTheory/Adjunction/ProjectionFormulaMap.lean`) written out
by its body `adj.homEquiv _ _ (α.app (R.obj G, H) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)))` and
`smallEtaleDerivedModuleAdjunction B S hS f` by the same body as `smallEtaleDerivedAdjunction`.
The projection map `Rf_* E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^* K)` (Stacks 08IN). -/
def projectionFormulaMap (f : X ⟶ Y) (E : D B S hS X) (K : D B S hS Y) :
    tensorObj ((push f).obj E) K ⟶ (push f).obj (tensorObj E ((pull f).obj K)) :=
  (pullPushAdj f).homEquiv _ _
    ((smallEtaleDerivedPullbackTensorIso f).hom.app ((push f).obj E, K) ≫
      (Functor.uncurry.obj (tensor X)).map ((pullPushAdj f).counit.app E ×ₘ 𝟙 ((pull f).obj K)))

end Bodies

/-- **Stacks 0D6D, the two spellings agree.**  AxiomMath's composition isomorphism
`smallEtaleDerivedModulePullbackCompIso` (through which its base change map
`smallEtaleDerivedModuleBaseChangeMap` and Stacks 08IR, 0A1K are stated) is the one of the
canonical pseudofunctoriality datum, `smallEtaleDerivedPullbackCompIsoOfTwoIso` (through which
`Spaces/BaseChange/PullPush.lean` builds `L(-)^*`).  AxiomMath:
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_eq`
(`Spaces/Morphisms/PseudoCoherent/DerivedPullbackCompositionAgree.lean`), verbatim, with
`smallEtaleDerivedModulePullbackCompIso` written out by its body (`moduleCompIso`). -/
def CompIsoAgreeInput : Prop :=
  ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
    moduleCompIso f g = smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS f g

/-- **Flat base change for a flat pushed morphism** (Stacks 0A1K at `𝒢 = 𝒪_X`, a case of
Stacks 08IR): for a cartesian square `g' ≫ f = f' ≫ g` of algebraic spaces with `f` flat,
quasi-compact and quasi-separated, the base change map `Lg^* Rf_* E ⟶ Rf'_* L(g')^* E` is an
isomorphism for `E ∈ D_qc(X)`.  AxiomMath:
`AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isFlat`
(`Spaces/Perfect/CohomologyBaseChangeIso.lean`), verbatim, with
`smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E` written out by its body
`Stacks.CategoryTheory.BaseChange.map (smallEtaleDerivedModuleAdjunction B S hS f)
(smallEtaleDerivedModuleAdjunction B S hS f') (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
(smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w) E` and the four definitions in it by
their bodies (module docstring), and `QcohDerived B S hS X` by `Dqc X`. -/
def FlatBaseChangeInput : Prop :=
  ∀ {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (_hfqc : IsQuasiCompact B S hS f.hom)
    (_hfqs : IsQuasiSeparated B S hS f.hom) (_hfl : IsFlat B S hS f.hom)
    (E : D B S hS X) (_hE : Dqc X E),
    IsIso (Stacks.CategoryTheory.BaseChange.map (pullPushAdj f) (pullPushAdj f')
      (moduleCompIso f' g) (moduleCompIso g' f ≪≫ eqToIso (congrArg (fun f ↦ pull f) sq.w)) E)

/-- **Stacks 08IN** (the projection formula) for algebraic spaces: for `f : X ⟶ Y`
quasi-compact and quasi-separated, `E ∈ D_qc(X)` and `K ∈ D_qc(Y)`, the projection map
`Rf_* E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^* K)` is an isomorphism.  AxiomMath:
`AlgebraicGeometry.Space.isIso_smallEtaleProjectionFormulaMap`
(`Spaces/SmallEtaleProjectionFormulaIso.lean`), verbatim, with `smallEtaleProjectionFormulaMap`
written out by its body (`projectionFormulaMap`) and `QcohDerived` by `Dqc`. -/
def Tag08INInput : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (_hfqc : IsQuasiCompact B S hS f.hom)
    (_hfqs : IsQuasiSeparated B S hS f.hom)
    (E : D B S hS X) (_hE : Dqc X E) (K : D B S hS Y) (_hK : Dqc Y K),
    IsIso (projectionFormulaMap f E K)

end RelativeFM.Spaces.BaseChange
