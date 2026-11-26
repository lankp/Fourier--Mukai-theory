/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Functors

/-!
# Tagged AxiomMath inputs of the `Spaces` library

CLAUDE.md rule 2 and `results/STACKS_POLICY.md`: the `Spaces` library imports only the
AxiomMath definition modules of `scripts/axiommath/spaces-imports.txt`.  An AxiomMath
*theorem* outside that import list is used through a `Prop` below, whose statement is the
AxiomMath statement verbatim (same binders, same hypotheses, same conclusion; a definition of
the AxiomMath module that is outside the import list is written out by its body, which is
said in the docstring), and which `SpacesVerified` discharges by the AxiomMath declaration it
names.  A result of `Spaces` that takes one of these as a hypothesis is conditional on it
until then.

| input | Stacks | AxiomMath declaration | AxiomMath file |
|---|---|---|---|
| `Tag06UQInput` | 06UQ | `AlgebraicGeometry.Space.isTriangulated_quasicoherentDerivedCategory` | `Spaces/QuasicoherentWeakSerre.lean` |
| `Tag08F4Input` | 08F4 | `AlgebraicGeometry.Space.derivedQuasicoherent_smallEtaleDerivedModulePullback` | `Spaces/QuasicoherentDerivedPullback.lean` |
| `Tag08F5Input` | 08F5 | `AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedTensor` | `Spaces/QuasicoherentDerivedTensorClosed.lean` |
| `Tag08FAInput` | 08FA (1) | `AlgebraicGeometry.Space.qcohDerived_derivedModulePushforward_obj` | `Spaces/QuasicoherentDerivedDirectImage.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, AxiomMath commit `f56a316`.)

Not inputs, because the import list provides them: `Lf^* ⊣ Rf_*` (Stacks 07A6,
`smallEtaleDerivedAdjunction`), `L(gf)^* ≅ Lf^*Lg^*` (0D6D, `smallEtaleDerivedPullbackCompIso`),
`R(gf)_* ≅ Rg_*Rf_*` (0D6E), `Lf^*(E ⊗^L F) ≅ Lf^*E ⊗^L Lf^*F` (07A4,
`smallEtaleDerivedPullbackTensorIso`).

Consumers here: `Dqc_isTriangulated` (06UQ) and the restrictions of `Lf^*`, `⊗^L`, `Rf_*` to
`D_qc` (`pullQc`, `tensorQc`, `pushQc`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06UQ** for `D_QCoh` on an algebraic space: `D_qc(𝒪_F)` is a triangulated
subcategory of `D(𝒪_F)`.  AxiomMath: the instance
`AlgebraicGeometry.Space.isTriangulated_quasicoherentDerivedCategory B S hS F hF`
(`Spaces/QuasicoherentWeakSerre.lean`), verbatim. -/
def Tag06UQInput : Prop :=
  ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F),
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)))).IsTriangulated

/-- **Stacks 08F4** for algebraic spaces: `Lf^*` sends `D_qc(X)` into `D_qc(Y)`, for every
`f : Y ⟶ X`.  AxiomMath:
`AlgebraicGeometry.Space.derivedQuasicoherent_smallEtaleDerivedModulePullback`
(`Spaces/QuasicoherentDerivedPullback.lean`), verbatim. -/
def Tag08F4Input : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (_hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E),
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      ((smallEtaleDerivedModulePullback B S hS f).obj E)

/-- **Stacks 08F5** for algebraic spaces: `D_qc(X)` is closed under `⊗^L`.  AxiomMath:
`AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedTensor`
(`Spaces/QuasicoherentDerivedTensorClosed.lean`), verbatim, with AxiomMath's abbreviation
`QcohDerived B S hS X` written out by its body
`DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} …)`
(`Spaces/QuasicoherentDerivedPushforward.lean`, outside the import list). -/
def Tag08F5Input : Prop :=
  ∀ (X : AlgebraicSpaces B S hS) (K L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (_hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) K)
    (_hL : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) L),
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
      (((smallEtaleDerivedTensor B S hS X).obj K).obj L)

/-- **Stacks 08FA, part (1)** for algebraic spaces: for `f : X ⟶ Y` quasi-compact and
quasi-separated, `Rf_*` sends `D_qc(X)` into `D_qc(Y)`.  AxiomMath:
`AlgebraicGeometry.Space.qcohDerived_derivedModulePushforward_obj`
(`Spaces/QuasicoherentDerivedDirectImage.lean`), verbatim, with `QcohDerived` written out
(as in `Tag08F5Input`) and AxiomMath's abbreviation `derivedModulePushforward B S hS f`
written out by its body
`derivedPushforward (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
(smallEtaleRingedToposHom B S hS f)`, which is also the body of
`smallEtaleDerivedModulePushforward B S hS f` (= `push f` here). -/
def Tag08FAInput : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (_hfqc : IsQuasiCompact B S hS f.hom)
    (_hfqs : IsQuasiSeparated B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (_hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E),
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      ((Stacks.Cohomology.DerivedPushforward.derivedPushforward
        (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f)).obj E)

variable {B S hS}

/-! ### Consumers -/

/-- `D_qc(X)` is a triangulated subcategory of `D(X)`, from Stacks 06UQ (`Tag06UQInput`). -/
theorem Dqc_isTriangulated (h : Tag06UQInput B S hS) (X : AlgebraicSpaces B S hS) :
    (Dqc X).IsTriangulated :=
  h X.1 X.2

/-- `Lf^* : D_qc(X) ⥤ D_qc(Y)` for `f : Y ⟶ X`, from Stacks 08F4 (`Tag08F4Input`). -/
def pullQc (h : Tag08F4Input B S hS) {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    (Dqc X).FullSubcategory ⥤ (Dqc Y).FullSubcategory :=
  (Dqc Y).lift ((Dqc X).ι ⋙ pull f) fun E => h f E.obj E.property

/-- `E ⊗^L - : D_qc(X) ⥤ D_qc(X)` for `E ∈ D_qc(X)`, from Stacks 08F5 (`Tag08F5Input`). -/
def tensorQc (h : Tag08F5Input B S hS) {X : AlgebraicSpaces B S hS}
    (E : (Dqc X).FullSubcategory) : (Dqc X).FullSubcategory ⥤ (Dqc X).FullSubcategory :=
  (Dqc X).lift ((Dqc X).ι ⋙ (tensor X).obj E.obj) fun F => h X E.obj F.obj E.property F.property

/-- `Rf_* : D_qc(X) ⥤ D_qc(Y)` for `f : X ⟶ Y` quasi-compact and quasi-separated, from
Stacks 08FA (`Tag08FAInput`). -/
def pushQc (h : Tag08FAInput B S hS) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    (Dqc X).FullSubcategory ⥤ (Dqc Y).FullSubcategory :=
  (Dqc Y).lift ((Dqc X).ι ⋙ push f) fun E => h f hfqc hfqs E.obj E.property

end RelativeFM.Spaces
