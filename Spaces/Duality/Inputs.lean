/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.AxiomMathInputs

/-!
# Tagged AxiomMath inputs of GL26 §2.4 (duality for spaces)

Guisado Villalgordo–Lank (GL26), §2.4 (`sec:duality`): the AxiomMath theorems outside the
`Spaces` import list that `Spaces/Duality/` uses, each stated verbatim (conventions of
`Spaces/AxiomMathInputs.lean`) and discharged in `SpacesVerified` by the declaration it names.

| input | Stacks | AxiomMath declaration | AxiomMath file |
|---|---|---|---|
| `Tag0E55Input` | 0E55 | `AlgebraicGeometry.Space.isLeftAdjoint_quasicoherentDerivedPushforward` | `Spaces/CompactGeneration/QcqsCompactGeneration.lean` |
| `Tag04NXInput` | 04NX (2) | `AlgebraicGeometry.Space.isProper_of_comp_of_isSeparated` | `Spaces/SeparationCancellation.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, AxiomMath commit `f56a316`.)

The other inputs used by `Spaces/Duality/` are already in the tree: `Tag08FAInput`,
`Tag08F4Input` (`Spaces/AxiomMathInputs.lean`), the recollement and support inputs of
`Spaces/LP26/Inputs.lean` and `SupportTriangulatedInput` (`Spaces/Supported/Inputs.lean`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Duality

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0E55** for algebraic spaces: for `f : X ⟶ Y` with `X` quasi-compact and
quasi-separated and `Y` quasi-separated, the restricted derived direct image
`Rf_* : D_qc(X) ⥤ D_qc(Y)` is a left adjoint.  AxiomMath:
`AlgebraicGeometry.Space.isLeftAdjoint_quasicoherentDerivedPushforward hZ f hXqc hXqs hYqs`
(`Spaces/CompactGeneration/QcqsCompactGeneration.lean`), verbatim, with three definitions of
modules outside the import list written out by their bodies:
`QuasicoherentDerivedCategory B S hS X.1 X.2` is
`(DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite …)).FullSubcategory`,
which is `(Spaces.Dqc X).FullSubcategory` (`Spaces.Dqc_fullSubcategory_eq`, by `rfl`),
`derivedModulePushforward B S hS f` is
`derivedPushforward (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
(smallEtaleRingedToposHom B S hS f)` (as in `Spaces.Tag08FAInput`), and
`quasicoherentDerivedPushforward B S hS f hfqc hfqs` is
`ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ derivedModulePushforward B S hS f) h` for the proof
`h` of Stacks 08FA (1).  The proofs that AxiomMath's statement passes as arguments (quasi-
compactness and quasi-separatedness of `f`, and `h`) are bound here as `hR`; by proof
irrelevance the statement does not depend on them, so AxiomMath's theorem proves this one. -/
def Tag0E55Input : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (_hXqc : IsQuasiCompactSpace B S hS X.1) (_hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (_hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hR : ∀ E : (Dqc X).FullSubcategory,
      Dqc Y ((Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f)).obj E.obj)),
    ((Dqc Y).lift ((Dqc X).ι ⋙
      Stacks.Cohomology.DerivedPushforward.derivedPushforward
        (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f)) hR).IsLeftAdjoint

/-- **Stacks 04NX, part (2)**: if `f ≫ g` is proper and `g` is separated, then `f` is proper.
AxiomMath: `AlgebraicGeometry.Space.isProper_of_comp_of_isSeparated B S hS hX hY hZ f g hfg hg`
(`Spaces/SeparationCancellation.lean`), verbatim. -/
def Tag04NXInput : Prop :=
  ∀ {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y)
    (_hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (_hfg : IsProper B S hS (f ≫ g)) (_hg : IsSeparated B S hS g),
    IsProper B S hS f

end RelativeFM.Spaces.Duality
