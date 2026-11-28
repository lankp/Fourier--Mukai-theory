/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.AxiomMathInputs
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMap

/-!
# Tagged AxiomMath inputs for the internal Hom of GL26 §2.2

Conventions of `Spaces/AxiomMathInputs.lean` (CLAUDE.md rule 2, `results/STACKS_POLICY.md`): each
input is a `Prop` whose statement is the AxiomMath statement verbatim, discharged in
`SpacesVerified` by the AxiomMath declaration named in its docstring.

| input | Stacks | AxiomMath declaration | AxiomMath file |
|---|---|---|---|
| `Tag0CR4Input` | 0CR4 (coherator of a qcqs space) | `AlgebraicGeometry.Space.isLeftAdjoint_ι_qcohDerived` | `Spaces/CompactGeneration/QcqsDerivedCoherator.lean` |
| `Tag0A8AInput` | 0A8A | `AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedSheafHom` | `Spaces/Perfect/DerivedSheafHomQuasicoherent.lean` |
| `Tag08I3PerfectInput` | 08I3 / 08JP, perfect source | `AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_isPerfect` | `Spaces/Perfect/SmallEtaleDerivedPullbackSheafHomMapPerfect.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, AxiomMath commit `f56a316`.)

**Spelling.**  As in `Spaces/BaseChange/Inputs.lean`, the statements are elaborated in the
instance environment of `Spaces` and use `Spaces` names whose bodies are the AxiomMath
declarations: `Spaces.Dqc X` is, by `abbrev`, the body
`DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} …)` of
AxiomMath's `QcohDerived B S hS X` (whose module is outside the import list), so
`(Spaces.Dqc X).ι` is AxiomMath's `(QcohDerived B S hS X).ι`.  Everything else
(`smallEtaleDerivedSheafHom`, `smallEtaleDerivedModulePullback`,
`smallEtaleDerivedPullbackSheafHomMap`, `RingedSite.IsPerfect`, `RingedSite.IsPseudoCoherent`,
`DerivedCategoryB.derivedCategoryBPlus`, `IsQuasiCompactSpace`, `IsAbsolutelyQuasiSeparated`) is
AxiomMath's own name, provided by the import list.

**Not inputs**, because the import list now provides them (`scripts/axiommath/spaces-imports.txt`,
wave 10): `R𝓗om` on `D(𝒪_X)` (`smallEtaleDerivedSheafHom`), the adjunction
`- ⊗^L P ⊣ R𝓗om(P, -)` (Stacks 08J8, `smallEtaleDerivedTensorSheafHomAdjunction`), the
perfectness of the dual and `(E^∨)^∨ ≅ E` (08JJ, `isPerfect_smallEtaleDerivedDual`,
`smallEtaleDerivedBidualIso`), `R𝓗om(E, G) ≅ E^∨ ⊗^L G` for perfect `E` (08JJ,
`smallEtaleDerivedSheafHomIsoTensorDual`, with the naturality of the model's isomorphism
`RingedSite.derivedDualTensorSheafHomIso_naturality`), the map of Stacks 08I3
(`smallEtaleDerivedPullbackSheafHomMap`) and the associator of `⊗^L`
(`Stacks.SheafOfModules.DerivedTensorProduct.associatorGeneral`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Space Opposite

namespace RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CR4** (existence of the coherator) for algebraic spaces: for a quasi-compact and
quasi-separated algebraic space `X`, the inclusion `D_qc(X) ⥤ D(X)` has a right adjoint.
AxiomMath: `AlgebraicGeometry.Space.isLeftAdjoint_ι_qcohDerived`
(`Spaces/CompactGeneration/QcqsDerivedCoherator.lean`), verbatim, with `QcohDerived B S hS X`
written as `Dqc X` (same body).  (`hZ` says that the site contains `Spec ℤ`, through which
AxiomMath expresses quasi-separatedness.) -/
def Tag0CR4Input : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (_hqc : IsQuasiCompactSpace B S hS X.1) (_hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1),
    (Dqc X).ι.IsLeftAdjoint

/-- **Stacks 0A8A** for algebraic spaces: `R𝓗om(K, L)` has quasi-coherent cohomology if either
`K` is pseudo-coherent and `L ∈ D^+_qc(X)`, or `K` is perfect and `L ∈ D_qc(X)`.  AxiomMath:
`AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedSheafHom`
(`Spaces/Perfect/DerivedSheafHomQuasicoherent.lean`), verbatim, with `QcohDerived` written as
`Dqc`. -/
def Tag0A8AInput : Prop :=
  ∀ (X : AlgebraicSpaces B S hS)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (_h : (RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) K ∧
        DerivedCategoryB.derivedCategoryBPlus
          (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) L) ∨
      (RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) K ∧ Dqc X L)),
    Dqc X (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj L)

/-- **Stacks 08I3 / 08JP out of a perfect object**, for algebraic spaces: for `f : X ⟶ Y`,
`K ∈ D(𝒪_Y)` perfect and any `L`, the canonical map `Lf^*R𝓗om(K, L) ⟶ R𝓗om(Lf^*K, Lf^*L)` is an
isomorphism.  AxiomMath:
`AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_isPerfect`
(`Spaces/Perfect/SmallEtaleDerivedPullbackSheafHomMapPerfect.lean`), verbatim. -/
def Tag08I3PerfectInput : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (_hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K)
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))),
    IsIso (smallEtaleDerivedPullbackSheafHomMap f K L)

end RelativeFM.Spaces
