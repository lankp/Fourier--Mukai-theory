/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.AxiomMathInputs
import StacksFrontier.CategoryTheory.Triangulated.CompactObjects.ThickSubcategory

/-!
# Tagged AxiomMath inputs of GL26 §5 (quasi-perfect objects over algebraic spaces)

Guisado Villalgordo–Lank (GL26), §5 (`sec:quasi-perfect`): the AxiomMath theorems outside the
`Spaces` import list that `Spaces/QuasiPerfect/` uses and that are not already tagged elsewhere in
the tree, each stated verbatim (conventions of `Spaces/AxiomMathInputs.lean`) and discharged in
`SpacesVerified` by the declaration it names.

| input | Stacks | AxiomMath declaration | AxiomMath file |
|---|---|---|---|
| `Tag09JBInput` | 09JB | `AlgebraicGeometry.Space.isPerfect_derivedTensorProductFunctor_obj_obj` | `Spaces/Perfect/DerivedTensorPowersPerfect.lean` |
| `Tag0GFHInput` | 0GFH, (7) ⇒ (1) | `AlgebraicGeometry.Space.exists_isLE_of_highHomVanishingOnCompact` | `Spaces/Perfect/DetectingBoundedAbove.lean` |
| `Tag0GFIInput` | 0GFI, (7) ⇒ (1) | `AlgebraicGeometry.Space.exists_isGE_of_lowHomVanishingOnCompact` | `Spaces/Perfect/DetectingBoundedBelow.lean` |
| `QcohTruncLEInput` | 06UQ (truncations) | `AlgebraicGeometry.Space.qcohDerived_truncLE` | `Spaces/CompactGeneration/AffineGenerator.lean` |
| `StructureSheafQcohInput` | 06UQ (`𝒪_X[0]`) | `AlgebraicGeometry.Space.qcohDerived_singleFunctor_structureModule` | `Spaces/CompactGeneration/AffineGenerator.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, AxiomMath commit `f56a316`.)

The other inputs used by `Spaces/QuasiPerfect/` are already in the tree: `Tag08F4Input`,
`Tag08F5Input`, `Tag08FAInput` (`Spaces/AxiomMathInputs.lean`), `Tag0E55Input`
(`Spaces/Duality/Inputs.lean`), `Tag0A8AInput` (`Spaces/InternalHom/Inputs.lean`),
`BaseChange.Tag08INInput` (the projection formula, `Spaces/BaseChange/Inputs.lean`) and, from
`Spaces/LP26/Inputs.lean`, `PerfectQcohInput`, `Tag09M8Input`, `Tag09MBInput`, `Tag08FABoundInput`.

**Spelling.**  As in `Spaces/LP26/Inputs.lean`, AxiomMath's `B.contains_terminal` is bound as
`hZ`, and the bodies of AxiomMath definitions of modules outside the import list are written out:
`QcohDerived B S hS X` is `Spaces.Dqc X`; `HighHomVanishingOnCompact X hX E` is
`∀ P : QuasicoherentDerivedCategory B S hS X hX, IsCompactObject.{u} P → highHomVanishing E P.obj`
with `highHomVanishing M P = ∃ N, ∀ i, N ≤ i → Subsingleton (P⟦-i⟧ ⟶ M)`;
`LowHomVanishingOnCompact` likewise, with `lowHomVanishing M P = ∃ N, ∀ i, i ≤ N →
Subsingleton (P⟦-i⟧ ⟶ M)`; `structureModule ⟨X, hX⟩` is `SheafOfModules.unit _` (as in
`Spaces/Supported/DetectingInputs.lean`).  `Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleRingedSite B S hS F hF)`
is, by `abbrev`, `(Stacks.SheafOfModules.canonicalDerivedTensorProduct _).tensor`, the body of
AxiomMath's `smallEtaleDerivedTensor B S hS ⟨F, hF⟩` (= `Spaces.tensor`); `tensorObj_eq` below
checks this by `rfl`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.QuasiPerfect

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 09JB** for algebraic spaces: the derived tensor product of two perfect objects of
`D(𝒪_X)` is perfect.  AxiomMath:
`AlgebraicGeometry.Space.isPerfect_derivedTensorProductFunctor_obj_obj E E' hE hE'`
(`Spaces/Perfect/DerivedTensorPowersPerfect.lean`), verbatim. -/
def Tag09JBInput : Prop :=
  ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    (E E' : DerivedCategory (Modules.{u, u} B S hS F hF))
    (_hE : (smallEtaleRingedSite B S hS F hF).IsPerfect E)
    (_hE' : (smallEtaleRingedSite B S hS F hF).IsPerfect E'),
    (smallEtaleRingedSite B S hS F hF).IsPerfect
      (((Stacks.SheafOfModules.derivedTensorProductFunctor
        (smallEtaleRingedSite B S hS F hF)).obj E).obj E')

/-- **Stacks 0GFH, (7) ⇒ (1)**, for algebraic spaces: on a quasi-compact quasi-separated `X`, an
object `E` of `D_qc(X)` such that `Hom(P[-i], E) = 0` for `i ≫ 0` for every compact `P` of
`D_qc(X)` is bounded above.  AxiomMath:
`AlgebraicGeometry.Space.exists_isLE_of_highHomVanishingOnCompact X hqc hqs E hE`
(`Spaces/Perfect/DetectingBoundedAbove.lean`), verbatim, with `HighHomVanishingOnCompact` and
`highHomVanishing` written out by their bodies (module docstring) and `B.contains_terminal` bound
as `hZ`. -/
def Tag0GFHInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (_hqc : IsQuasiCompactSpace B S hS X.1) (_hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (_hE : ∀ P : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2, IsCompactObject.{u} P →
      ∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (P.obj⟦-i⟧ ⟶ E.obj)),
    ∃ a : ℤ, E.obj.IsLE a

/-- **Stacks 0GFI, (7) ⇒ (1)**, for algebraic spaces: on a quasi-compact quasi-separated `X`, an
object `E` of `D_qc(X)` such that `Hom(P[-i], E) = 0` for `i ≪ 0` for every compact `P` of
`D_qc(X)` is bounded below.  AxiomMath:
`AlgebraicGeometry.Space.exists_isGE_of_lowHomVanishingOnCompact X hqc hqs E hE`
(`Spaces/Perfect/DetectingBoundedBelow.lean`), verbatim, with `LowHomVanishingOnCompact` and
`lowHomVanishing` written out by their bodies and `B.contains_terminal` bound as `hZ`. -/
def Tag0GFIInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (_hqc : IsQuasiCompactSpace B S hS X.1) (_hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (_hE : ∀ P : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2, IsCompactObject.{u} P →
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P.obj⟦-i⟧ ⟶ E.obj)),
    ∃ a : ℤ, E.obj.IsGE a

/-- **The truncations `τ_{≤ n}` preserve `D_qc`** (Stacks 06UQ: quasi-coherent modules form a weak
Serre subcategory).  AxiomMath: `AlgebraicGeometry.Space.qcohDerived_truncLE E n hE`
(`Spaces/CompactGeneration/AffineGenerator.lean`), verbatim, with `QcohDerived` written as
`Dqc`. -/
def QcohTruncLEInput : Prop :=
  ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    (E : DerivedCategory (Modules.{u, u} B S hS X hX)) (n : ℤ) (_hE : Dqc ⟨X, hX⟩ E),
    Dqc ⟨X, hX⟩ ((DerivedCategory.TStructure.t.truncLE n).obj E)

/-- **`𝒪_X[0]` lies in `D_qc(X)`**.  AxiomMath:
`AlgebraicGeometry.Space.qcohDerived_singleFunctor_structureModule`
(`Spaces/CompactGeneration/AffineGenerator.lean`), verbatim, with `QcohDerived` written as `Dqc`
and `structureModule ⟨X, hX⟩` as `SheafOfModules.unit _`. -/
def StructureSheafQcohInput : Prop :=
  ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X},
    Dqc ⟨X, hX⟩ ((DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)))

variable {B S hS}

/-- The tensor product of `Tag09JBInput` is `Spaces.tensorObj`. -/
theorem tensorObj_eq (X : AlgebraicSpaces B S hS) (E E' : D B S hS X) :
    (((Stacks.SheafOfModules.derivedTensorProductFunctor
        (smallEtaleRingedSite B S hS X.1 X.2)).obj E).obj E') = tensorObj E E' :=
  rfl

/-- Perfect objects are closed under `⊗^L`, from Stacks 09JB (`Tag09JBInput`). -/
theorem perf_tensorObj (h : Tag09JBInput B S hS) {X : AlgebraicSpaces B S hS} {E E' : D B S hS X}
    (hE : Perf X E) (hE' : Perf X E') : Perf X (tensorObj E E') :=
  h (F := X.1) (hF := X.2) E E' hE hE'

end RelativeFM.Spaces.QuasiPerfect
