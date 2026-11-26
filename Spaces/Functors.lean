/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Categories
import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor

/-!
# The functors of GL26 §2.2 over algebraic spaces

GL26 §2.2, `sec:prelim_stacks_functors`: for a morphism `f : X ⟶ Y` of algebraic spaces,
the derived pullback `Lf^* : D(Y) ⥤ D(X)`, the derived direct image `Rf_* : D(X) ⥤ D(Y)`,
the adjunction `Lf^* ⊣ Rf_*`, and the derived tensor product `⊗^L` on `D(X)`.  All four are
AxiomMath's, renamed (`AXIOMMATH_MAP.md`, A.4):

| here | AxiomMath | Stacks |
|---|---|---|
| `pull f` (`Lf^*`) | `smallEtaleDerivedModulePullback B S hS f` | 06YY, 03G8 |
| `push f` (`Rf_*`) | `smallEtaleDerivedModulePushforward B S hS f` | 07A5 |
| `pullPushAdj f` (`Lf^* ⊣ Rf_*`) | `smallEtaleDerivedAdjunction B S hS f` | 07A6 |
| `tensor X` (`⊗^L`) | `smallEtaleDerivedTensor B S hS X` | 06YU |

`push f` is, by definition, AxiomMath's `derivedModulePushforward B S hS f` (the derived
pushforward of the morphism of small étale ringed topoi; the latter is defined in a module
outside the import list with the same body), and AxiomMath identifies it with the total
right derived functor of the direct image of modules
(`smallEtaleDerivedModulePushforwardIso`).

All four functors are defined on the whole of `D(𝒪)`.  That `Rf_*` preserves `D_qc` (for
`f` quasi-compact and quasi-separated, Stacks 08FA), that `Lf^*` does (Stacks 08F4) and that
`⊗^L` does (Stacks 08F5) are AxiomMath theorems outside the import list; they are the tagged
inputs of `Spaces/AxiomMathInputs.lean`.

What is proved here (no input): the four functors send zero objects to zero objects
(`pull`/`push` as adjoints, `⊗^L` by exactness in each variable, which is part of
AxiomMath's `DerivedTensorProduct` structure).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS}

/-- **`Lf^*`** (GL26 `sec:prelim_stacks_functors`): the derived pullback
`D(Y) ⥤ D(X)` along `f : X ⟶ Y`, AxiomMath's `smallEtaleDerivedModulePullback` (Stacks
06YY for the morphism of small étale ringed topoi of 03G8). -/
abbrev pull (f : X ⟶ Y) : D B S hS Y ⥤ D B S hS X :=
  smallEtaleDerivedModulePullback B S hS f

/-- **`Rf_*`** (GL26 `sec:prelim_stacks_functors`): the derived direct image
`D(X) ⥤ D(Y)` along `f : X ⟶ Y`, AxiomMath's `smallEtaleDerivedModulePushforward`. -/
abbrev push (f : X ⟶ Y) : D B S hS X ⥤ D B S hS Y :=
  smallEtaleDerivedModulePushforward B S hS f

/-- **`Lf^* ⊣ Rf_*`** on `D(𝒪)` (Stacks 07A6), AxiomMath's `smallEtaleDerivedAdjunction`. -/
def pullPushAdj (f : X ⟶ Y) : pull f ⊣ push f :=
  smallEtaleDerivedAdjunction B S hS f

/-- **`⊗^L`** on `D(X)` (GL26 `sec:prelim_stacks_functors`, Stacks 06YU): AxiomMath's
`smallEtaleDerivedTensor`; `((tensor X).obj E).obj F = E ⊗^L F`. -/
abbrev tensor (X : AlgebraicSpaces B S hS) : D B S hS X ⥤ D B S hS X ⥤ D B S hS X :=
  smallEtaleDerivedTensor B S hS X

/-- `E ⊗^L F`. -/
abbrev tensorObj {X : AlgebraicSpaces B S hS} (E F : D B S hS X) : D B S hS X :=
  ((tensor X).obj E).obj F

instance (f : X ⟶ Y) : (pull f).IsLeftAdjoint := (pullPushAdj f).isLeftAdjoint

instance (f : X ⟶ Y) : (push f).IsRightAdjoint := (pullPushAdj f).isRightAdjoint

/-- `Lf^*` sends zero objects to zero objects (it is a left adjoint). -/
theorem isZero_pull_obj (f : X ⟶ Y) {E : D B S hS Y} (hE : IsZero E) :
    IsZero ((pull f).obj E) :=
  (pull f).map_isZero hE

/-- `Rf_*` sends zero objects to zero objects (it is a right adjoint). -/
theorem isZero_push_obj (f : X ⟶ Y) {E : D B S hS X} (hE : IsZero E) :
    IsZero ((push f).obj E) :=
  (push f).map_isZero hE

/-- `0 ⊗^L F` is zero: tensoring in the left variable is exact (a field of AxiomMath's
`DerivedTensorProduct`). -/
theorem isZero_tensorObj_left {X : AlgebraicSpaces B S hS} {E : D B S hS X} (hE : IsZero E)
    (F : D B S hS X) : IsZero (tensorObj E F) := by
  let T := smallEtaleDerivedTensorProduct B S hS X
  let _ := T.commShift_left F
  have := T.exact_left F
  have : (T.tensor.flip.obj F).PreservesZeroMorphisms :=
    Functor.IsTriangulated.instPreservesZeroMorphisms (F := T.tensor.flip.obj F)
  exact (T.tensor.flip.obj F).map_isZero hE

/-- `E ⊗^L 0` is zero: tensoring in the right variable is exact. -/
theorem isZero_tensorObj_right {X : AlgebraicSpaces B S hS} (E : D B S hS X) {F : D B S hS X}
    (hF : IsZero F) : IsZero (tensorObj E F) := by
  let T := smallEtaleDerivedTensorProduct B S hS X
  let _ := T.commShift_right E
  have := T.exact_right E
  have : (T.tensor.obj E).PreservesZeroMorphisms :=
    Functor.IsTriangulated.instPreservesZeroMorphisms (F := T.tensor.obj E)
  exact (T.tensor.obj E).map_isZero hF

end RelativeFM.Spaces
