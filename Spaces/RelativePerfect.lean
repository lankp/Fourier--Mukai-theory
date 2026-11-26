/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Functors

/-!
# `f`-perfect and `f`-quasi-perfect objects over algebraic spaces

GL26, **Definition 4.1** (`def:relative_perf_stacks`) and **Definition 5.1**
(`def:quasi_perf`), over algebraic spaces, with GL26 §2.2's `D_qc`, `D^b_qc`, `Perf`, `Lf^*`,
`Rf_*`, `⊗^L` (`Spaces/Categories.lean`, `Spaces/Functors.lean`).

For a morphism `f : Y ⟶ X` of algebraic spaces and `E ∈ D_qc(Y)`:

* `E` is **`f`-perfect** if `E ⊗^L Lf^*A ∈ D^b_qc(Y)` for every `A ∈ D^b_qc(X)`;
* `E` is **`f`-quasi-perfect** if `Rf_*(E ⊗^L P) ∈ Perf(X)` for every `P ∈ Perf(Y)`.

These are GL26's own notions.  AxiomMath's `IsPerfectRelativeTo` (Stacks 0DKN) is a
different definition (flat, locally of finite presentation, pseudo-coherent with finite Tor
dimension over `X`); GL26 compares them in `rem:comparison_stacks_project`, which AxiomMath
does not prove (`AXIOMMATH_MAP.md`, A.6).  Nothing of 0DKN is used here.

## Differences from GL26

GL26 states both definitions for a morphism of quasi-compact quasi-separated algebraic
spaces.  The Lean `Prop`s impose the same condition on every morphism `f`; for qcqs `f`
they are GL26's definitions verbatim.  No hypothesis is added or dropped otherwise.
Nothing here needs a tagged input: the definitions use only `D(𝒪)`-level functors.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS}

/-- **Definition 4.1** (`def:relative_perf_stacks`): `E ∈ D_qc(Y)` is *`f`-perfect*
(perfect relative to `f : Y ⟶ X`) if `E ⊗^L Lf^*A ∈ D^b_qc(Y)` for every `A ∈ D^b_qc(X)`.
GL26 states it for `f` a morphism of qcqs algebraic spaces; the condition is the same. -/
def IsRelativelyPerfect (f : Y ⟶ X) (E : D B S hS Y) : Prop :=
  Dqc Y E ∧ ∀ A : D B S hS X, Dbqc X A → Dbqc Y (tensorObj E ((pull f).obj A))

/-- **Definition 5.1** (`def:quasi_perf`): `E ∈ D_qc(Y)` is *`f`-quasi-perfect* if
`Rf_*(E ⊗^L P) ∈ Perf(X)` for every `P ∈ Perf(Y)`.  GL26 states it for `f` a morphism of
qcqs algebraic spaces; the condition is the same. -/
def IsQuasiPerfect (f : Y ⟶ X) (E : D B S hS Y) : Prop :=
  Dqc Y E ∧ ∀ P : D B S hS Y, Perf Y P → Perf X ((push f).obj (tensorObj E P))

/-- The `f`-perfect objects, as a property of objects of `D(Y)`. -/
abbrev relativelyPerfect (f : Y ⟶ X) : ObjectProperty (D B S hS Y) :=
  fun E => IsRelativelyPerfect f E

/-- The `f`-quasi-perfect objects, as a property of objects of `D(Y)`. -/
abbrev quasiPerfect (f : Y ⟶ X) : ObjectProperty (D B S hS Y) :=
  fun E => IsQuasiPerfect f E

end RelativeFM.Spaces
