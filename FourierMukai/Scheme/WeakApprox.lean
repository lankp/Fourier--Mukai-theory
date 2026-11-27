/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.MainMinimal
import WeakApprox.CompactVanishing
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The scheme route through Lank--Pauwels: the measured interface

This file separates the *last categorical implication* of the scheme rehaul from
the geometric construction of its input package.  There are no `sorry`s and no
new axioms: every missing geometric fact is an explicit structure field with a
docstring saying where it comes from.

## What is left

`SchemeOpenClosed` (Mathlib's open immersion with its closed complement) and
`Stacks09SR`.  The interface `SchemeOpenClosedDerived` and its consumers
(`weakApprox_dqcX_of_gluing`, `weakApprox_dqcX_of_eventual`,
`weakApprox_dqcX_of_compactHomZeroAtTop`, `weakApprox_open`, `weakApprox_closed`,
`jShriek_compact`, `iLower_supported`), and the `SetupMainMinimal` lemmas
`satisfiesWA_of_compactHomZeroAtTop`, `toSetup44OfCompactHomZeroAtTop`,
`toSetup44ReducedOfCompactHomZeroAtTop`, `GU_compact`, with
`compactHomZeroAtTop_of_satisfiesWA`, were deleted in wave 7
(`results/OPEN_INPUTS.md` row 7.3): they are built on `SetupMainMinimal` and
`SatisfiesWA`, the `IsGenerator` form, which is false for `D(ℤ)` (F2).  The paper
form over algebraic spaces is `Spaces/`.

## Primary source

Neeman, *Bounded `t`-structures on the category of perfect complexes*, Acta
Math. 233 (2024), 239--284, Theorem 3.2(i)--(iv), for qcqs schemes: compacts are
supported perfect complexes, there is a single compact generator, the standard
`t`-structure is preferred, and `D_qc,Z(X)` is weakly approximable.
https://doi.org/10.4310/ACTA.2024.v233.n2.a2 .  Noetherianity is not needed.

Found by a member of the Ultramath run `smwuyellz` (direction D5).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open AlgebraicGeometry

universe v u uZ uD uU

#check AlgebraicGeometry.Scheme
#check AlgebraicGeometry.IsNoetherian
#check AlgebraicGeometry.IsOpenImmersion
#check AlgebraicGeometry.Scheme.Hom.opensRange
#check RelativeWeakApprox.SetupMainMinimal.theorem_1_1
#check RelativeWeakApprox.exists_setup_4_4_3_of_compactHomZeroAtTop
#check RelativeWeakApprox.recollement_jShriek_compact
#check RelativeWeakApprox.satisfiesWA_of_setup
#check RelativeWeakApprox.CompactHomZeroAtTop
#check RelativeWeakApprox.compactHomZeroAtTop_of_isClassicalGeneratorOnCompacts
#check RelativeWeakApprox.WeakApproximationData.eventuallyHomZero_self
#check RelativeWeakApprox.WeakApproximationData.monoBound
#check RelativeWeakApprox.Setup44Reduced.toSetup44
#check RelativeWeakApprox.Recollement.kernel

/-- An open immersion of schemes and its closed set-theoretic complement.
This is the actual Mathlib scheme layer; derived categories are added
separately because Mathlib 4.33.1 does not supply their `D_qc` instantiation. -/
structure SchemeOpenClosed where
  /-- Ambient scheme. -/
  X : Scheme.{u}
  /-- Open subscheme, represented separately. -/
  U : Scheme.{u}
  /-- The open immersion `j : U ⟶ X`. -/
  j : U ⟶ X
  /-- `j` is an open immersion. -/
  [j_open : IsOpenImmersion j]
  /-- The complement of the image of `j`. -/
  Z : Set X
  /-- The displayed complement is closed. -/
  Z_closed : IsClosed Z
  /-- Identification with the complement of `j`'s open image. -/
  Z_eq : Z = ((j.opensRange : X.Opens) : Set X)ᶜ

attribute [instance] SchemeOpenClosed.j_open

/-- Stacks Tag 09SR, in the exact form required by `theorem_1_1`.
For a scheme instantiation the geometric input identifying compacts with
perfect complexes is Neeman 2024, Theorem 3.2(i); the finite thick-envelope
statement itself remains the cited Stacks input. -/
def Stacks09SR (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] : Prop :=
  ∀ (G : C), IsGenerator G → IsCompactAb G → IsClassicalGeneratorOnCompacts G

end RelativeWeakApprox

