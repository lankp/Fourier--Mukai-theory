/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Basic

/-!
# Weak and standard weak approximability

This file gives the categorical rendering of Definition 5.3 and Remark 5.4
requested for this layer of *Gluing weak approximability along recollements*.
Weak approximability is exactly the existence of the weak approximation data of
Definition 2.1.  Standard weak approximability additionally prescribes the
`t`-structure used by those data.

## Rendering

The geometric definition of W.A. for an algebraic space also quantifies over
closed support subsets with quasi-compact complement (and is therefore stated
only once the Stacks library's `D_qc,S` is available; see `results/archive/WEAK_APPROX.md`).  Algebraic spaces and
their support categories are not introduced here, so `SatisfiesWA` records only
the underlying categorical condition.

`SatisfiesWA` uses the `IsGenerator` (morphism-separation) form of
`WeakApproximationData`, which is false for `D(ℤ)` (`results/OPEN_INPUTS.md` F2,
`VacuityF2.not_satisfiesWA_int`).  It is kept only for the pinned
`SetupMainMinimal.theorem_1_1` and that refutation; the paper form is
`PaperM2.SatisfiesPaperWA`.  `SatisfiesStandardWA` and its consumers were deleted
in wave 7 (row 7.3).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

/-- **Definition 5.3, categorical form.** A triangulated category is weakly
approximable when it admits weak approximation data in the sense of Definition
2.1.

This is a re-rendering for a bare triangulated category: the additional
support-set quantification in the geometric definition of W.A. is not encoded.
Only `Pretriangulated` is needed, just as for `WeakApproximationData`. -/
def SatisfiesWA (T : Type u) [Category.{v} T] [Preadditive T]
    [HasZeroObject T] [HasShift T ℤ] [∀ (n : ℤ), (shiftFunctor T n).Additive]
    [Pretriangulated T] : Prop :=
  Nonempty (WeakApproximationData T)
