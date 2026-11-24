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
only once the Stacks library's `D_qc,S` is available; see `results/WEAK_APPROX.md`).  Algebraic spaces and
their support categories are not introduced here, so `SatisfiesWA` records only
the underlying categorical condition.  Likewise, `SatisfiesStandardWA` takes a
chosen `t`-structure as a parameter; it does not construct the standard
`t`-structure on a derived category or formalize its preferred equivalence
class.  For the preferred-class reading, take the parameter to be a member of
that class.
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

/-- **Standard weak approximability relative to a chosen `t`-structure.**
There is weak approximation data whose underlying `t`-structure is `t`.

The chosen `t` may be the standard `t`-structure or a representative of the
preferred equivalence class.  This definition does not itself assert either
property, and it does not encode the geometric support-set quantification from
Definition 5.3. -/
def SatisfiesStandardWA (T : Type u) [Category.{v} T] [Preadditive T]
    [HasZeroObject T] [HasShift T ℤ] [∀ (n : ℤ), (shiftFunctor T n).Additive]
    [Pretriangulated T] (t : TStructure T) : Prop :=
  ∃ data : WeakApproximationData T, data.t = t

/-- **Remark 5.4, categorical implication.** Standard weak approximability
relative to any chosen `t`-structure implies weak approximability. -/
theorem satisfiesWA_of_satisfiesStandardWA {T : Type u} [Category.{v} T]
    [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
    [∀ (n : ℤ), (shiftFunctor T n).Additive] [Pretriangulated T]
    {t : TStructure T} (h : SatisfiesStandardWA T t) : SatisfiesWA T := by
  obtain ⟨data, _⟩ := h
  exact ⟨data⟩
