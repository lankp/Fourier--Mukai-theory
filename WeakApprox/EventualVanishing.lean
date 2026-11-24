/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Lemma43
import WeakApprox.WeakApproximable

/-!
# Eventual self-Hom vanishing of a weak approximation generator

Weak approximation data (Definition 2.1) already force the generator's
positive self-shifts to vanish: if `G ∈ T^{≤A}` then `G⟦n⟧ ∈ T^{≤A-n}`, which
lies in `T^{≤-A}` as soon as `n ≥ 2A`, so `hom_vanishing` applies.  This is the
input used by the forward direction of Theorem 1.1 (`WeakApprox/Main.lean`),
together with transport along the finite thick envelope.

Found by a member of the Ultramath run `smwuoh1xz` (direction D5, second run).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u
section WeakApproximationData

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The self-Hom vanishing implicit in weak approximation data.

If `G ∈ t.le A`, then `G⟦n⟧ ∈ t.le (A - n)`.  For `n ≥ 2*A` this is
contained in `t.le (-A)`, so Definition 2.1's `hom_vanishing` field applies.
This is the formal input to Lemma 4.3's finite-thick-envelope argument. -/
theorem WeakApproximationData.eventuallyHomZero_self (W : WeakApproximationData C) :
    EventuallyHomZero W.G W.G := by
  refine ⟨2 * W.A, fun n hn f => W.hom_vanishing ?_ f⟩
  apply W.t.le_monotone (show W.A - n ≤ -W.A by omega)
  exact W.t.le_shift W.A n (W.A - n) (by omega) W.G W.G_mem_le

/-- Transport of self-Hom vanishing from a weak-approximation generator to any
object in its finite thick envelope.  This is the precise envelope input used
in the forward direction of Theorem 1.1. -/
theorem eventuallyHomZero_self_of_mem_triangEnvelope
    (W : WeakApproximationData C) {G' : C}
    (hG' : (ObjectProperty.singleton W.G).triangEnvelope G') :
    EventuallyHomZero G' G' :=
  eventuallyHomZero_of_mem_triangEnvelope W.eventuallyHomZero_self hG' hG'

/-- Classical generation on compacts for the weak-approximation generator is a
sufficient input for the reverse envelope membership.  Together with
`eventuallyHomZero_self_of_mem_triangEnvelope`, this isolates the only extra
input needed to derive self-Hom vanishing for another compact object without
assuming that vanishing in advance. -/
theorem eventuallyHomZero_self_of_isClassicalGeneratorOnCompacts
    (W : WeakApproximationData C) {G' : C} (hG'compact : IsCoproductCompact G')
    (hgen : IsClassicalGeneratorOnCompacts W.G) : EventuallyHomZero G' G' :=
  eventuallyHomZero_self_of_mem_triangEnvelope W (hgen G' hG'compact)

end WeakApproximationData

end RelativeWeakApprox
