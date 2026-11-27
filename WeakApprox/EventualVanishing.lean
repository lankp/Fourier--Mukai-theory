/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Lemma43
import WeakApprox.WeakApproximable

/-!
# Closure properties of eventual Hom vanishing

`EventuallyHomZero` is stable under retracts and shifts.

The lemmas `WeakApproximationData.eventuallyHomZero_self` and
`eventuallyHomZero_self_of_mem_triangEnvelope` (the `IsGenerator` form of
Definition 2.1, `def:weak_approx`), used only by the forward direction of the
deleted `SetupMainMinimal.theorem_1_1`, were deleted in wave 8
(`results/OPEN_INPUTS.md` row 7.3).  The paper's form is in
`WeakApprox/PaperGeneratorM2.lean`.

Found by a member of the Ultramath run `smwuoh1xz` (direction D5, second run).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

section Closure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Eventual Hom-vanishing is a retract invariant: if `X` is a retract of `Y`
through `i : X ⟶ Y` and `r : Y ⟶ X` with `i ≫ r = 𝟙 X`, then `Y`'s
self-vanishing bounds `X`'s, with the same cutoff. -/
theorem EventuallyHomZero.of_retract {X Y : C} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r = 𝟙 X) (hY : EventuallyHomZero Y Y) : EventuallyHomZero X X := by
  obtain ⟨N, hN⟩ := hY
  refine ⟨N, fun n hn f => ?_⟩
  have hf : r ≫ f ≫ i⟦n⟧' = 0 := hN n hn _
  calc f = 𝟙 X ≫ f ≫ 𝟙 (X⟦n⟧) := by simp
    _ = (i ≫ r) ≫ f ≫ (i⟦n⟧' ≫ r⟦n⟧') := by rw [h, ← Functor.map_comp, h]; simp
    _ = i ≫ (r ≫ f ≫ i⟦n⟧') ≫ r⟦n⟧' := by simp only [Category.assoc]
    _ = 0 := by rw [hf, zero_comp, comp_zero]

/-- Eventual Hom-vanishing of an object is invariant under shifts. -/
theorem EventuallyHomZero.shift [CategoryTheory.IsTriangulated C] {X : C}
    (h : EventuallyHomZero X X) (k : ℤ) : EventuallyHomZero (X⟦k⟧) (X⟦k⟧) := by
  have hbase : (ObjectProperty.singleton X).triangEnvelope X :=
    ObjectProperty.le_triangEnvelope _ _ ((ObjectProperty.singleton_iff _ _).2 rfl)
  exact eventuallyHomZero_of_mem_triangEnvelope h
    ((ObjectProperty.singleton X).triangEnvelope.le_shift k _ hbase)
    ((ObjectProperty.singleton X).triangEnvelope.le_shift k _ hbase)

end Closure

end RelativeWeakApprox
