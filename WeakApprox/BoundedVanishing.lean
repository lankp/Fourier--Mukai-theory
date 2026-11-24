/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.EventualVanishing

/-!
# Bounded objects vanish against each other: the direction the grading gives

In `WeakApprox/EventualVanishing.lean`, `EventuallyHomZero X Y` says
`Hom(X, Y⟦n⟧) = 0` for all `n ≥ N`.  The classical way of producing such a
vanishing is boundedness: `X ∈ T^{≤n}` and `Y ∈ T^{≥m}` give
`Hom(X, Y[k]) = 0` for `k ≫ 0`, because classically `T^{≥m}[k] ⊆ T^{≥ m+k}`.

In this Mathlib the `t`-structure axioms move both indices *down* under `⟦a⟧`:
`TStructure.le_shift (n a n') (h : a + n' = n) : t.le n X → t.le n' (X⟦a⟧)`
gives `T^{≤n}⟦a⟧ ⊆ T^{≤ n-a}`, and `TStructure.ge_shift` gives
`T^{≥m}⟦a⟧ ⊆ T^{≥ m-a}`.  Consequently the boundedness statement that holds
here is the one for `k` *below* a bound: `X ∈ D^{≤n}` and `Y ∈ D^{≥m}` give
`Hom(X, Y⟦k⟧) = 0` for `k ≤ m - n - 1`, since then `Y⟦k⟧ ∈ D^{≥m-k} ⊆ D^{≥n+1}`
is orthogonal to `X`.

`hom_zero_of_shift_le` and `eventuallyHomZero_neg` below prove exactly that.
They are recorded because they exhibit the sign: the analogue of
`EventuallyHomZero` for this grading quantifies over `k ≤ N`, not `k ≥ N`.
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Bounded objects vanish below a shift.**  If `X ∈ D^{≤n}` and `Y ∈ D^{≥m}`,
then every morphism `X ⟶ Y⟦k⟧` vanishes for `k ≤ m - n - 1`. -/
theorem hom_zero_of_shift_le (t : TStructure C) {X Y : C} {n m : ℤ}
    (hX : t.le n X) (hY : t.ge m Y) {k : ℤ} (hk : k ≤ m - n - 1) :
    ∀ f : X ⟶ Y⟦k⟧, f = 0 := by
  have hYk : t.ge (m - k) (Y⟦k⟧) := t.ge_shift m k (m - k) (by ring) Y hY
  have hY' : t.ge (n + 1) (Y⟦k⟧) := t.ge_antitone (by omega) (Y⟦k⟧) hYk
  intro f
  exact t.zero_of_isLE_of_isGE f n (n + 1) (by omega)
    ((t.le_iff_isLE X n).1 hX) ((t.ge_iff_isGE (Y⟦k⟧) (n + 1)).1 hY')

/-- The `∃`-form of `hom_zero_of_shift_le`: an object bounded above and an object
bounded below have no maps between them shifted by a large negative amount. -/
theorem hom_zero_of_exists_bounded (t : TStructure C) {X Y : C}
    (hX : ∃ n : ℤ, t.le n X) (hY : ∃ m : ℤ, t.ge m Y) :
    ∃ N : ℤ, ∀ k : ℤ, k ≤ N → ∀ f : X ⟶ Y⟦k⟧, f = 0 := by
  obtain ⟨n, hn⟩ := hX
  obtain ⟨m, hm⟩ := hY
  exact ⟨m - n - 1, fun k hk f => hom_zero_of_shift_le t hn hm hk f⟩

end RelativeWeakApprox

#print axioms RelativeWeakApprox.hom_zero_of_shift_le
#print axioms RelativeWeakApprox.hom_zero_of_exists_bounded
