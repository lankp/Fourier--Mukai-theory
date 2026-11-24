/-
Copyright (c) 2026 Formalization of Lank--Pauwels--Peng.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Basic
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Aisles are closed under extensions (Lemma 3.3)

Lemma 3.3 of

  P. Lank, B. Pauwels, F. Peng, *Gluing weak approximability along recollements*:
in a distinguished triangle `E ⟶ F ⟶ D ⟶ E⟦1⟧` with `F ∈ T^{≤0}` and
`D ∈ T^{≤-m}` for some `m ≥ 1`, one has `E ∈ T^{≤0}`.

The proof, found by a member of the Ultramath run `smwufzlp4`, is one application
of `TStructure.isLE₂` to the inversely rotated triangle `D⟦-1⟧ ⟶ E ⟶ F`.
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe w v u

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T]
  [HasShift T ℤ] [∀ (n : ℤ), (shiftFunctor T n).Additive] [Pretriangulated T]

/-- **Lemma 3.3**: an aisle is closed under extensions.  In a distinguished
triangle `E ⟶ F ⟶ D ⟶ E⟦1⟧`, if `F` is in degree `≤ 0` and `D` is in degree
`≤ -m` with `1 ≤ m`, then `E` is in degree `≤ 0`. -/
theorem mem_le_zero_of_distinguished_triangle
    (t : TStructure T) {E F D : T} (f : E ⟶ F) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang T) {m : ℤ} (hm : 1 ≤ m)
    (hF : t.le 0 F) (hD : t.le (-m) D) : t.le 0 E := by
  have hD₁ : t.le (-1) D := t.le_monotone (by omega) D hD
  have hD₀ : t.le 0 (D⟦(-1 : ℤ)⟧) :=
    t.le_shift (-1) (-1) 0 (by simp) D hD₁
  exact (t.isLE₂ (Triangle.mk f g h).invRotate
    (inv_rot_of_distTriang _ hT) 0 ⟨hD₀⟩ ⟨hF⟩).le

end RelativeWeakApprox
