/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.Lemma433TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Tactic

/-!
# The grading convention of Mathlib's `TStructure` against the paper

The paper (§2.1.3, `main-3.tex` line 314) defines
`T^{≤ n} := T^{≤ 0}[-n]` and `T^{≥ n} := T^{≥ 0}[-n]`.

**Conclusion, checked in Lean.**  With the paper's `[n]` identified with
Mathlib's `⟦n⟧`, `t.le n` is the paper's `T^{≤ n}` and `t.ge n` is the paper's
`T^{≥ n}`: the equivalences `le_eq_shiftImage_neg : t.le n = (t.le 0)⟦-n⟧` and
`ge_eq_shiftImage_neg : t.ge n = (t.ge 0)⟦-n⟧` are literally the paper's
definition of its graded aisles and co-aisles.  The shift axioms move the
`le`-index down under `⟦a⟧` (`t.le n X → t.le (n - a) (X⟦a⟧)`), which is the
same convention, not a different one: `T^{≤ n} = T^{≤ 0}[-n]` says exactly that
shifting an object up lowers its grade.

So the library's `le`-indexed *and* shift-indexed statements are the paper's
under `paper[n] = ⟦n⟧`.  The opposite reading would require simultaneously
translating `paper[n] = ⟦-n⟧`, i.e. a different identification, not a second
reading of the axioms.

The file also records the comparisons that pin the sign: Mathlib's rotation
axiom is the paper's TR2, the truncation triangle is the paper's, and
`truncLE n = truncLT (n + 1)`.

Found by a member of the Ultramath run `smwuug9t7` (direction D1).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Operative aisle equivariance, negative-shift form. This follows directly
from `TStructure.le_shift` in one direction and from that axiom applied to the
inverse shift in the other. It is the grading law of §2.1.3 of the paper. -/
theorem le_shift_iff (t : TStructure C) (n a : ℤ) (X : C) :
    t.le n X ↔ t.le (n + a) (X⟦-a⟧) := by
  constructor
  · intro hX
    exact t.le_shift n (-a) (n + a) (by omega) X hX
  · intro hX
    have h := t.le_shift (n + a) a n (by omega) (X⟦-a⟧) hX
    exact (t.le n).prop_of_iso (shiftNegShift X a) h

/-- Operative aisle equivariance, positive-shift form. -/
theorem le_shift_pos (t : TStructure C) (n a : ℤ) {X : C}
    (hX : t.le n X) : t.le (n - a) (X⟦a⟧) :=
  t.le_shift n a (n - a) (by omega) X hX

/-- The positive-shift form is also an equivalence. -/
theorem le_shift_pos_iff (t : TStructure C) (n a : ℤ) (X : C) :
    t.le n X ↔ t.le (n - a) (X⟦a⟧) := by
  constructor
  · exact le_shift_pos t n a
  · intro hX
    have h := t.le_shift (n - a) (-a) n (by omega) (X⟦a⟧) hX
    exact (t.le n).prop_of_iso (shiftShiftNeg X a) h

/-- Operative co-aisle equivariance, negative-shift form, proved from
`TStructure.ge_shift`. -/
theorem ge_shift_iff (t : TStructure C) (n a : ℤ) (X : C) :
    t.ge n X ↔ t.ge (n + a) (X⟦-a⟧) := by
  constructor
  · intro hX
    exact t.ge_shift n (-a) (n + a) (by omega) X hX
  · intro hX
    have h := t.ge_shift (n + a) a n (by omega) (X⟦-a⟧) hX
    exact (t.ge n).prop_of_iso (shiftNegShift X a) h

/-- Operative co-aisle equivariance, positive-shift form. -/
theorem ge_shift_pos (t : TStructure C) (n a : ℤ) {X : C}
    (hX : t.ge n X) : t.ge (n - a) (X⟦a⟧) :=
  t.ge_shift n a (n - a) (by omega) X hX

/-- The positive-shift form for co-aisles is also an equivalence. -/
theorem ge_shift_pos_iff (t : TStructure C) (n a : ℤ) (X : C) :
    t.ge n X ↔ t.ge (n - a) (X⟦a⟧) := by
  constructor
  · exact ge_shift_pos t n a
  · intro hX
    have h := t.ge_shift (n - a) (-a) n (by omega) (X⟦a⟧) hX
    exact (t.ge n).prop_of_iso (shiftShiftNeg X a) h

/-- Co-aisles are antitone: this is the elementwise inclusion
`T^{≥ b} ⊆ T^{≥ a}` for `a ≤ b` in the paper's §2.1.3. -/
theorem ge_of_ge_of_le (t : TStructure C) {a b : ℤ} (hab : a ≤ b)
    {X : C} (hX : t.ge b X) : t.ge a X := by
  rw [TStructure.ge_iff_rightOrthogonal_le_pred] at hX ⊢
  intro Y f hY
  exact hX f (t.le_monotone (by omega) Y hY)

/-- `t.ge` is antitone, proved via
`TStructure.ge_iff_rightOrthogonal_le_pred` and `t.le_monotone`. -/
theorem ge_antitone_from_orthogonal (t : TStructure C) : Antitone t.ge := by
  intro a b hab X hX
  exact ge_of_ge_of_le t hab hX

/-- Membership in degree `n` is membership of the `n`-shift in degree zero.
Under `paper[n] = ⟦n⟧`, this is precisely the paper's definition
`T^{≤ n} = T^{≤ 0}[-n]` from §2.1.3: an object of `T^{≤ 0}[-n]` is sent back
to `T^{≤ 0}` by `[n]`. -/
theorem le_iff_paper_degree (t : TStructure C) (n : ℤ) (X : C) :
    t.le n X ↔ t.le 0 (X⟦n⟧) := by
  simpa using le_shift_pos_iff t n n X

/-- Co-aisle analogue of `le_iff_paper_degree`, matching
`T^{≥ n} = T^{≥ 0}[-n]` in the paper's §2.1.3. -/
theorem ge_iff_paper_degree (t : TStructure C) (n : ℤ) (X : C) :
    t.ge n X ↔ t.ge 0 (X⟦n⟧) := by
  simpa using ge_shift_pos_iff t n n X

/-- Orthogonality in the paper's grading: `t.ge (n + 1)` consists precisely
of objects receiving no nonzero map from an object whose `⟦n⟧`-shift lies in
`t.le 0`. This is the classical identity
`T^{≥ n+1} = (T^{≤ n})^\perp` after `T^{≤ n} = T^{≤ 0}[-n]`. It also shows why
reading `t.le n` as `T^{≤ -n}` would give the wrong orthogonal. -/
theorem ge_succ_iff_paper_orthogonal (t : TStructure C) (n : ℤ) (X : C) :
    t.ge (n + 1) X ↔ ∀ (Y : C) (f : Y ⟶ X), t.le 0 (Y⟦n⟧) → f = 0 := by
  rw [TStructure.ge_iff_rightOrthogonal_le_pred]
  simp only [add_sub_cancel_right, ObjectProperty.rightOrthogonal_iff]
  constructor
  · intro h Y f hY
    exact h f ((le_iff_paper_degree t n Y).2 hY)
  · intro h Y f hY
    exact h Y f ((le_iff_paper_degree t n Y).1 hY)

/-- The paper's graded aisle, literally as its direct-image notation:
`t.le n = (t.le 0)⟦-n⟧`. Here `shiftImage P s` is the isomorphism-closed
image of `P` under `⟦s⟧`, exactly the library's rendering of paper `P[s]`. -/
theorem le_eq_shiftImage_neg (t : TStructure C) (n : ℤ) :
    t.le n = shiftImage (t.le 0) (-n) := by
  ext X
  constructor
  · intro hX
    exact ⟨X⟦n⟧, (le_iff_paper_degree t n X).1 hX,
      ⟨(shiftShiftNeg X n).symm⟩⟩
  · rintro ⟨Y, hY, ⟨e⟩⟩
    have h := le_shift_pos t 0 (-n) hY
    rw [zero_sub, neg_neg] at h
    exact (t.le n).prop_of_iso e.symm h

/-- The paper's graded co-aisle, literally as its direct-image notation:
`t.ge n = (t.ge 0)⟦-n⟧`. -/
theorem ge_eq_shiftImage_neg (t : TStructure C) (n : ℤ) :
    t.ge n = shiftImage (t.ge 0) (-n) := by
  ext X
  constructor
  · intro hX
    exact ⟨X⟦n⟧, (ge_iff_paper_degree t n X).1 hX,
      ⟨(shiftShiftNeg X n).symm⟩⟩
  · rintro ⟨Y, hY, ⟨e⟩⟩
    have h := ge_shift_pos t 0 (-n) hY
    rw [zero_sub, neg_neg] at h
    exact (t.ge n).prop_of_iso e.symm h

/-- Mathlib's rotation axiom is the paper's TR2 rotation (§2.1.1): a
distinguished `X ⟶ Y ⟶ Z ⟶ X[1]` rotates to
`Y ⟶ Z ⟶ X[1] ⟶ Y[1]`, with the last map negated. -/
theorem distTriang_rotate_iff_paper (T : Triangle C) :
    T ∈ distTriang C ↔ T.rotate ∈ distTriang C :=
  rotate_distinguished_triangle T

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The third map in Mathlib's rotated triangle is `-f⟦1⟧`, exactly the
paper's `-u[1]` in §2.1.1. -/
theorem rotate_mor₃_eq_paper (T : Triangle C) :
    T.rotate.mor₃ = -T.mor₁⟦(1 : ℤ)⟧' := rfl

/-- The axiom `TStructure.exists_triangle_zero_one` **is** the paper's
truncation triangle in §2.1.3:
`τ^{≤0} A ⟶ A ⟶ τ^{≥1} A ⟶ (τ^{≤0} A)[1]`, with the first object in the
aisle and the third object in co-aisle degree one. -/
theorem exists_paper_truncation_triangle (t : TStructure C) (A : C) :
    ∃ (X Y : C) (_ : t.le 0 X) (_ : t.ge 1 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C :=
  t.exists_triangle_zero_one A

/-- Mathlib's non-strict truncation is indexed in the same classical way:
`truncLE n` is `truncLT (n + 1)`, as specified in `TruncLEGT.lean`. -/
theorem truncLE_eq_truncLT_add_one (t : TStructure C) (n : ℤ) :
    t.truncLE n = t.truncLT (n + 1) := rfl

/-- The functorial degree-zero truncation triangle has the paper's membership
convention: its first object is `≤ 0`, its third object is `≥ 1`, and the
whole triangle is distinguished. Together with `rotate_mor₃_eq_paper`, this
identifies the final `⟦1⟧` with the paper's `[1]`. -/
theorem truncLEGT_zero_is_paper (t : TStructure C) (A : C) :
    t.le 0 ((t.truncLE 0).obj A) ∧
      t.ge 1 ((t.truncGT 0).obj A) ∧
      (t.triangleLEGT 0).obj A ∈ distTriang C := by
  exact ⟨t.le_of_isLE _ _, (t.isGE_truncGT_obj A 0 1 (by omega)).ge,
    t.triangleLEGT_distinguished 0 A⟩


end RelativeWeakApprox

#print axioms RelativeWeakApprox.le_shift_iff
#print axioms RelativeWeakApprox.le_eq_shiftImage_neg
#print axioms RelativeWeakApprox.ge_eq_shiftImage_neg
#print axioms RelativeWeakApprox.exists_paper_truncation_triangle
#print axioms RelativeWeakApprox.truncLE_eq_truncLT_add_one
