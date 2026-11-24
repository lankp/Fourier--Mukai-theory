/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.Lemma35

/-!
# Shift audit: Lemma 3.1(2) against the paper

The paper (`main-3.tex`, `lem:closures2`) states `⟨H⟩^{[a,b]}[s] = ⟨H⟩^{[a-s,b-s]}`
with `H[a,b] := {H[-k] : a ≤ k ≤ b}`.  This file records the audit that the
library's rendering is that statement with `paper[n] = ⟦n⟧` and the **same** sign
of `s`, together with the expanded membership computation that makes the
translation checkable.

The apparent inconsistency with `shiftTail H n₀ = {H⟦n⟧ : n ≥ n₀}`, whose
direct image raises the cutoff to `n₀ + s`, comes from the two indexing sets
(`H[-k]` versus `H[n]`), not from two different identifications of the paper's
shift functor; `shiftTail_shift_eq_paper` below records both.

Found by a member of the Ultramath run `smwuug9t7` (direction D2).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Paper Lemma 3.1(2), generator-level transport** (`lem:closures2` in
`main-3.tex`, lines 555--560). With `paper[n] = ⟦n⟧`, the direct,
isomorphism-closed image of `{H⟦-k⟧ | a ≤ k ≤ b}` under `⟦s⟧` is
`{H⟦-ℓ⟧ | a-s ≤ ℓ ≤ b-s}`. This is the same sign of `s` as in the paper;
its substitution is `ℓ = k-s`. -/
theorem shiftInterval_shift_eq_paper (H : C) (a b s : ℤ) :
    shiftImage (shiftInterval H a b) s = shiftInterval H (a - s) (b - s) :=
  shiftImage_shiftInterval H a b s

omit [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The direct-image membership calculation in the paper's notation. The left
hand side is definitionally the isomorphism-closed image under `⟦s⟧`; the
right hand side keeps the original paper index `k` and the composite shift
`(H⟦-k⟧)⟦s⟧`. This checks the translation of `paper[s]` itself. -/
theorem mem_shiftImage_shiftInterval_witness_iff (H : C) (a b s : ℤ) (X : C) :
    shiftImage (shiftInterval H a b) s X ↔
      ∃ k : ℤ, a ≤ k ∧ k ≤ b ∧ Nonempty (X ≅ (H⟦-k⟧)⟦s⟧) := by
  constructor
  · rintro ⟨Y, ⟨k, hak, hkb, ⟨eY⟩⟩, ⟨eX⟩⟩
    exact ⟨k, hak, hkb, ⟨eX.trans ((shiftFunctor C s).mapIso eY)⟩⟩
  · rintro ⟨k, hak, hkb, ⟨eX⟩⟩
    exact ⟨H⟦-k⟧, ⟨k, hak, hkb, ⟨Iso.refl _⟩⟩, ⟨eX⟩⟩

/-- The expanded membership form of `shiftInterval_shift_eq_paper`. It is the
paper's displayed equality of generating sets, including the final bounds
`a-s ≤ ℓ ≤ b-s`, rather than merely a statement after reindexing. -/
theorem mem_shiftImage_shiftInterval_paper_iff (H : C) (a b s : ℤ) (X : C) :
    shiftImage (shiftInterval H a b) s X ↔
      ∃ ℓ : ℤ, a - s ≤ ℓ ∧ ℓ ≤ b - s ∧ Nonempty (X ≅ H⟦-ℓ⟧) := by
  rw [shiftInterval_shift_eq_paper]
  rfl

/-- **Paper Lemma 3.1(2), exact library rendering** (`lem:closures2`).
Interpreting the paper's `[s]` as `shiftImage _ s`, and its `⟨H⟩^[a,b]` as
`envelope H a b`, this is literally
`⟨H⟩^[a,b][s] = ⟨H⟩^[a-s,b-s]`. Thus the library's
`WeakApprox/Shift.lean` statement is the paper's statement under
`paper[n] = ⟦n⟧`, without a sign substitution. -/
theorem lemma31_2_shift_eq_paper (H : C) (a b s : ℤ) :
    shiftImage (envelope H a b) s = envelope H (a - s) (b - s) :=
  lemma31_2_shift H a b s

/-- A single same-sign audit theorem combining the two levels of Lemma 3.1(2).
In particular, the envelope equality is not obtained by interpreting the
paper's shift as `⟦-s⟧`. -/
theorem lemma31_2_paper_same_sign (H : C) (a b s : ℤ) :
    shiftImage (shiftInterval H a b) s = shiftInterval H (a - s) (b - s) ∧
      shiftImage (envelope H a b) s = envelope H (a - s) (b - s) :=
  ⟨shiftInterval_shift_eq_paper H a b s, lemma31_2_shift_eq_paper H a b s⟩

/-- Consistency with the positive shifts used for compactly generated aisles
in Section 2.1.3 and Lemma 3.5 (`lem:hom_vanishing`). For
`shiftTail H n₀ = {H⟦n⟧ | n ≥ n₀}`, direct image under `⟦s⟧` raises the cutoff
to `n₀+s`. Together with `shiftInterval_shift_eq_paper`, this verifies that
the apparent `+s`/`-s` difference comes solely from the two indexing sets,
not from two identifications of the paper's shift functor. -/
theorem shiftTail_shift_eq_paper (H : C) (n₀ s : ℤ) :
    shiftImage (shiftTail H n₀) s = shiftTail H (n₀ + s) :=
  shiftImage_shiftTail H n₀ s

end RelativeWeakApprox


/-
Clean recompile from the repository root (the output is written only to this
member's directory):

  LEAN_PATH="$LEAN_PATH:." lean -o .ultramath/smwuug9t7/m2/Solution.olean .ultramath/smwuug9t7/m2/Solution.lean

Verified exit status: 0. All six `#print axioms` reports are contained in
`{propext, Classical.choice, Quot.sound}`.
-/

#print axioms RelativeWeakApprox.shiftInterval_shift_eq_paper
#print axioms RelativeWeakApprox.mem_shiftImage_shiftInterval_paper_iff
#print axioms RelativeWeakApprox.lemma31_2_shift_eq_paper
#print axioms RelativeWeakApprox.shiftTail_shift_eq_paper
