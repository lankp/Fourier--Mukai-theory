/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Recollement
import WeakApprox.Closure
import WeakApprox.Lemma35
import WeakApprox.Lemma42
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
import Mathlib.Tactic

/-!
# Aisle closure lemmas (formerly Setup 4.4, `IsGenerator` form)

This file used to package LP26 Setup 4.4 (`setup:standing`) as the structure
`Setup44`, with `IsGenerator` (morphism separation) for "compact generator".
That form is vacuous at `D(ℤ)` (`RelativeFM.VacuityF2`), and `Setup44` with its
lemmas was deleted in wave 8 together with the pinned endpoint
`SetupMainMinimal.theorem_1_1` that used it (`results/OPEN_INPUTS.md` row 7.3).
The paper's Setup 4.4 is `PaperM2.PaperSetup44M2` (`WeakApprox/PaperSetup44M2.lean`).

What remains are two general facts about a fixed degree `D^{≤n}` of a t-structure,
used elsewhere in the tree: closure under existing colimits of any shape, and closure
under extensions.
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe vD uD vU uU

section AisleClosure

variable {C : Type uD} [Category.{vD} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Every existent colimit of objects in an aisle again lies in that aisle.
This is the orthogonality argument behind coproduct closure of aisles. -/
theorem TStructure.le_isClosedUnderColimitsOfShape (t : TStructure C) (n : ℤ)
    (J : Type uU) [Category.{vU} J] : (t.le n).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    apply (t.le_iff_isLE X n).2
    rw [t.isLE_iff_orthogonal n (n + 1) rfl]
    intro Y f hY
    apply p.isColimit.hom_ext
    intro j
    simpa using (t.isLE_iff_orthogonal n (n + 1) rfl _).1
      ⟨p.prop_diag_obj j⟩ Y (p.ι.app j ≫ f) hY

/-- A fixed degree of a t-structure is closed under extensions. -/
theorem TStructure.le_isTriangulatedClosed₂ (t : TStructure C) (n : ℤ) :
    (t.le n).IsTriangulatedClosed₂ :=
  .mk' fun T hT h₁ h₃ => (t.isLE₂ T hT n ⟨h₁⟩ ⟨h₃⟩).le

end AisleClosure

end RelativeWeakApprox
