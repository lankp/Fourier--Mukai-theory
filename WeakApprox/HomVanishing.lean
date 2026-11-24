/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Basic
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Lemma 3.1(4): vanishing of `Hom` on the coproduct/extension envelope

Lemma 3.1(4) of

  P. Lank, B. Pauwels, *Gluing weak approximability along recollements*:
if `Hom(H⟦-k⟧, Y) = 0` for all `a ≤ k ≤ b`, then `Hom(X, Y) = 0` for every
`X ∈ ⟨H⟩^[a,b]`; and, when `H` is compact, the class `{Y : Hom(H, Y) = 0}` is
closed under small coproducts, extensions and direct summands.  The second part
is proved here in the stronger form where only the coproduct closure needs
compactness.

Found by a member of the Ultramath run `smwufzlp4` (direction D4).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Objects `X` for which every morphism `X ⟶ Y` is zero. -/
def homZeroLeft (Y : C) : ObjectProperty C := fun X => ∀ f : X ⟶ Y, f = 0

/-- Objects `Y` for which every morphism `H ⟶ Y` is zero. -/
def homZeroRight (H : C) : ObjectProperty C := fun Y => ∀ f : H ⟶ Y, f = 0

instance homZeroLeft_isClosedUnderIsomorphisms (Y : C) :
    (homZeroLeft Y).IsClosedUnderIsomorphisms where
  of_iso e h := by
    intro f
    rw [← cancel_epi e.hom, comp_zero]
    exact h _

/-- In fact, Hom into a fixed object turns every colimit into a limit; the
instance is stated only for the discrete shapes needed here. -/
instance homZeroLeft_isClosedUnderSmallCoproducts (Y : C) (J : Type v) :
    (homZeroLeft Y).IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := by
    rintro X ⟨p⟩ f
    apply p.isColimit.hom_ext
    intro j
    rw [comp_zero]
    exact p.prop_diag_obj j _

instance homZeroLeft_isTriangulatedClosed₂ (Y : C) :
    (homZeroLeft Y).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ => by
    intro f
    obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₂ T hT f (h₁ _)
    rw [h₃ g, comp_zero])

instance homZeroLeft_isStableUnderRetracts (Y : C) :
    (homZeroLeft Y).IsStableUnderRetracts where
  of_retract r h := by
    intro f
    rw [← cancel_epi r.r, comp_zero]
    exact h _

/-- **Lemma 3.1(4), first part.** If `H⟦-k⟧` has no nonzero maps to `Y`
for `a ≤ k ≤ b`, then no object of `⟨H⟩^[a,b]` has a nonzero map to `Y`.
No compactness hypothesis is needed. -/
theorem hom_zero_of_mem_envelope {H X Y : C} {a b : ℤ}
    (h : ∀ k : ℤ, a ≤ k → k ≤ b → ∀ f : H⟦-k⟧ ⟶ Y, f = 0)
    (hX : envelope H a b X) : ∀ f : X ⟶ Y, f = 0 := by
  have hle : envelope H a b ≤ homZeroLeft Y := by
    unfold envelope
    rw [ObjectProperty.retractClosure_le_iff]
    apply Coprod.le
    intro Z hZ
    obtain ⟨k, hak, hkb, ⟨e⟩⟩ := hZ
    intro f
    rw [← cancel_epi e.inv, comp_zero]
    exact h k hak hkb _
  exact hle X hX

instance homZeroRight_isClosedUnderIsomorphisms (H : C) :
    (homZeroRight H).IsClosedUnderIsomorphisms where
  of_iso e h := by
    intro f
    rw [← cancel_mono e.inv, zero_comp]
    exact h _

/-- Auxiliary general form: covariant Hom vanishing is closed under every
colimit shape preserved by the Hom functor. -/
instance homZeroRight_isClosedUnderColimitsOfShape (H : C)
    (J : Type*) [Category* J]
    [PreservesColimitsOfShape J (coyoneda.obj (.op H))] :
    (homZeroRight H).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro Y ⟨p⟩ f
    obtain ⟨j, g, hg⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (coyoneda.obj (.op H)) p.isColimit) f
    rw [← hg]
    change g ≫ p.ι.app j = 0
    rw [p.prop_diag_obj j g, zero_comp]

instance homZeroRight_isTriangulatedClosed₂ (H : C) :
    (homZeroRight H).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ => by
    intro f
    obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₂ T hT f (h₃ _)
    rw [h₁ g, zero_comp])

instance homZeroRight_isStableUnderRetracts (H : C) :
    (homZeroRight H).IsStableUnderRetracts where
  of_retract r h := by
    intro f
    rw [← cancel_mono r.i, zero_comp]
    exact h _

/-- **Lemma 3.1(4), compactness part: coproducts.** For a coproduct-compact
object `H`, `{Y | Hom(H,Y) = 0}` is closed under small coproducts. -/
theorem homZeroRight_closedUnderSmallCoproducts (H : C) [IsCoproductCompact H]
    (J : Type v) : (homZeroRight H).IsClosedUnderColimitsOfShape (Discrete J) :=
  inferInstance

/-- **Lemma 3.1(4), compactness part: extensions.** -/
theorem homZeroRight_closedUnderExtensions (H : C) :
    (homZeroRight H).IsTriangulatedClosed₂ := inferInstance

/-- **Lemma 3.1(4), compactness part: direct summands.** -/
theorem homZeroRight_closedUnderDirectSummands (H : C) :
    (homZeroRight H).IsStableUnderRetracts := inferInstance

/-- **Lemma 3.1(4), compactness part, combined.** If `H` is compact (in the
coproduct-preserving sense above), then `{Y | Hom(H,Y) = 0}` is closed under
small coproducts, extensions and direct summands. -/
theorem homZeroRight_closed (H : C) [IsCoproductCompact H] :
    (∀ J : Type v, (homZeroRight H).IsClosedUnderColimitsOfShape (Discrete J)) ∧
      (homZeroRight H).IsTriangulatedClosed₂ ∧
      (homZeroRight H).IsStableUnderRetracts :=
  ⟨homZeroRight_closedUnderSmallCoproducts H,
    homZeroRight_closedUnderExtensions H,
    homZeroRight_closedUnderDirectSummands H⟩

end RelativeWeakApprox
