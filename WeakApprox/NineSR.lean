/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.Lemma43
import FourierMukai.Prelim.Lemma25

/-!
# The compact-generator bridge (Stacks 09SR)

This file uses the project's existing `IsCoproductCompact` rendering of
compactness.  It separates the formal consequences of separation from the
Ravenel--Neeman/Stacks finite-generation theorem.  The latter is represented by
its final finite-stage retract conclusion; no separation-only proof of that
conclusion is claimed.
-/

@[expose] public section

namespace RelativeWeakApprox

open _root_.CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- If shifts of `G` separate morphisms, then an object receiving only zero
maps from all shifts of `G` is zero.  This is the soft zero-detection
consequence of `IsGenerator`; it says nothing about membership of compact
objects in the finite thick envelope. -/
theorem isZero_of_isGenerator_of_hom_eq_zero {G Y : C} (hG : IsGenerator G)
    (h : ∀ n : ℤ, ∀ f : G⟦n⟧ ⟶ Y, f = 0) : IsZero Y := by
  rw [IsZero.iff_id_eq_zero]
  apply hG (𝟙 Y) 0
  intro Z hZ a
  obtain ⟨A, n, e, hA⟩ := hZ
  obtain rfl : G = A := (ObjectProperty.singleton_iff _ _).1 hA
  rw [Category.comp_id, comp_zero, ← cancel_epi e.inv, comp_zero]
  simpa only [Category.assoc] using h n (e.inv ≫ a)

/-- The finite-stage retract output isolated from the proof of Stacks 09SR
(Proposition 13.37.6).  There, 09SN produces a homotopy-colimit approximation,
compactness (via 094A) makes `X` a retract of a finite stage, and 09SP places
that stage in `⟨G⟩`.  This predicate packages exactly that resulting data,
including the finite envelope stage.  The unresolved input is the homotopy
colimit/compactness argument, not the closure arguments below. -/
def IsCompactRetractGenerated (G : C) : Prop :=
  ∀ X : C, IsCoproductCompact X →
    ∃ (n : ℕ) (Y : C), (ObjectProperty.singleton G).triangEnvelopeIter n Y ∧
      Nonempty (Retract X Y)

/-- The Stacks-09SR finite-stage retract output implies classical generation
on compacts, using only that `triangEnvelope` contains every finite stage and
is stable under retracts. -/
theorem isClassicalGeneratorOnCompacts_of_isCompactRetractGenerated {G : C}
    (h : IsCompactRetractGenerated G) : IsClassicalGeneratorOnCompacts G := by
  intro X hX
  obtain ⟨n, Y, hY, ⟨r⟩⟩ := h X hX
  exact ObjectProperty.prop_of_retract _ r
    ((ObjectProperty.singleton G).triangEnvelopeIter_le_triangEnvelope n Y hY)

/-- Conversely, classical generation on compacts supplies the finite-stage
retract output (with the identity retract).  Thus the explicitly isolated
09SR input is equivalent to, and does not silently weaken, the library's
`IsClassicalGeneratorOnCompacts` predicate. -/
theorem isCompactRetractGenerated_of_isClassicalGeneratorOnCompacts {G : C}
    (h : IsClassicalGeneratorOnCompacts G) : IsCompactRetractGenerated G := by
  intro X hX
  obtain ⟨n, hn⟩ := (ObjectProperty.prop_triangEnvelope_iff
    (ObjectProperty.singleton G) X).1 (h X hX)
  exact ⟨n, X, hn, ⟨Retract.refl X⟩⟩

/-- A precise, proved reduction of the library predicate to the finite-stage
retract conclusion in Stacks 09SR. -/
theorem isCompactRetractGenerated_iff_isClassicalGeneratorOnCompacts (G : C) :
    IsCompactRetractGenerated G ↔ IsClassicalGeneratorOnCompacts G :=
  ⟨isClassicalGeneratorOnCompacts_of_isCompactRetractGenerated,
    isCompactRetractGenerated_of_isClassicalGeneratorOnCompacts⟩

section Triangulated

variable [CategoryTheory.IsTriangulated C]

/-- A generator lying in the thick envelope of `H` has its whole thick envelope
contained in that of `H`. -/
lemma triangEnvelope_singleton_le_of_mem {G H : C}
    (hG : (ObjectProperty.singleton H).triangEnvelope G) :
    (ObjectProperty.singleton G).triangEnvelope ≤
      (ObjectProperty.singleton H).triangEnvelope := by
  rw [ObjectProperty.triangEnvelope_le_iff]
  intro X hX
  obtain rfl : G = X := (ObjectProperty.singleton_iff _ _).1 hX
  exact hG

/-- Classical generation on compacts passes to an isomorphic generator. -/
theorem isClassicalGeneratorOnCompacts_of_iso {G H : C} (e : G ≅ H)
    (hG : IsClassicalGeneratorOnCompacts G) : IsClassicalGeneratorOnCompacts H := by
  have hmem : (ObjectProperty.singleton H).triangEnvelope G :=
    ObjectProperty.prop_of_iso _ e.symm
      (ObjectProperty.le_triangEnvelope _ _ ((ObjectProperty.singleton_iff _ _).2 rfl))
  intro X hX
  exact triangEnvelope_singleton_le_of_mem hmem X (hG X hX)

/-- Classical generation on compacts is stable under every integer shift of the
generator. -/
theorem isClassicalGeneratorOnCompacts_shift {G : C} (n : ℤ)
    (hG : IsClassicalGeneratorOnCompacts G) :
    IsClassicalGeneratorOnCompacts (G⟦n⟧) := by
  have hbase : (ObjectProperty.singleton (G⟦n⟧)).triangEnvelope (G⟦n⟧) :=
    ObjectProperty.le_triangEnvelope _ _ ((ObjectProperty.singleton_iff _ _).2 rfl)
  have hshift : (ObjectProperty.singleton (G⟦n⟧)).triangEnvelope ((G⟦n⟧)⟦-n⟧) :=
    (ObjectProperty.singleton (G⟦n⟧)).triangEnvelope.le_shift (-n) _ hbase
  have hmem : (ObjectProperty.singleton (G⟦n⟧)).triangEnvelope G :=
    ObjectProperty.prop_of_iso _ (shiftShiftNeg G n) hshift
  intro X hX
  exact triangEnvelope_singleton_le_of_mem hmem X (hG X hX)

omit [CategoryTheory.IsTriangulated C] in
/-- Separation implies that the *right* orthogonal of the finite thick envelope
contains only zero objects.  This is not classical generation: it gives no
inclusion of a compact `X` in that envelope in the first place. -/
theorem isZero_of_rightOrthogonal_triangEnvelope {G Y : C} (hG : IsGenerator G)
    (hY : (ObjectProperty.singleton G).triangEnvelope.rightOrthogonal Y) : IsZero Y := by
  apply isZero_of_isGenerator_of_hom_eq_zero hG
  intro n f
  apply hY f
  exact (ObjectProperty.singleton G).triangEnvelope.le_shift n _
    (ObjectProperty.le_triangEnvelope _ _ ((ObjectProperty.singleton_iff _ _).2 rfl))

omit [CategoryTheory.IsTriangulated C] in
/-- Eventual Hom-vanishing on pairs of compact objects, with classical
generation supplied by the Stacks-09SR finite-stage retract input.  This is the
use form needed by Lemma 4.3. -/
theorem eventuallyHomZero_of_compact_of_isCompactRetractGenerated {G X Y : C}
    (hG : EventuallyHomZero G G) (hgen : IsCompactRetractGenerated G)
    (hX : IsCoproductCompact X) (hY : IsCoproductCompact Y) :
    EventuallyHomZero X Y :=
  eventuallyHomZero_of_compact hG
    (isClassicalGeneratorOnCompacts_of_isCompactRetractGenerated hgen) hX hY

/-- The finite-stage retract formulation of the 09SR input is likewise
isomorphism invariant. -/
theorem isCompactRetractGenerated_of_iso {G H : C} (e : G ≅ H)
    (hG : IsCompactRetractGenerated G) : IsCompactRetractGenerated H :=
  isCompactRetractGenerated_of_isClassicalGeneratorOnCompacts
    (isClassicalGeneratorOnCompacts_of_iso e
      (isClassicalGeneratorOnCompacts_of_isCompactRetractGenerated hG))

/-- The finite-stage retract formulation of the 09SR input is stable under
integer shifts. -/
theorem isCompactRetractGenerated_shift {G : C} (n : ℤ)
    (hG : IsCompactRetractGenerated G) : IsCompactRetractGenerated (G⟦n⟧) :=
  isCompactRetractGenerated_of_isClassicalGeneratorOnCompacts
    (isClassicalGeneratorOnCompacts_shift n
      (isClassicalGeneratorOnCompacts_of_isCompactRetractGenerated hG))

end Triangulated

end RelativeWeakApprox
