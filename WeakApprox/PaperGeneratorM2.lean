/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.MainMinimal
import WeakApprox.GeneratorBridge

/-!
# Weak approximation with the paper's zero-detection generation

This module isolates the change from morphism separation (`IsGenerator`) to
zero detection (`IsPaperGenerator`). No other field of Definition 2.1 is
changed. The transport lemmas are the zero-detection counterparts of the
generation arguments in Lemma 4.3(2).
-/

@[expose] public section

namespace RelativeWeakApprox.PaperM2

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox

universe v u u'

section Basic

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- Definition 2.1 with the paper's actual zero-detection condition.
The approximation, compactness, aisle-bound and Hom-vanishing fields are
literally those of `WeakApproximationData`. -/
structure PaperWeakApproximationData (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [Pretriangulated C] where
  G : C
  t : TStructure C
  A : ℤ
  A_pos : 0 < A
  G_compact : IsCompactAb G
  G_paperGenerates : IsPaperGenerator G
  G_mem_le : t.le A G
  hom_vanishing : ∀ {Y : C}, t.le (-A) Y → ∀ f : G ⟶ Y, f = 0
  exists_triangle : ∀ F : C, t.le 0 F →
    ∃ (E D : C) (f : E ⟶ F) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ envelope G (-A) A E ∧ t.le (-1) D

/-- Weak approximability with zero detection, rather than ghost-freeness. -/
def SatisfiesPaperWA (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [Pretriangulated C] : Prop :=
  Nonempty (PaperWeakApproximationData C)

/-- The old, stronger data forget to the paper's data. -/
def PaperWeakApproximationData.ofStrong (W : WeakApproximationData C) :
    PaperWeakApproximationData C where
  G := W.G
  t := W.t
  A := W.A
  A_pos := W.A_pos
  G_compact := W.G_compact
  G_paperGenerates := isPaperGenerator_of_isGenerator W.G_generates
  G_mem_le := W.G_mem_le
  hom_vanishing := W.hom_vanishing
  exists_triangle := W.exists_triangle

/-- Bounds may be enlarged exactly as for the original structure. -/
def PaperWeakApproximationData.monoBound (W : PaperWeakApproximationData C)
    {A' : ℤ} (hA : W.A ≤ A') : PaperWeakApproximationData C where
  G := W.G
  t := W.t
  A := A'
  A_pos := lt_of_lt_of_le W.A_pos hA
  G_compact := W.G_compact
  G_paperGenerates := W.G_paperGenerates
  G_mem_le := W.t.le_monotone hA W.G W.G_mem_le
  hom_vanishing := by
    intro Y hY f
    exact W.hom_vanishing (W.t.le_monotone (by omega) Y hY) f
  exists_triangle := by
    intro F hF
    obtain ⟨E, D, f, g, h, hT, hE, hD⟩ := W.exists_triangle F hF
    exact ⟨E, D, f, g, h, hT,
      lemma31_2_mono W.G (a := -W.A) (b := W.A) (a' := -A') (b' := A')
        (by omega) hA E hE, hD⟩

@[simp] lemma PaperWeakApproximationData.monoBound_G
    (W : PaperWeakApproximationData C) {A' : ℤ} (hA : W.A ≤ A') :
    (W.monoBound hA).G = W.G := rfl

@[simp] lemma PaperWeakApproximationData.monoBound_t
    (W : PaperWeakApproximationData C) {A' : ℤ} (hA : W.A ≤ A') :
    (W.monoBound hA).t = W.t := rfl

@[simp] lemma PaperWeakApproximationData.monoBound_A
    (W : PaperWeakApproximationData C) {A' : ℤ} (hA : W.A ≤ A') :
    (W.monoBound hA).A = A' := rfl

/-- The self-vanishing argument uses none of the generation field. -/
theorem PaperWeakApproximationData.eventuallyHomZero_self
    (W : PaperWeakApproximationData C) : EventuallyHomZero W.G W.G := by
  refine ⟨2 * W.A, fun n hn f => W.hom_vanishing ?_ f⟩
  apply W.t.le_monotone (show W.A - n ≤ -W.A by omega)
  exact W.t.le_shift W.A n (W.A - n) (by omega) W.G W.G_mem_le

/-- The forward finite-thick-envelope argument also uses no generation. -/
theorem eventuallyHomZero_self_of_mem_triangEnvelope
    (W : PaperWeakApproximationData C) {G' : C}
    (hG' : (ObjectProperty.singleton W.G).triangEnvelope G') :
    EventuallyHomZero G' G' :=
  eventuallyHomZero_of_mem_triangEnvelope W.eventuallyHomZero_self hG' hG'

/-- Consequently the old weak approximability implies the corrected one. -/
theorem satisfiesPaperWA_of_satisfiesWA : SatisfiesWA C → SatisfiesPaperWA C := by
  rintro ⟨W⟩
  exact ⟨PaperWeakApproximationData.ofStrong W⟩

end Basic

section Transport

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]
variable {D : Type u'} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- Zero detection is inherited from a retract, with no separation argument. -/
lemma isPaperGenerator_of_retract {H G : C} (r : Retract H G)
    (hH : IsPaperGenerator H) : IsPaperGenerator G := by
  intro E hE
  apply hH
  intro n f
  rw [← cancel_epi ((shiftFunctor C n).map r.r), comp_zero]
  exact hE n _

/-- A shift of a zero-detecting generator again detects zero. -/
lemma isPaperGenerator_shift (G : C) (m : ℤ) (hG : IsPaperGenerator G) :
    IsPaperGenerator (G⟦m⟧) := by
  intro E hE
  apply hG
  intro n f
  let e : G⟦n⟧ ≅ (G⟦m⟧)⟦n - m⟧ :=
    (shiftFunctorAdd' C m (n - m) n (by omega)).app G
  rw [← cancel_epi e.inv, comp_zero]
  exact hE (n - m) (e.inv ≫ f)

/-- A left adjoint with faithful right adjoint preserves zero detection.
Faithfulness reflects zero objects; shift compatibility identifies the
adjuncts. -/
lemma isPaperGenerator_leftAdjoint_obj {F : C ⥤ D} {H : D ⥤ C}
    (adj : F ⊣ H) [F.CommShift ℤ] [F.Additive] [H.Faithful] [H.Additive] {X : C}
    (hX : IsPaperGenerator X) : IsPaperGenerator (F.obj X) := by
  intro E hE
  have hHE : IsZero (H.obj E) := by
    apply hX
    intro n f
    let e := (F.commShiftIso n).app X
    let f' : F.obj (X⟦n⟧) ⟶ E := (adj.homEquiv _ _).symm f
    have hz : e.inv ≫ f' = 0 := hE n _
    have hf' : f' = 0 := by
      rw [← cancel_epi e.inv, comp_zero]
      exact hz
    exact (adj.homEquiv _ _).symm.injective (by
      simpa only [f', Adjunction.homEquiv_counit, F.map_zero, zero_comp] using hf')
  rw [IsZero.iff_id_eq_zero] at hHE ⊢
  apply H.map_injective
  simpa using hHE

end Transport

end RelativeWeakApprox.PaperM2

#print axioms RelativeWeakApprox.PaperM2.PaperWeakApproximationData.ofStrong
#print axioms RelativeWeakApprox.PaperM2.PaperWeakApproximationData.monoBound
#print axioms RelativeWeakApprox.PaperM2.PaperWeakApproximationData.eventuallyHomZero_self
#print axioms RelativeWeakApprox.PaperM2.isPaperGenerator_of_retract
#print axioms RelativeWeakApprox.PaperM2.isPaperGenerator_shift
#print axioms RelativeWeakApprox.PaperM2.isPaperGenerator_leftAdjoint_obj
