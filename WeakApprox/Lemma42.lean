/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Aisle
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Tactic

/-!
# Lemma 4.2: degrees and right `t`-exactness for a glued `t`-structure

This file formalizes Lemma 4.2 of P. Lank and B. Pauwels,
*Gluing weak approximability along recollements*.

Found by a member of the Ultramath run `smwun9hk2` (direction D2).

The degree-zero aisle of the glued `t`-structure is specified by the two
conditions involving `i^*` and `j^*`.  We do not construct the glued
`t`-structure itself: an existing `tD : TStructure D` and the equality
`tD.le 0 = gluedLe ... 0` are hypotheses.  Thus the theorem is about the glued
`t`-structure, but does not assert its existence.  Commutation of `i^*` and
`j^*` with integer shifts is supplied by `Functor.CommShift` instances.

For independence from the concurrent D1 development, a recollement is rendered
at the theorem level by its relevant functors, adjunctions, full-faithfulness
instances, and composite-vanishing isomorphisms, rather than by a new record.
These are precisely the recollement consequences used in the paper's proof; no
additional vanishing or exactness hypothesis is introduced.
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

universe vD uD vZ uZ vU uU

variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
variable {DZ : Type uZ} [Category.{vZ} DZ] [Preadditive DZ] [HasZeroObject DZ]
  [HasShift DZ ℤ] [∀ (n : ℤ), (shiftFunctor DZ n).Additive] [Pretriangulated DZ]
variable {DU : Type uU} [Category.{vU} DU] [Preadditive DU] [HasZeroObject DU]
  [HasShift DU ℤ] [∀ (n : ℤ), (shiftFunctor DU n).Additive] [Pretriangulated DU]

/-- The degree-`n` aisle determined by the gluing conditions on `i^*` and
`j^*`.  For `n = 0` this is the defining aisle of the glued `t`-structure. -/
def gluedLe (iStar : D ⥤ DZ) (jStar : D ⥤ DU)
    (tZ : TStructure DZ) (tU : TStructure DU) (n : ℤ) : ObjectProperty D :=
  fun E => tZ.le n (iStar.obj E) ∧ tU.le n (jStar.obj E)

/-- Membership in degree `n` is equivalent to membership of the `n`-fold shift
in degree zero.  This is the elementwise version of `TStructure.shift_le`. -/
lemma le_iff_shift_zero {C : Type uD} [Category.{vD} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : TStructure C) (n : ℤ) (X : C) :
    t.le n X ↔ t.le 0 (X⟦n⟧) := by
  constructor
  · intro hX
    exact t.le_shift n n 0 (by omega) X hX
  · intro hX
    have h := t.le_shift 0 (-n) n (by omega) (X⟦n⟧) hX
    exact (t.le n).prop_of_iso (shiftShiftNeg X n) h

omit [Preadditive D] [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- The two gluing conditions commute with the degree shift. -/
lemma gluedLe_zero_shift_iff (iStar : D ⥤ DZ) (jStar : D ⥤ DU)
    [iStar.CommShift ℤ] [jStar.CommShift ℤ]
    (tZ : TStructure DZ) (tU : TStructure DU) (n : ℤ) (E : D) :
    gluedLe iStar jStar tZ tU 0 (E⟦n⟧) ↔ gluedLe iStar jStar tZ tU n E := by
  constructor
  · rintro ⟨hi, hj⟩
    constructor
    · rw [le_iff_shift_zero]
      exact (tZ.le 0).prop_of_iso ((iStar.commShiftIso n).app E) hi
    · rw [le_iff_shift_zero]
      exact (tU.le 0).prop_of_iso ((jStar.commShiftIso n).app E) hj
  · rintro ⟨hi, hj⟩
    rw [le_iff_shift_zero] at hi hj
    exact ⟨(tZ.le 0).prop_of_iso ((iStar.commShiftIso n).app E).symm hi,
      (tU.le 0).prop_of_iso ((jStar.commShiftIso n).app E).symm hj⟩

/-- **Lemma 4.2, shifted description of the glued aisle.**  If `tD` is the
glued `t`-structure, in the sense that its degree-zero aisle is the one from
Setup 4.1, then for every integer `n` its degree-`n` aisle is detected by
`i^*` and `j^*` in degree `n`.

The existence of `tD` is assumed; only its degree-zero gluing identity is
needed. -/
theorem lemma_4_2 (iStar : D ⥤ DZ) (jStar : D ⥤ DU)
    [iStar.CommShift ℤ] [jStar.CommShift ℤ]
    (tD : TStructure D) (tZ : TStructure DZ) (tU : TStructure DU)
    (hzero : tD.le 0 = gluedLe iStar jStar tZ tU 0) (n : ℤ) :
    tD.le n = gluedLe iStar jStar tZ tU n := by
  ext E
  rw [le_iff_shift_zero tD n E, hzero]
  exact gluedLe_zero_shift_iff iStar jStar tZ tU n E

/-- **Lemma 4.2, first containment:** `i^* D^{≤n} ⊆ D_Z^{≤n}`. -/
theorem lemma_4_2_iStar (iStar : D ⥤ DZ) (jStar : D ⥤ DU)
    [iStar.CommShift ℤ] [jStar.CommShift ℤ]
    (tD : TStructure D) (tZ : TStructure DZ) (tU : TStructure DU)
    (hzero : tD.le 0 = gluedLe iStar jStar tZ tU 0) (n : ℤ)
    {E : D} (hE : tD.le n E) : tZ.le n (iStar.obj E) := by
  rw [lemma_4_2 iStar jStar tD tZ tU hzero n] at hE
  exact hE.1

/-- **Lemma 4.2, second containment:** `j^* D^{≤n} ⊆ D_U^{≤n}`. -/
theorem lemma_4_2_jStar (iStar : D ⥤ DZ) (jStar : D ⥤ DU)
    [iStar.CommShift ℤ] [jStar.CommShift ℤ]
    (tD : TStructure D) (tZ : TStructure DZ) (tU : TStructure DU)
    (hzero : tD.le 0 = gluedLe iStar jStar tZ tU 0) (n : ℤ)
    {E : D} (hE : tD.le n E) : tU.le n (jStar.obj E) := by
  rw [lemma_4_2 iStar jStar tD tZ tU hzero n] at hE
  exact hE.2

/-- **Lemma 4.2, third containment:** `i_* D_Z^{≤n} ⊆ D^{≤n}`.
The counit of `i^* ⊣ i_*` is an isomorphism because `i_*` is fully faithful,
and `j^*i_*` vanishes. -/
theorem lemma_4_2_iLower (iStar : D ⥤ DZ) (iLower : DZ ⥤ D) (jStar : D ⥤ DU)
    [iStar.CommShift ℤ] [jStar.CommShift ℤ]
    (tD : TStructure D) (tZ : TStructure DZ) (tU : TStructure DU)
    (hzero : tD.le 0 = gluedLe iStar jStar tZ tU 0)
    (adj : iStar ⊣ iLower) [iLower.Full] [iLower.Faithful]
    (hvanish : iLower ⋙ jStar ≅ 0) (n : ℤ)
    {Y : DZ} (hY : tZ.le n Y) : tD.le n (iLower.obj Y) := by
  rw [lemma_4_2 iStar jStar tD tZ tU hzero n]
  constructor
  · exact (tZ.le n).prop_of_iso (asIso (adj.counit.app Y)).symm hY
  · exact (tU.isLE_of_isZero
      (IsZero.of_iso (Functor.zero_obj Y) (hvanish.app Y)) n).le

/-- **Lemma 4.2, fourth containment:** `j_! D_U^{≤n} ⊆ D^{≤n}`.
The unit of `j_! ⊣ j^*` is an isomorphism because `j_!` is fully faithful,
and `i^*j_!` vanishes. -/
theorem lemma_4_2_jShriek (iStar : D ⥤ DZ) (jShriek : DU ⥤ D) (jStar : D ⥤ DU)
    [iStar.CommShift ℤ] [jStar.CommShift ℤ]
    (tD : TStructure D) (tZ : TStructure DZ) (tU : TStructure DU)
    (hzero : tD.le 0 = gluedLe iStar jStar tZ tU 0)
    (adj : jShriek ⊣ jStar) [jShriek.Full] [jShriek.Faithful]
    (hvanish : jShriek ⋙ iStar ≅ 0) (n : ℤ)
    {Y : DU} (hY : tU.le n Y) : tD.le n (jShriek.obj Y) := by
  rw [lemma_4_2 iStar jStar tD tZ tU hzero n]
  constructor
  · exact (tZ.isLE_of_isZero
      (IsZero.of_iso (Functor.zero_obj Y) (hvanish.app Y)) n).le
  · exact (tU.le n).prop_of_iso (asIso (adj.unit.app Y)) hY
