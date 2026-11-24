/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Recollement
import WeakApprox.Lemma42
import WeakApprox.Lemma35
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Tactic

/-!
# Lemma 4.3(2)--(3): generation and the glued compactly generated aisle

This file proves the categorical parts of Lemma 4.3 of Lank--Pauwels.
Compactly generated aisles are rendered exactly as in `WeakApprox.Lemma35`,
namely `t.le 0 = Coprod (shiftTail H 0)`.  Instantiations of `Recollement`
here use a common hom universe for the three categories, since `Coprod` and
`IsCoproductCompact` quantify over that universe.
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

universe w v u u' u''

section Compactness

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v} D]

/-- Compactness in the `WeakApprox` sense is invariant under isomorphism. -/
lemma isCoproductCompact_of_iso {X Y : C} (e : X ≅ Y)
    (hX : IsCoproductCompact X) : IsCoproductCompact Y := by
  constructor
  intro J
  letI : PreservesColimitsOfShape (Discrete J) (coyoneda.obj (.op X)) := hX.preserves J
  exact preservesColimitsOfShape_of_natIso (coyoneda.mapIso e.symm.op)

/-- Neeman's compactness argument: a left adjoint preserves compact objects if
its right adjoint preserves the relevant small coproducts.  The common hom
universe is needed because `IsCoproductCompact` quantifies over that universe. -/
lemma isCoproductCompact_leftAdjoint_obj' {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {X : C} (hX : IsCoproductCompact X)
    (hG : ∀ (J : Type v), PreservesColimitsOfShape (Discrete J) G) :
    IsCoproductCompact (F.obj X) := by
  constructor
  intro J
  letI : PreservesColimitsOfShape (Discrete J) G := hG J
  letI : PreservesColimitsOfShape (Discrete J) (coyoneda.obj (.op X)) := hX.preserves J
  let e : coyoneda.obj (.op (F.obj X)) ≅ G ⋙ coyoneda.obj (.op X) :=
    (CategoryTheory.Adjunction.compCoyonedaIso adj).app (.op X)
  exact preservesColimitsOfShape_of_natIso e.symm

/-- Shifts preserve coproduct-compactness, since both the shift and its inverse
are adjoint equivalences. -/
lemma isCoproductCompact_shift [HasShift C ℤ] (X : C) (n : ℤ)
    (hX : IsCoproductCompact X) : IsCoproductCompact (X⟦n⟧) :=
  isCoproductCompact_leftAdjoint_obj' (shiftEquiv C n).toAdjunction hX
    (fun _ => inferInstance)

end Compactness

section Generation

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {D : Type u'} [Category.{v} D] [HasShift D ℤ]

/-- If `H` is a retract of `G`, generation by `H` implies generation by `G`. -/
lemma isGenerator_of_retract {H G : C} (r : Retract H G)
    (hH : IsGenerator H) : IsGenerator G := by
  intro X Y f g hfg
  apply hH f g
  rintro Z ⟨W, a, e, hW⟩ h
  obtain rfl : H = W := (ObjectProperty.singleton_iff H W).1 hW
  apply (cancel_epi e.inv).1
  apply (cancel_epi ((shiftFunctor C a).map r.r)).1
  have hm : (ObjectProperty.singleton G).shiftClosure ℤ (G⟦a⟧) :=
    ⟨G, a, Iso.refl _, by simp⟩
  have heq := hfg (G⟦a⟧) hm ((shiftFunctor C a).map r.r ≫ e.inv ≫ h)
  simpa only [Category.assoc, e.inv_hom_id_assoc] using heq

/-- A nonzero shift of a generator is again a generator. -/
lemma isGenerator_shift (G : C) (m : ℤ) (hG : IsGenerator G) :
    IsGenerator (G⟦m⟧) := by
  have h := hG.of_equivalence (shiftEquiv C m)
  apply h.of_le
  rintro X ⟨Y, ⟨Z, a, e, hZ⟩⟩
  obtain rfl : G = Z := (ObjectProperty.singleton_iff G Z).1 hZ
  refine ⟨G⟦m⟧, a, ?_, by simp⟩
  exact (shiftEquiv C m).functor.mapIso e ≪≫
    (shiftFunctorAdd' C a m (a + m) rfl).symm.app G ≪≫
    (shiftFunctorAdd' C m a (a + m) (by omega)).app G

/-- Generation passes along a left adjoint whose right adjoint is faithful.
The shift compatibility is used only to identify the image of the shift
closure. -/
lemma isGenerator_leftAdjoint_obj {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [F.CommShift ℤ] [G.Faithful] {H : C}
    (hH : IsGenerator H) : IsGenerator (F.obj H) := by
  have hstrict : (((ObjectProperty.singleton H).shiftClosure ℤ).strictMap F).IsSeparating := by
    intro X Y f g hfg
    apply G.map_injective
    apply hH
    intro Z hZ h
    obtain ⟨h', rfl⟩ := (adj.homEquiv Z X).surjective h
    simp only [Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp]
    rw [hfg (F.obj Z) (ObjectProperty.strictMap_obj _ F hZ) h']
  apply hstrict.of_le
  rintro X ⟨Y, Z, a, e, hZ⟩
  obtain rfl : H = Z := (ObjectProperty.singleton_iff H Z).1 hZ
  exact ⟨F.obj H, a, F.mapIso e ≪≫ (F.commShiftIso a).app H, by simp⟩

end Generation

section AisleHelpers

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A fixed-degree aisle is closed under retracts, by its orthogonality
characterization. -/
lemma aisle_le_of_retract (t : TStructure C) {X Y : C}
    (r : Retract X Y) {n : ℤ} (hY : t.le n Y) : t.le n X := by
  have h : t.IsLE Y n := ⟨hY⟩
  rw [t.le_iff_isLE]
  rw [t.isLE_iff_orthogonal n (n + 1) rfl] at h ⊢
  intro Z f hZ
  rw [← cancel_epi r.r, comp_zero]
  exact h Z (r.r ≫ f) hZ

/-- A fixed-degree aisle contains the binary biproduct of any two of its
objects. -/
lemma aisle_le_biprod (t : TStructure C) {X Y : C} {n : ℤ}
    (hX : t.le n X) (hY : t.le n Y) : t.le n (X ⊞ Y) := by
  exact (t.isLE₂ (binaryBiproductTriangle X Y)
    (binaryBiproductTriangle_distinguished X Y) n ⟨hX⟩ ⟨hY⟩).le

/-- The generating object belongs to its compactly generated degree-zero aisle. -/
lemma generator_mem_le_zero (t : TStructure C) (H : C)
    (hgen : t.le 0 = Coprod (shiftTail H 0)) : t.le 0 H := by
  rw [hgen]
  exact Coprod.of_mem H ⟨0, le_rfl, ⟨(shiftFunctorZero C ℤ).symm.app H⟩⟩

/-- Every nonnegative shift of the generating object belongs to its compactly
generated degree-zero aisle. -/
lemma shift_mem_le_zero (t : TStructure C) (H : C)
    (hgen : t.le 0 = Coprod (shiftTail H 0)) {n : ℤ} (hn : 0 ≤ n) :
    t.le 0 (H⟦n⟧) := by
  rw [hgen]
  exact Coprod.of_mem (H⟦n⟧) ⟨n, hn, ⟨Iso.refl _⟩⟩

end AisleHelpers

section CoprodMap

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u'} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

/-- An exact coproduct-preserving functor maps the inductive `Coprod` closure
into any target class with the same closure properties. -/
lemma coprod_map_le (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hpres : ∀ (J : Type v), PreservesColimitsOfShape (Discrete J) F)
    {P : ObjectProperty C} {Q : ObjectProperty D}
    [Q.IsClosedUnderIsomorphisms]
    [∀ (J : Type v), Q.IsClosedUnderColimitsOfShape (Discrete J)]
    [Q.IsTriangulatedClosed₂]
    (h : ∀ X, P X → Q (F.obj X)) {Y : C} (hY : Coprod P Y) : Q (F.obj Y) := by
  induction hY with
  | of_mem X hX => exact h X hX
  | of_isoClosure e _ ih => exact Q.prop_of_iso (F.mapIso e) ih
  | @of_colimitPresentation X J pres _ ih =>
      letI : PreservesColimitsOfShape (Discrete J) F := hpres J
      exact Q.prop_of_isColimit (isColimitOfPreserves F pres.isColimit) ih
  | of_extension T hT _ _ ih₁ ih₃ =>
      exact Q.ext_of_isTriangulatedClosed₂ (F.mapTriangle.obj T)
        (F.map_distinguished T hT) ih₁ ih₃

end CoprodMap

section RecollementNormalization

universe uZ uD uU

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

variable (R : Recollement DZ D DU)

/-- The left adjoint `j_!` preserves compactness, since its right adjoint `j^*`
is itself a left adjoint. -/
lemma recollement_jShriek_compact {GU : DU} (hGU : IsCoproductCompact GU) :
    IsCoproductCompact (R.jShriek.obj GU) :=
  isCoproductCompact_leftAdjoint_obj' R.jShriekAdj hGU
    (fun _ => R.jStarAdj.leftAdjoint_preservesColimits.preservesColimitsOfShape)

/-- The quotient `i^*` preserves compactness, since its right adjoint `i_*` is
itself a left adjoint. -/
lemma recollement_iStar_compact {G : D} (hG : IsCoproductCompact G) :
    IsCoproductCompact (R.iStar.obj G) :=
  isCoproductCompact_leftAdjoint_obj' R.iStarAdj hG
    (fun _ => R.iLowerAdj.leftAdjoint_preservesColimits.preservesColimitsOfShape)

/-- **Lemma 4.3(2), generation.**  Both `G` and `i^*G` generate.  This part uses
neither compactness nor the normalization bound on `j^*G'`.  The three
categories use the common hom universe `v`. -/
theorem lemma_4_3_2_generation (G' : D) (GU : DU) (m : ℤ)
    (hG' : IsGenerator G') :
    IsGenerator (G'⟦m⟧ ⊞ R.jShriek.obj GU) ∧
      IsGenerator (R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)) := by
  have hG : IsGenerator (G'⟦m⟧ ⊞ R.jShriek.obj GU) :=
    isGenerator_of_retract
      (BinaryBiproduct.bicone (G'⟦m⟧) (R.jShriek.obj GU)).retract_left
      (isGenerator_shift G' m hG')
  exact ⟨hG, isGenerator_leftAdjoint_obj R.iStarAdj hG⟩

/-- **Lemma 4.3(2), compactness API.**  The two summands of the normalized `G`
are compact.  Closure under the binary biproduct is deliberately not asserted:
with the repository's ordinary `Type`-valued `coyoneda` rendering of
compactness, that closure does not follow (and is false in general). -/
theorem lemma_4_3_2_compact_summands (G' : D) (GU : DU) (m : ℤ)
    (hG' : IsCoproductCompact G') (hGU : IsCoproductCompact GU) :
    IsCoproductCompact (G'⟦m⟧) ∧ IsCoproductCompact (R.jShriek.obj GU) := by
  exact ⟨isCoproductCompact_shift G' m hG', recollement_jShriek_compact R hGU⟩

/-- **Lemma 4.3(2), packaged with an explicit compactness hypothesis.**
The conclusions are the two compact-generator pairs for `G` and `i^*G`.
Compactness of the binary biproduct `G` is the explicit argument `hG`; it is not
inferred from its summands because `IsCoproductCompact` uses the ordinary
`Type`-valued `coyoneda` (see `lemma_4_3_2_compact_summands`).  As elsewhere in
this section, the three categories use the common hom universe `v`. -/
theorem lemma_4_3_2 (G' : D) (GU : DU) (m : ℤ)
    (hG' : IsGenerator G')
    (hG : IsCoproductCompact (G'⟦m⟧ ⊞ R.jShriek.obj GU)) :
    (IsCoproductCompact (G'⟦m⟧ ⊞ R.jShriek.obj GU) ∧
      IsGenerator (G'⟦m⟧ ⊞ R.jShriek.obj GU)) ∧
    (IsCoproductCompact (R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)) ∧
      IsGenerator (R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU))) := by
  obtain ⟨hgen, higen⟩ := lemma_4_3_2_generation R G' GU m hG'
  exact ⟨⟨hG, hgen⟩, ⟨recollement_iStar_compact R hG, higen⟩⟩

/-- **Lemma 4.3(3).**  The aisle compactly generated by the normalized `G` is
exactly the glued aisle.  All three compactly generated aisles are rendered by
`Coprod (shiftTail _ 0)`, as in `WeakApprox.Lemma35` (no retract closure is
added).  No preferred-equivalence-class assertion is needed in this statement;
the three categories use the common hom universe `v`. -/
theorem lemma_4_3_3 (tD : TStructure D) (tZ : TStructure DZ) (tU : TStructure DU)
    (G' : D) (GU : DU) (m : ℤ)
    (hjG' : tU.le m (R.jStar.obj G'))
    (hgenD : tD.le 0 = Coprod (shiftTail (G'⟦m⟧ ⊞ R.jShriek.obj GU) 0))
    (hgenZ : tZ.le 0 = Coprod
      (shiftTail (R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)) 0))
    (hgenU : tU.le 0 = Coprod (shiftTail GU 0)) :
    tD.le 0 = gluedLe R.iStar R.jStar tZ tU 0 := by
  let G : D := G'⟦m⟧ ⊞ R.jShriek.obj GU
  change tD.le 0 = Coprod (shiftTail G 0) at hgenD
  change tZ.le 0 = Coprod (shiftTail (R.iStar.obj G) 0) at hgenZ
  change tD.le 0 = gluedLe R.iStar R.jStar tZ tU 0
  letI (J : Type v) : (tD.le 0).IsClosedUnderColimitsOfShape (Discrete J) := by
    rw [hgenD]
    infer_instance
  letI : (tD.le 0).IsTriangulatedClosed₂ := by
    rw [hgenD]
    infer_instance
  letI (J : Type v) : (tZ.le 0).IsClosedUnderColimitsOfShape (Discrete J) := by
    rw [hgenZ]
    infer_instance
  letI : (tZ.le 0).IsTriangulatedClosed₂ := by
    rw [hgenZ]
    infer_instance
  letI (J : Type v) : (tU.le 0).IsClosedUnderColimitsOfShape (Discrete J) := by
    rw [hgenU]
    infer_instance
  letI : (tU.le 0).IsTriangulatedClosed₂ := by
    rw [hgenU]
    infer_instance
  letI : (gluedLe R.iStar R.jStar tZ tU 0).IsClosedUnderIsomorphisms := by
    constructor
    intro X Y e h
    exact ⟨(tZ.le 0).prop_of_iso (R.iStar.mapIso e) h.1,
      (tU.le 0).prop_of_iso (R.jStar.mapIso e) h.2⟩
  letI (J : Type v) :
      (gluedLe R.iStar R.jStar tZ tU 0).IsClosedUnderColimitsOfShape (Discrete J) := by
    constructor
    letI : PreservesColimitsOfShape (Discrete J) R.iStar :=
      R.iStarAdj.leftAdjoint_preservesColimits.preservesColimitsOfShape
    letI : PreservesColimitsOfShape (Discrete J) R.jStar :=
      R.jStarAdj.leftAdjoint_preservesColimits.preservesColimitsOfShape
    rintro X ⟨pres⟩
    exact ⟨(tZ.le 0).prop_of_isColimit
        (isColimitOfPreserves R.iStar pres.isColimit)
        (fun j => (pres.prop_diag_obj j).1),
      (tU.le 0).prop_of_isColimit
        (isColimitOfPreserves R.jStar pres.isColimit)
        (fun j => (pres.prop_diag_obj j).2)⟩
  letI : (gluedLe R.iStar R.jStar tZ tU 0).IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ =>
      ⟨(tZ.isLE₂ (R.iStar.mapTriangle.obj T) (R.iStar.map_distinguished T hT) 0
          ⟨h₁.1⟩ ⟨h₃.1⟩).le,
        (tU.isLE₂ (R.jStar.mapTriangle.obj T) (R.jStar.map_distinguished T hT) 0
          ⟨h₁.2⟩ ⟨h₃.2⟩).le⟩)
  have hGtail {n : ℤ} (hn : 0 ≤ n) : tD.le 0 (G⟦n⟧) :=
    shift_mem_le_zero tD G hgenD hn
  have hbase : shiftTail G 0 ≤ gluedLe R.iStar R.jStar tZ tU 0 := by
    intro X hX
    obtain ⟨n, hn, ⟨e⟩⟩ := hX
    have hi : tZ.le 0 (R.iStar.obj (G⟦n⟧)) :=
      (tZ.le 0).prop_of_iso ((R.iStar.commShiftIso n).app G).symm
        (shift_mem_le_zero tZ (R.iStar.obj G) hgenZ hn)
    have hA : tU.le 0 (R.jStar.obj (G'⟦m⟧)) := by
      apply (tU.le 0).prop_of_iso ((R.jStar.commShiftIso m).app G').symm
      exact tU.le_shift m m 0 (by omega) _ hjG'
    have hB : tU.le 0 (R.jStar.obj (R.jShriek.obj GU)) :=
      (tU.le 0).prop_of_iso (asIso (R.jShriekAdj.unit.app GU))
        (generator_mem_le_zero tU GU hgenU)
    have hG₀ : tU.le 0 (R.jStar.obj G) := by
      letI : PreservesBiproductsOfShape WalkingPair R.jStar := inferInstance
      letI : PreservesBinaryBiproducts R.jStar :=
        preservesBinaryBiproducts_of_preservesBiproducts R.jStar
      apply (tU.le 0).prop_of_iso (R.jStar.mapBiprod (G'⟦m⟧) (R.jShriek.obj GU)).symm
      exact aisle_le_biprod tU hA hB
    have hGshift : tU.le (-n) ((R.jStar.obj G)⟦n⟧) :=
      tU.le_shift 0 n (-n) (by omega) _ hG₀
    have hj : tU.le 0 (R.jStar.obj (G⟦n⟧)) :=
      (tU.le 0).prop_of_iso ((R.jStar.commShiftIso n).app G).symm
        (tU.le_monotone (by omega) _ hGshift)
    exact (gluedLe R.iStar R.jStar tZ tU 0).prop_of_iso e.symm ⟨hi, hj⟩
  have hforward : tD.le 0 ≤ gluedLe R.iStar R.jStar tZ tU 0 := by
    intro E hE
    rw [hgenD] at hE
    exact Coprod.le hbase E hE
  have hJ (E : D) (hE : tU.le 0 (R.jStar.obj E)) :
      tD.le 0 (R.jShriek.obj (R.jStar.obj E)) := by
    rw [hgenU] at hE
    refine coprod_map_le R.jShriek
      (fun _ => R.jShriekAdj.leftAdjoint_preservesColimits.preservesColimitsOfShape) ?_ hE
    intro X hX
    obtain ⟨n, hn, ⟨e⟩⟩ := hX
    have hs : tD.le 0 ((R.jShriek.obj GU)⟦n⟧) :=
      aisle_le_of_retract tD
        ((BinaryBiproduct.bicone (G'⟦m⟧) (R.jShriek.obj GU)).retract_right.map
          (shiftFunctor D n)) (hGtail hn)
    exact (tD.le 0).prop_of_iso
      (R.jShriek.mapIso e ≪≫ (R.jShriek.commShiftIso n).app GU).symm hs
  have hIbase (n : ℤ) (hn : 0 ≤ n) :
      tD.le 0 (R.iLower.obj (R.iStar.obj (G⟦n⟧))) := by
    have hJE : tD.le 0 (R.jShriek.obj (R.jStar.obj (G⟦n⟧))) :=
      hJ (G⟦n⟧) (hforward (G⟦n⟧) (hGtail hn)).2
    have hJEshift : tD.le 0 ((R.jShriek.obj (R.jStar.obj (G⟦n⟧)))⟦(1 : ℤ)⟧) :=
      tD.le_monotone (show (-1 : ℤ) ≤ 0 by omega) _
        (tD.le_shift 0 1 (-1) (by omega) _ hJE)
    exact (tD.isLE₂ (R.firstTriangle (G⟦n⟧)).rotate
      (rot_of_distTriang _ (R.first_distinguished (G⟦n⟧))) 0
      ⟨hGtail hn⟩ ⟨hJEshift⟩).le
  have hI (E : D) (hE : tZ.le 0 (R.iStar.obj E)) :
      tD.le 0 (R.iLower.obj (R.iStar.obj E)) := by
    rw [hgenZ] at hE
    refine coprod_map_le R.iLower
      (fun _ => R.iLowerAdj.leftAdjoint_preservesColimits.preservesColimitsOfShape) ?_ hE
    intro X hX
    obtain ⟨n, hn, ⟨e⟩⟩ := hX
    exact (tD.le 0).prop_of_iso
      (R.iLower.mapIso e ≪≫
        R.iLower.mapIso ((R.iStar.commShiftIso n).app G).symm).symm
      (hIbase n hn)
  apply le_antisymm hforward
  intro E hE
  exact (tD.isLE₂ (R.firstTriangle E) (R.first_distinguished E) 0
    ⟨hJ E hE.2⟩ ⟨hI E hE.1⟩).le

end RecollementNormalization

end RelativeWeakApprox
