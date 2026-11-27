/-
Endgame assembly for the affine LP theorem in the small-Hom derived model.

This file is self-contained apart from the repository imports. In particular,
it does not add axioms or use `sorry`.

The small-Hom endpoints `affine_theorem_1_1_small_neeman_only` and
`affine_theorem_1_1_small_standard_neeman_only` (and
`smallCompactHomZeroAtTop_of_neeman`) moved to `Scheme/Neeman32Inputs.lean` on
`wave5/neeman-prune`, renamed `…_of_tag09SR`: they took the Neeman 2024,
Theorem 3.2(i) interface `SmallNeemanCompactToPerfectInput`, which was deleted,
and now take Stacks 09SR.  They, `SetupMainMinimal.replaceMiddleTStructure` and
`SetupMainMinimal.theorem_1_1_of_middleAisleCoproducts_of_compactHomZeroAtTop` were
deleted in wave 7 (`results/OPEN_INPUTS.md` row 7.3: the `IsGenerator` form, F2).
-/
import FourierMukai.Scheme.AisleCoproducts
import FourierMukai.Scheme.AffineMain

@[expose] public section

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u uZ uU

noncomputable section

/-- The regular module, concentrated in degree zero in the small-Hom affine
derived category. -/
noncomputable def smallRingObject (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) : SmallAffineD A H := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)

/-- Perfect complexes in the small-Hom affine derived model: the thick
triangulated envelope of the regular module. -/
noncomputable def SmallPerf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) : ObjectProperty (SmallAffineD A H) :=
  (ObjectProperty.singleton (smallRingObject A H)).triangEnvelope

theorem smallRingObject_mem_smallPerf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) : SmallPerf A H (smallRingObject A H) := by
  apply ObjectProperty.le_triangEnvelope
  exact ObjectProperty.ofObj_apply _ Unit.unit

/-- Positive self-extensions of the regular module vanish in the small-Hom
model. The proof is projectivity of the regular module; it uses no geometric
or compactness input. -/
theorem smallRingObject_eventuallyHomZero_self (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    EventuallyHomZero (smallRingObject A H) (smallRingObject A H) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  let _ : HasExt.{u} (ModuleCat.{u} A) :=
    hasExt_of_hasDerivedCategory (ModuleCat.{u} A)
  refine ⟨1, fun n hn f => ?_⟩
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n by omega)
  cases k with
  | zero => omega
  | succ k =>
      let e : Abelian.Ext.{u} (ModuleCat.of A A) (ModuleCat.of A A) (k + 1) :=
        Abelian.Ext.homEquiv.symm f
      have he : e = 0 := Abelian.Ext.eq_zero_of_projective e
      have hz : Abelian.Ext.homEquiv e = 0 := by
        rw [he]
        exact Abelian.Ext.zero_hom (ModuleCat.of A A) (ModuleCat.of A A) (k + 1)
      exact (Abelian.Ext.homEquiv.apply_symm_apply f).symm.trans hz

/-- Eventual positive Hom-vanishing for perfect complexes in the small-Hom
model, by transport around the defining thick triangulated envelope. -/
theorem smallPerf_eventuallyHomZero (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X Y : SmallAffineD A H}
    (hX : SmallPerf A H X) (hY : SmallPerf A H Y) : EventuallyHomZero X Y :=
  eventuallyHomZero_of_mem_triangEnvelope
    (smallRingObject_eventuallyHomZero_self A H) hX hY

end

end RelativeFM

#print axioms RelativeFM.smallRingObject_eventuallyHomZero_self
#print axioms RelativeFM.smallPerf_eventuallyHomZero

