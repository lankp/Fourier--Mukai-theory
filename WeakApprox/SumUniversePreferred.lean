/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.SumUniverse
import WeakApprox.SumUniverseTransport
import FourierMukai.Scheme.NeemanPreferred

/-!
# The preferred equivalence class with a separate coproduct universe

Source: Neeman, *Strong generators in `D^perf(X)` and `D^b_coh(X)`*, Definition 2.9 and
Remark 2.11, as used in LP26 §2.1.3 and GL26 Lemma A.9 (`lem:preferred_eq_class`).

`RelativeFM.NeemanPreferredM6.InPreferredClass t` asks for a compact generator `G`
(`IsCompactAb`) and a `t`-structure with aisle `Coprod({G[n] : n ≥ 0})` equivalent to `t`;
both notions index direct sums by the Hom universe.  `SumUniverse.InPreferredClass.{w}` is the
same definition with `SumUniverse.IsCompactAb.{w}` and `SumUniverse.Coprod.{w}`, so that it
applies to AxiomMath's `D(𝒪_X)` (morphisms in `Type (u + 1)`, direct sums over `Type u`).

## Main results

* `inPreferredClass_iff`: at `w = v` it is `RelativeFM.NeemanPreferredM6.InPreferredClass`.
* `inPreferredClass_transport`: membership is invariant under triangulated equivalences, across
  Hom universes (the `t`-structure is transported by `transportTStructure`).

## Assumptions

None.
-/

@[expose] public section

namespace RelativeWeakApprox.SumUniverse

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeFM.NeemanPreferredM6

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Membership in the preferred equivalence class** (Neeman, Definition 2.9 and
Remark 2.11), for a coproduct universe `w`: there are a compact (`IsCompactAb.{w}`)
zero-detecting `G` and a `t`-structure `t_G` with `t_G^{≤0} = Coprod.{w}({G[n] : n ≥ 0})`,
equivalent to `t`.  At `w = v` it is `RelativeFM.NeemanPreferredM6.InPreferredClass`
(`inPreferredClass_iff`). -/
def InPreferredClass (t : TStructure C) : Prop :=
  ∃ (G : C) (tG : TStructure C), IsCompactAb.{w} G ∧ IsPaperGenerator G ∧
    tG.le 0 = Coprod.{w} (shiftTail G 0) ∧ TStructureEquivalent t tG

/-- **At `w = v`, the preferred class is the repository's `InPreferredClass`.** -/
theorem inPreferredClass_iff (t : TStructure C) :
    InPreferredClass.{v} t ↔ RelativeFM.NeemanPreferredM6.InPreferredClass t := by
  simp only [InPreferredClass, RelativeFM.NeemanPreferredM6.InPreferredClass, isCompactAb_iff,
    coprod_eq]

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  (e : C ≌ D) [e.functor.Additive] [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
  [e.functor.IsTriangulated] [e.inverse.IsTriangulated]

omit [e.functor.Additive] in
/-- The image of `Coprod.{w}({G[n] : n ≥ n₀})` under a triangulated equivalence is
`Coprod.{w}({(eG)[n] : n ≥ n₀})`: an object `Y` of `D` lies in the second iff `e⁻¹ Y` lies in the
first. -/
theorem coprod_shiftTail_transport (G : C) (n₀ : ℤ) (Y : D) :
    Coprod.{w} (shiftTail (e.functor.obj G) n₀) Y ↔
      Coprod.{w} (shiftTail G n₀) (e.inverse.obj Y) := by
  have : ∀ J : Type w, PreservesColimitsOfShape (Discrete J) e.functor := fun _ =>
    e.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : ∀ J : Type w, PreservesColimitsOfShape (Discrete J) e.inverse := fun _ =>
    e.symm.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  constructor
  · intro h
    refine Coprod.map_obj e.inverse (fun Z hZ => ?_) h
    obtain ⟨n, hn, ⟨i⟩⟩ := hZ
    exact .of_mem _ ⟨n, hn, ⟨e.inverse.mapIso i ≪≫ (e.inverse.commShiftIso n).app _ ≪≫
      ((shiftFunctor C n).mapIso (e.unitIso.app G)).symm⟩⟩
  · intro h
    refine (Coprod.{w} _).prop_of_iso (e.counitIso.app Y) (Coprod.map_obj e.functor
      (fun Z hZ => ?_) h)
    obtain ⟨n, hn, ⟨i⟩⟩ := hZ
    exact .of_mem _ ⟨n, hn, ⟨e.functor.mapIso i ≪≫ (e.functor.commShiftIso n).app G⟩⟩

omit [e.inverse.IsTriangulated] in
/-- Neeman's equivalence of `t`-structures transports along a triangulated equivalence. -/
theorem tStructureEquivalent_transport {t₁ t₂ : TStructure C} (h : TStructureEquivalent t₁ t₂) :
    TStructureEquivalent (transportTStructure e t₁) (transportTStructure e t₂) := by
  obtain ⟨n, hn, h₁, h₂⟩ := h
  exact ⟨n, hn, fun Y hY => h₁ _ hY, fun Y hY => h₂ _ hY⟩

/-- **The preferred class is invariant under triangulated equivalences**, across Hom
universes, for a fixed coproduct universe `w`. -/
theorem inPreferredClass_transport {t : TStructure C} (h : InPreferredClass.{w} t) :
    InPreferredClass.{w} (transportTStructure e t) := by
  obtain ⟨G, tG, hGc, hGg, htG, heq⟩ := h
  refine ⟨e.functor.obj G, transportTStructure e tG, (isCompactAb_functor_obj_iff e G).2 hGc,
    isPaperGenerator_functor_obj e hGg, ?_, tStructureEquivalent_transport e heq⟩
  funext Y
  apply propext
  rw [coprod_shiftTail_transport e G 0 Y]
  exact Iff.of_eq (congrFun htG (e.inverse.obj Y))

end RelativeWeakApprox.SumUniverse

#print axioms RelativeWeakApprox.SumUniverse.inPreferredClass_iff
#print axioms RelativeWeakApprox.SumUniverse.inPreferredClass_transport
