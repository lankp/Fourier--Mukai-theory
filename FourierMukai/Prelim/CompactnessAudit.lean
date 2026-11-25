/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Prelim.Lemma24

/-!
# Audit: the `Type`-valued compactness `RelativeFM.IsCompact` is never satisfied

`RelativeFM.IsCompact.{w} X` (`Prelim/Lemma25.lean`) asks that the `Type`-valued functor
`Hom(X, -)` preserve coproducts indexed by `Type w`.  A coproduct in `Type` is a disjoint
union, so in any category with zero morphisms and a zero object this fails for every `X`:
the coproduct `0 ⨿ 0 ≅ 0` indexed by `ULift Bool` would have to be sent to a two-element
set, but `Hom(X, 0)` is a singleton.  `WeakApprox/Basic.lean` already notes that this
`Type`-valued notion (there `IsCoproductCompact`) is strictly stronger than the paper's
additive compactness `IsCompactAb`; this file proves that in a pretriangulated category
it is uninhabited.

## Consequences (25 November 2026)

* `SinglyCompactlyGenerated C G` (`Prelim/Lemma25.lean`) is false for every `G` in a
  pretriangulated category (`not_singlyCompactlyGenerated`), so `RelativeFM.lemma_2_5`,
  GL26 Lemma 2.5 as rendered there, holds vacuously.
* In `Prelim/Lemma24.lean`, `CompactBousfieldLocalization C` holds trivially
  (`compactBousfieldLocalization_trivial`), and `lemma_2_4` and
  `singlyCompactlyGenerated_iff` are vacuous.  The compactness-free results there,
  `isPaperGenerator_of_isLocalizingGenerator` and
  `isPaperGenerator_iff_isLocalizingGenerator` (from `HasBousfieldTriangles G`), are not
  affected.
* `WeakApprox` is not affected: the LP26 chain assumes `IsCompactAb`.

The fix is to render compactness additively (`IsCompactAb`, the `AddCommGrpCat`-valued
`Hom(X, -)` preserving coproducts) and re-prove Lemmas 2.4 and 2.5 under it; see
`results/SWARM.md`.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory Limits

universe w v u

/-- In any category with zero morphisms and a zero object, no object is
`RelativeFM.IsCompact.{w}`: the `Type`-valued `Hom(X, -)` cannot send the coproduct
`0 ⨿ 0 ≅ 0` (indexed by `ULift Bool`) to a two-element disjoint union. -/
theorem not_isCompact_of_hasZeroObject {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] (X : C) : ¬ IsCompact.{w} X := by
  open ZeroObject in
  intro h
  let J : Type w := ULift.{w} Bool
  let K : Discrete J ⥤ C := Discrete.functor (fun _ => (0 : C))
  have hK := h J K
  let c : Cocone K := ⟨0, Discrete.natTrans (fun _ => 0)⟩
  have hc : IsColimit c := by
    refine ⟨fun s => 0, fun s j => ?_, fun s m _ => ?_⟩
    · exact (isZero_zero C).eq_of_src _ _
    · exact (isZero_zero C).eq_of_src _ _
  have hc' := isColimitOfPreserves (coyoneda.obj (Opposite.op X)) hc
  -- map the image cocone to `ULift Bool`, sending the `j`-th summand to `j`
  let s : Cocone (K ⋙ coyoneda.obj (Opposite.op X)) :=
    ⟨ULift.{v} Bool, Discrete.natTrans (fun j => TypeCat.ofHom (fun _ => ULift.up j.as.down))⟩
  have hfac := fun j : Discrete J => ConcreteCategory.congr_hom (hc'.fac s j) (0 : X ⟶ K.obj j)
  have h0 := hfac ⟨ULift.up false⟩
  have h1 := hfac ⟨ULift.up true⟩
  simp [s, c] at h0 h1
  exact Bool.false_ne_true (congrArg ULift.down (h0.symm.trans h1))

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- `SinglyCompactlyGenerated` (`Prelim/Lemma25.lean`) is never satisfied, so
`RelativeFM.lemma_2_5` is vacuous as stated. -/
theorem not_singlyCompactlyGenerated (G : C) : ¬ SinglyCompactlyGenerated.{w} C G :=
  fun h => not_isCompact_of_hasZeroObject G h.1

/-- `CompactBousfieldLocalization` (`Prelim/Lemma24.lean`) holds trivially, so
`RelativeFM.lemma_2_4` and `singlyCompactlyGenerated_iff` are vacuous as stated. -/
theorem compactBousfieldLocalization_trivial : CompactBousfieldLocalization.{w} C :=
  fun G hG => absurd hG (not_isCompact_of_hasZeroObject G)

end RelativeFM
