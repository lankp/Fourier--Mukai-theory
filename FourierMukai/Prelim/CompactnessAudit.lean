/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Prelim.Lemma24
import FourierMukai.Scheme.AffineCompactness
import FourierMukai.Scheme.AffineSpaltenstein
import FourierMukai.Scheme.PaperGeneratorM5
import WeakApprox.CompactThick

/-!
# Audit: the `Type`-valued compactness `RelativeFM.IsCompact` is never satisfied

`RelativeFM.IsCompact.{w} X` (`Prelim/Lemma25.lean`) asks that the `Type`-valued functor
`Hom(X, -)` preserve coproducts indexed by `Type w`.  A coproduct in `Type` is a disjoint
union, so in any category with zero morphisms and a zero object this fails for every `X`:
the coproduct `0 ⨿ 0 ≅ 0` indexed by `ULift Bool` would have to be sent to a two-element
set, but `Hom(X, 0)` is a singleton (`not_isCompact_of_hasZeroObject`).
`WeakApprox/Basic.lean` already notes that this `Type`-valued notion (there
`IsCoproductCompact`) is strictly stronger than the paper's additive compactness
`IsCompactAb`.

## History and fix (25 November 2026)

Until this date, `SinglyCompactlyGenerated` (`Prelim/Lemma25.lean`) was stated with
`IsCompact`, so it was never satisfied and `RelativeFM.lemma_2_5` (GL26 Lemma 2.5) held
vacuously; in `Prelim/Lemma24.lean` the input `CompactBousfieldLocalization` held
trivially and `lemma_2_4`, `singlyCompactlyGenerated_iff` were vacuous.

The defect is fixed:

* compactness in Lemmas 2.4 and 2.5 is now the paper's additive one,
  `RelativeWeakApprox.IsCompactAb` (the `AddCommGrpCat`-valued `Hom(X, -)` preserves
  `Type v`-small coproducts); `IsCompact` is kept only as the refuted notion;
* `CompactBousfieldLocalization` and the old `lemma_2_4`/`singlyCompactlyGenerated_iff`
  are deleted; the new `lemma_2_4` uses the tagged Stacks input `Tag09SN`
  (`Prelim/Stacks09SN.lean`).

## Non-vacuity of the new hypotheses

* `isCompactAb_zero`: the zero object of any preadditive category is `IsCompactAb`.
* `smallRingObject_isCompactAb_and_isPaperGenerator`: for every commutative ring `A`, the
  regular module `A` in the derived category `D(A)` (small-Hom model
  `SmallAffineD A (affineSpaltensteinInput A)`, with `Type u`-small coproducts) is
  `IsCompactAb` and detects zero through its shifts (`IsPaperGenerator`).  Both are proved
  in the tree (`NeemanM1.smallRingObject_isCompactAb`,
  `NeemanGeneratorM5.Paper.smallRingObject_isPaperGenerator`).
* `singlyCompactlyGenerated_smallRingObject`: hence, given Stacks 09SN for `D(A)`, the
  hypothesis `SinglyCompactlyGenerated` of `lemma_2_5` holds for `A ∈ D(A)`.
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

open RelativeWeakApprox ZeroObject in
/-- Non-vacuity of `IsCompactAb`: a zero object is compact (in any preadditive
category). -/
theorem isCompactAb_zero {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] :
    IsCompactAb (0 : C) :=
  isCompactAb_of_isZero (isZero_zero C)

section AffineExample

open RelativeWeakApprox

/-- Non-vacuity, explicit example: for every commutative ring `A`, the regular module in
the derived category `D(A)` (small-Hom model) is compact (`IsCompactAb`) and detects zero
through its shifts (`IsPaperGenerator`). -/
theorem smallRingObject_isCompactAb_and_isPaperGenerator (A : Type u) [CommRing A] :
    IsCompactAb (smallRingObject A (Spaltenstein.affineSpaltensteinInput A)) ∧
      IsPaperGenerator (smallRingObject A (Spaltenstein.affineSpaltensteinInput A)) :=
  ⟨NeemanM1.smallRingObject_isCompactAb A _,
    NeemanGeneratorM5.Paper.smallRingObject_isPaperGenerator A _⟩

/-- Non-vacuity of the hypothesis of **Lemma 2.5**
(`lem:equivalence_or_fully_faithful_via_compacts`): given Stacks 09SN for `D(A)` (the
tagged input `StacksInterface.Tag09SN`), the regular module singly compactly generates
`D(A)` in the sense of `SinglyCompactlyGenerated`. -/
theorem singlyCompactlyGenerated_smallRingObject (A : Type u) [CommRing A]
    (h09SN : letI := smallAffineHasCoproducts A (Spaltenstein.affineSpaltensteinInput A)
      StacksInterface.Tag09SN (SmallAffineD A (Spaltenstein.affineSpaltensteinInput A))) :
    SinglyCompactlyGenerated (SmallAffineD A (Spaltenstein.affineSpaltensteinInput A))
      (smallRingObject A (Spaltenstein.affineSpaltensteinInput A)) := by
  have := smallAffineHasCoproducts A (Spaltenstein.affineSpaltensteinInput A)
  exact (singlyCompactlyGenerated_iff h09SN _).2
    (smallRingObject_isCompactAb_and_isPaperGenerator A)

end AffineExample

end RelativeFM
