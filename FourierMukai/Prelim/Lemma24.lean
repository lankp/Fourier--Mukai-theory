/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Prelim.Lemma25
import FourierMukai.Prelim.Stacks09SN
import WeakApprox.GeneratorBridge

/-!
# Lemma 2.4: compact generation by one object versus localizing generation

**Lemma 2.4** (`lem:localizing_iff_cpt_gen`) of

  E. Guisado Villalgordo, P. Lank, *Relative Fourier--Mukai theory for algebraic spaces*:

in a compactly generated triangulated category `T`, a compact object `G`
compactly generates `T` if and only if the smallest localizing subcategory
containing `G` is all of `T`.

## Rendering

* "`G ∈ T^c`" is `RelativeWeakApprox.IsCompactAb G` (additive compactness).
* "`G` compactly generates `T`" is zero detection by the shifts of `G`:
  `RelativeWeakApprox.IsPaperGenerator G`, i.e. `Hom(G⟦n⟧, E) = 0` for all `n : ℤ`
  implies `IsZero E`.
* "`⟨G⟩‾ = T`" is `ObjectProperty.IsLocalizingGenerator.{w} (singleton G)` of
  `Prelim/Lemma25.lean` (the language of Lemma 2.5): every triangulated,
  isomorphism-closed property closed under `w`-small coproducts and containing `G`
  holds everywhere.  This file also defines the paper's `⟨S⟩‾` itself,
  `localizingClosure P` (the intersection of all such properties), proves that it
  is localizing and contains `P` (so it is the smallest localizing subcategory
  containing `P`), and proves
  `IsLocalizingGenerator P ↔ localizingClosure P = ⊤`
  (`isLocalizingGenerator_iff_localizingClosure_eq_top`).

## What is proved, and what is assumed

* `isPaperGenerator_of_isLocalizingGenerator`: `⟨G⟩‾ = T ⇒ G detects zero`,
  unconditionally (no compactness, no coproducts, no compact generation).  For
  fixed `E`, the objects `A` with `Hom(A, E⟦n⟧) = 0` for all `n` form a localizing
  subcategory; this is `IsLocalizingGenerator.isZero_of_rightOrthogonal` of
  `Prelim/Lemma25.lean`, applied to the shift closure of `G`.
* `lemma_2_4` (headline): for a compact `G` (`RelativeWeakApprox.IsCompactAb`) in a
  pretriangulated category with small coproducts, `IsPaperGenerator G ↔ ⟨G⟩‾ = T`.  The
  converse direction is `StacksInterface.isLocalizingGenerator_of_tag09SN`
  (`Prelim/Stacks09SN.lean`), from the tagged input `StacksInterface.Tag09SN C`
  (Stacks 09SN, AxiomMath's `exists_isHomotopyColimit_of_compactlyGenerated`): every
  object is a homotopy colimit of cells built from sums of shifts of `G`, hence lies in
  every localizing subcategory containing `G`.  This replaces the paper's appeal to
  Neeman's Bousfield localization; the paper's §2.1 cites 09SN for the related fact.
* `singlyCompactlyGenerated_iff` and `lemma_2_5_of_tag09SN`: under 09SN, the rendering
  `SinglyCompactlyGenerated` of Lemma 2.5 is the paper's "compact and detects zero", and
  Lemma 2.5 holds with the paper's hypothesis.
* The secondary route from the named input `HasBousfieldTriangles G` (Bousfield
  triangles, what the paper takes from Neeman, *Triangulated categories*, Remark 1.16,
  Theorem 1.17 and Proposition 9.1.19) was deleted in wave 6 (`results/OPEN_INPUTS.md`
  row 6.16): the headline uses 09SN.

## Deviations from the paper's statement

* Compactness is `RelativeWeakApprox.IsCompactAb` (the additive `Hom(G, -)` preserves
  `Type v₁`-small coproducts), and `⟨G⟩‾` is formed with `Type v₁`-small coproducts.
* The paper's hypothesis "`T` is compactly generated" is not assumed: the proof uses only
  that `G` is compact, that `T` has small coproducts, and 09SN (whose own hypothesis is
  that the given compact family generates).  The Lean statement is stronger in this
  respect.
* The converse direction depends on the tagged Stacks input `Tag09SN C` (row in
  `results/ASSUMPTIONS.md`), with AxiomMath's `IsCompactObject` replaced by `IsCompactAb`
  (see `Prelim/Stacks09SN.lean`).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory Limits Pretriangulated RelativeWeakApprox ZeroObject

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace ObjectProperty

/-- The paper's `⟨S⟩‾` (Section 2.1): the intersection of all triangulated,
isomorphism-closed properties closed under `w`-small coproducts that contain `P`.
By `le_localizingClosure` and the instances below it is the smallest localizing
subcategory containing `P`. -/
def localizingClosure (P : CategoryTheory.ObjectProperty C) :
    CategoryTheory.ObjectProperty C := fun X =>
  ∀ (Q : CategoryTheory.ObjectProperty C), Q.IsTriangulated → Q.IsClosedUnderIsomorphisms →
    (∀ (J : Type w), Q.IsClosedUnderColimitsOfShape (Discrete J)) → P ≤ Q → Q X

variable (P : CategoryTheory.ObjectProperty C)

lemma le_localizingClosure : P ≤ localizingClosure.{w} P :=
  fun _ hX _ _ _ _ hPQ => hPQ _ hX

/-- `localizingClosure P` lies in every localizing property containing `P`. -/
lemma localizingClosure_le (Q : CategoryTheory.ObjectProperty C) [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] [∀ (J : Type w), Q.IsClosedUnderColimitsOfShape (Discrete J)]
    (hPQ : P ≤ Q) : localizingClosure.{w} P ≤ Q :=
  fun _ hX => hX Q inferInstance inferInstance (fun _ => inferInstance) hPQ

instance : (localizingClosure.{w} P).IsClosedUnderIsomorphisms where
  of_iso e hX Q hQ hQiso hQcolim hPQ := Q.prop_of_iso e (hX Q hQ hQiso hQcolim hPQ)

instance (J : Type w) : (localizingClosure.{w} P).IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := by
    rintro X ⟨h⟩ Q hQ hQiso hQcolim hPQ
    exact Q.prop_of_isColimit h.isColimit (fun j => h.prop_diag_obj j Q hQ hQiso hQcolim hPQ)

instance : (localizingClosure.{w} P).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, fun Q hQ hQiso _ _ => by
    obtain ⟨Z, hZ, hQZ⟩ := hQ.exists_zero
    exact Q.prop_of_iso (hZ.iso (isZero_zero C)) hQZ⟩
  isStableUnderShiftBy n := ⟨fun X hX Q hQ hQiso hQcolim hPQ =>
    Q.le_shift n X (hX Q hQ hQiso hQcolim hPQ)⟩
  ext₂' T hT h₁ h₃ := ⟨T.obj₂, fun Q hQ hQiso hQcolim hPQ => by
    have h := Q.ext_of_isTriangulatedClosed₂' T hT (h₁ Q hQ hQiso hQcolim hPQ)
      (h₃ Q hQ hQiso hQcolim hPQ)
    rwa [Q.isoClosure_eq_self] at h, ⟨Iso.refl _⟩⟩

/-- `P` generates by shifts, cones and `w`-small coproducts (`⟨P⟩‾ = T`, in the
universal-property form `IsLocalizingGenerator` of `Prelim/Lemma25.lean`) if and
only if its localizing closure is everything. -/
lemma isLocalizingGenerator_iff_localizingClosure_eq_top :
    IsLocalizingGenerator.{w} P ↔ localizingClosure.{w} P = ⊤ := by
  constructor
  · intro h
    ext X
    simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
    exact fun Q hQ hQiso hQcolim hPQ => h Q hQ hQiso hQcolim hPQ X
  · intro h Q hQ hQiso hQcolim hPQ X
    have hX : localizingClosure.{w} P X := by rw [h]; trivial
    exact hX Q hQ hQiso hQcolim hPQ

end ObjectProperty

open ObjectProperty in
/-- **Lemma 2.4** (`lem:localizing_iff_cpt_gen`), direction `⟨G⟩‾ = T ⇒ G compactly
generates`: if `G` generates by shifts, cones and `w`-small coproducts, then `G`
detects zero objects through its shifts.  No compactness, coproducts or compact
generation is needed.  Reduced to `IsLocalizingGenerator.isZero_of_rightOrthogonal`
(`Prelim/Lemma25.lean`) for the shift closure of `G`. -/
theorem isPaperGenerator_of_isLocalizingGenerator {G : C}
    (hL : ObjectProperty.IsLocalizingGenerator.{w} (ObjectProperty.singleton G)) :
    IsPaperGenerator G := by
  intro E hE
  have hL' : ObjectProperty.IsLocalizingGenerator.{w}
      ((ObjectProperty.singleton G).shiftClosure ℤ) :=
    hL.mono ((ObjectProperty.singleton G).le_shiftClosure (A := ℤ))
  exact hL'.isZero_of_rightOrthogonal ((rightOrthogonal_shiftClosure_singleton_iff G E).2 hE)

section Tag09SN

open StacksInterface

/-- **Lemma 2.4** (`lem:localizing_iff_cpt_gen`), direction `G compactly generates ⇒
⟨G⟩‾ = T`, from Stacks 09SN (`StacksInterface.Tag09SN`, a tagged input): a compact `G`
detecting zero through its shifts lies in no proper localizing subcategory. -/
theorem isLocalizingGenerator_of_isPaperGenerator_of_tag09SN [HasCoproducts.{v₁} C]
    (h09SN : Tag09SN C) {G : C} (hGc : IsCompactAb G) (hG : IsPaperGenerator G) :
    ObjectProperty.IsLocalizingGenerator.{v₁} (ObjectProperty.singleton G) :=
  have : IsCompactAb G := hGc
  isLocalizingGenerator_of_tag09SN h09SN hG

/-- **Lemma 2.4** (`lem:localizing_iff_cpt_gen`).  Let `C` be a pretriangulated category
with small (`Type v₁`-indexed) coproducts satisfying Stacks 09SN, and `G` a compact object
(`RelativeWeakApprox.IsCompactAb`).  Then `G` compactly generates `C` (zero detection by
the shifts of `G`, `IsPaperGenerator G`) if and only if `⟨G⟩‾ = C`.

The paper assumes in addition that `C` is compactly generated; this is not needed.  The
converse direction uses Stacks 09SN in place of Neeman's Bousfield localization (module
docstring). -/
theorem lemma_2_4 [HasCoproducts.{v₁} C] (h09SN : Tag09SN C)
    {G : C} (hG : IsCompactAb G) :
    IsPaperGenerator G ↔
      ObjectProperty.localizingClosure.{v₁} (ObjectProperty.singleton G) = ⊤ :=
  (Iff.intro (isLocalizingGenerator_of_isPaperGenerator_of_tag09SN h09SN hG)
      isPaperGenerator_of_isLocalizingGenerator).trans
    (ObjectProperty.isLocalizingGenerator_iff_localizingClosure_eq_top _)

/-- **Lemma 2.4** (`lem:localizing_iff_cpt_gen`) in the language of Lemma 2.5: under
Stacks 09SN, `G` is a single compact generator in the sense of `SinglyCompactlyGenerated`
(compact and `⟨G⟩‾ = C`) iff it is compact and detects zero through its shifts (the
paper's definition, GL26 §2.1). -/
theorem singlyCompactlyGenerated_iff [HasCoproducts.{v₁} C] (h09SN : Tag09SN C) (G : C) :
    SinglyCompactlyGenerated C G ↔ IsCompactAb G ∧ IsPaperGenerator G :=
  ⟨fun h => ⟨h.1, isPaperGenerator_of_isLocalizingGenerator h.2⟩,
    fun h => ⟨h.1, isLocalizingGenerator_of_isPaperGenerator_of_tag09SN h09SN h.1 h.2⟩⟩

end Tag09SN

section Lemma25Paper

open StacksInterface

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Lemma 2.5** (`lem:equivalence_or_fully_faithful_via_compacts`) with the paper's
hypothesis "compactly generated by a single object" read as in GL26 §2.1: `GT` and `GS`
are compact (`IsCompactAb`) and detect zero objects through their shifts
(`IsPaperGenerator`).  Both categories have small coproducts and satisfy Stacks 09SN
(tagged input), which is the paper's own justification that every object is built from
compacts.  `F ⊣ G` with `F` exact and `G` preserving small coproducts; then `F` is an
equivalence iff its restriction to compact objects is.  Reduced to `lemma_2_5` through
`singlyCompactlyGenerated_iff`. -/
theorem lemma_2_5_of_tag09SN [HasCoproducts.{v₁} C] [HasCoproducts.{v₁} D]
    (h09SN_C : Tag09SN C) (h09SN_D : Tag09SN D)
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (GT : C) (hGTc : IsCompactAb GT) (hGTg : IsPaperGenerator GT)
    (GS : D) (hGSc : IsCompactAb GS) (hGSg : IsPaperGenerator GS)
    [∀ (J : Type v₁), PreservesColimitsOfShape (Discrete J) G]
    [F.CommShift ℤ] [F.IsTriangulated] :
    F.IsEquivalence ↔ (Adjunction.compactRestriction adj).IsEquivalence :=
  lemma_2_5 adj GT ((singlyCompactlyGenerated_iff h09SN_C GT).2 ⟨hGTc, hGTg⟩)
    GS ((singlyCompactlyGenerated_iff h09SN_D GS).2 ⟨hGSc, hGSg⟩)

end Lemma25Paper

end RelativeFM
