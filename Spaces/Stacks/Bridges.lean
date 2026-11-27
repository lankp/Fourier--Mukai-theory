/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import StacksFrontier.CategoryTheory.Triangulated.CompactObjects.ThickSubcategory
import StacksFrontier.CategoryTheory.Triangulated.Generators
import WeakApprox.CompactAb
import WeakApprox.GeneratorBridge
import WeakApprox.Lemma43
import WeakApprox.CompactThick
import WeakApprox.SumUniverse

/-!
# Bridges between AxiomMath/Stacks' categorical notions and the repository's

The categorical Stacks results that GL26 and LP26 use (Stacks 09SR, 09SN) are theorems of
AxiomMath/Stacks, stated with AxiomMath's notions of compact object, weak generator and
classical generator of the compact objects.  The repository states the same results with
its own notions (LP26 §2.1.2, GL26 §2.1).  This file proves that the notions agree, so
that `Spaces/Stacks/Tags.lean` can discharge the repository's `Prop`s
`OpenClosedCompletionW3.Tag09SRPaper` and `StacksInterface.Tag09SN` from AxiomMath's
theorems (gap C.10 of `results/AXIOMMATH_MAP.md`).

## What is proved

* `isCompactObject_iff_sumUniverse_isCompactAb`: for **any coproduct universe `w`**,
  independent of the Hom universe `v`, AxiomMath's `CategoryTheory.IsCompactObject.{w} K`
  (Stacks 07LS: for every `Type w`-indexed family with a coproduct,
  `⨁ i, (K ⟶ E i) → (K ⟶ ∐ E)` is bijective) is the repository's
  `RelativeWeakApprox.SumUniverse.IsCompactAb.{w} K` (`WeakApprox/SumUniverse.lean`).  At
  `w = u`, `v = u + 1` this is compactness in AxiomMath's `D(𝒪_X)`.
* `isCompactObject_iff_isCompactAb`: the case `w = v`, where `SumUniverse.IsCompactAb.{v}` is
  `RelativeWeakApprox.IsCompactAb K` (the `AddCommGrpCat`-valued `Hom(K, -)` preserves
  `Type v`-indexed coproducts; `SumUniverse.isCompactAb_iff`).  No coproducts are assumed in
  `C`.
* `isWeakTriangulatedGenerator_singleton_iff`: AxiomMath's
  `(ObjectProperty.singleton G).IsWeakTriangulatedGenerator` (Stacks 09SJ(3)) is
  `RelativeWeakApprox.IsPaperGenerator G` (zero detection by the shifts of `G`).
* `rightOrthogonal_ofObj_isZero_iff_isWeakTriangulatedGenerator`: the hypothesis of
  AxiomMath's 09SN, for a family `E`, is `(ObjectProperty.ofObj E).IsWeakTriangulatedGenerator`.
* `isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq_univ`: for a pretriangulated `C` with
  `Type w`-indexed coproducts and a compact `G` (`SumUniverse.IsCompactAb.{w}`),
  `SumUniverse.IsClassicalGeneratorOnCompacts.{w} G` is
  `(singleton G).triangEnvelope = IsCompactObject.{w}`; the compact objects form a thick
  subcategory by AxiomMath's `isTriangulated_isCompactObject` and `isCompactObject_of_retract`
  (`ThickSubcategory`, on the import list).
* `isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq`: for a pretriangulated `C` and
  a compact `G`, the repository's `IsClassicalGeneratorOnCompacts G` (every compact object
  lies in the thick envelope of `G`) is AxiomMath's `(singleton G).triangEnvelope =
  IsCompactObject.{v}` (the form of "`⟨G⟩ = D_c`" in AxiomMath's 09SR).  The inequality
  `⟨G⟩ ≤ D_c` is automatic: the compact objects form a triangulated subcategory stable
  under retracts (`RelativeWeakApprox.isCompactAb_of_mem_triangEnvelope`, proved in the
  tree without coproducts).

## Assumptions

None.  AxiomMath/Stacks is the pinned dependency of the `Spaces` library; the modules
imported here (`ThickSubcategory`, `Generators`) are on
`scripts/axiommath/spaces-imports.txt`.
-/

namespace RelativeFM.Spaces.Stacks

open CategoryTheory CategoryTheory.Limits RelativeWeakApprox

universe w v u

section Compact

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **Stacks 07LS** (bridge, any coproduct universe `w`): AxiomMath's compactness
`IsCompactObject.{w} K` is the repository's `SumUniverse.IsCompactAb.{w} K`; the two are the
same condition (bijectivity of `⨁ i, (K ⟶ E i) → (K ⟶ ∐ E)` for `Type w`-indexed families).
The coproduct universe `w` is independent of the Hom universe `v`. -/
theorem isCompactObject_iff_sumUniverse_isCompactAb (K : C) :
    IsCompactObject.{w} K ↔ SumUniverse.IsCompactAb.{w} K :=
  ⟨fun h => ⟨h.bijective_toAddMonoid_rightComp_sigmaι⟩, fun h => ⟨h.bijective⟩⟩

/-- **Stacks 07LS** (bridge): for an object `K` of a preadditive category with Hom
universe `v`, AxiomMath's `IsCompactObject.{v} K` is the repository's `IsCompactAb K`.
No coproducts in `C` are assumed.  The case `w = v` of
`isCompactObject_iff_sumUniverse_isCompactAb`, with `SumUniverse.isCompactAb_iff`. -/
theorem isCompactObject_iff_isCompactAb (K : C) :
    IsCompactObject.{v} K ↔ IsCompactAb K :=
  (isCompactObject_iff_sumUniverse_isCompactAb K).trans (SumUniverse.isCompactAb_iff K)

/-- **Stacks 07LS** (bridge, one direction): AxiomMath's compactness
`IsCompactObject.{v} K` implies the repository's `IsCompactAb K`. -/
theorem isCompactAb_of_isCompactObject {K : C} (hK : IsCompactObject.{v} K) :
    IsCompactAb K :=
  (isCompactObject_iff_isCompactAb K).1 hK

/-- **Stacks 07LS** (bridge, other direction): the repository's `IsCompactAb K` implies
AxiomMath's compactness `IsCompactObject.{v} K`. -/
theorem isCompactObject_of_isCompactAb {K : C} (hK : IsCompactAb K) :
    IsCompactObject.{v} K :=
  (isCompactObject_iff_isCompactAb K).2 hK

/-- The two compactness properties of objects coincide. -/
theorem isCompactObject_eq_isCompactAb :
    (IsCompactObject.{v, v, u} (C := C) : ObjectProperty C) = fun K => IsCompactAb K := by
  funext K
  exact propext (isCompactObject_iff_isCompactAb K)

end Compact

section Generator

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- **Stacks 09SJ(3)** (bridge): AxiomMath's weak generator
`(ObjectProperty.singleton G).IsWeakTriangulatedGenerator` is the paper's generation
condition `IsPaperGenerator G` (LP26 §2.1.2, GL26 §2.1): an object receiving only zero
maps from the shifts of `G` is zero. -/
theorem isWeakTriangulatedGenerator_singleton_iff (G : C) :
    (ObjectProperty.singleton G).IsWeakTriangulatedGenerator ↔ IsPaperGenerator G := by
  constructor
  · intro h E hE
    exact h E ((rightOrthogonal_shiftClosure_singleton_iff G E).2 hE)
  · intro h K hK
    exact h ((rightOrthogonal_shiftClosure_singleton_iff G K).1 hK)

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The hypothesis of AxiomMath's 09SN for a family `E` is AxiomMath's weak generation
by `ObjectProperty.ofObj E` (definitional). -/
theorem rightOrthogonal_ofObj_isZero_iff_isWeakTriangulatedGenerator {ι : Type*}
    (E : ι → C) :
    (∀ Y : C, ((ObjectProperty.ofObj E).shiftClosure ℤ).rightOrthogonal Y → IsZero Y) ↔
      (ObjectProperty.ofObj E).IsWeakTriangulatedGenerator :=
  Iff.rfl

/-- The triangulated envelope of a compact object consists of compact objects: the
`IsCompactAb` objects form a triangulated subcategory stable under retracts
(`RelativeWeakApprox.isCompactAb_of_mem_triangEnvelope`, `WeakApprox/CompactThick.lean`;
no coproducts needed), and the two compactness notions agree. -/
theorem triangEnvelope_singleton_le_isCompactObject (G : C) (hG : IsCompactAb G) :
    (ObjectProperty.singleton G).triangEnvelope ≤ IsCompactObject.{v, v, u} (C := C) :=
  fun _ hX => isCompactObject_of_isCompactAb (isCompactAb_of_mem_triangEnvelope hG hX)

/-- **Classical generation of the compact objects** (bridge): for a compact `G`, the
repository's `IsClassicalGeneratorOnCompacts G` (every `IsCompactAb` object lies in the
triangulated envelope of `G`) is AxiomMath's `(singleton G).triangEnvelope =
IsCompactObject.{v}` (the form of "`⟨G⟩ = D_c`" in AxiomMath's 09SR). -/
theorem isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq (G : C) (hG : IsCompactAb G) :
    IsClassicalGeneratorOnCompacts G ↔
      (ObjectProperty.singleton G).triangEnvelope = IsCompactObject.{v, v, u} (C := C) := by
  constructor
  · intro h
    refine le_antisymm (triangEnvelope_singleton_le_isCompactObject G hG) fun X hX => ?_
    exact h X (isCompactAb_of_isCompactObject hX)
  · intro h X hX
    rw [h]
    exact isCompactObject_of_isCompactAb hX

end Generator

section GeneratorUniv

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproducts.{w} C]

/-- The triangulated envelope of a compact object consists of compact objects, for any
coproduct universe `w`: AxiomMath's `IsCompactObject.{w}` is a triangulated subcategory
(`isTriangulated_isCompactObject`) stable under retracts (`isCompactObject_of_retract`). -/
theorem triangEnvelope_singleton_le_isCompactObject_univ (G : C)
    (hG : SumUniverse.IsCompactAb.{w} G) :
    (ObjectProperty.singleton G).triangEnvelope ≤ IsCompactObject.{w, v, u} (C := C) := by
  have := isTriangulated_isCompactObject.{w} (D := C)
  have : ObjectProperty.IsStableUnderRetracts (IsCompactObject.{w, v, u} (C := C)) :=
    ⟨fun r h => isCompactObject_of_retract h r.i r.r r.retract⟩
  refine (ObjectProperty.triangEnvelope_le_iff _).2 fun X hX => ?_
  obtain rfl : G = X := (ObjectProperty.singleton_iff _ _).1 hX
  exact (isCompactObject_iff_sumUniverse_isCompactAb G).2 hG

/-- **Classical generation of the compact objects** (bridge, any coproduct universe `w`): for
a compact `G`, `SumUniverse.IsClassicalGeneratorOnCompacts.{w} G` (every compact object lies
in the triangulated envelope of `G`) is AxiomMath's
`(singleton G).triangEnvelope = IsCompactObject.{w}`. -/
theorem isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq_univ (G : C)
    (hG : SumUniverse.IsCompactAb.{w} G) :
    SumUniverse.IsClassicalGeneratorOnCompacts.{w} G ↔
      (ObjectProperty.singleton G).triangEnvelope = IsCompactObject.{w, v, u} (C := C) := by
  constructor
  · intro h
    refine le_antisymm (triangEnvelope_singleton_le_isCompactObject_univ G hG) fun X hX => ?_
    exact h X ((isCompactObject_iff_sumUniverse_isCompactAb X).1 hX)
  · intro h X hX
    rw [h]
    exact (isCompactObject_iff_sumUniverse_isCompactAb X).2 hX

end GeneratorUniv

end RelativeFM.Spaces.Stacks

#print axioms RelativeFM.Spaces.Stacks.isCompactObject_iff_sumUniverse_isCompactAb
#print axioms RelativeFM.Spaces.Stacks.isCompactObject_iff_isCompactAb
#print axioms RelativeFM.Spaces.Stacks.isWeakTriangulatedGenerator_singleton_iff
#print axioms RelativeFM.Spaces.Stacks.isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq
#print axioms RelativeFM.Spaces.Stacks.isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq_univ
