/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Stacks.Bridges
import StacksFrontier.CategoryTheory.Triangulated.CompactObjects.CellStructure
import StacksFrontier.CategoryTheory.Triangulated.CompactObjects.CompactGenerators
import FourierMukai.Scheme.OpenClosedCompletion
import FourierMukai.Prelim.Stacks09SN

/-!
# Stacks 09SR and 09SN, discharged from AxiomMath/Stacks

The repository carried two categorical Stacks results as `Prop`-valued hypotheses:

* `RelativeFM.OpenClosedCompletionW3.Tag09SRPaper C` (`Scheme/OpenClosedCompletion.lean`):
  **Stacks Tag 09SR**, direction "compact generator ⇒ classical generator of the
  compacts", single generator;
* `RelativeFM.StacksInterface.Tag09SN D` (`Prelim/Stacks09SN.lean`): **Stacks Tag 09SN**,
  every object of a compactly generated category is a homotopy colimit of cells.

Both are theorems of AxiomMath/Stacks:

* 09SR is
  `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated`
  (`StacksFrontier/CategoryTheory/Triangulated/CompactObjects/CompactGenerators.lean`);
* 09SN is `CategoryTheory.Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated`
  (`StacksFrontier/CategoryTheory/Triangulated/CompactObjects/CellStructure.lean`).

This file proves the repository's two `Prop`s from those theorems, through the bridges of
`Spaces/Stacks/Bridges.lean` (`IsCompactObject.{v} ↔ IsCompactAb`,
`IsWeakTriangulatedGenerator (singleton G) ↔ IsPaperGenerator G`,
`(singleton G).triangEnvelope = IsCompactObject.{v} ↔ IsClassicalGeneratorOnCompacts G`).

## Comparison with AxiomMath's hypotheses

* **09SN.**  `Tag09SN D` has exactly AxiomMath's typeclass hypotheses (`D` pretriangulated,
  `HasCoproducts.{v} D`) and AxiomMath's conclusion; the repository's
  `StacksInterface.IsHomotopyColimit` is AxiomMath's `Pretriangulated.IsHomotopyColimit`
  verbatim (the two `HasCoproduct F.obj` instances are equal, being proofs of a `Prop`).
  `tag09SN` holds for every such `D`; nothing is lost.
* **09SR.**  AxiomMath's theorem assumes `[IsTriangulated D]` (the octahedron axiom: the
  triangulated envelope is closed under extensions only there).  The repository's
  `Tag09SRPaper C` is stated under the same `[IsTriangulated C]`, so `tag09SRPaper` proves it
  exactly as AxiomMath states the tag; nothing is lost and nothing is strengthened.
-/

namespace RelativeFM.Spaces.Stacks

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated RelativeWeakApprox

universe v u

/-- **Stacks Tag 09SR** (direction "compact generator ⇒ `⟨G⟩ = D_c`"), proved from
AxiomMath/Stacks: in a triangulated category with `Type v`-indexed coproducts, a compact
object `G` detecting zero objects through its shifts classically generates the compact
objects: every compact object lies in the triangulated (thick) envelope of `G`.

This is AxiomMath's
`ObjectProperty.isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated`
read through the bridges of `Spaces/Stacks/Bridges.lean`. -/
theorem isClassicalGeneratorOnCompacts_of_isPaperGenerator
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [HasCoproducts.{v} C] {G : C} (hGc : IsCompactAb G) (hGg : IsPaperGenerator G) :
    IsClassicalGeneratorOnCompacts G := by
  have : IsCompactObject.{v} G := isCompactObject_of_isCompactAb hGc
  have h :=
    (ObjectProperty.isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated
      G).1 ((isWeakTriangulatedGenerator_singleton_iff G).2 hGg)
  exact (isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq G hGc).2 h.1

/-- **Stacks Tag 09SR**: the repository's `Prop` `OpenClosedCompletionW3.Tag09SRPaper C`
holds for every triangulated category `C`, by AxiomMath/Stacks.  The repository's `Prop`
does not assume `IsTriangulated C`; AxiomMath's theorem does (module docstring). -/
theorem tag09SRPaper (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] : OpenClosedCompletionW3.Tag09SRPaper C := by
  intro hcop G hGc hGg
  have := hcop
  exact isClassicalGeneratorOnCompacts_of_isPaperGenerator hGc hGg

/-- **Stacks Tag 09SR**, in the hypothesis form of LP26 Theorem 1.1
(`PaperHypothesesW6.theorem_1_1_paper`, arguments `h09SR`, `h09SRZ`). -/
theorem tag09SR_paperForm (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [HasCoproducts.{v} C] :
    ∀ G : C, IsPaperGenerator G → IsCompactAb G → IsClassicalGeneratorOnCompacts G :=
  fun _ hGg hGc => isClassicalGeneratorOnCompacts_of_isPaperGenerator hGc hGg

/-- **Stacks Tag 09SN** (`lemma-write-as-colimit`): the repository's `Prop`
`StacksInterface.Tag09SN D` holds for every pretriangulated category `D` with
`Type v`-indexed coproducts, by AxiomMath/Stacks
`Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated`.  The hypotheses are
AxiomMath's; the compactness of the family is converted by
`isCompactObject_of_isCompactAb`. -/
theorem tag09SN (D : Type u) [Category.{v} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    [HasCoproducts.{v} D] : StacksInterface.Tag09SN D := by
  intro ι E hE hgen X
  have : ∀ i, IsCompactObject.{v} (E i) := fun i => isCompactObject_of_isCompactAb (hE i)
  obtain ⟨F, hF, h0, hn⟩ := exists_isHomotopyColimit_of_compactlyGenerated E hgen X
  exact ⟨F, hF, h0, hn⟩

end RelativeFM.Spaces.Stacks

#print axioms RelativeFM.Spaces.Stacks.isClassicalGeneratorOnCompacts_of_isPaperGenerator
#print axioms RelativeFM.Spaces.Stacks.tag09SRPaper
#print axioms RelativeFM.Spaces.Stacks.tag09SR_paperForm
#print axioms RelativeFM.Spaces.Stacks.tag09SN
