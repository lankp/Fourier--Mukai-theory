/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Stacks.Corollaries
import Spaces.Supported.CompactGeneration

/-!
# Non-vacuity of the sum-universe notions on AxiomMath's `D(𝒪_X)`

Sources: Lank--Pauwels (LP26), Theorem 1.1 (`thm:glueing_weak_approx`), §2.1.2; GL26 Lemma A.9
(`lem:preferred_eq_class`).

AxiomMath's derived category `D(𝒪_X)` of an algebraic space (`Spaces.D`, at
`HasDerivedCategory.standard`) has morphisms in `Type (u + 1)` and direct sums indexed by
`Type u`.  The notions of `WeakApprox/SumUniverse.lean` at `w = u` are the ones that fit it.
This file checks CLAUDE.md verification step 5 for them at `w = u`, `v = u + 1`.

## What is proved

* `theorem_1_1_univ_zero_D`: every hypothesis of `theorem_1_1_univ` at `w = u` holds for the
  trivial recollement of the zero subcategory of `D(𝒪_X)`, a category with morphisms in
  `Type (u + 1)`; no input is used.
* `isCompactAb_zero_D`: `0 : D(𝒪_X)` is compact for `Type u`-indexed sums.
* `lemma_A_9_sumUniverse`: for `X` quasi-compact quasi-separated and `T ⊆ |X|` closed with
  quasi-compact complement, `D_{qc,T}(X)` (morphisms in `Type (u + 1)`) has `Type u`-indexed
  direct sums (AxiomMath's, Stacks 08F3) and a single generator `P` that is compact in the
  sense of `SumUniverse.IsCompactAb.{u}`, detects zero objects through its shifts, and
  classically generates the compact objects (`SumUniverse.IsClassicalGeneratorOnCompacts.{u}`).
  From `Spaces.Supported.lemma_A_9` through the bridges of `Spaces/Stacks/Bridges.lean`.
* `lemma_A_9_sumUniverse_affine`: at an affine `X = h_{T₀}` and `T = |X|`, with every
  hypothesis discharged, `D_{qc}(X)` has `Type u`-indexed direct sums and an
  `IsCompactAb.{u}` object (the perfect generator).

## Assumptions

`theorem_1_1_univ_zero_D` and `isCompactAb_zero_D`: none.  `lemma_A_9_sumUniverse` and
`lemma_A_9_sumUniverse_affine`: the tagged AxiomMath inputs of `Spaces/Supported/Inputs.lean`
and `Spaces.Tag06UQInput` already used by `Spaces.Supported.lemma_A_9` (08F3, 0AEC, 0AED,
0GFD, the two remarks preceding 0AED, 03JX, `BigFppfSite.contains_terminal`), all AxiomMath
theorems discharged in `SpacesVerified` or to be.  No new input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Space RelativeWeakApprox
open scoped ZeroObject

namespace RelativeFM.Spaces.Stacks

universe u

section D

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **LP26 Theorem 1.1** for a coproduct universe `w` (`theorem_1_1_univ`), non-vacuity at
`w = u` on AxiomMath's `D(𝒪_X)`, whose morphisms are in `Type (u + 1)`: the trivial recollement
`0 → ZeroSub D(𝒪_X) → ZeroSub D(𝒪_X)` meets every hypothesis (`theorem_1_1_univ_zero`). -/
theorem theorem_1_1_univ_zero_D (X : AlgebraicSpaces B S hS) :
    SumUniverse.SatisfiesPaperWA.{u}
        (PaperHypothesesW6.NonVacuity.ZeroSub (Spaces.D B S hS X)) ↔
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
        ∀ f : (⟨0, isZero_zero _⟩ : PaperHypothesesW6.NonVacuity.ZeroSub (Spaces.D B S hS X)) ⟶
          (⟨0, isZero_zero _⟩ : PaperHypothesesW6.NonVacuity.ZeroSub (Spaces.D B S hS X))⟦n⟧,
          f = 0 :=
  theorem_1_1_univ_zero.{u} (Spaces.D B S hS X)

/-- The zero object of AxiomMath's `D(𝒪_X)` is compact for `Type u`-indexed direct sums
(`SumUniverse.IsCompactAb.{u}`), equivalently AxiomMath's `IsCompactObject.{u}`. -/
theorem isCompactAb_zero_D (X : AlgebraicSpaces B S hS) :
    SumUniverse.IsCompactAb.{u} (0 : Spaces.D B S hS X) ∧
      IsCompactObject.{u} (0 : Spaces.D B S hS X) :=
  ⟨SumUniverse.isCompactAb_of_isZero (isZero_zero _),
    (isCompactObject_iff_sumUniverse_isCompactAb _).2
      (SumUniverse.isCompactAb_of_isZero (isZero_zero _))⟩

end D

section Supported

open RelativeFM.Spaces.Supported

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **GL26 Lemma A.9** (`lem:preferred_eq_class`), generation part, in the notions of
`WeakApprox/SumUniverse.lean` at `w = u`: for `X` quasi-compact quasi-separated and `T ⊆ |X|`
closed with `|X| ∖ T` quasi-compact, `D_{qc,T}(X)` (morphisms in `Type (u + 1)`) has
`Type u`-indexed direct sums and a generator `P` that is compact for those sums
(`SumUniverse.IsCompactAb.{u}`), detects zero objects through its shifts, and classically
generates the compact objects (`SumUniverse.IsClassicalGeneratorOnCompacts.{u}`).  From
`Spaces.Supported.lemma_A_9` (Stacks 08F3, 0AEC, 0AED, 0GFD) and the bridges
`isCompactObject_iff_sumUniverse_isCompactAb`,
`isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq_univ`.  The preferred-class clause of
Lemma A.9 is not included (`Spaces/Supported/CompactGeneration.lean`). -/
theorem lemma_A_9_sumUniverse (h08F3 : Tag08F3Input B S hS)
    (hsum : SupportedDirectSumsInput B S hS)
    (h0AEC : Tag0AECInput B S hS) (h0AED : Tag0AEDInput B S hS) (h0GFD : Tag0GFDInput B S hS)
    (X : AlgebraicSpaces B S hS) [(qcohDerived X).IsTriangulated]
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) :
    HasCoproducts.{u} (DqcZ X T) ∧
      ∃ P : DqcZ X T, SumUniverse.IsCompactAb.{u} P ∧ IsPaperGenerator P ∧
        SumUniverse.IsClassicalGeneratorOnCompacts.{u} P := by
  obtain ⟨hcop, ⟨P, -, hPc, hPg, htri⟩, -⟩ :=
    lemma_A_9 h08F3 hsum h0AEC h0AED h0GFD X hXqc hZ hXqs T hT hTc
  have := hcop
  have hPc' := (isCompactObject_iff_sumUniverse_isCompactAb P).1 hPc
  exact ⟨hcop, P, hPc', hPg,
    (isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq_univ P hPc').2 htri⟩

/-- Non-vacuity of `lemma_A_9_sumUniverse`: at an affine `X = h_{T₀}` and `T = |X|`, every
hypothesis is discharged (from the inputs only, the two instance arguments by 06UQ and
`SupportTriangulatedInput`), so `D_{qc}(X)`, a category with morphisms in `Type (u + 1)`, has
`Type u`-indexed direct sums and a `SumUniverse.IsCompactAb.{u}` object, the perfect generator
of `lemma_A_9_sumUniverse` (its generation clauses need the triangulated structure in the
statement, which the inputs only supply inside the proof; they are those of
`lemma_A_9_sumUniverse`). -/
theorem lemma_A_9_sumUniverse_affine (h06 : Tag06UQInput B S hS)
    (hsupp : SupportTriangulatedInput B S hS)
    (h08F3 : Tag08F3Input B S hS) (hsum : SupportedDirectSumsInput B S hS)
    (h0AEC : Tag0AECInput B S hS) (h0AED : Tag0AEDInput B S hS) (h0GFD : Tag0GFDInput B S hS)
    (hqs : AffineQuasiSeparatedInput B S hS) (hterm : ContainsTerminalInput.{u})
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    HasCoproducts.{u} (DqcZ (representedSpace T₀) Set.univ) ∧
      ∃ P : DqcZ (representedSpace T₀) Set.univ, SumUniverse.IsCompactAb.{u} P := by
  have := isTriangulated_qcohDerived h06 (representedSpace T₀)
  have := isTriangulated_support hsupp (representedSpace T₀) Set.univ
  obtain ⟨hqc, hqs', hcl, hco⟩ := nonVacuity_affine_univ hqs (hterm B) T₀ hT₀
  obtain ⟨hcop, P, hP, -⟩ := lemma_A_9_sumUniverse h08F3 hsum h0AEC h0AED h0GFD
    (representedSpace T₀) hqc (hterm B) hqs' Set.univ hcl hco
  exact ⟨hcop, P, hP⟩

end Supported

end RelativeFM.Spaces.Stacks

#print axioms RelativeFM.Spaces.Stacks.theorem_1_1_univ_zero_D
#print axioms RelativeFM.Spaces.Stacks.isCompactAb_zero_D
#print axioms RelativeFM.Spaces.Stacks.lemma_A_9_sumUniverse
#print axioms RelativeFM.Spaces.Stacks.lemma_A_9_sumUniverse_affine
