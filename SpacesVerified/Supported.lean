/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces
import SpacesVerified.Discharge
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectSums
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedQuasicoherentDerived
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectGenerator
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedCompactPerfect
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectClassicalGenerator
import StacksFrontier.AlgebraicGeometry.Spaces.AbsolutelyQuasiSeparatedAffine
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated

/-!
# Discharge of the tagged inputs for `D_{qc,Z}(X)`; GL26 Lemma A.9, generation part

The eight tagged AxiomMath inputs of `Spaces/Supported/Inputs.lean` are proved here by the
AxiomMath/Stacks declarations they name (commit `f56a316`), so that **GL26 Lemma A.9**
(`lem:preferred_eq_class`), in the form of `Spaces.Supported.lemma_A_9` (direct sums, a single
compact perfect generator whose thick envelope is the compact objects, compact = perfect), holds
with nothing assumed: `lemma_A_9_unconditional`, with the non-vacuity witness
`lemma_A_9_affine_univ_unconditional`.

| input | Stacks | proved by |
|---|---|---|
| `Tag08F3Input` | 08F3 | `AlgebraicGeometry.Space.hasCoproducts_quasicoherentDerivedCategory_ringUniverse` |
| `SupportTriangulatedInput` | 0AED (remark), 08GF | `AlgebraicGeometry.Space.isTriangulated_cohomologySupportedOn` |
| `SupportedDirectSumsInput` | 0AED (remark) | `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentDerivedSupportedOn` |
| `Tag0AECInput` | 0AEC | `AlgebraicGeometry.Space.exists_isPerfect_generator_of_supported` |
| `Tag0AEDInput` | 0AED | `AlgebraicGeometry.Space.isCompactObject_iff_isPerfect_of_supported` |
| `Tag0GFDInput` | 0GFD | `AlgebraicGeometry.Space.triangEnvelope_singleton_eq_isPerfect_of_supported` |
| `AffineQuasiSeparatedInput` | 03JX (ι), 03BS (3) | `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_yoneda_of_isAffine` |
| `ContainsTerminalInput` | — | `AlgebraicGeometry.BigFppfSite.contains_terminal` |

The instance context is AxiomMath's, as in `Spaces/Supported/Inputs.lean`.

**Difference from the paper** (as for `Spaces.Supported.lemma_A_9`): the clause of Lemma A.9 on
the preferred equivalence class of `t`-structures is not part of the statement.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Space RelativeWeakApprox

namespace RelativeFM.SpacesVerified

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify
  AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

open RelativeFM.Spaces.Supported

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 08F3**, proved: `D_QCoh(𝒪_F)` has direct sums indexed by `Type u`. -/
theorem tag08F3 : Tag08F3Input B S hS := fun F hF =>
  hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS F hF

/-- `D_T(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`, proved. -/
theorem supportTriangulated : SupportTriangulatedInput B S hS := fun X T =>
  isTriangulated_cohomologySupportedOn X T

/-- `D_{QCoh,T}(𝒪_X)` is closed under direct sums in `D_QCoh(𝒪_X)` for `T` closed, proved. -/
theorem supportedDirectSums : SupportedDirectSumsInput B S hS := fun X T hT J =>
  isClosedUnderColimitsOfShape_quasicoherentDerivedSupportedOn X T hT J

/-- **Stacks 0AEC**, proved: a single perfect generator of `D_{QCoh,T}(𝒪_X)`. -/
theorem tag0AEC : Tag0AECInput B S hS := fun _ X hXqc hXqs T hT hTc =>
  exists_isPerfect_generator_of_supported B S hS X hXqc hXqs T hT hTc

/-- **Stacks 0AED**, proved: compact objects of `D_{QCoh,T}(𝒪_X)` are the perfect ones. -/
theorem tag0AED : Tag0AEDInput B S hS := fun _ X hXqc hXqs T hT hTc E =>
  isCompactObject_iff_isPerfect_of_supported X hXqc hXqs T hT hTc E

/-- **Stacks 0GFD**, proved: a perfect generator classically generates the perfect objects. -/
theorem tag0GFD : Tag0GFDInput B S hS :=
  fun _ X _ hXqc hXqs T _ hT hTc G hG hGq hGs hgen =>
    triangEnvelope_singleton_eq_isPerfect_of_supported X hXqc hXqs T hT hTc G hG hGq hGs hgen

/-- **Stacks 03JX (ι), 03BS (3)**, proved: an affine object represents an absolutely
quasi-separated algebraic space. -/
theorem affineQuasiSeparatedYoneda : Spaces.Supported.AffineQuasiSeparatedInput B S hS :=
  fun hZ T hT => isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS hZ T hT

/-- A big fppf site contains `Spec ℤ`, proved. -/
theorem containsTerminal : ContainsTerminalInput.{u} := fun B => B.contains_terminal

variable {B S hS}

/-- `D_QCoh(𝒪_X)` is triangulated (Stacks 06UQ, proved in `SpacesVerified/Discharge.lean`), as
an instance in the context of this file. -/
theorem isTriangulated_qcohDerived' (X : AlgebraicSpaces B S hS) :
    (qcohDerived X).IsTriangulated :=
  isTriangulated_qcohDerived (tag06UQ B S hS) X

/-- `D_T(𝒪_X)` is triangulated (`supportTriangulated`), as an instance in this file. -/
theorem isTriangulated_support' (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) :
    ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T) :=
  supportTriangulated B S hS X T

attribute [local instance] isTriangulated_qcohDerived' isTriangulated_support'

/-- **GL26 Lemma A.9** (`lem:preferred_eq_class`), generation part, unconditional.  Let `X` be a
quasi-compact quasi-separated algebraic space and `T ⊆ |X|` closed with `|X| ∖ T`
quasi-compact.  Then `D_{qc,T}(X)` has small direct sums, a single compact generator `P` which
is a perfect complex and whose thick envelope is the subcategory of compact objects, and its
compact objects are exactly the perfect complexes.  `Spaces.Supported.lemma_A_9` with its tagged
inputs (08F3, 0AEC, 0AED, 0GFD and the direct-sum remark) and its two instance arguments
(06UQ, `SupportTriangulatedInput`) proved.  **Difference from the paper**: the
preferred-equivalence-class clause is not included (`Spaces/Supported/CompactGeneration.lean`). -/
theorem lemma_A_9_unconditional (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) :
    HasCoproducts.{u} (DqcZ X T) ∧
      (∃ P : DqcZ X T, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect ((ιZ X T).obj P) ∧
        IsCompactObject.{u} P ∧ IsPaperGenerator P ∧
        (ObjectProperty.singleton P).triangEnvelope =
          IsCompactObject.{u, u + 1, u + 1} (C := DqcZ X T)) ∧
      ∀ E : DqcZ X T, IsCompactObject.{u} E ↔
        (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect ((ιZ X T).obj E) :=
  lemma_A_9 (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0AEC B S hS) (tag0AED B S hS)
    (tag0GFD B S hS) X hXqc hZ hXqs T hT hTc

/-- **Non-vacuity of GL26 Lemma A.9**, unconditional: at an affine `X = h_{T₀}` with `Z = |X|`
every hypothesis holds, and `D_{qc,|X|}(X)` has small direct sums and a compact perfect object
(`Spaces.Supported.lemma_A_9_affine_univ` with its inputs proved). -/
theorem lemma_A_9_affine_univ_unconditional
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    HasCoproducts.{u} (DqcZ (representedSpace T₀) Set.univ) ∧
      ∃ P : DqcZ (representedSpace T₀) Set.univ,
        (smallEtaleRingedSite B S hS (representedSpace T₀).1 (representedSpace T₀).2).IsPerfect
          ((ιZ _ _).obj P) ∧ IsCompactObject.{u} P :=
  lemma_A_9_affine_univ (tag06UQ B S hS) (supportTriangulated B S hS) (tag08F3 B S hS)
    (supportedDirectSums B S hS) (tag0AEC B S hS) (tag0AED B S hS) (tag0GFD B S hS)
    (affineQuasiSeparatedYoneda B S hS) containsTerminal T₀ hT₀

end RelativeFM.SpacesVerified

#print axioms RelativeFM.SpacesVerified.tag08F3
#print axioms RelativeFM.SpacesVerified.supportTriangulated
#print axioms RelativeFM.SpacesVerified.supportedDirectSums
#print axioms RelativeFM.SpacesVerified.tag0AEC
#print axioms RelativeFM.SpacesVerified.tag0AED
#print axioms RelativeFM.SpacesVerified.tag0GFD
#print axioms RelativeFM.SpacesVerified.affineQuasiSeparatedYoneda
#print axioms RelativeFM.SpacesVerified.containsTerminal
#print axioms RelativeFM.SpacesVerified.lemma_A_9_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_9_affine_univ_unconditional
