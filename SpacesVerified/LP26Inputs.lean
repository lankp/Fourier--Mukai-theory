/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces
import SpacesVerified.Supported
import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportedVanishing
import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackSupport
import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardSupport
import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupportEtaleRestriction
import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBoundedBelow
import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
import StacksFrontier.AlgebraicGeometry.Spaces.ModuleSectionsWithSupport
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqs
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CompactHomVanishing
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DetectingBoundedBelow
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.EnlargementInduction
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompactQcqs
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedAffinePullbackGenerator
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplementClauses
import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomologyEquivalence
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardDirectSums
import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
import StacksFrontier.AlgebraicGeometry.Spaces.VanishingAboveTheDimensionInduction
import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsTriangulatedSubcategory
import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitudeGeneral
import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles
import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentabilityShrinkHoms
import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts

/-!
# Discharge of the tagged inputs of LP26 §5 and of the preferred class of GL26 Lemma A.9

Every tagged AxiomMath input of `Spaces/LP26/Inputs.lean`, and the two inputs added to
`Spaces/Supported/Inputs.lean` for the preferred-class clause of GL26 Lemma A.9
(`Tag0GFIInput`, `PerfectBoundedAboveInput`), is proved here by the AxiomMath/Stacks declaration
it names (commit `f56a316`).  Each discharge is that declaration applied to the input's binders
(named arguments where AxiomMath's binders are section variables), so that it typechecks is the
check that the input's statement is AxiomMath's, up to unfolding the AxiomMath abbreviations the
input writes out by their bodies.

| input | Stacks | proved by (`AlgebraicGeometry.Space.` unless stated) |
|---|---|---|
| `Supported.Tag0GFIInput` | 0GFI | `exists_isGE_of_lowHomVanishingOnCompact` |
| `Supported.PerfectBoundedAboveInput`, `LP26.PerfectBoundedAboveInput` | (08G8) | `exists_isLE_of_isPerfect` |
| `Tag09M8Input` | 09M8 | `isCompactObject_iff_isPerfect` |
| `Tag09MBInput` | 09MB (1) | `exists_hom_eq_zero_of_isCompactObject` |
| `Tag08FBInput` | 08FB | `preservesColimit_derivedModulePushforward` |
| `Tag08FABoundInput` | 08FA (2) | `exists_isLE_derivedModulePushforward_obj` |
| `Tag0AFJInput` | 0AFJ | `derivedCategoryB_supportedModules_derivedPushforward` |
| `PerfectPseudoCoherentInput` | 08G8 | `AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isPerfect_general` |
| `Tag08FVTwoInput` | 08FV (2) | `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_two_general` |
| `PseudoCoherentFromOfIsLEInput` | (08FT) | `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isLE_sub_one` |
| `Tag08FU2Input` | 08FU (2) | `AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom` |
| `PerfectQcohInput` | (08G8) | `qcohDerived_of_isPerfect_derivedCategoryB` |
| `Tag08HPInput` | 08HP | `approximationByPerfectComplexes_of_qcqs` |
| `Tag073BInput` | 073B (1) | `isQuasiCompact_of_isQuasiCompactSpace` |
| `OpenSubspaceQuasiCompactInput` | 06RV, 03IR, 03E4 | `isQuasiCompactSpace_of_isCompact_range` |
| `Tag08IKInput` | 08IK | `isPseudoCoherent_iff_of_isNoetherian` |
| `Tag079QInput` | 079Q | `Stacks.ModulesOnACategory.CartesianSubcategory.locallySmall_derivedCategory` |
| `Tag0A8GInput` | 0A8G | `CategoryTheory.Pretriangulated.isLeftAdjoint_of_compact_generator` |
| `RightAdjointCoproductsInput` | (08DZ) | `CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map` |
| `PullbackSupportInput` | 08GF | `cohomologySupportedOn_smallEtaleDerivedModulePullback` |
| `PullbackDisjointInput` | 08GF, 04K5 | `isZero_smallEtaleDerivedModulePullback_of_disjoint` |
| `EtaleRestrictionSupportInput` | 08GF, 04K5 | `cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback` |
| `OpenImmersionCounitInput` | (08GE) | `isIso_etaleDerivedModuleAdjunction_counit_of_mono` |
| `QuasiCompactSourceInput` | — | `isQuasiCompactSpace_of_isQuasiCompact` |
| `Tag073BTwoInput` | 073B (2) | `isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source` |
| `CompactComplPreimageInput` | (0EMK, 06RV) | `isCompact_compl_preimage_of_isQuasiCompact` |
| `PerfectPullbackInput` | 08H6 | `isPerfect_smallEtaleDerivedModulePullback` |
| `Tag08GGUnitInput` | 08GG (1)(a) | `isIso_unit_derivedRestrict_of_cohomologySupportedOn` |
| `Tag08GGCounitInput` | 08GG (2)(b) | `isIso_counit_derivedPushforward_of_cohomologySupportedOn` |
| `EDSTopInput` | 08GM | `isElementaryDistinguishedSquare_top` |
| `SupportEmptyInput` | 04K5 | `supportOfSheaf_eq_empty_iff_isZero` |
| `Tag09ITInput` | 09IT | `qcqs_induction_on_enlargement` |
| `EDSOfComplSubsetInput` | 08GM | `isElementaryDistinguishedSquare_of_compl_subset` |

The instance context is that of `Spaces/LP26/Inputs.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.SpacesVerified

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify
  AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The preferred-class inputs of `Spaces/Supported/Inputs.lean` -/

/-- **Stacks 0GFI**, proved: low Hom-vanishing against compact objects bounds below. -/
theorem tag0GFI : Spaces.Supported.Tag0GFIInput B S hS := fun _ X hqc hqs E hE =>
  AlgebraicGeometry.Space.exists_isGE_of_lowHomVanishingOnCompact X hqc hqs E hE

/-- A perfect object over a quasi-compact space is bounded above, proved (the input of
`Spaces/Supported/Inputs.lean`). -/
theorem perfectBoundedAboveSupported : Spaces.Supported.PerfectBoundedAboveInput B S hS :=
  fun hX E hE => AlgebraicGeometry.Space.exists_isLE_of_isPerfect hX E hE

/-! ### The inputs of `Spaces/LP26/Inputs.lean` -/

open RelativeFM.Spaces.LP26

/-- **Stacks 09M8**, proved. -/
theorem tag09M8 : Tag09M8Input B S hS := fun _ X hqc hqs E =>
  AlgebraicGeometry.Space.isCompactObject_iff_isPerfect X hqc hqs E

/-- A perfect object over a quasi-compact space is bounded above, proved (the input of
`Spaces/LP26/Inputs.lean`). -/
theorem perfectBoundedAbove : Spaces.LP26.PerfectBoundedAboveInput B S hS := fun hX E hE =>
  AlgebraicGeometry.Space.exists_isLE_of_isPerfect hX E hE

/-- **Stacks 09MB (1)**, half, proved. -/
theorem tag09MB : Tag09MBInput B S hS := fun _ X hqc hqs K hK =>
  AlgebraicGeometry.Space.exists_hom_eq_zero_of_isCompactObject X hqc hqs K hK

/-- **Stacks 08FB**, proved. -/
theorem tag08FB : Tag08FBInput B S hS := fun {_ _} f hfqc hfqs {_} E hE =>
  AlgebraicGeometry.Space.preservesColimit_derivedModulePushforward (B := B) (S := S) (hS := hS)
    f hfqc hfqs E hE

/-- **Stacks 08FA (2)**, the uniform bound, proved. -/
theorem tag08FABound : Tag08FABoundInput B S hS := fun f hfqc hfqs hY =>
  AlgebraicGeometry.Space.exists_isLE_derivedModulePushforward_obj f hfqc hfqs hY

/-- **Stacks 0AFJ**, proved. -/
theorem tag0AFJ : Tag0AFJInput B S hS := fun f _ _ T hT Rf αf _ E hE =>
  AlgebraicGeometry.Space.derivedCategoryB_supportedModules_derivedPushforward B S hS f T hT Rf
    αf E hE

/-- **Stacks 08G8**, perfect ⇒ pseudo-coherent, proved (at the small étale site). -/
theorem perfectPseudoCoherent : PerfectPseudoCoherentInput B S hS := fun X {_} hE =>
  AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isPerfect_general
    (smallEtaleRingedSite B S hS X.1 X.2) hE

/-- **Stacks 08FV (2)**, proved (at the small étale site). -/
theorem tag08FVTwo : Tag08FVTwoInput B S hS := fun X m T hT hK hM =>
  AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_two_general
    (smallEtaleRingedSite B S hS X.1 X.2) m T hT hK hM

/-- An object of `D^{≤ t - 1}` is `t`-pseudo-coherent, proved (at the small étale site). -/
theorem pseudoCoherentFromOfIsLE : PseudoCoherentFromOfIsLEInput B S hS := fun X E t hE =>
  AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isLE_sub_one
    (smallEtaleRingedSite B S hS X.1 X.2) E t hE

/-- **Stacks 08FU (2)**, proved (at the small étale site). -/
theorem tag08FU2 : Tag08FU2Input B S hS := fun X E =>
  AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom
    (smallEtaleRingedSite B S hS X.1 X.2) E

/-- A perfect object lies in `D_QCoh`, proved. -/
theorem perfectQcoh : PerfectQcohInput B S hS := fun X E hE =>
  AlgebraicGeometry.Space.qcohDerived_of_isPerfect_derivedCategoryB X E hE

/-- **Stacks 08HP**, proved. -/
theorem tag08HP : Tag08HPInput B S hS := fun hZ X hX hXqc hXqs =>
  AlgebraicGeometry.Space.approximationByPerfectComplexes_of_qcqs B S hS hZ X hX hXqc hXqs

/-- **Stacks 073B (1)**, proved. -/
theorem tag073B : Tag073BInput B S hS := fun hZ {_ _} hX hXqs hUqc ι =>
  AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace (B := B) (S := S) (hS := hS)
    (hZ := hZ) hX hXqs hUqc ι

/-- An open subspace with compact set of points is quasi-compact, proved. -/
theorem openSubspaceQuasiCompact : OpenSubspaceQuasiCompactInput B S hS := fun {_} hX {_} hG hc =>
  AlgebraicGeometry.Space.isQuasiCompactSpace_of_isCompact_range B S hS hX hG hc

/-- **Stacks 08IK**, proved. -/
theorem tag08IK : Tag08IKInput B S hS := fun F hF hZ hFN E hE =>
  AlgebraicGeometry.Space.isPseudoCoherent_iff_of_isNoetherian (B := B) (S := S) (hS := hS)
    (F := F) (hF := hF) hZ hFN E hE

/-- **Stacks 079Q**, proved. -/
theorem tag079Q : Tag079QInput.{u} := fun A _ _ _ _ =>
  Stacks.ModulesOnACategory.CartesianSubcategory.locallySmall_derivedCategory A

/-- **Stacks 0A8G** (Brown representability), proved. -/
theorem tag0A8G : Tag0A8GInput.{u} := fun functor functorShift hT _ generator _ hgen =>
  CategoryTheory.Pretriangulated.isLeftAdjoint_of_compact_generator functor functorShift hT
    generator hgen

/-- A right adjoint preserving compactness of a weak generator's image commutes with direct sums,
proved. -/
theorem rightAdjointCoproducts : RightAdjointCoproductsInput.{u} := fun adj E hE hcompact hmap =>
  CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map adj E hE hcompact hmap

/-- **Stacks 08GF** for derived pullbacks, proved. -/
theorem pullbackSupport : PullbackSupportInput B S hS := fun {_ _} g {_} E hE =>
  AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedModulePullback g E hE

/-- The derived pullback along a morphism missing the support vanishes, proved. -/
theorem pullbackDisjoint : PullbackDisjointInput B S hS := fun g Q E hE hdisj =>
  AlgebraicGeometry.Space.isZero_smallEtaleDerivedModulePullback_of_disjoint g Q E hE hdisj

/-- Vanishing étale restriction forces support off the image, proved. -/
theorem etaleRestrictionSupport : EtaleRestrictionSupportInput B S hS := fun g hg E hE =>
  AlgebraicGeometry.Space.cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback B S hS
    g hg E hE

/-- The counit of restriction to an open immersion is invertible, proved. -/
theorem openImmersionCounit : OpenImmersionCounitInput B S hS := fun j hj _ =>
  AlgebraicGeometry.Space.isIso_etaleDerivedModuleAdjunction_counit_of_mono B S hS j hj

/-- The source of a quasi-compact morphism to a quasi-compact space is quasi-compact, proved. -/
theorem quasiCompactSource : QuasiCompactSourceInput B S hS := fun hY hYqc f hf =>
  AlgebraicGeometry.Space.isQuasiCompactSpace_of_isQuasiCompact (B := B) (S := S) (hS := hS)
    hY hYqc f hf

/-- **Stacks 073B (2)**, proved. -/
theorem tag073BTwo : Tag073BTwoInput B S hS := fun hZ {_ _} hF hFqs f =>
  AlgebraicGeometry.Space.isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source (B := B) (S := S)
    (hS := hS) (hZ := hZ) hF hFqs f

/-- The complement of a preimage of a closed set with quasi-compact complement is quasi-compact,
proved. -/
theorem compactComplPreimage : CompactComplPreimageInput B S hS :=
  fun _ {_ _} g hXqc hX₀qs T₀ hT₀ hT₀c =>
    AlgebraicGeometry.Space.isCompact_compl_preimage_of_isQuasiCompact g hXqc hX₀qs T₀ hT₀ hT₀c

/-- **Stacks 08H6**, proved. -/
theorem perfectPullback : PerfectPullbackInput B S hS := fun f E hE =>
  AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback f E hE

/-- **Stacks 08GG (1)(a)**, proved. -/
theorem tag08GGUnit : Tag08GGUnitInput B S hS := fun {_ _ _ _} hsq {_} adjPush E hE =>
  AlgebraicGeometry.Space.isIso_unit_derivedRestrict_of_cohomologySupportedOn (B := B) (S := S)
    (hS := hS) (hsq := hsq) adjPush E hE

/-- **Stacks 08GG (2)(b)**, proved. -/
theorem tag08GGCounit : Tag08GGCounitInput B S hS := fun {_ _ _ _} hsq {_} adjPush F hF =>
  AlgebraicGeometry.Space.isIso_counit_derivedPushforward_of_cohomologySupportedOn (B := B)
    (S := S) (hS := hS) (hsq := hsq) adjPush F hF

/-- An open subspace and the identity form an elementary distinguished square, proved. -/
theorem edsTop : EDSTopInput B S hS := fun {_} hX {_} hU =>
  AlgebraicGeometry.Space.isElementaryDistinguishedSquare_top B S hS hX hU

/-- **Stacks 04K5**, a module with empty support is zero, proved. -/
theorem supportEmpty : SupportEmptyInput B S hS := fun X F =>
  AlgebraicGeometry.Space.supportOfSheaf_eq_empty_iff_isZero B S hS X F

/-- **Stacks 09IT**, proved. -/
theorem tag09IT : Tag09ITInput B S hS := fun hZ X hXqc hXqs W hWopen hWqc P hPW hstep =>
  AlgebraicGeometry.Space.qcqs_induction_on_enlargement B S hS hZ X hXqc hXqs W hWopen hWqc P hPW
    hstep

/-- An open subspace and an open immersion covering its complement form an elementary
distinguished square, proved. -/
theorem edsOfComplSubset : EDSOfComplSubsetInput B S hS := fun hW U hU hV g hg h =>
  AlgebraicGeometry.Space.isElementaryDistinguishedSquare_of_compl_subset B S hS hW U hU hV g hg h

end RelativeFM.SpacesVerified

#print axioms RelativeFM.SpacesVerified.tag0GFI
#print axioms RelativeFM.SpacesVerified.perfectBoundedAboveSupported
#print axioms RelativeFM.SpacesVerified.tag09M8
#print axioms RelativeFM.SpacesVerified.perfectBoundedAbove
#print axioms RelativeFM.SpacesVerified.tag09MB
#print axioms RelativeFM.SpacesVerified.tag08FB
#print axioms RelativeFM.SpacesVerified.tag08FABound
#print axioms RelativeFM.SpacesVerified.tag0AFJ
#print axioms RelativeFM.SpacesVerified.perfectPseudoCoherent
#print axioms RelativeFM.SpacesVerified.tag08FVTwo
#print axioms RelativeFM.SpacesVerified.pseudoCoherentFromOfIsLE
#print axioms RelativeFM.SpacesVerified.tag08FU2
#print axioms RelativeFM.SpacesVerified.perfectQcoh
#print axioms RelativeFM.SpacesVerified.tag08HP
#print axioms RelativeFM.SpacesVerified.tag073B
#print axioms RelativeFM.SpacesVerified.openSubspaceQuasiCompact
#print axioms RelativeFM.SpacesVerified.tag08IK
#print axioms RelativeFM.SpacesVerified.tag079Q
#print axioms RelativeFM.SpacesVerified.tag0A8G
#print axioms RelativeFM.SpacesVerified.rightAdjointCoproducts
#print axioms RelativeFM.SpacesVerified.pullbackSupport
#print axioms RelativeFM.SpacesVerified.pullbackDisjoint
#print axioms RelativeFM.SpacesVerified.etaleRestrictionSupport
#print axioms RelativeFM.SpacesVerified.openImmersionCounit
#print axioms RelativeFM.SpacesVerified.quasiCompactSource
#print axioms RelativeFM.SpacesVerified.tag073BTwo
#print axioms RelativeFM.SpacesVerified.compactComplPreimage
#print axioms RelativeFM.SpacesVerified.perfectPullback
#print axioms RelativeFM.SpacesVerified.tag08GGUnit
#print axioms RelativeFM.SpacesVerified.tag08GGCounit
#print axioms RelativeFM.SpacesVerified.edsTop
#print axioms RelativeFM.SpacesVerified.supportEmpty
#print axioms RelativeFM.SpacesVerified.tag09IT
#print axioms RelativeFM.SpacesVerified.edsOfComplSubset
