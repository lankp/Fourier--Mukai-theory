/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai
import WeakApprox.Theorem11PaperNonVacuity

/-!
# Axiom audit

Run `lean FourierMukai/Audit.lean` to print the axioms of the headline declarations.
None depends on `sorryAx`: the tree has no `sorry`.
-/

open RelativeFM

-- Proved (no `sorryAx` expected):
#print axioms RelativeFM.Trinatural.isIso_app_shift
#print axioms RelativeFM.Trinatural.isIso_app_zero
#print axioms RelativeFM.Trinatural.isIso_app_of_distinguished
#print axioms RelativeFM.Trinatural.isoLocus_isTriangulated
#print axioms RelativeFM.Trinatural.isoLocus_isClosedUnderIsomorphisms
#print axioms RelativeFM.FinitelyBuiltBy.mono
#print axioms RelativeFM.isClassicalGenerator_iff
-- Audit: the Type-valued `IsCompact` is uninhabited (`Prelim/CompactnessAudit.lean`):
#print axioms RelativeFM.not_isCompact_of_hasZeroObject
-- Non-vacuity of the additive compactness used by Lemmas 2.4 and 2.5:
#print axioms RelativeFM.isCompactAb_zero
#print axioms RelativeFM.smallRingObject_isCompactAb_and_isPaperGenerator
#print axioms RelativeFM.singlyCompactlyGenerated_smallRingObject
-- Stacks 09SN consequence (`Prelim/Stacks09SN.lean`):
#print axioms RelativeFM.StacksInterface.isZero_of_rightOrthogonal_ofObj_punit_iff
#print axioms RelativeFM.StacksInterface.isLocalizingGenerator_of_tag09SN
-- Lemma 2.4 (`lem:localizing_iff_cpt_gen`), `Prelim/Lemma24.lean`:
#print axioms RelativeFM.ObjectProperty.isLocalizingGenerator_iff_localizingClosure_eq_top
#print axioms RelativeFM.isPaperGenerator_of_isLocalizingGenerator
#print axioms RelativeFM.isLocalizingGenerator_of_isPaperGenerator_of_tag09SN
#print axioms RelativeFM.lemma_2_4
#print axioms RelativeFM.singlyCompactlyGenerated_iff
#print axioms RelativeFM.lemma_2_5_of_tag09SN
#print axioms RelativeFM.Trinatural.id
#print axioms RelativeFM.Trinatural.comp
#print axioms RelativeFM.isIso_app_of_retract
#print axioms RelativeFM.Trinatural.isoLocus_isStableUnderRetracts
#print axioms RelativeFM.Trinatural.isIso_of_isClassicalGenerator
#print axioms RelativeFM.isIso_app_coproduct
#print axioms RelativeFM.Trinatural.isIso_app_coprod
#print axioms RelativeFM.matesEquiv
#print axioms RelativeFM.mate_bijective
#print axioms RelativeFM.isIso_mate_iff
#print axioms RelativeFM.Adjunction.twist
#print axioms RelativeFM.Bicategorical.twist
#print axioms RelativeFM.lemma_C_1
#print axioms RelativeFM.Adjunction.existsUnique_twist_eq
#print axioms RelativeFM.representablyFullyFaithful_iff
#print axioms RelativeFM.lemmaDef_7_10
-- GL26 §7.2, Lemmas 7.12, 7.13, 7.15, 7.17 (`Prelim/BaseChangeMates.lean`):
#print axioms RelativeFM.BaseChangeMates.PullPushData.lemma_7_12
#print axioms RelativeFM.BaseChangeMates.PullPushData.lemma_7_13
#print axioms RelativeFM.BaseChangeMates.PullPushData.isIso_theta_of_isIso_xi
#print axioms RelativeFM.BaseChangeMates.PullPushData.lemma_7_15
#print axioms RelativeFM.BaseChangeMates.PullPushData.lemma_7_17_theta
#print axioms RelativeFM.BaseChangeMates.PullPushData.lemma_7_17_xi
#print axioms RelativeFM.BaseChangeMates.constPullPushData
#print axioms RelativeFM.BaseChangeMates.constPullPushData_isIso_theta
-- GL26 Lemmas 6.11, 10.1, 10.2 in the cube of Setup 2.20 (`Scheme/FMCube.lean`):
#print axioms RelativeFM.FMCube.lemma_6_11
#print axioms RelativeFM.FMCube.lemma_10_1
#print axioms RelativeFM.FMCube.lemma_10_2
#print axioms RelativeFM.FMCube.lemma_10_2'
#print axioms RelativeFM.FMCube.lemma_10_2_iso
#print axioms RelativeFM.FMCube.constFMCube_flatBaseChangeLeft
#print axioms RelativeFM.FMCube.constFMCube_flatBaseChangeRight
#print axioms RelativeFM.FMCube.constFMCube_projectionFormula
-- GL26 §7.2 wired into `Scheme/Duality.lean` (`Scheme/DualityMates.lean`):
#print axioms RelativeFM.DualityMates.BaseChangeCoherenceData.pushComp_hom_eq
#print axioms RelativeFM.DualityMates.BaseChangeCoherenceData.subsingleton
#print axioms RelativeFM.DualityMates.DerivedPseudofunctorInput.lemma_7_12
#print axioms RelativeFM.DualityMates.DerivedPseudofunctorInput.coherence
#print axioms RelativeFM.DualityMates.DerivedPseudofunctorInput.coherence_eq
#print axioms RelativeFM.DualityMates.DerivedPseudofunctorInput.lemma_7_15
#print axioms RelativeFM.DualityMates.DerivedPseudofunctorInput.lemma_7_17_theta
#print axioms RelativeFM.DualityMates.DerivedPseudofunctorInput.lemma_7_17_lowerStarUpperCross
#print axioms RelativeFM.DualityMates.trivialInput
#print axioms RelativeFM.DualityMates.trivialInput_isIso_theta
#print axioms RelativeFM.mates_hom_square
#print axioms RelativeFM.mates_hom_square_eq_mate
#print axioms RelativeFM.lemma_7_4
#print axioms RelativeFM.unit_isMate
#print axioms RelativeFM.counit_isMate
#print axioms RelativeFM.lemma_7_6
#print axioms RelativeFM.lemma_7_9_id
#print axioms RelativeFM.lemma_7_9_comp
#print axioms RelativeFM.Trinatural.isIso_iff_of_precomp_essentiallyDense₀
#print axioms RelativeFM.lemma_2_5
#print axioms RelativeFM.Adjunction.isCompactAb_leftAdjoint_obj
#print axioms RelativeFM.Trinatural.ofNatTrans
#print axioms RelativeFM.Trans.lemma_B4_unitCounit
#print axioms RelativeFM.Trans.instBicategory
#print axioms RelativeFM.Trans.instStrict
#print axioms RelativeFM.Trans.forget
#print axioms RelativeFM.Trans.lemma_B2_faithful
#print axioms RelativeFM.Trans.lemma_B2_unique
#print axioms RelativeFM.Trans.TwoCellData.ofBicategory_isOverCat
#print axioms RelativeFM.Trans.IsTransnatural.hcomp
#print axioms RelativeFM.Trans.isTransAdjunction_iff
#print axioms RelativeFM.Trans.lemma_B4
#print axioms RelativeFM.Trans.lemma_B5_existsUnique_bicategory
#print axioms RelativeFM.Trans.isAdjunctionInTrans_id
#print axioms RelativeFM.Trans.isAdjunctionInTrans_ofId
#print axioms RelativeFM.Trans.lemma_B5_existsUnique
#print axioms RelativeFM.Trans.lemma_B5_iff
#print axioms RelativeFM.Trans.lemma_B5_equivalence
#print axioms RelativeFM.lemma_B7
#print axioms RelativeFM.lemma_B7_natTrans
#print axioms RelativeFM.natTransCommShift_of_one
#print axioms RelativeFM.lemma_B10_exists
#print axioms RelativeFM.lemma_B10_unique
#print axioms RelativeFM.lemma_B10_commShiftIso
#print axioms RelativeFM.lemma_B10_equivalence
#print axioms RelativeFM.lemma_2_25
#print axioms RelativeFM.Noetherian.lemma_2_25Statement_proved
#print axioms RelativeFM.AffineDiagonalContext.affine_lemma_2_25
#print axioms RelativeFM.DerivedDiagonalInput.identityIso
#print axioms RelativeFM.DiagonalFunctorialityInput.identityTransformIso

#print axioms RelativeFM.RegularCompact.ringObject_isCompactAb
#print axioms RelativeFM.RegularCompact.affine_satisfiesPaperWA
#print axioms RelativeFM.RegularCompact.principalSupported_satisfiesPaperWA
#print axioms RelativeFM.RegularCompact.neemanWeakApproximability_spec
#print axioms RelativeFM.Recollement.JUpperConstruction.adjunction
#print axioms RelativeFM.Recollement.JUpperConstruction.jStarAdjOfIShriek
#print axioms RelativeFM.Recollement.JUpperConstruction.affineRecollementInputOfIShriek
#print axioms RelativeFM.Recollement.JUpperConstruction.affineRecollementInputOfStacks0E55
#print axioms RelativeFM.Recollement.JUpperConstruction.affineRecollementInputOfExactCoextension

-- Wave 3: open/closed glue without per-package completion (`Scheme/OpenClosedCompletion.lean`)
#print axioms RelativeFM.OpenClosedCompletionW3.exists_changeGenerator
#print axioms RelativeFM.OpenClosedCompletionW3.tStructureEquivalent_of_inPreferredClass
#print axioms RelativeFM.OpenClosedCompletionW3.OpenClosedFrame.exists_paperData
#print axioms RelativeFM.OpenClosedCompletionW3.compact_open_closed_glue_of_frameInput
#print axioms RelativeFM.OpenClosedCompletionW3.neemanSupported_of_qcqs_of_frameInput
#print axioms RelativeFM.KoszulInputs.not_koszulScalarSupportInput
#print axioms RelativeFM.KoszulInputs.scalarConeData_isSupported
#print axioms RelativeFM.KoszulInputs.scalarConeData_le_zero
#print axioms RelativeFM.KoszulInputs.idealSupportedCoproductInput
#print axioms RelativeFM.KoszulInputs.idealSupportedCompactnessInput
#print axioms RelativeFM.Neeman32Inputs.smallAffine_neeman_3_2_i
#print axioms RelativeFM.Neeman32Inputs.affine_neeman_3_2_i
#print axioms RelativeFM.Neeman32Inputs.affine_neeman_3_2_ii
-- Wave 5 (neeman-prune): endpoints that took Neeman 3.2(i) inputs (large model: no input; small: Stacks 09SR)
#print axioms RelativeFM.affineCompactHomZeroAtTop
#print axioms RelativeFM.compact_iff_dbcoh
#print axioms RelativeFM.affine_theorem_1_1_small_of_tag09SR
#print axioms RelativeFM.affine_theorem_1_1_small_standard_of_tag09SR
#print axioms RelativeFM.AffineNeemanEndpointM3.small_affine_regularGenerator_package
#print axioms RelativeFM.Stacks07LT.M4.compactToPerfectInput_unconditional
#print axioms RelativeFM.KoszulInputs.isLeftAdjoint_affineDZIdealι
#print axioms RelativeFM.KoszulConeSwap.coneSwapIso
#print axioms RelativeFM.KoszulFiniteInputs.IsScalarCone.swap
#print axioms RelativeFM.KoszulFiniteInputs.koszulList_power_coprod
#print axioms RelativeFM.KoszulFiniteInputs.koszulList_detects_zero
#print axioms RelativeFM.FiniteKoszulM1.koszulPowerCoprodInput
#print axioms RelativeFM.StacksInterface.koszulDetectionInput
#print axioms RelativeFM.IdealNeemanM1.satisfiesPaperWA_idealSupported
#print axioms RelativeFM.NeemanAffineSupport.satisfiesPaperWA_idealSupported
#print axioms RelativeFM.NeemanAffineSupport.satisfiesPaperWA_of_fg
-- Wave 6 (vacuity-refutations): F1--F3 of `results/OPEN_INPUTS.md` §0, proved false in the tree
#print axioms RelativeFM.VacuityF1.not_hasCoproducts_affineD
#print axioms RelativeFM.VacuityF1.isEmpty_affineDerivedCoproducts
#print axioms RelativeFM.VacuityF1.affine_theorem_1_1_unconditional_hypotheses_false
#print axioms RelativeFM.VacuityF1.affine_theorem_1_1_stacks07LT_hypotheses_false
#print axioms RelativeFM.VacuityF2.not_isGenerator_of_isCompactAb_int
#print axioms RelativeFM.VacuityF2.isEmpty_weakApproximationData_int
#print axioms RelativeFM.VacuityF2.not_satisfiesWA_int
#print axioms RelativeFM.VacuityF2.isEmpty_setupMainMinimal_int
#print axioms RelativeFM.VacuityF2.isCompactAb_affineQhComparison_inverse
#print axioms RelativeFM.VacuityF2.smallPerf_of_isCompactAb
#print axioms RelativeFM.VacuityF2.not_isGenerator_of_isCompactAb_smallInt
#print axioms RelativeFM.VacuityF2.isEmpty_weakApproximationData_smallInt
#print axioms RelativeFM.VacuityF2.not_satisfiesWA_smallInt
#print axioms RelativeFM.VacuityF2.isEmpty_setupMainMinimal_smallInt
#print axioms RelativeFM.VacuityF2.affine_theorem_1_1_small_hypotheses_false_int
#print axioms RelativeFM.VacuityF3.not_quasiCoherent_isClosedUnderSubobjects_spec_int
#print axioms RelativeFM.VacuityF3.not_quasicoherentSerreInput_spec_int
#print axioms RelativeFM.VacuityF3.not_quasicoherentStrongClosureInput_spec_int
-- LP26 Theorem 1.1 with the paper's hypotheses (wave 6, `WeakApprox/Theorem11Paper.lean`):
#print axioms RelativeWeakApprox.CompactTStructureW6.compactTStructure_le_zero
#print axioms RelativeWeakApprox.WABoundsW6.bnp_3_10_1
#print axioms RelativeWeakApprox.WABoundsW6.ge_of_hom_vanishing
#print axioms RelativeWeakApprox.PaperHypothesesW6.inPreferredClass_of_paperData
#print axioms RelativeWeakApprox.PaperHypothesesW6.bnp310Input_of_tag09SR
#print axioms RelativeWeakApprox.PaperHypothesesW6.exists_paperSetupMainMinimal
#print axioms RelativeWeakApprox.PaperHypothesesW6.theorem_1_1_paper
#print axioms RelativeWeakApprox.PaperHypothesesW6.NonVacuity.theorem_1_1_paper_zero
#print axioms RelativeWeakApprox.PaperHypothesesW6.NonVacuity.theorem_1_1_paper_affine
-- Stacks 09SR and 09SN are discharged from AxiomMath/Stacks in the `Spaces` library
-- (not a default target, so not imported here): the `#print axioms` lines for
-- `RelativeFM.Spaces.Stacks.{tag09SRPaper, tag09SN, theorem_1_1, lemma_2_4, lemma_2_5,
-- smallAffine_neeman_3_2_i, ...}` are at the end of `Spaces/Stacks/{Bridges,Tags,Corollaries}.lean`.
