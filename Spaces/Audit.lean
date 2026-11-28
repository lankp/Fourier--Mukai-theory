/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Affine.WeakApprox
import Spaces.AxiomMathInputs
import Spaces.NonVacuity
import Spaces.Statements
import Spaces.Supported.CompactGeneration
import Spaces.Supported.Preferred
import Spaces.BaseChange.Cube
import Spaces.Conservative.NonVacuity
import Spaces.Duality.NonVacuity
import Spaces.InternalHom.NonVacuity
import Spaces.QuasiPerfect.NonVacuity
import Spaces.Kernels.NonVacuity
import Spaces.LP26.Coherence
import Spaces.LP26.Corollary12
import Spaces.LP26.Lemma59
import Spaces.LP26.NonVacuity
import Spaces.LP26.Proposition58
import Spaces.LP26.Recollement
import Spaces.LP26.StandardTStructure
import Spaces.LP26.StandardWA
import Spaces.Stacks.UniverseNonVacuity

/-!
# Axiom audit of the algebraic-space layer

`#print axioms` for the definitions and non-vacuity theorems of `Spaces/`.  It lives in the
`Spaces` library, not in `FourierMukai/Audit.lean`, because importing `Spaces` there would
make the default build compile AxiomMath.  Every line must print a subset of `propext`,
`Classical.choice`, `Quot.sound`.  The tagged inputs of `Spaces/AxiomMathInputs.lean` are
`Prop` definitions, not axioms; a theorem that uses one takes it as a hypothesis.
-/

open RelativeFM.Spaces

-- Categories (GL26 §2.2)
#print axioms RelativeFM.Spaces.Dqc
#print axioms RelativeFM.Spaces.Dbqc
#print axioms RelativeFM.Spaces.DminusCoh
#print axioms RelativeFM.Spaces.DbCoh
#print axioms RelativeFM.Spaces.Perf
#print axioms RelativeFM.Spaces.supp
#print axioms RelativeFM.Spaces.DqcSupported
#print axioms RelativeFM.Spaces.cohomologySupportedOn_iff_supp_subset
-- Functors
#print axioms RelativeFM.Spaces.pull
#print axioms RelativeFM.Spaces.push
#print axioms RelativeFM.Spaces.pullPushAdj
#print axioms RelativeFM.Spaces.tensor
-- Definitions 4.1 and 5.1
#print axioms RelativeFM.Spaces.IsRelativelyPerfect
#print axioms RelativeFM.Spaces.IsQuasiPerfect
-- Integral transforms (GL26 §2.3)
#print axioms RelativeFM.Spaces.transform
#print axioms RelativeFM.Spaces.transformOver
#print axioms RelativeFM.Spaces.isZero_transform_of_isZero
#print axioms RelativeFM.Spaces.isZero_transformOver_of_isZero
-- Tagged inputs and their consumers
#print axioms RelativeFM.Spaces.Tag06UQInput
#print axioms RelativeFM.Spaces.Tag08F4Input
#print axioms RelativeFM.Spaces.Tag08F5Input
#print axioms RelativeFM.Spaces.Tag08FAInput
#print axioms RelativeFM.Spaces.Dqc_isTriangulated
#print axioms RelativeFM.Spaces.pullQc
#print axioms RelativeFM.Spaces.tensorQc
#print axioms RelativeFM.Spaces.pushQc
-- Non-vacuity
#print axioms RelativeFM.Spaces.baseSpace
#print axioms RelativeFM.Spaces.Dqc_of_isZero
#print axioms RelativeFM.Spaces.Dbqc_of_isZero
#print axioms RelativeFM.Spaces.DminusQc_of_isZero
#print axioms RelativeFM.Spaces.DminusCoh_of_isZero
#print axioms RelativeFM.Spaces.Perf_of_isZero
#print axioms RelativeFM.Spaces.IsPseudoCoherent_of_isZero
#print axioms RelativeFM.Spaces.DbCoh_of_isZero
#print axioms RelativeFM.Spaces.DqcSupported_univ_of_isZero
#print axioms RelativeFM.Spaces.isRelativelyPerfect_of_isZero
#print axioms RelativeFM.Spaces.isQuasiPerfect_of_isZero
#print axioms RelativeFM.Spaces.isCoherentOnSite_of_isZero
-- GL26 headline statements over spaces (wave7/spaces-statements): notions
#print axioms RelativeFM.Spaces.Statements.FullyFaithfulOn
#print axioms RelativeFM.Spaces.Statements.IsEquivalenceOn
#print axioms RelativeFM.Spaces.Statements.FFOrEquivOn
#print axioms RelativeFM.Spaces.Statements.IsNoetherianSpace
#print axioms RelativeFM.Spaces.Statements.IsProperHom
#print axioms RelativeFM.Spaces.Statements.IsFlatHom
#print axioms RelativeFM.Spaces.Statements.IsFiniteTypeHom
#print axioms RelativeFM.Spaces.Statements.IsQuasiAffineHom
#print axioms RelativeFM.Spaces.Statements.Pts
#print axioms RelativeFM.Spaces.Statements.ptsTopology
#print axioms RelativeFM.Spaces.Statements.ptsMap
#print axioms RelativeFM.Spaces.Statements.Representative
#print axioms RelativeFM.Spaces.Statements.Representative.hom
#print axioms RelativeFM.Spaces.Statements.IsClosedPt
#print axioms RelativeFM.Spaces.Statements.cubeMap
#print axioms RelativeFM.Spaces.Statements.baseChangeKernel
#print axioms RelativeFM.Spaces.Statements.fibreTransform
#print axioms RelativeFM.Spaces.Statements.fmLocus
#print axioms RelativeFM.Spaces.Statements.FMLocus
-- the statements (Props; targets, not proved)
#print axioms RelativeFM.Spaces.Statements.theorem_1_2Statement
#print axioms RelativeFM.Spaces.Statements.theorem_12_9Statement
#print axioms RelativeFM.Spaces.Statements.corollary_12_4Statement
#print axioms RelativeFM.Spaces.Statements.theorem_1_3Statement
#print axioms RelativeFM.Spaces.Statements.theorem_1_6Statement
#print axioms RelativeFM.Spaces.Statements.theorem_10_13Statement
#print axioms RelativeFM.Spaces.Statements.corollary_6_18Statement
#print axioms RelativeFM.Spaces.Statements.lemma_12_2Statement
#print axioms RelativeFM.Spaces.Statements.theorem_12_3Statement
-- tagged inputs used only for non-vacuity
#print axioms RelativeFM.Spaces.Statements.Tag06LTInput
#print axioms RelativeFM.Spaces.Statements.IsQuasiCompactOfIsIsoInput
#print axioms RelativeFM.Spaces.Statements.UniversallyClosedOfIsIsoInput
#print axioms RelativeFM.Spaces.Statements.IsFlatIdInput
#print axioms RelativeFM.Spaces.Statements.AffineQuasiSeparatedInput
-- non-vacuity
#print axioms RelativeFM.Spaces.Statements.IsEquivalenceOn.fullyFaithfulOn
#print axioms RelativeFM.Spaces.Statements.isEquivalenceOn_id
#print axioms RelativeFM.Spaces.Statements.fullyFaithfulOn_id
#print axioms RelativeFM.Spaces.Statements.fFOrEquivOn_id
#print axioms RelativeFM.Spaces.Statements.Representative.exists_represents
#print axioms RelativeFM.Spaces.Statements.isQuasiAffineHom_id
#print axioms RelativeFM.Spaces.Statements.zero_kernel_hypotheses
#print axioms RelativeFM.Spaces.Statements.FMLocus_subset_fmLocus
#print axioms RelativeFM.Spaces.Statements.isProperHom_id
#print axioms RelativeFM.Spaces.Statements.isFlatHom_id
#print axioms RelativeFM.Spaces.Statements.isNoetherianSpace_baseSpace
#print axioms RelativeFM.Spaces.Statements.setup_hypotheses_satisfiable
-- LP26 Corollary 1.2, affine base case (Spaces/Affine/, wave 7)
#print axioms RelativeFM.Spaces.Affine.associated
#print axioms RelativeFM.Spaces.Affine.zeroLocusPoints
#print axioms RelativeFM.Spaces.Affine.Tag06Z0ExactInput
#print axioms RelativeFM.Spaces.Affine.Tag06Z0QcohInput
#print axioms RelativeFM.Spaces.Affine.Tag06Z0Input
#print axioms RelativeFM.Spaces.Affine.Tag07TYInput
#print axioms RelativeFM.Spaces.Affine.Tag021RInput
#print axioms RelativeFM.Spaces.Affine.mem_supportOfSheaf_associated_iff
#print axioms RelativeFM.Spaces.Affine.cohomologySupportedOn_iff
#print axioms RelativeFM.Spaces.Affine.dqcSupported_eq_map
#print axioms RelativeFM.Spaces.Affine.isTriangulated_dqcSupported
#print axioms RelativeFM.Spaces.Affine.supportedComparison
#print axioms RelativeFM.Spaces.Affine.isEquivalence_supportedComparison
#print axioms RelativeFM.Spaces.Affine.satisfiesPaperWA_dqcSupported
#print axioms RelativeFM.Spaces.Affine.lp26_cor_1_2_affine
#print axioms RelativeFM.Spaces.Affine.lp26_cor_1_2_affine_int
-- GL26 Lemma A.9 (`lem:preferred_eq_class`), compact generation of `D_{qc,Z}(X)`
-- (`Spaces/Supported/`); tagged inputs in `Spaces/Supported/Inputs.lean`
#print axioms RelativeFM.Spaces.Supported.Tag08F3Input
#print axioms RelativeFM.Spaces.Supported.SupportTriangulatedInput
#print axioms RelativeFM.Spaces.Supported.SupportedDirectSumsInput
#print axioms RelativeFM.Spaces.Supported.Tag0AECInput
#print axioms RelativeFM.Spaces.Supported.Tag0AEDInput
#print axioms RelativeFM.Spaces.Supported.Tag0GFDInput
#print axioms RelativeFM.Spaces.Supported.AffineQuasiSeparatedInput
#print axioms RelativeFM.Spaces.Supported.ContainsTerminalInput
#print axioms RelativeFM.Spaces.Supported.isClosedUnderIsomorphisms_cohomologySupportedOn'
#print axioms RelativeFM.Spaces.Supported.dqcSupported_iff_exists
#print axioms RelativeFM.Spaces.Supported.perf_iff
#print axioms RelativeFM.Spaces.Supported.isTriangulated_qcohDerived
#print axioms RelativeFM.Spaces.Supported.isTriangulated_support
#print axioms RelativeFM.Spaces.Supported.hasCoproducts
#print axioms RelativeFM.Spaces.Supported.isPaperGenerator_of_detects
#print axioms RelativeFM.Spaces.Supported.lemma_A_9_generator
#print axioms RelativeFM.Spaces.Supported.lemma_A_9_isCompactObject_iff
#print axioms RelativeFM.Spaces.Supported.lemma_A_9_isCompactObject_iff_perf
#print axioms RelativeFM.Spaces.Supported.lemma_A_9_triangEnvelope
#print axioms RelativeFM.Spaces.Supported.lemma_A_9
#print axioms RelativeFM.Spaces.Supported.nonVacuity_affine_univ
#print axioms RelativeFM.Spaces.Supported.nonVacuity_base
#print axioms RelativeFM.Spaces.Supported.isAffine_terminal
#print axioms RelativeFM.Spaces.Supported.lemma_A_9_affine_univ
-- GL26 Lemma A.9, preferred-class clause (wave 8, `Spaces/Supported/NeemanAbstract.lean`,
-- `StandardTStructure.lean`, `Preferred.lean`)
#print axioms RelativeFM.Spaces.Supported.Tag0GFIInput
#print axioms RelativeFM.Spaces.Supported.PerfectBoundedAboveInput
#print axioms RelativeFM.Spaces.Supported.genCoaisle
#print axioms RelativeFM.Spaces.Supported.DetectsBelowUniformly
#print axioms RelativeFM.Spaces.Supported.eq_zero_of_shift
#print axioms RelativeFM.Spaces.Supported.isGE_of_retract
#print axioms RelativeFM.Spaces.Supported.tStructureEquivalent_of_detectsBelowUniformly
#print axioms RelativeFM.Spaces.Supported.bndFrom
#print axioms RelativeFM.Spaces.Supported.triangEnvelope_le_bndFrom
#print axioms RelativeFM.Spaces.Supported.detectsBelowUniformly_of_mem_triangEnvelope
#print axioms RelativeFM.Spaces.Supported.detectsBelowUniformly_of_detectsBelow
#print axioms RelativeFM.Spaces.Supported.compactTStructure_hypotheses
#print axioms RelativeFM.Spaces.Supported.isIso_homologyMap_mor₁
#print axioms RelativeFM.Spaces.Supported.isIso_homologyMap_mor₂
#print axioms RelativeFM.Spaces.Supported.homologyProp_obj₁_of_triangle
#print axioms RelativeFM.Spaces.Supported.homologyProp_obj₃_of_triangle
#print axioms RelativeFM.Spaces.Supported.supportIn
#print axioms RelativeFM.Spaces.Supported.supportIn_of_isZero
#print axioms RelativeFM.Spaces.Supported.qcoh_of_isZero
#print axioms RelativeFM.Spaces.Supported.hasInducedTStructure_qcohDerived
#print axioms RelativeFM.Spaces.Supported.stdQc
#print axioms RelativeFM.Spaces.Supported.hasInducedTStructure_qcSupportedOn
#print axioms RelativeFM.Spaces.Supported.stdT
#print axioms RelativeFM.Spaces.Supported.stdT_isLE_iff
#print axioms RelativeFM.Spaces.Supported.stdT_isGE_iff
#print axioms RelativeFM.Spaces.Supported.SupportedDetectsBelowStatement
#print axioms RelativeFM.Spaces.Supported.detectsBelowUniformly_of_statement
#print axioms RelativeFM.Spaces.Supported.tStructureEquivalent_of_statement
#print axioms RelativeFM.Spaces.Supported.isEquivalence_ι_univ
#print axioms RelativeFM.Spaces.Supported.supportedDetectsBelowStatement_univ
#print axioms RelativeFM.Spaces.Supported.lemma_A_9_preferred_univ
#print axioms RelativeFM.Spaces.Supported.lemma_A_9_detectsBelowUniformly_univ
#print axioms RelativeFM.Spaces.Supported.nonVacuity_detectsBelowUniformly_affine
#print axioms RelativeFM.Spaces.Supported.nonVacuity_instances
-- The supported Stacks 0GFI and GL26 Lemma A.9's preferred-class clause for general supports
-- (wave 9, `Spaces/Supported/DetectingInputs.lean`, `Detecting.lean`, `Preferred.lean`)
#print axioms RelativeFM.Spaces.Supported.koszulSp
#print axioms RelativeFM.Spaces.Supported.VanishesWhereUnitSp
#print axioms RelativeFM.Spaces.Supported.unitLocusSieveSp
#print axioms RelativeFM.Spaces.Supported.KoszulTorsionInput
#print axioms RelativeFM.Spaces.Supported.KoszulDetectionInput
#print axioms RelativeFM.Spaces.Supported.KoszulQcohInput
#print axioms RelativeFM.Spaces.Supported.KoszulCompactInput
#print axioms RelativeFM.Spaces.Supported.UnitLocusInput
#print axioms RelativeFM.Spaces.Supported.KoszulRestrictInput
#print axioms RelativeFM.Spaces.Supported.VanishesWhereUnitInput
#print axioms RelativeFM.Spaces.Supported.EdsOpenQcInput
#print axioms RelativeFM.Spaces.Supported.EdsOpenQsInput
#print axioms RelativeFM.Spaces.Supported.OpenCounitInput
#print axioms RelativeFM.Spaces.Supported.PushforwardQcohInput
#print axioms RelativeFM.Spaces.Supported.PerfectQcohInput
#print axioms RelativeFM.Spaces.Supported.RangeOpenInput
#print axioms RelativeFM.Spaces.Supported.PreimageQcInput
#print axioms RelativeFM.Spaces.Supported.ShriekSupportInput
#print axioms RelativeFM.Spaces.Supported.ShriekPerfectInput
#print axioms RelativeFM.Spaces.Supported.ShriekRestrictOpenInput
#print axioms RelativeFM.Spaces.Supported.Tag09IVInput
#print axioms RelativeFM.Spaces.Supported.SupportPullbackInput
#print axioms RelativeFM.Spaces.Supported.modules_eq_ringedToposModules
#print axioms RelativeFM.Spaces.Supported.exists_distTriang_koszulSp_cons
#print axioms RelativeFM.Spaces.Supported.suppDetectsBelow_of_isAffineSpace
#print axioms RelativeFM.Spaces.Supported.koszulSp_peel
#print axioms RelativeFM.Spaces.Supported.suppDetectsBelow_of_eds
#print axioms RelativeFM.Spaces.Supported.suppDetectsBelow
#print axioms RelativeFM.Spaces.Supported.supportedDetectsBelowStatement
#print axioms RelativeFM.Spaces.Supported.lemma_A_9_preferred
#print axioms RelativeFM.Spaces.Supported.lemma_A_9_detectsBelowUniformly
#print axioms RelativeFM.Spaces.Supported.nonVacuity_detectsBelowUniformly
#print axioms RelativeFM.Spaces.Supported.nonVacuity_detectsBelowUniformly_affine_general
-- Base change over algebraic spaces (wave 7, `Spaces/BaseChange/`)
#print axioms RelativeFM.Spaces.BaseChange.PullPseudofunctor.toPullPushData
#print axioms RelativeFM.Spaces.BaseChange.canonical_iso_comp_id
#print axioms RelativeFM.Spaces.BaseChange.pullPushData
#print axioms RelativeFM.Spaces.BaseChange.lemma_7_12
#print axioms RelativeFM.Spaces.BaseChange.lemma_7_13
#print axioms RelativeFM.Spaces.BaseChange.lemma_7_17_theta
#print axioms RelativeFM.Spaces.BaseChange.lemma_7_17_xi
#print axioms RelativeFM.Spaces.BaseChange.lemma_7_17_xi_id
#print axioms RelativeFM.Spaces.BaseChange.CompIsoAgreeInput
#print axioms RelativeFM.Spaces.BaseChange.FlatBaseChangeInput
#print axioms RelativeFM.Spaces.BaseChange.Tag08INInput
#print axioms RelativeFM.Spaces.BaseChange.tensorPullPushData
#print axioms RelativeFM.Spaces.BaseChange.theta_app_eq_baseChangeMap
#print axioms RelativeFM.Spaces.BaseChange.flatBaseChangeRightQc_of_isFlat
#print axioms RelativeFM.Spaces.BaseChange.projMap_app_eq
#print axioms RelativeFM.Spaces.BaseChange.projectionFormulaQc_of
#print axioms RelativeFM.Spaces.BaseChange.lemma_6_11
#print axioms RelativeFM.Spaces.BaseChange.lemma_6_11_of_isFlat
#print axioms RelativeFM.Spaces.BaseChange.lemma_10_1
#print axioms RelativeFM.Spaces.BaseChange.lemma_10_1_of
#print axioms RelativeFM.Spaces.BaseChange.lemma_10_2
#print axioms RelativeFM.Spaces.BaseChange.lemma_6_11_id
#print axioms RelativeFM.Spaces.BaseChange.lemma_10_1_id
-- LP26 §5 over algebraic spaces (wave 8, `Spaces/LP26/`)
#print axioms RelativeFM.Spaces.LP26.qcohDerived_shift
#print axioms RelativeFM.Spaces.LP26.lemma_5_5
#print axioms RelativeFM.Spaces.LP26.eq_zero_of_ambient
#print axioms RelativeFM.Spaces.LP26.lemma_5_5_dqc
#print axioms RelativeFM.Spaces.LP26.lemma_5_6_of_isCompactObject
#print axioms RelativeFM.Spaces.LP26.lemma_5_6
#print axioms RelativeFM.Spaces.LP26.lemma_5_6_dqcZ
#print axioms RelativeFM.Spaces.LP26.isQuasiCompact_of_isIso'
#print axioms RelativeFM.Spaces.LP26.isQuasiSeparated_of_mono'
#print axioms RelativeFM.Spaces.LP26.isQuasiSeparated_of_isOpenImmersion
#print axioms RelativeFM.Spaces.LP26.isClosed_compl_image_and_preimage
#print axioms RelativeFM.Spaces.LP26.push_dqcSupported
#print axioms RelativeFM.Spaces.LP26.lemma_5_7
#print axioms RelativeFM.Spaces.LP26.lemma_5_7_supported
#print axioms RelativeFM.Spaces.LP26.nonVacuity_lemma_5_5
#print axioms RelativeFM.Spaces.LP26.nonVacuity_lemma_5_6
#print axioms RelativeFM.Spaces.LP26.nonVacuity_lemma_5_6_instances
#print axioms RelativeFM.Spaces.LP26.isOpenImmersion_id
#print axioms RelativeFM.Spaces.LP26.nonVacuity_lemma_5_7
#print axioms RelativeFM.Spaces.LP26.hasInducedTStructure_inverseImage
#print axioms RelativeFM.Spaces.LP26.forall_homology_truncLE_truncGE
#print axioms RelativeFM.Spaces.LP26.isQuasicoherentOnSite_of_isZero
#print axioms RelativeFM.Spaces.LP26.supportOfSheaf_subset_of_isZero
#print axioms RelativeFM.Spaces.LP26.supportOfSheaf_subset_of_iso
#print axioms RelativeFM.Spaces.LP26.hasInducedTStructure_qcohDerived
#print axioms RelativeFM.Spaces.LP26.standardTStructureQc
#print axioms RelativeFM.Spaces.LP26.hasInducedTStructure_qcSupportedOn
#print axioms RelativeFM.Spaces.LP26.standardTStructure
#print axioms RelativeFM.Spaces.LP26.standardTStructure_isLE_iff
#print axioms RelativeFM.Spaces.LP26.standardTStructure_isGE_iff
#print axioms RelativeFM.Spaces.LP26.standardTStructure_le_iff
#print axioms RelativeFM.Spaces.LP26.standardTStructure_ge_iff
-- LP26 Lemma 5.9 over algebraic spaces (wave 8, `Spaces/LP26/Lemma59.lean`)
#print axioms RelativeFM.Spaces.LP26.minusC
#print axioms RelativeFM.Spaces.LP26.boundedC
#print axioms RelativeFM.Spaces.LP26.isZero_homology_obj₃_of_epi_of_mono
#print axioms RelativeFM.Spaces.LP26.isPseudoCoherentComplexFrom_of_le
#print axioms RelativeFM.Spaces.LP26.isPseudoCoherentFrom_of_le
#print axioms RelativeFM.Spaces.LP26.isQuasiCompact_ι_compl
#print axioms RelativeFM.Spaces.LP26.standardMinusC_of_isCompactObject
#print axioms RelativeFM.Spaces.LP26.lemma_5_9
#print axioms RelativeFM.Spaces.LP26.standardTStructure_plus_iff
#print axioms RelativeFM.Spaces.LP26.standardTStructure_minus_iff
#print axioms RelativeFM.Spaces.LP26.lemma_5_9_minus_noetherian
#print axioms RelativeFM.Spaces.LP26.lemma_5_9_bounded_noetherian
#print axioms RelativeFM.Spaces.LP26.lemma_5_9_minus_eq
#print axioms RelativeFM.Spaces.LP26.lemma_5_9_bounded_eq
#print axioms RelativeFM.Spaces.LP26.nonVacuity_lemma_5_9
#print axioms RelativeFM.Spaces.LP26.nonVacuity_lemma_5_9_noetherian
-- LP26 Theorem 1.1 and compactness for a coproduct universe `w` independent of the Hom
-- universe (wave 8, `Spaces/Stacks/{Bridges,Corollaries,UniverseNonVacuity}.lean`)
#print axioms RelativeFM.Spaces.Stacks.isCompactObject_iff_sumUniverse_isCompactAb
#print axioms RelativeFM.Spaces.Stacks.isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq_univ
#print axioms RelativeFM.Spaces.Stacks.theorem_1_1_univ
#print axioms RelativeFM.Spaces.Stacks.theorem_1_1
#print axioms RelativeFM.Spaces.Stacks.theorem_1_1_univ_zero
#print axioms RelativeFM.Spaces.Stacks.theorem_1_1_univ_zero_D
#print axioms RelativeFM.Spaces.Stacks.isCompactAb_zero_D
#print axioms RelativeFM.Spaces.Stacks.lemma_A_9_sumUniverse
#print axioms RelativeFM.Spaces.Stacks.lemma_A_9_sumUniverse_affine
-- GL26 Lemmas A.4 and A.6 over algebraic spaces (wave 8, `Spaces/LP26/Recollement.lean`)
#print axioms RelativeFM.Spaces.LP26.RecollementOfAdjoints.exists_distinguished
#print axioms RelativeFM.Spaces.LP26.RecollementOfAdjoints.exists_natural_connecting
#print axioms RelativeFM.Spaces.LP26.RecollementOfAdjoints.Data.toRecollement
#print axioms RelativeFM.Spaces.LP26.pushFullyFaithful
#print axioms RelativeFM.Spaces.LP26.exists_inclZ_of_isZero_pullZ
#print axioms RelativeFM.Spaces.LP26.lemma_A_4
#print axioms RelativeFM.Spaces.LP26.lemma_A_4_nonVacuity
#print axioms RelativeFM.Spaces.LP26.isLE_isGE_rightAdjoint_of_equivalence
#print axioms RelativeFM.Spaces.LP26.lemma_A_6_aux
#print axioms RelativeFM.Spaces.LP26.lemma_A_6
#print axioms RelativeFM.Spaces.LP26.lemma_A_6_bounded
#print axioms RelativeFM.Spaces.LP26.lemma_A_6_nonVacuity
-- LP26 Definition 5.3 and Proposition 5.8 (W.A.) over algebraic spaces (wave 8)
#print axioms RelativeFM.Spaces.LP26.SatisfiesWA
#print axioms RelativeFM.Spaces.LP26.SatisfiesStandardWA
#print axioms RelativeFM.Spaces.LP26.satisfiesWA_of_satisfiesStandardWA
#print axioms RelativeFM.Spaces.LP26.proposition_5_8
#print axioms RelativeFM.Spaces.LP26.satisfiesPaperWA_of_forall_isZero
#print axioms RelativeFM.Spaces.LP26.satisfiesWA_of_isEmpty
#print axioms RelativeFM.Spaces.LP26.proposition_5_8_nonVacuity
-- LP26 Corollary 1.2 over algebraic spaces (wave 8, `Spaces/LP26/Corollary12.lean`)
#print axioms RelativeFM.Spaces.LP26.UniverseDescent.small_nonzero
#print axioms RelativeFM.Spaces.LP26.UniverseDescent.isCompactAb_of_max
#print axioms RelativeFM.Spaces.LP26.UniverseDescent.coprod_le
#print axioms RelativeFM.Spaces.LP26.UniverseDescent.satisfiesPaperWA_of_max
#print axioms RelativeFM.Spaces.LP26.satisfiesPaperWA_dqcZ_of_dqcSupported
#print axioms RelativeFM.Spaces.LP26.satisfiesPaperWA_dqcZ_of_paperM2
#print axioms RelativeFM.Spaces.LP26.exists_fg_eq_zeroLocusPoints
#print axioms RelativeFM.Spaces.LP26.satisfiesWA_space
#print axioms RelativeFM.Spaces.LP26.isOpenImmersion_of_isIso'
#print axioms RelativeFM.Spaces.LP26.satisfiesWA_of_iso
#print axioms RelativeFM.Spaces.LP26.corollary_1_2
#print axioms RelativeFM.Spaces.LP26.corollary_1_2_dqc
#print axioms RelativeFM.Spaces.LP26.corollary_1_2_nonVacuity
#print axioms RelativeFM.Spaces.LP26.corollary_1_2_int_witness

-- LP26 Proposition 5.8 and Corollary 1.2, standard W.A. (wave 9, `Spaces/LP26/StandardWA.lean`)
#print axioms RelativeFM.Spaces.LP26.GluedPreferred.tStructureEquivalent_of_paperData
#print axioms RelativeFM.Spaces.LP26.GluedPreferred.exists_paperData_of_gluedBounds
#print axioms RelativeFM.Spaces.LP26.GluedPreferred.exists_paperData_of_gluedBounds_univ
#print axioms RelativeFM.Spaces.LP26.GluedPreferred.exists_paperData_eq_of_forall_isZero
#print axioms RelativeFM.Spaces.LP26.satisfiesStandardWA_of_isEmpty
#print axioms RelativeFM.Spaces.LP26.proposition_5_8_standard
#print axioms RelativeFM.Spaces.LP26.proposition_5_8_standard_nonVacuity
#print axioms RelativeFM.Spaces.LP26.exists_affineData_standard
#print axioms RelativeFM.Spaces.LP26.isLE_derivedAssociated_iff
#print axioms RelativeFM.Spaces.LP26.satisfiesStandardWA_space
#print axioms RelativeFM.Spaces.LP26.satisfiesStandardWA_of_iso
#print axioms RelativeFM.Spaces.LP26.corollary_1_2_standard
#print axioms RelativeFM.Spaces.LP26.corollary_1_2_standard_nonVacuity

-- LP26 Corollary 1.2, coherence for Noetherian `X` (wave 9, `Spaces/LP26/Coherence.lean`)
#print axioms RelativeFM.Spaces.LP26.minusC_eq_of_tStructureEquivalent
#print axioms RelativeFM.Spaces.LP26.boundedC_eq_of_tStructureEquivalent
#print axioms RelativeFM.Spaces.LP26.tStructureEquivalent_of_inPreferredClass
#print axioms RelativeFM.Spaces.LP26.inPreferredClass_of_paperData_univ
#print axioms RelativeFM.Spaces.LP26.isCoherent_of_restricts
#print axioms RelativeFM.Spaces.LP26.coherent_homology_truncLE_truncGE
#print axioms RelativeFM.Spaces.LP26.standardMinusC_trunc
#print axioms RelativeFM.Spaces.LP26.inPreferredClass_standardTStructure
#print axioms RelativeFM.Spaces.LP26.minusC_boundedC_eq_standard
#print axioms RelativeFM.Spaces.LP26.corollary_1_2_coherent
#print axioms RelativeFM.Spaces.LP26.corollary_1_2_coherent_nonVacuity

-- GL26 Lemmas 2.14, 2.15, 2.18, 3.2 (wave 10, `Spaces/Conservative/`)
#print axioms RelativeFM.Spaces.Conservative.homologyPullIsoOfIsFlat
#print axioms RelativeFM.Spaces.Conservative.isZero_of_isZero_modulePullback
#print axioms RelativeFM.Spaces.Conservative.lemma_2_14
#print axioms RelativeFM.Spaces.Conservative.lemma_2_14_isIso
#print axioms RelativeFM.Spaces.Conservative.lemma_2_15
#print axioms RelativeFM.Spaces.Conservative.lemma_2_15_homology
#print axioms RelativeFM.Spaces.Conservative.lemma_2_18
#print axioms RelativeFM.Spaces.Conservative.lemma_3_2_of_factorization
#print axioms RelativeFM.Spaces.Conservative.nonVacuity_faithfullyFlat
#print axioms RelativeFM.Spaces.Conservative.nonVacuity_lemma_2_15
#print axioms RelativeFM.Spaces.Conservative.isQuasiAffineHom_of_isIso
#print axioms RelativeFM.Spaces.Conservative.nonVacuity_lemma_2_18
#print axioms RelativeFM.Spaces.Conservative.nonVacuity_lemma_3_2
-- GL26 §2.4, duality for spaces (wave 10, `Spaces/Duality/`)
#print axioms RelativeFM.Spaces.Duality.Tag0E55Input
#print axioms RelativeFM.Spaces.Duality.Tag04NXInput
#print axioms RelativeFM.Spaces.Duality.IsNoethSepFpHom
#print axioms RelativeFM.Spaces.Duality.Compactification
#print axioms RelativeFM.Spaces.Duality.upperTimes
#print axioms RelativeFM.Spaces.Duality.upperTimesAdj
#print axioms RelativeFM.Spaces.Duality.upperTimesCompIso
#print axioms RelativeFM.Spaces.Duality.upperShriek
#print axioms RelativeFM.Spaces.Duality.hom_push_eq_zero
#print axioms RelativeFM.Spaces.Duality.bijective_comp_unit
#print axioms RelativeFM.Spaces.Duality.pushPullAdj
#print axioms RelativeFM.Spaces.Duality.upperTimesIsoPullQc
#print axioms RelativeFM.Spaces.Duality.upperTimesIsoUpperShriek
#print axioms RelativeFM.Spaces.Duality.lemma_2_22
#print axioms RelativeFM.Spaces.Duality.isNoethSepFpHom_id
#print axioms RelativeFM.Spaces.Duality.lemma_2_22_hypotheses_satisfiable
-- GL26 §2.2 internal Hom: Lemmas 2.10, 2.11, 2.16 (wave 10, `Spaces/InternalHom/`)
#print axioms RelativeFM.Spaces.coherator
#print axioms RelativeFM.Spaces.coheratorAdj
#print axioms RelativeFM.Spaces.tensorQcRightQcHomAdj
#print axioms RelativeFM.Spaces.lemma_2_11
#print axioms RelativeFM.Spaces.lemma_2_11_of_mem
#print axioms RelativeFM.Spaces.lemma_2_11_of_mem_hom
#print axioms RelativeFM.Spaces.lemma_2_11_of_isPseudoCoherent
#print axioms RelativeFM.Spaces.sheafHomObj_mem_Dqc_of_isPseudoCoherent
#print axioms RelativeFM.Spaces.sheafHomObj_mem_Dqc_of_perfect
#print axioms RelativeFM.Spaces.sheafHomIsoTensorDualRight
#print axioms RelativeFM.Spaces.tensorBraiding
#print axioms RelativeFM.Spaces.tensorAssoc
#print axioms RelativeFM.Spaces.lemma_2_10
#print axioms RelativeFM.Spaces.lemma_2_10_app
#print axioms RelativeFM.Spaces.lemma_2_10_naturality
#print axioms RelativeFM.Spaces.qcHomPullbackMap
#print axioms RelativeFM.Spaces.qcHomPullbackMap_comp_counit
#print axioms RelativeFM.Spaces.isIso_qcHomPullbackMap_of_isIso
#print axioms RelativeFM.Spaces.lemma_2_16_perfect
#print axioms RelativeFM.Spaces.lemma_2_16_perfect_qcqs
#print axioms RelativeFM.Spaces.lemma_2_16_pseudoCoherent_of_isIso
#print axioms RelativeFM.Spaces.exists_coherator_affine
#print axioms RelativeFM.Spaces.lemma_2_11_nonVacuity
#print axioms RelativeFM.Spaces.lemma_2_10_nonVacuity
#print axioms RelativeFM.Spaces.lemma_2_16_perfect_nonVacuity
#print axioms RelativeFM.Spaces.lemma_2_16_pseudoCoherent_nonVacuity
-- GL26 §5 quasi-perfect objects: Lemmas 5.3 (1), (2), 5.9 (wave 11, `Spaces/QuasiPerfect/`)
#print axioms RelativeFM.Spaces.QuasiPerfect.Tag09JBInput
#print axioms RelativeFM.Spaces.QuasiPerfect.Tag0GFHInput
#print axioms RelativeFM.Spaces.QuasiPerfect.Tag0GFIInput
#print axioms RelativeFM.Spaces.QuasiPerfect.QcohTruncLEInput
#print axioms RelativeFM.Spaces.QuasiPerfect.StructureSheafQcohInput
#print axioms RelativeFM.Spaces.QuasiPerfect.perf_tensorObj
#print axioms RelativeFM.Spaces.QuasiPerfect.pullQcPushQcAdj
#print axioms RelativeFM.Spaces.QuasiPerfect.projectionFormulaMap_naturality
#print axioms RelativeFM.Spaces.QuasiPerfect.projNatTrans
#print axioms RelativeFM.Spaces.QuasiPerfect.projIsoQc
#print axioms RelativeFM.Spaces.QuasiPerfect.lemma_5_9_of_adj
#print axioms RelativeFM.Spaces.QuasiPerfect.lemma_5_9
#print axioms RelativeFM.Spaces.QuasiPerfect.lemma_5_9_app
#print axioms RelativeFM.Spaces.QuasiPerfect.lemma_5_3_tensor
#print axioms RelativeFM.Spaces.QuasiPerfect.upperTimes_isGE
#print axioms RelativeFM.Spaces.QuasiPerfect.homEquivShift
#print axioms RelativeFM.Spaces.QuasiPerfect.lemma_5_3_bounded_of_bounded
#print axioms RelativeFM.Spaces.QuasiPerfect.structureSheafQc
#print axioms RelativeFM.Spaces.QuasiPerfect.lemma_5_3_bounded
#print axioms RelativeFM.Spaces.QuasiPerfect.isQcqsHom_id
#print axioms RelativeFM.Spaces.QuasiPerfect.lemma_5_9_nonVacuity
#print axioms RelativeFM.Spaces.QuasiPerfect.lemma_5_3_nonVacuity
-- GL26 §2.3 functoriality on kernels: Lemmas 2.25, 2.26 (wave 11, `Spaces/Kernels/`)
#print axioms RelativeFM.Spaces.Kernels.tensorLeftUnitor
#print axioms RelativeFM.Spaces.Kernels.Dqc_structureObj
#print axioms RelativeFM.Spaces.Kernels.projNatRight
#print axioms RelativeFM.Spaces.Kernels.isPullback_triple
#print axioms RelativeFM.Spaces.Kernels.isQuasiCompact_diagonal
#print axioms RelativeFM.Spaces.Kernels.isQuasiSeparated_diagonal
#print axioms RelativeFM.Spaces.Kernels.diagTrans
#print axioms RelativeFM.Spaces.Kernels.isIso_diagTrans_app
#print axioms RelativeFM.Spaces.Kernels.lemma_2_25Iso
#print axioms RelativeFM.Spaces.Kernels.lemma_2_25IsoQc
#print axioms RelativeFM.Spaces.Kernels.lemma_2_25_of_isProper
#print axioms RelativeFM.Spaces.Kernels.lemma_2_25
#print axioms RelativeFM.Spaces.Kernels.convolution
#print axioms RelativeFM.Spaces.Kernels.isIso_theta_app
#print axioms RelativeFM.Spaces.Kernels.convRight
#print axioms RelativeFM.Spaces.Kernels.isIso_convRight_app
#print axioms RelativeFM.Spaces.Kernels.lemma_2_26_of
#print axioms RelativeFM.Spaces.Kernels.lemma_2_26
#print axioms RelativeFM.Spaces.Kernels.lemma_2_25_nonVacuity
#print axioms RelativeFM.Spaces.Kernels.lemma_2_26_nonVacuity
