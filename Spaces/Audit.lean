/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Affine.WeakApprox
import Spaces.AxiomMathInputs
import Spaces.NonVacuity
import Spaces.Statements
import Spaces.Supported.CompactGeneration
import Spaces.Supported.Preferred
import Spaces.BaseChange.Cube
import Spaces.LP26.Lemma59
import Spaces.LP26.NonVacuity
import Spaces.LP26.StandardTStructure
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
