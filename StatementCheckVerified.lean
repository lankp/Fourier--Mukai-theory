/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpacesVerified

/-!
# Statement check for `SpacesVerified`

The pinned statements of `SpacesVerified`: the tagged AxiomMath inputs of
`Spaces/AxiomMathInputs.lean`, proved by the AxiomMath theorems they name, and the
unconditional consequences.  Checked by `scripts/check_statements.sh --verified` against
`results/statement-baseline-verified.txt`; it needs `lake build SpacesVerified` (the full
AxiomMath build), so it is separate from the `--spaces` check.
-/

@[expose] public section
#check @RelativeFM.SpacesVerified.tag06UQ
#check @RelativeFM.SpacesVerified.tag08F4
#check @RelativeFM.SpacesVerified.tag08F5
#check @RelativeFM.SpacesVerified.tag08FA
#check @RelativeFM.SpacesVerified.Dqc_isTriangulated
#check @RelativeFM.SpacesVerified.tag06LT
#check @RelativeFM.SpacesVerified.isQuasiCompactOfIsIso
#check @RelativeFM.SpacesVerified.universallyClosedOfIsIso
#check @RelativeFM.SpacesVerified.isFlatId
#check @RelativeFM.SpacesVerified.affineQuasiSeparated
#check @RelativeFM.SpacesVerified.setup_hypotheses_satisfiable_unconditional
#check @RelativeFM.SpacesVerified.tag06Z0Exact
#check @RelativeFM.SpacesVerified.tag06Z0Qcoh
#check @RelativeFM.SpacesVerified.tag06Z0
#check @RelativeFM.SpacesVerified.tag07TY
#check @RelativeFM.SpacesVerified.tag021R
#check @RelativeFM.SpacesVerified.lp26_cor_1_2_affine_unconditional
#check @RelativeFM.SpacesVerified.lp26_cor_1_2_affine_int_unconditional
#check @RelativeFM.SpacesVerified.tag08F3
#check @RelativeFM.SpacesVerified.supportTriangulated
#check @RelativeFM.SpacesVerified.supportedDirectSums
#check @RelativeFM.SpacesVerified.tag0AEC
#check @RelativeFM.SpacesVerified.tag0AED
#check @RelativeFM.SpacesVerified.tag0GFD
#check @RelativeFM.SpacesVerified.affineQuasiSeparatedYoneda
#check @RelativeFM.SpacesVerified.containsTerminal
#check @RelativeFM.SpacesVerified.lemma_A_9_unconditional
#check @RelativeFM.SpacesVerified.lemma_A_9_affine_univ_unconditional
#check @RelativeFM.SpacesVerified.compIsoAgree
#check @RelativeFM.SpacesVerified.flatBaseChange
#check @RelativeFM.SpacesVerified.tag08IN
#check @RelativeFM.SpacesVerified.lemma_6_11_unconditional
#check @RelativeFM.SpacesVerified.lemma_10_1_of_flatBaseChange
#check @RelativeFM.SpacesVerified.lemma_6_11_id_unconditional
#check @RelativeFM.SpacesVerified.lemma_10_1_id_unconditional
#check @RelativeFM.SpacesVerified.tag0GFI
#check @RelativeFM.SpacesVerified.perfectBoundedAboveSupported
#check @RelativeFM.SpacesVerified.tag09M8
#check @RelativeFM.SpacesVerified.perfectBoundedAbove
#check @RelativeFM.SpacesVerified.tag09MB
#check @RelativeFM.SpacesVerified.tag08FB
#check @RelativeFM.SpacesVerified.tag08FABound
#check @RelativeFM.SpacesVerified.tag0AFJ
#check @RelativeFM.SpacesVerified.perfectPseudoCoherent
#check @RelativeFM.SpacesVerified.tag08FVTwo
#check @RelativeFM.SpacesVerified.pseudoCoherentFromOfIsLE
#check @RelativeFM.SpacesVerified.tag08FU2
#check @RelativeFM.SpacesVerified.perfectQcoh
#check @RelativeFM.SpacesVerified.tag08HP
#check @RelativeFM.SpacesVerified.tag073B
#check @RelativeFM.SpacesVerified.openSubspaceQuasiCompact
#check @RelativeFM.SpacesVerified.tag08IK
#check @RelativeFM.SpacesVerified.tag079Q
#check @RelativeFM.SpacesVerified.tag0A8G
#check @RelativeFM.SpacesVerified.rightAdjointCoproducts
#check @RelativeFM.SpacesVerified.pullbackSupport
#check @RelativeFM.SpacesVerified.pullbackDisjoint
#check @RelativeFM.SpacesVerified.etaleRestrictionSupport
#check @RelativeFM.SpacesVerified.openImmersionCounit
#check @RelativeFM.SpacesVerified.quasiCompactSource
#check @RelativeFM.SpacesVerified.tag073BTwo
#check @RelativeFM.SpacesVerified.compactComplPreimage
#check @RelativeFM.SpacesVerified.perfectPullback
#check @RelativeFM.SpacesVerified.tag08GGUnit
#check @RelativeFM.SpacesVerified.tag08GGCounit
#check @RelativeFM.SpacesVerified.edsTop
#check @RelativeFM.SpacesVerified.supportEmpty
#check @RelativeFM.SpacesVerified.tag09IT
#check @RelativeFM.SpacesVerified.edsOfComplSubset
#check @RelativeFM.SpacesVerified.lemma_5_5_unconditional
#check @RelativeFM.SpacesVerified.lemma_5_5_dqc_unconditional
#check @RelativeFM.SpacesVerified.lemma_5_6_unconditional
#check @RelativeFM.SpacesVerified.lemma_5_6_dqcZ_unconditional
#check @RelativeFM.SpacesVerified.lemma_5_7_unconditional
#check @RelativeFM.SpacesVerified.lemma_5_7_supported_unconditional
#check @RelativeFM.SpacesVerified.lemma_5_9_unconditional
#check @RelativeFM.SpacesVerified.lemma_5_9_minus_noetherian_unconditional
#check @RelativeFM.SpacesVerified.lemma_5_9_bounded_noetherian_unconditional
#check @RelativeFM.SpacesVerified.lemma_5_9_minus_eq_unconditional
#check @RelativeFM.SpacesVerified.lemma_5_9_bounded_eq_unconditional
#check @RelativeFM.SpacesVerified.proposition_5_8_unconditional
#check @RelativeFM.SpacesVerified.corollary_1_2_unconditional
#check @RelativeFM.SpacesVerified.corollary_1_2_dqc_unconditional
#check @RelativeFM.SpacesVerified.lemma_A_4_unconditional
#check @RelativeFM.SpacesVerified.lemma_A_6_unconditional
#check @RelativeFM.SpacesVerified.lemma_A_6_bounded_unconditional
#check @RelativeFM.SpacesVerified.lemma_A_9_preferred_univ_unconditional
#check @RelativeFM.SpacesVerified.nonVacuity_lemma_5_5_unconditional
#check @RelativeFM.SpacesVerified.nonVacuity_lemma_5_6_unconditional
#check @RelativeFM.SpacesVerified.nonVacuity_lemma_5_7_unconditional
#check @RelativeFM.SpacesVerified.nonVacuity_lemma_5_9_unconditional
#check @RelativeFM.SpacesVerified.nonVacuity_lemma_5_9_noetherian_unconditional
#check @RelativeFM.SpacesVerified.proposition_5_8_nonVacuity_unconditional
#check @RelativeFM.SpacesVerified.corollary_1_2_nonVacuity_unconditional
#check @RelativeFM.SpacesVerified.corollary_1_2_int_witness_unconditional
#check @RelativeFM.SpacesVerified.lemma_A_4_nonVacuity_unconditional
#check @RelativeFM.SpacesVerified.lemma_A_6_nonVacuity_unconditional
#check @RelativeFM.SpacesVerified.nonVacuity_detectsBelowUniformly_affine_unconditional
#check @RelativeFM.SpacesVerified.koszulSp_eq_koszul
#check @RelativeFM.SpacesVerified.vanishesWhereUnitSp_eq
#check @RelativeFM.SpacesVerified.unitLocusSieveSp_eq
#check @RelativeFM.SpacesVerified.koszulTorsion
#check @RelativeFM.SpacesVerified.koszulDetection
#check @RelativeFM.SpacesVerified.koszulQcoh
#check @RelativeFM.SpacesVerified.koszulCompact
#check @RelativeFM.SpacesVerified.unitLocusList
#check @RelativeFM.SpacesVerified.koszulRestrict
#check @RelativeFM.SpacesVerified.vanishesWhereUnit
#check @RelativeFM.SpacesVerified.edsOpenQc
#check @RelativeFM.SpacesVerified.edsOpenQs
#check @RelativeFM.SpacesVerified.openCounit
#check @RelativeFM.SpacesVerified.pushforwardQcohDerived
#check @RelativeFM.SpacesVerified.perfectQcohSupported
#check @RelativeFM.SpacesVerified.rangeOpenSubspace
#check @RelativeFM.SpacesVerified.preimageQc
#check @RelativeFM.SpacesVerified.shriekSupport
#check @RelativeFM.SpacesVerified.shriekPerfect
#check @RelativeFM.SpacesVerified.shriekRestrictOpen
#check @RelativeFM.SpacesVerified.tag09IV
#check @RelativeFM.SpacesVerified.supportPullbackEtale
#check @RelativeFM.SpacesVerified.stepInputs
#check @RelativeFM.SpacesVerified.supportedDetectsBelowStatement_unconditional
#check @RelativeFM.SpacesVerified.lemma_A_9_preferred_unconditional
#check @RelativeFM.SpacesVerified.lemma_A_9_detectsBelowUniformly_unconditional
#check @RelativeFM.SpacesVerified.nonVacuity_detectsBelowUniformly_unconditional
#check @RelativeFM.SpacesVerified.nonVacuity_detectsBelowUniformly_affine_general_unconditional
#check @RelativeFM.SpacesVerified.proposition_5_8_standard_unconditional
#check @RelativeFM.SpacesVerified.corollary_1_2_standard_unconditional
#check @RelativeFM.SpacesVerified.proposition_5_8_standard_nonVacuity_unconditional
#check @RelativeFM.SpacesVerified.corollary_1_2_standard_nonVacuity_unconditional
#check @RelativeFM.SpacesVerified.locallySmall_D
#check @RelativeFM.SpacesVerified.locallySmall_dqcZ_unconditional
#check @RelativeFM.SpacesVerified.locallySmall_qcohDerived
#check @RelativeFM.SpacesVerified.theorem_1_1_dqcZ_unconditional
#check @RelativeFM.SpacesVerified.theorem_1_1_dqcZ_nonVacuity_unconditional
#check @RelativeFM.SpacesVerified.theorem_1_1_dqcZ_nonVacuity_affine_unconditional
#print axioms RelativeFM.SpacesVerified.tag06UQ
#print axioms RelativeFM.SpacesVerified.tag08F4
#print axioms RelativeFM.SpacesVerified.tag08F5
#print axioms RelativeFM.SpacesVerified.tag08FA
#print axioms RelativeFM.SpacesVerified.Dqc_isTriangulated
#print axioms RelativeFM.SpacesVerified.tag06LT
#print axioms RelativeFM.SpacesVerified.isQuasiCompactOfIsIso
#print axioms RelativeFM.SpacesVerified.universallyClosedOfIsIso
#print axioms RelativeFM.SpacesVerified.isFlatId
#print axioms RelativeFM.SpacesVerified.affineQuasiSeparated
#print axioms RelativeFM.SpacesVerified.setup_hypotheses_satisfiable_unconditional
#print axioms RelativeFM.SpacesVerified.tag06Z0Exact
#print axioms RelativeFM.SpacesVerified.tag06Z0Qcoh
#print axioms RelativeFM.SpacesVerified.tag06Z0
#print axioms RelativeFM.SpacesVerified.tag07TY
#print axioms RelativeFM.SpacesVerified.tag021R
#print axioms RelativeFM.SpacesVerified.lp26_cor_1_2_affine_unconditional
#print axioms RelativeFM.SpacesVerified.lp26_cor_1_2_affine_int_unconditional
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
#print axioms RelativeFM.SpacesVerified.compIsoAgree
#print axioms RelativeFM.SpacesVerified.flatBaseChange
#print axioms RelativeFM.SpacesVerified.tag08IN
#print axioms RelativeFM.SpacesVerified.lemma_6_11_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_10_1_of_flatBaseChange
#print axioms RelativeFM.SpacesVerified.lemma_6_11_id_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_10_1_id_unconditional
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
#print axioms RelativeFM.SpacesVerified.lemma_5_5_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_5_dqc_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_6_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_6_dqcZ_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_7_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_7_supported_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_9_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_9_minus_noetherian_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_9_bounded_noetherian_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_9_minus_eq_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_9_bounded_eq_unconditional
#print axioms RelativeFM.SpacesVerified.proposition_5_8_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_dqc_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_4_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_6_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_6_bounded_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_9_preferred_univ_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_lemma_5_5_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_lemma_5_6_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_lemma_5_7_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_lemma_5_9_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_lemma_5_9_noetherian_unconditional
#print axioms RelativeFM.SpacesVerified.proposition_5_8_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_int_witness_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_4_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_6_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_detectsBelowUniformly_affine_unconditional
#print axioms RelativeFM.SpacesVerified.koszulSp_eq_koszul
#print axioms RelativeFM.SpacesVerified.vanishesWhereUnitSp_eq
#print axioms RelativeFM.SpacesVerified.unitLocusSieveSp_eq
#print axioms RelativeFM.SpacesVerified.koszulTorsion
#print axioms RelativeFM.SpacesVerified.koszulDetection
#print axioms RelativeFM.SpacesVerified.koszulQcoh
#print axioms RelativeFM.SpacesVerified.koszulCompact
#print axioms RelativeFM.SpacesVerified.unitLocusList
#print axioms RelativeFM.SpacesVerified.koszulRestrict
#print axioms RelativeFM.SpacesVerified.vanishesWhereUnit
#print axioms RelativeFM.SpacesVerified.edsOpenQc
#print axioms RelativeFM.SpacesVerified.edsOpenQs
#print axioms RelativeFM.SpacesVerified.openCounit
#print axioms RelativeFM.SpacesVerified.pushforwardQcohDerived
#print axioms RelativeFM.SpacesVerified.perfectQcohSupported
#print axioms RelativeFM.SpacesVerified.rangeOpenSubspace
#print axioms RelativeFM.SpacesVerified.preimageQc
#print axioms RelativeFM.SpacesVerified.shriekSupport
#print axioms RelativeFM.SpacesVerified.shriekPerfect
#print axioms RelativeFM.SpacesVerified.shriekRestrictOpen
#print axioms RelativeFM.SpacesVerified.tag09IV
#print axioms RelativeFM.SpacesVerified.supportPullbackEtale
#print axioms RelativeFM.SpacesVerified.stepInputs
#print axioms RelativeFM.SpacesVerified.supportedDetectsBelowStatement_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_9_preferred_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_9_detectsBelowUniformly_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_detectsBelowUniformly_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_detectsBelowUniformly_affine_general_unconditional
#print axioms RelativeFM.SpacesVerified.proposition_5_8_standard_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_standard_unconditional
#print axioms RelativeFM.SpacesVerified.proposition_5_8_standard_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_standard_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.locallySmall_D
#print axioms RelativeFM.SpacesVerified.locallySmall_dqcZ_unconditional
#print axioms RelativeFM.SpacesVerified.locallySmall_qcohDerived
#print axioms RelativeFM.SpacesVerified.theorem_1_1_dqcZ_unconditional
#print axioms RelativeFM.SpacesVerified.theorem_1_1_dqcZ_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.theorem_1_1_dqcZ_nonVacuity_affine_unconditional
