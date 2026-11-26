/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.AxiomMathInputs
import Spaces.NonVacuity
import Spaces.Statements

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
