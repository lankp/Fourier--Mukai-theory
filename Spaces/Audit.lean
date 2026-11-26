/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.AxiomMathInputs
import Spaces.NonVacuity
import Spaces.Supported.CompactGeneration

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
