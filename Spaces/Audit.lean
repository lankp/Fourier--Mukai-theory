/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.AxiomMathInputs
import Spaces.NonVacuity
import Spaces.BaseChange.Cube

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
