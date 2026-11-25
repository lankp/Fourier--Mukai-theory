/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai

/-!
# Axiom audit

Run `lean FourierMukai/Audit.lean` to see which declarations depend on `sorryAx`.
Everything under `FourierMukai.Prelim` and `FourierMukai.Examples` should be free
of `sorryAx`; the statements in `FourierMukai.Paper.Statements` are expected to
depend on it (they are formalization targets, not proved theorems), with the one
exception of `lemma_2_25`, which is proved from the inputs its paper proof uses.
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
#print axioms RelativeFM.Trinatural.isIso_iff_of_precomp_essentiallyDense₀
#print axioms RelativeFM.lemma_2_5
#print axioms RelativeFM.Trinatural.ofNatTrans
#print axioms RelativeFM.lemma_2_25
#print axioms RelativeFM.Noetherian.lemma_2_25Statement_proved
#print axioms RelativeFM.AffineDiagonalContext.affine_lemma_2_25
#print axioms RelativeFM.DerivedDiagonalInput.identityIso
#print axioms RelativeFM.DiagonalFunctorialityInput.identityTransformIso

-- Stated only (expected to depend on `sorryAx`):
#print axioms RelativeFM.theorem_1_3
#print axioms RelativeFM.theorem_12_3
#print axioms RelativeFM.theorem_1_2_open
#print axioms RelativeFM.theorem_1_2_baseChange
#print axioms RelativeFM.corollary_6_18
#print axioms RelativeFM.lemma_12_2
#print axioms RelativeFM.theorem_1_6
#print axioms RelativeFM.lemma_2_26
#print axioms RelativeFM.theorem_1_7
