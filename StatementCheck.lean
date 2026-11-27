/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai
import WeakApprox

/-!
# Statement check

An independent check of the *statements* the repository proves, separate from
the proofs.  Every declaration below is printed with `#check` (its full type,
implicits included) and with `#print axioms`; `scripts/check_statements.sh`
diffs that output against `results/statement-baseline.txt`, so a silently
weakened statement, a strengthened hypothesis or a new axiom fails CI even when
every proof still compiles.

This is the repository's version of the "challenge / comparator" pattern: a
pinned statement surface plus a permitted-axiom list.  It is weaker than a full
`lean4export` + `comparator` run, which additionally replays each proof term
against a trusted kernel; what it does establish is that the *statements* have
not drifted since the baseline was recorded.

Regenerate after an intentional change:

    scripts/check_statements.sh --update
-/

@[expose] public section

/-! ## GL26 Lemma 2.25 — `Φ_{RΔ_*O_Y} ≅ 𝟭` -/

#check @RelativeFM.Noetherian.lemma_2_25Statement_proved
#check @RelativeFM.Noetherian.lemma_2_25Statement_proved_no_properFlat
#check @RelativeFM.lemma_2_25
#check @RelativeFM.AffineDiagonalContext.affine_lemma_2_25
#check @RelativeFM.DerivedDiagonalInput.identityIso
#check @RelativeFM.DiagonalFunctorialityInput.identityTransformIso
#print axioms RelativeFM.Noetherian.lemma_2_25Statement_proved
#print axioms RelativeFM.Noetherian.lemma_2_25Statement_proved_no_properFlat
#print axioms RelativeFM.lemma_2_25
#print axioms RelativeFM.AffineDiagonalContext.affine_lemma_2_25
#print axioms RelativeFM.DerivedDiagonalInput.identityIso
#print axioms RelativeFM.DiagonalFunctorialityInput.identityTransformIso

/-! ## GL26 Lemma 2.26 and Lemma 5.4 -/

#check @RelativeFM.Convolution.NoetherianBridge.lemma_2_26_of_correction
#check @RelativeFM.Lemma54.externalTensor_compactlyGenerates
#print axioms RelativeFM.Convolution.NoetherianBridge.lemma_2_26_of_correction
#print axioms RelativeFM.Lemma54.externalTensor_compactlyGenerates

/-! ## LP (gluing weak approximability) Theorem 1.1 -/

#check @RelativeWeakApprox.PaperM2.PaperSetupMainMinimal.theorem_1_1
#check @RelativeWeakApprox.PaperHypothesesW6.theorem_1_1_paper
#print axioms RelativeWeakApprox.PaperM2.PaperSetupMainMinimal.theorem_1_1
#print axioms RelativeWeakApprox.PaperHypothesesW6.theorem_1_1_paper

/-! ## Neeman's weak approximability: the affine supported base -/

#check @RelativeFM.PrincipalNeemanM1.satisfiesPaperWA
#check @RelativeFM.IdealNeemanM1.satisfiesPaperWA_idealSupported
#check @RelativeFM.AffineSupportedSchemeBaseM1.neemanSupported_of_qc_closedComplement
#check @RelativeFM.AffineSupportedSchemeBaseM1.neemanSupportedWeakApproximability_of_isAffine
#check @RelativeFM.NeemanAffineSupport.satisfiesPaperWA_of_fg
#print axioms RelativeFM.PrincipalNeemanM1.satisfiesPaperWA
#print axioms RelativeFM.IdealNeemanM1.satisfiesPaperWA_idealSupported
#print axioms RelativeFM.AffineSupportedSchemeBaseM1.neemanSupported_of_qc_closedComplement
#print axioms RelativeFM.AffineSupportedSchemeBaseM1.neemanSupportedWeakApproximability_of_isAffine
#print axioms RelativeFM.NeemanAffineSupport.satisfiesPaperWA_of_fg
