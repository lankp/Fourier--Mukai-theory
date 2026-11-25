/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.RegularCompact
import FourierMukai.Scheme.AffineNeemanEndpointM3
import FourierMukai.Scheme.PrincipalNeemanM1
import FourierMukai.Scheme.AffineSupportedSchemeBaseM1
import FourierMukai.Scheme.FinalStatementCrosscheck
import FourierMukai.Scheme.PerfectCompactThick

/-!
# Affine endpoints without the regular-compactness hypothesis

Corollaries of `RegularCompact.ringObject_isCompactAb`: every affine endpoint
that carried `hAc : IsCompactAb (ringObject A)` is restated here with that
argument discharged.  Nothing else changes; every remaining argument of the
original theorem (Stacks-tagged inputs, the named geometric comparisons
`AffineDerivedGammaInput` / `AffineSupportedSchemeComparisonInput`, Neeman's
compact-to-perfect direction `CompactToPerfectInput`) is kept verbatim.

Sources: GL26 / Neeman, *Acta Math.* 233 (2024), Thm 3.2 (affine case) as
recorded in `results/SCHEMES.md`.  The headline new fact is unconditional:
weak approximability of `D(A-Mod)` (`affine_satisfiesPaperWA`) and of the
principal supported category `D_{V(f)}(A-Mod)`
(`principalSupported_satisfiesPaperWA`), from no input at all.
-/

@[expose] public section

namespace RelativeFM.RegularCompact

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open RelativeFM.StacksInterface RelativeFM.FiniteKoszulM1 RelativeFM.AffinePerfect

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Paper weak approximation data on `D(A-Mod)` with generator `A[0]`,
standard `t`-structure and bound `1`; no hypothesis. -/
noncomputable def affinePaperData (A : Type u) [CommRing A] :
    PaperM2.PaperWeakApproximationData (AffineD A) :=
  AffineNeemanEndpointM3.regularModulePaperData A (ringObject_isCompactAb A)

/-- **Weak approximability of `D(A-Mod)`, unconditionally.** -/
theorem affine_satisfiesPaperWA (A : Type u) [CommRing A] :
    PaperM2.SatisfiesPaperWA (AffineD A) :=
  AffineNeemanEndpointM3.regularModule_satisfiesPaperWA A (ringObject_isCompactAb A)

/-- Neeman 3.2(iii), affine form: the standard `t`-structure on `D(A-Mod)` is
in the preferred equivalence class; no hypothesis. -/
theorem affine_standard_inPreferredClass (A : Type u) [CommRing A] :
    NeemanPreferredM6.InPreferredClass (AffineD.standardTStructure A) :=
  NeemanPreferredM6.standard_inPreferredClass A (ringObject_isCompactAb A)

/-- Every object of `Perf A` (thick envelope of `A[0]`) is compact. -/
theorem perf_le_compact (A : Type u) [CommRing A] :
    Perf A ≤ compactObjectProperty (AffineD A) :=
  perf_le_isCompactAb A (ringObject_isCompactAb A)

/-- The perfect-to-compact interface, now proved. -/
theorem perfectToCompactInput (A : Type u) [CommRing A] : PerfectToCompactInput A :=
  perfectToCompactInput_of_ringObject A (ringObject_isCompactAb A)

/-- The affine package with only Neeman's compact-to-perfect direction as input. -/
theorem affine_regularGenerator_package (A : Type u) [CommRing A]
    (I : CompactToPerfectInput A) :
    PaperM2.SatisfiesPaperWA (AffineD A) ∧
      NeemanPreferredM6.InPreferredClass (AffineD.standardTStructure A) ∧
      ∀ X : AffineD A, IsCompactAb X ↔ Perf A X :=
  AffineNeemanEndpointM3.affine_regularGenerator_package A (ringObject_isCompactAb A) I

/-- **Principal supported weak approximability, unconditionally**: the
category `D_{V(f)}(A-Mod)` of complexes supported on `V(f)` satisfies the
paper's weak approximability. -/
theorem principalSupported_satisfiesPaperWA (A : Type u) [CommRing A] (f : A) :
    PaperM2.SatisfiesPaperWA (AffineDZ A f) :=
  PrincipalNeemanM1.satisfiesPaperWA A f (ringObject_isCompactAb A)

/-- The principal supported Koszul generator is compact; no hypothesis. -/
theorem supportedGenerator_isCompactAb (A : Type u) [CommRing A] (f : A) :
    IsCompactAb (SupportedAisleM6.Koszul.supportedGenerator A f) :=
  AffineSupportedBaseM1.supportedGenerator_isCompactAb A f (ringObject_isCompactAb A)

/-- The quasi-coherent affine regular generator is compact; no hypothesis. -/
theorem qcRingObject_isCompactAb (A : CommRingCat.{u}) : IsCompactAb (qcRingObject A) :=
  isCompactAb_qcRingObject A (ringObject_isCompactAb A)

/-- Affine scheme-level weak approximability (`D_qc(Spec A)`, standard
`t`-structure); the named all-sheaves comparison `I` is the only input. -/
theorem neemanWeakApproximability_spec (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) :
    SchemeWeakApproxStatementM1.NeemanWeakApproximability (Spec A) :=
  SchemeNeemanFinalAuditSmww16bpbM6.neemanWeakApproximability_spec A I
    (ringObject_isCompactAb A)

/-- Affine Neeman 3.2(iii)--(iv) in the `D_qc` model; `I` is the only input. -/
theorem dqcSpec_neemanPackage (A : CommRingCat.{u}) (I : AffineDerivedGammaInput A) :
    SchemeNeemanAffineM5.RegularModuleDqcWeakApproximation A I ∧
      NeemanPreferredM6.InPreferredClass
        (SchemeNeemanAffineM5.transportedStandardTStructure A I) :=
  SchemeNeemanAffineM5.regularModule_dqcSpec_neemanPackage A I (ringObject_isCompactAb A)

/-- The finite-ideal supported scheme base with `hAc` discharged; all other
inputs are those of `neemanSupported_of_finiteIdeal`. -/
theorem neemanSupported_of_finiteIdeal
    (A : Type u) [CommRing A] (hS : KoszulScalarSupportInput A)
    (fs : List A)
    (hD : IdealSupportedCoproductInput A (functionIdeal A fs))
    (hP : FiniteKoszulM1.KoszulPowerCoprodInput A hS fs)
    (hC : IdealSupportedCompactnessInput A (functionIdeal A fs))
    (hDet : KoszulDetectionInput A hS fs)
    (hQ : AffineSupportedSchemeBaseM1.AffineSupportedSchemeComparisonInput A
      (functionIdeal A fs)) :
    SchemeWeakApproxStatementM1.NeemanSupportedWeakApproximability (Spec (CommRingCat.of A))
      (AffineSupportedSchemeBaseM1.closedZeroLocus A
        (functionIdeal A fs)) :=
  AffineSupportedSchemeBaseM1.neemanSupported_of_finiteIdeal A hS fs hD hP hC hDet
    (ringObject_isCompactAb A) hQ

/-- The supported scheme base for closed sets with quasi-compact complement,
with `hAc` discharged; all other inputs as in
`AffineSupportedSchemeBaseM1.neemanSupported_of_qc_closedComplement`. -/
theorem neemanSupported_of_qc_closedComplement
    (A : Type u) [CommRing A] (hS : KoszulScalarSupportInput A)
    (hD : ∀ fs : List A, IdealSupportedCoproductInput A (functionIdeal A fs))
    (hP : ∀ fs : List A, FiniteKoszulM1.KoszulPowerCoprodInput A hS fs)
    (hC : ∀ fs : List A, IdealSupportedCompactnessInput A (functionIdeal A fs))
    (hDet : ∀ fs : List A, KoszulDetectionInput A hS fs)
    (hQ : ∀ fs : List A, AffineSupportedSchemeBaseM1.AffineSupportedSchemeComparisonInput A
      (functionIdeal A fs))
    (Z : TopologicalSpace.Closeds (Spec (CommRingCat.of A)))
    (hcZ : SchemeNeemanFiniteCoverAssemblyM5.IsCompactClosedComplement Z) :
    SchemeWeakApproxStatementM1.NeemanSupportedWeakApproximability
      (Spec (CommRingCat.of A)) Z :=
  AffineSupportedSchemeBaseM1.neemanSupported_of_qc_closedComplement A hS hD hP hC hDet hQ
    (ringObject_isCompactAb A) Z hcZ

/-- The affine supported base in `IsAffine` form, with the family `hAc`
discharged; all other inputs as in
`AffineSupportedSchemeBaseM1.neemanSupportedWeakApproximability_of_isAffine`. -/
theorem neemanSupportedWeakApproximability_of_isAffine
    (hS : ∀ (A : Type u) [CommRing A], KoszulScalarSupportInput A)
    (hD : ∀ (A : Type u) [CommRing A] (fs : List A),
      IdealSupportedCoproductInput A (functionIdeal A fs))
    (hP : ∀ (A : Type u) [CommRing A] (fs : List A),
      FiniteKoszulM1.KoszulPowerCoprodInput A (hS A) fs)
    (hC : ∀ (A : Type u) [CommRing A] (fs : List A),
      IdealSupportedCompactnessInput A (functionIdeal A fs))
    (hDet : ∀ (A : Type u) [CommRing A] (fs : List A),
      KoszulDetectionInput A (hS A) fs)
    (hQ : ∀ (A : Type u) [CommRing A] (fs : List A),
      AffineSupportedSchemeBaseM1.AffineSupportedSchemeComparisonInput A (functionIdeal A fs))
    (X : Scheme.{u}) [IsAffine X] (Z : TopologicalSpace.Closeds X)
    (hcZ : SchemeNeemanFiniteCoverAssemblyM5.IsCompactClosedComplement Z) :
    SchemeWeakApproxStatementM1.NeemanSupportedWeakApproximability X Z :=
  AffineSupportedSchemeBaseM1.neemanSupportedWeakApproximability_of_isAffine
    hS hD hP hC hDet hQ (fun A _ => ringObject_isCompactAb A) X Z hcZ

end

end RelativeFM.RegularCompact

#print axioms RelativeFM.RegularCompact.affinePaperData
#print axioms RelativeFM.RegularCompact.affine_satisfiesPaperWA
#print axioms RelativeFM.RegularCompact.affine_standard_inPreferredClass
#print axioms RelativeFM.RegularCompact.perf_le_compact
#print axioms RelativeFM.RegularCompact.perfectToCompactInput
#print axioms RelativeFM.RegularCompact.affine_regularGenerator_package
#print axioms RelativeFM.RegularCompact.principalSupported_satisfiesPaperWA
#print axioms RelativeFM.RegularCompact.supportedGenerator_isCompactAb
#print axioms RelativeFM.RegularCompact.qcRingObject_isCompactAb
#print axioms RelativeFM.RegularCompact.neemanWeakApproximability_spec
#print axioms RelativeFM.RegularCompact.dqcSpec_neemanPackage
#print axioms RelativeFM.RegularCompact.neemanSupported_of_finiteIdeal
#print axioms RelativeFM.RegularCompact.neemanSupported_of_qc_closedComplement
#print axioms RelativeFM.RegularCompact.neemanSupportedWeakApproximability_of_isAffine
