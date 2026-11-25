/-
Consumer audit for scheme-level Neeman weak approximability.

This module deliberately proves implications only in the valid direction:
legacy morphism-separation data imply the paper's zero-detection data, not
conversely.  It also isolates the exact zero-detection 09SR input needed to
obtain compact Hom-vanishing, and records the non-vacuous affine integers
example which distinguishes the two generator notions.
-/
import FourierMukai.Scheme.Inputs
import FourierMukai.Scheme.GeneratorCounterexampleM5
import FourierMukai.Scheme.AffineNeemanEndpointM3
import WeakApprox.PaperMainMinimalM2

@[expose] public section

namespace RelativeFM.SchemeNeemanConsumerAuditSmww16bpbM6

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox
open RelativeWeakApprox.PaperM2

universe v u

section LegacyBoundary

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The repository's old `Neeman_3_2_iv` is stronger than the paper's statement.
It can be forgotten to zero-detection weak approximability.  There is no theorem
in the reverse direction: `IsPaperGenerator` does not imply `IsGenerator`. -/
theorem satisfiesPaperWA_of_legacyNeeman_3_2_iv
    (h : RelativeFM.Neeman_3_2_iv C) : SatisfiesPaperWA C :=
  satisfiesPaperWA_of_satisfiesWA h

/-- Likewise, the old coherence-plus-weak-approximation interface has a valid
zero-detection projection.  Coherence is a separate input and is not proved by
this implication. -/
theorem paperWA_and_coherent_of_legacyNeeman_coherent_example_5_4
    (CoherentTriangulated : Prop)
    (h : RelativeFM.Neeman_coherent_example_5_4 C CoherentTriangulated) :
    SatisfiesPaperWA C ∧ CoherentTriangulated :=
  ⟨satisfiesPaperWA_of_legacyNeeman_3_2_iv C h.1, h.2⟩

/-- Zero-detection weak approximability supplies the compact Hom-vanishing used
by the LP/gluing arguments, provided 09SR is stated for the same zero-detection
notion of compact generator.  No morphism-separation field occurs here. -/
theorem compactHomZeroAtTop_of_paperWA_of_paper09SR
    (hWA : SatisfiesPaperWA C)
    (h09SR : ∀ G : C, IsPaperGenerator G → IsCompactAb G →
      IsClassicalGeneratorOnCompacts G) :
    RelativeWeakApprox.CompactHomZeroAtTop C := by
  obtain ⟨W⟩ := hWA
  exact compactHomZeroAtTop_of_isClassicalGeneratorOnCompacts
    W.eventuallyHomZero_self (h09SR W.G W.G_paperGenerates W.G_compact)

/-- The same conclusion in the namespace used by `Scheme/Inputs.lean`. -/
theorem schemeCompactHomZeroAtTop_of_paperWA_of_paper09SR
    (hWA : SatisfiesPaperWA C)
    (h09SR : ∀ G : C, IsPaperGenerator G → IsCompactAb G →
      IsClassicalGeneratorOnCompacts G) :
    RelativeFM.CompactHomZeroAtTop C :=
  compactHomZeroAtTop_of_paperWA_of_paper09SR C hWA h09SR

end LegacyBoundary

/-- Over the integers, the regular generator satisfies the actual paper notion
and the corresponding weak-approximation package exists, while no legacy
`WeakApproximationData` with that same generator can exist.  This is a compiled
non-vacuity and non-reversibility check, not merely a documentation warning. -/
theorem small_int_paperWA_exists_but_legacy_regular_generator_impossible
    (H : AffineSpaltensteinInput ℤ) :
    SatisfiesPaperWA (SmallAffineD ℤ H) ∧
      ∀ W : WeakApproximationData (SmallAffineD ℤ H),
        W.G ≠ smallRingObject ℤ H :=
  ⟨AffineNeemanEndpointM3.smallRegularModule_satisfiesPaperWA ℤ H,
    NeemanGeneratorM5.Counterexample.IntExample.smallWeakApproximationData_int_G_ne_ringObject H⟩

end RelativeFM.SchemeNeemanConsumerAuditSmww16bpbM6

#print axioms RelativeFM.SchemeNeemanConsumerAuditSmww16bpbM6.satisfiesPaperWA_of_legacyNeeman_3_2_iv
#print axioms RelativeFM.SchemeNeemanConsumerAuditSmww16bpbM6.paperWA_and_coherent_of_legacyNeeman_coherent_example_5_4
#print axioms RelativeFM.SchemeNeemanConsumerAuditSmww16bpbM6.compactHomZeroAtTop_of_paperWA_of_paper09SR
#print axioms RelativeFM.SchemeNeemanConsumerAuditSmww16bpbM6.schemeCompactHomZeroAtTop_of_paperWA_of_paper09SR
#print axioms RelativeFM.SchemeNeemanConsumerAuditSmww16bpbM6.small_int_paperWA_exists_but_legacy_regular_generator_impossible
