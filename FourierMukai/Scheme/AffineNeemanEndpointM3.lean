import FourierMukai.Scheme.NeemanSmallApproximationM3
import FourierMukai.Scheme.NeemanSmallAisleGenerationM3
import FourierMukai.Scheme.AffineCompactness
import FourierMukai.Scheme.AffineSpaltenstein
import FourierMukai.Scheme.NeemanPreferred
import FourierMukai.Scheme.PaperGeneratorM5
import FourierMukai.Scheme.PerfectCompactThick
import WeakApprox.PaperGeneratorM2

/-!
# The regular-generator affine Neeman endpoint

This module constructs weak approximation data with the paper's zero-detection
condition, using `PaperM2.PaperWeakApproximationData`.  It deliberately does
not construct the old `WeakApproximationData`: its `IsGenerator` field is false
for the regular module over the integers.

Both the large-Hom and small-Hom affine data have the standard `t`-structure,
regular generator and bound one.  In the large-Hom model compactness remains
an explicit argument.  In the small-Hom model it is discharged by
`AffineCompactness`; the canonical Spaltenstein replacement yields both weak
approximability and preferred-class membership from a commutative ring alone.
Compact-to-perfect inputs are used only in separate comparison theorems.
-/

@[expose] public section

namespace RelativeFM.AffineNeemanEndpointM3

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u

noncomputable section

section LargeAffine

attribute [local instance] HasDerivedCategory.standard

/-- Standard regular-generator paper weak approximation data on `D(A-Mod)`.
Compactness of `A[0]` is the only argument; no compact-perfect comparison or
morphism-separation hypothesis is used. -/
noncomputable def regularModulePaperData (A : Type u) [CommRing A]
    (hAc : IsCompactAb (ringObject A)) :
    PaperM2.PaperWeakApproximationData (AffineD A) where
  G := ringObject A
  t := AffineD.standardTStructure A
  A := 1
  A_pos := by omega
  G_compact := hAc
  G_paperGenerates := NeemanGeneratorM5.Paper.Modules.ringObject_isPaperGenerator A
  G_mem_le := NeemanGeneratorM5.ringObject_mem_standard_le_of_nonneg A (by omega)
  hom_vanishing := by
    intro Y hY f
    exact NeemanGeneratorM5.ringObject_hom_zero_of_standard_le_neg_of_pos A
      (by omega) hY f
  exists_triangle := NeemanApproximation.M3.exists_approximation_triangle A

/-- The large-Hom affine derived category satisfies the corrected, paper-style
weak approximability predicate, modulo exactly compactness of `A[0]`. -/
theorem regularModule_satisfiesPaperWA (A : Type u) [CommRing A]
    (hAc : IsCompactAb (ringObject A)) : PaperM2.SatisfiesPaperWA (AffineD A) :=
  ⟨regularModulePaperData A hAc⟩

@[simp] theorem regularModulePaperData_G (A : Type u) [CommRing A]
    (hAc : IsCompactAb (ringObject A)) :
    (regularModulePaperData A hAc).G = ringObject A := rfl

@[simp] theorem regularModulePaperData_t (A : Type u) [CommRing A]
    (hAc : IsCompactAb (ringObject A)) :
    (regularModulePaperData A hAc).t = AffineD.standardTStructure A := rfl

@[simp] theorem regularModulePaperData_A (A : Type u) [CommRing A]
    (hAc : IsCompactAb (ringObject A)) :
    (regularModulePaperData A hAc).A = 1 := rfl

end LargeAffine

/-- The small-Hom version has exactly the same six mathematical fields.  The
replacement data construct the derived-category instance.  Compactness is now
a theorem of `AffineCompactness`, so there is no compactness hypothesis. -/
noncomputable def smallRegularModulePaperData (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    PaperM2.PaperWeakApproximationData (SmallAffineD A H) where
  G := smallRingObject A H
  t := NeemanGeneratorM5.smallStandardTStructure A H
  A := 1
  A_pos := by omega
  G_compact := NeemanM1.smallRingObject_isCompactAb A H
  G_paperGenerates := NeemanGeneratorM5.Paper.smallRingObject_isPaperGenerator A H
  G_mem_le := NeemanGeneratorM5.smallRingObject_mem_standard_le_of_nonneg A H (by omega)
  hom_vanishing := by
    intro Y hY f
    exact NeemanGeneratorM5.smallRingObject_hom_zero_of_standard_le_neg_of_pos A H
      (by omega) hY f
  exists_triangle := NeemanApproximation.SmallM3.exists_approximation_triangle A H

/-- Unconditional small-Hom affine weak approximability with the standard
`t`-structure, regular zero-detecting generator and bound one. -/
theorem smallRegularModule_satisfiesPaperWA (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    PaperM2.SatisfiesPaperWA (SmallAffineD A H) :=
  ⟨smallRegularModulePaperData A H⟩

@[simp] theorem smallRegularModulePaperData_G (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    (smallRegularModulePaperData A H).G = smallRingObject A H := rfl

@[simp] theorem smallRegularModulePaperData_t (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    (smallRegularModulePaperData A H).t =
      NeemanGeneratorM5.smallStandardTStructure A H := rfl

@[simp] theorem smallRegularModulePaperData_A (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    (smallRegularModulePaperData A H).A = 1 := rfl

/-- The canonical Spaltenstein replacement makes the small-Hom affine theorem
a construction from a commutative ring alone. -/
theorem small_affine_satisfiesPaperWA (A : Type u) [CommRing A] :
    PaperM2.SatisfiesPaperWA
      (SmallAffineD A (Spaltenstein.affineSpaltensteinInput A)) :=
  smallRegularModule_satisfiesPaperWA A _

/-- The standard small-Hom `t`-structure belongs to Neeman's preferred class,
unconditionally: its generator is compact, detects zero and generates the aisle. -/
theorem smallRegularModule_preferred (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    NeemanPreferredM6.InPreferredClass (NeemanGeneratorM5.smallStandardTStructure A H) :=
  NeemanPreferredM6.inPreferredClass_of_compactlyGenerated _ _
    (NeemanM1.smallRingObject_isCompactAb A H)
    (NeemanGeneratorM5.Paper.smallRingObject_isPaperGenerator A H)
    (NeemanSmallAisleGenerationM3.smallStandard_le_zero_eq_coprod A H)

/-- Preferred-class membership in the canonical small model constructed from
a commutative ring alone. -/
theorem small_affine_inPreferredClass (A : Type u) [CommRing A] :
    NeemanPreferredM6.InPreferredClass
      (NeemanGeneratorM5.smallStandardTStructure A (Spaltenstein.affineSpaltensteinInput A)) :=
  smallRegularModule_preferred A _

/-- Consolidated unsupported affine base form of Neeman 3.2(iii)--(iv).  Neither
the closed-support categories nor the non-affine scheme case is asserted. -/
theorem small_affine_neeman_3_2_iii_iv_base (A : Type u) [CommRing A] :
    PaperM2.SatisfiesPaperWA
      (SmallAffineD A (Spaltenstein.affineSpaltensteinInput A)) ∧
    NeemanPreferredM6.InPreferredClass
      (NeemanGeneratorM5.smallStandardTStructure A
        (Spaltenstein.affineSpaltensteinInput A)) :=
  ⟨small_affine_satisfiesPaperWA A, small_affine_inPreferredClass A⟩

/-- Compact objects are exactly `SmallPerf` once the directed compact-to-perfect
input is supplied; the converse uses the proved compactness of `A[0]`. -/
theorem small_compact_iff_smallPerf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (I : SmallNeemanCompactToPerfectInput A H)
    (X : SmallAffineD A H) : IsCompactAb X ↔ SmallPerf A H X :=
  NeemanM1.isCompactAb_iff_smallPerf_of_neeman A H I X

/-- Weak approximability and preferred-class membership are unconditional.
Only the separate compact/perfect comparison needs compact-to-perfect. -/
theorem small_affine_regularGenerator_package (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (I : SmallNeemanCompactToPerfectInput A H) :
    PaperM2.SatisfiesPaperWA (SmallAffineD A H) ∧
      NeemanPreferredM6.InPreferredClass (NeemanGeneratorM5.smallStandardTStructure A H) ∧
      ∀ X : SmallAffineD A H, IsCompactAb X ↔ SmallPerf A H X :=
  ⟨smallRegularModule_satisfiesPaperWA A H, smallRegularModule_preferred A H,
    small_compact_iff_smallPerf A H I⟩

/-- The standard preferred-class assertion in the large-Hom model has the same
sole compactness hypothesis. -/
theorem regularModule_preferred (A : Type u) [CommRing A]
    (hAc : IsCompactAb (ringObject A)) :
    NeemanPreferredM6.InPreferredClass (AffineD.standardTStructure A) :=
  NeemanPreferredM6.standard_inPreferredClass A hAc

/-- Compactness of `A[0]` supplies the perfect-to-compact half; together with
Neeman's directed compact-to-perfect input it gives the full comparison. -/
theorem compactPerfectInput_of_regularModule_compact (A : Type u) [CommRing A]
    (hAc : IsCompactAb (ringObject A)) (I : CompactToPerfectInput A) :
    CompactPerfectInput A :=
  compactPerfectInput_of_separateInputs A I
    (perfectToCompactInput_of_ringObject A hAc)

/-- The three affine assertions assembled separately, so that the external
compact-to-perfect input is visible and is not hidden in weak approximability. -/
theorem affine_regularGenerator_package (A : Type u) [CommRing A]
    (hAc : IsCompactAb (ringObject A)) (I : CompactToPerfectInput A) :
    PaperM2.SatisfiesPaperWA (AffineD A) ∧
      NeemanPreferredM6.InPreferredClass (AffineD.standardTStructure A) ∧
      ∀ X : AffineD A, IsCompactAb X ↔ Perf A X := by
  refine ⟨regularModule_satisfiesPaperWA A hAc,
    regularModule_preferred A hAc, ?_⟩
  exact (compactPerfectInput_of_regularModule_compact A hAc I).compact_iff_perfect

end

end RelativeFM.AffineNeemanEndpointM3

#print axioms RelativeFM.AffineNeemanEndpointM3.regularModulePaperData
#print axioms RelativeFM.AffineNeemanEndpointM3.regularModule_satisfiesPaperWA
#print axioms RelativeFM.AffineNeemanEndpointM3.smallRegularModulePaperData
#print axioms RelativeFM.AffineNeemanEndpointM3.smallRegularModule_satisfiesPaperWA
#print axioms RelativeFM.AffineNeemanEndpointM3.small_affine_satisfiesPaperWA
#print axioms RelativeFM.AffineNeemanEndpointM3.smallRegularModule_preferred
#print axioms RelativeFM.AffineNeemanEndpointM3.small_affine_inPreferredClass
#print axioms RelativeFM.AffineNeemanEndpointM3.small_affine_neeman_3_2_iii_iv_base
#print axioms RelativeFM.AffineNeemanEndpointM3.small_compact_iff_smallPerf
#print axioms RelativeFM.AffineNeemanEndpointM3.small_affine_regularGenerator_package
#print axioms RelativeFM.AffineNeemanEndpointM3.regularModule_preferred
#print axioms RelativeFM.AffineNeemanEndpointM3.compactPerfectInput_of_regularModule_compact
#print axioms RelativeFM.AffineNeemanEndpointM3.affine_regularGenerator_package
