/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces
import SpacesVerified.Discharge
import SpacesVerified.Supported
import SpacesVerified.LP26Inputs
import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.KoszulDetection
import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.UnitLocus
import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.GenerationStep
import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineLift
import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.SquareQcqs
import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.ExcisionDerived
import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquareGeometry
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectGenerator
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationExtensionByZero
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectSupportedExtension
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedLiftTransport

/-!
# Discharge of the supported-0GFI inputs; GL26 Lemma A.9, preferred class for every support

The 19 tagged AxiomMath inputs of `Spaces/Supported/DetectingInputs.lean` are proved here by the
AxiomMath/Stacks declarations they name (commit `f56a316`), so that the supported Stacks 0GFI
(`Spaces.Supported.supportedDetectsBelowStatement`) and **GL26 Lemma A.9**
(`lem:preferred_eq_class`), preferred-class clause, for every closed `T ⊆ |X|` with quasi-compact
complement (`Spaces.Supported.lemma_A_9_preferred`), hold with nothing assumed.

## The written-out definitions

`Spaces/Supported/DetectingInputs.lean` writes three AxiomMath definitions out by their bodies.
They are identified with AxiomMath's here:

* `koszulSp_eq_koszul`: `koszulSp hX l = koszul hX l`, by induction on `l` (the base cases
  `(DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)` and
  `(DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩)` agree by `rfl`, as
  AxiomMath's `structureModule` is an `abbrev` for `SheafOfModules.unit _`);
* `vanishesWhereUnitSp_eq` and `unitLocusSieveSp_eq`: `rfl`.

## The inputs

| input | proved by (`AlgebraicGeometry.Space.`) |
|---|---|
| `KoszulTorsionInput` | `exists_pow_smul_eq_zero_of_koszul` |
| `KoszulDetectionInput` | `isZero_homology_of_hom_koszul_eq_zero` |
| `KoszulQcohInput` | `qcohDerived_koszul` |
| `KoszulCompactInput` | `isCompactObject_koszulQuasicoherent` |
| `UnitLocusInput` | `exists_list_globalRing_unitLocus` |
| `KoszulRestrictInput` | `isZero_restrictSnd_koszul` |
| `VanishesWhereUnitInput` | `vanishesWhereUnit_of_isZero_restrict` |
| `EdsOpenQcInput` | `isQuasiCompact_edsOpenHom` |
| `EdsOpenQsInput` | `isQuasiSeparated_edsOpenHom` |
| `OpenCounitInput` | `isIso_etaleDerivedModuleAdjunction_counit_of_mono` |
| `PushforwardQcohInput` | `qcohDerived_derivedModulePushforward_obj` (Stacks 08DW) |
| `PerfectQcohInput` | `qcohDerived_of_isPerfect_derivedCategoryB` |
| `RangeOpenInput` | `range_openSubspacesOrderIso_symm` |
| `PreimageQcInput` | `isQuasiCompact_openSubspacesOrderIso_symm_preimage` (03HF) |
| `ShriekSupportInput` | `cohomologySupportedOn_lowerShriek_of_preimage` (08HA) |
| `ShriekPerfectInput` | `isPerfect_lowerShriek_of_cohomologySupportedOn` (08GG) |
| `ShriekRestrictOpenInput` | `isZero_restrictOpen_derivedShriekEtale` (08HA) |
| `Tag09IVInput` | `exists_isPerfect_retract_restrict_of_supported` (09IV) |
| `SupportPullbackInput` | `cohomologySupportedOn_etaleModulePullback` |

The remaining fields of `Spaces.Supported.StepInputs` are Stacks 06UQ (`tag06UQ`), 0AED
(`tag0AED`) and the boundedness of perfect objects (`perfectBoundedAboveSupported`), proved in
`SpacesVerified/Discharge.lean`, `Supported.lean`, `LP26Inputs.lean`.  The discharges use the
instance context of `Spaces/Supported/DetectingInputs.lean` (AxiomMath's); the headline theorems
that of `Spaces/Supported/Preferred.lean`.

## Headline results

* `supportedDetectsBelowStatement_unconditional`: the supported Stacks 0GFI on `D_{qc,T}(X)`;
* `lemma_A_9_preferred_unconditional`, `lemma_A_9_detectsBelowUniformly_unconditional`: **GL26
  Lemma A.9**, preferred-class clause and its uniform bound, for every closed `T` with
  quasi-compact complement;
* non-vacuity: `nonVacuity_detectsBelowUniformly_unconditional` (general `T`) and
  `nonVacuity_detectsBelowUniformly_affine_general_unconditional` (at `X = h_{T₀}`, `T₀` affine,
  `T = |X|`).

The differences from the paper are those of `Spaces.Supported.lemma_A_9_preferred` (the
existence of the compactly generated `t`-structure `tG` is not part of the statement).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open Opposite
open AlgebraicGeometry AlgebraicGeometry.Space RelativeWeakApprox
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

namespace RelativeFM.SpacesVerified

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open RelativeFM.Spaces RelativeFM.Spaces.Supported

/-! ### The discharges, in the instance context of `DetectingInputs.lean` -/

section Discharge

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify
  AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

attribute [local instance] pointTopology

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

section Koszul

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The Koszul object written out in `Spaces/Supported/DetectingInputs.lean` is AxiomMath's
`AlgebraicGeometry.Space.koszul`: by induction on the list, `rfl` for `[]` (AxiomMath's
`structureModule ⟨X, hX⟩` is an `abbrev` for `SheafOfModules.unit _`) and, for `a :: l`, the
induction hypothesis under `(distinguished_cocone_triangle (a • 𝟙 _)).choose`. -/
theorem koszulSp_eq_koszul : ∀ l : List (globalRingSp hX), koszulSp hX l = koszul hX l
  | [] => rfl
  | a :: l => by
    rw [koszulSp, koszul]
    exact congrArg (a₁ := koszulSp hX l) (a₂ := koszul hX l)
      (fun K => (Pretriangulated.distinguished_cocone_triangle (a • 𝟙 K)).choose)
      (koszulSp_eq_koszul l)

variable {hX} in
/-- `VanishesWhereUnitSp` is AxiomMath's `VanishesWhereUnit` (`rfl`). -/
theorem vanishesWhereUnitSp_eq (a : globalRingSp hX) :
    VanishesWhereUnitSp a = VanishesWhereUnit a := rfl

end Koszul

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `unitLocusSieveSp` is AxiomMath's `unitLocusSieve` (`rfl`). -/
theorem unitLocusSieveSp_eq {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1} (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (l : List (globalRingSp hsq.isAlgebraicSpace))
    (U' : SmallEtale B S hS (edsInter B S hS hsq).1) :
    unitLocusSieveSp B S hS hsq l U' = unitLocusSieve B S hS hsq l U' := rfl

/-- Torsion of maps out of Koszul objects, proved. -/
theorem koszulTorsion : KoszulTorsionInput B S hS := by
  intro X hX T hT hTa a l M hM hloc
  rw [koszulSp_eq_koszul hX l]
  exact exists_pow_smul_eq_zero_of_koszul T hT hTa a l M hM hloc

/-- Graded Koszul detection, proved. -/
theorem koszulDetection : KoszulDetectionInput B S hS := by
  intro X hX T hT hTa D l M hM hloc horth
  rw [koszulSp_eq_koszul hX l] at horth
  exact isZero_homology_of_hom_koszul_eq_zero T hT hTa D l M hM hloc horth

/-- Koszul objects have quasi-coherent cohomology, proved. -/
theorem koszulQcoh : KoszulQcohInput B S hS := by
  intro X hX l
  rw [koszulSp_eq_koszul hX l]
  exact qcohDerived_koszul l

/-- Koszul objects are compact in `D_QCoh(𝒪_X)`, proved. -/
theorem koszulCompact : KoszulCompactInput B S hS := by
  intro X hX T hT hTa l
  rw [koszulSp_eq_koszul hX l]
  intro _
  exact isCompactObject_koszulQuasicoherent T hT hTa l

/-- The intersection of an elementary distinguished square is a finite union of unit loci,
proved. -/
theorem unitLocusList : UnitLocusInput B S hS := by
  intro hZ W V Uo fV hsq hV hU hW
  exact exists_list_globalRing_unitLocus B S hS hsq hZ hV hU hW

/-- The Koszul object of functions whose unit loci cover `U ×_W V` vanishes there, proved. -/
theorem koszulRestrict : KoszulRestrictInput B S hS := by
  intro W V Uo fV hsq l hb
  rw [koszulSp_eq_koszul hsq.isAlgebraicSpace l]
  exact isZero_restrictSnd_koszul hsq l hb

/-- Vanishing where a function is a unit, from vanishing on an étale cover of the unit loci,
proved. -/
theorem vanishesWhereUnit : VanishesWhereUnitInput B S hS := by
  intro X Y j hj l hl N hNY
  exact vanishesWhereUnit_of_isZero_restrict j hj l hl N hNY

/-- The open immersion of an elementary distinguished square is quasi-compact, proved. -/
theorem edsOpenQc : EdsOpenQcInput B S hS := by
  intro hZ W V Uo fV hsq hWqs hUqc
  exact isQuasiCompact_edsOpenHom B S hS hZ (hsq := hsq) hWqs hUqc

/-- The open immersion of an elementary distinguished square is quasi-separated, proved. -/
theorem edsOpenQs : EdsOpenQsInput B S hS := by
  intro W V Uo fV hsq
  exact isQuasiSeparated_edsOpenHom B S hS hsq

/-- The counit of restriction to an open immersion is invertible, proved. -/
theorem openCounit : OpenCounitInput B S hS := by
  intro U X j hj _
  exact isIso_etaleDerivedModuleAdjunction_counit_of_mono B S hS j hj

/-- **Stacks 08DW** for algebraic spaces, proved. -/
theorem pushforwardQcohDerived : PushforwardQcohInput B S hS := by
  intro X Y f hfqc hfqs E hE
  exact qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs E hE

/-- A perfect object lies in `D_QCoh`, proved (the input of
`Spaces/Supported/DetectingInputs.lean`). -/
theorem perfectQcohSupported : Spaces.Supported.PerfectQcohInput B S hS := by
  intro X E hE
  exact qcohDerived_of_isPerfect_derivedCategoryB X E hE

/-- The points of the open subspace attached to `|X| ∖ T` form `|X| ∖ T`, proved. -/
theorem rangeOpenSubspace : RangeOpenInput B S hS := by
  intro F hF T hT
  exact range_openSubspacesOrderIso_symm B S hS F hF T hT

/-- **Stacks 03HF**, proved. -/
theorem preimageQc : PreimageQcInput B S hS := by
  intro X Y hX hY f T hT hTqc hT'
  exact isQuasiCompact_openSubspacesOrderIso_symm_preimage B S hS hX hY f T hT hTqc hT'

/-- Supports of extensions by zero (Stacks 08HA), proved. -/
theorem shriekSupport : ShriekSupportInput B S hS := by
  intro X U j hj T hT K hK
  exact cohomologySupportedOn_lowerShriek_of_preimage B S hS j hj T hT K hK

/-- Perfectness of extensions by zero (Stacks 08GG (2)(a)), proved. -/
theorem shriekPerfect : ShriekPerfectInput B S hS := by
  intro W V Uo fV hsq P hP hPs
  exact isPerfect_lowerShriek_of_cohomologySupportedOn B S hS hsq P hP hPs

/-- Restriction of an extension by zero to the open member (Stacks 08HA), proved. -/
theorem shriekRestrictOpen : ShriekRestrictOpenInput B S hS := by
  intro W V Uo fV hsq K hK
  exact isZero_restrictOpen_derivedShriekEtale B S hS hsq K hK

/-- **Stacks 09IV**, proved. -/
theorem tag09IV : Tag09IVInput B S hS := by
  intro hZ X hXqc hXqs W hW hWqc T hT hTqc E P hP hPT α
  exact exists_isPerfect_retract_restrict_of_supported hZ X hXqc hXqs W hW hWqc T hT hTqc E P hP
    hPT α

/-- Supports pull back along étale restriction, proved. -/
theorem supportPullbackEtale : SupportPullbackInput B S hS := by
  intro X Y g hg T E hE
  exact cohomologySupportedOn_etaleModulePullback B S hS g hg T E hE

/-- **The inputs of the supported Stacks 0GFI** (`Spaces.Supported.StepInputs`), all proved. -/
theorem stepInputs : StepInputs B S hS where
  h06 := tag06UQ B S hS
  h0AED := tag0AED B S hS
  hbdd := perfectBoundedAboveSupported B S hS
  hKT := koszulTorsion B S hS
  hKD := koszulDetection B S hS
  hKQ := koszulQcoh B S hS
  hKC := koszulCompact B S hS
  hUL := unitLocusList B S hS
  hKR := koszulRestrict B S hS
  hVW := vanishesWhereUnit B S hS
  hEOqc := edsOpenQc B S hS
  hEOqs := edsOpenQs B S hS
  hOC := openCounit B S hS
  hPQ := pushforwardQcohDerived B S hS
  hrange := rangeOpenSubspace B S hS
  hPre := preimageQc B S hS
  hSS := shriekSupport B S hS
  hSP := shriekPerfect B S hS
  hSRO := shriekRestrictOpen B S hS
  h09IV := tag09IV B S hS
  hSPb := supportPullbackEtale B S hS

end Discharge

/-! ### Headline results, in the instance context of `Preferred.lean` -/

section Headlines

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify
  AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

attribute [local instance] isTriangulated_qcohDerived' isTriangulated_support'

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The supported Stacks 0GFI** ((7) ⇒ (1)), unconditional: for `X` quasi-compact
quasi-separated and `T ⊆ |X|` closed with quasi-compact complement, an object `F` of
`D_{qc,T}(X)` with `Hom(P[-i], F) = 0` for `i ≪ 0` for every compact `P` of `D_{qc,T}(X)` is
bounded below for the standard `t`-structure (`Spaces.Supported.supportedDetectsBelowStatement`
with its inputs proved).  The input of GL26 Lemma A.9 (`lem:preferred_eq_class`), preferred-class
clause. -/
theorem supportedDetectsBelowStatement_unconditional (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) :
    SupportedDetectsBelowStatement X T :=
  supportedDetectsBelowStatement (stepInputs B S hS) (perfectQcohSupported B S hS) X hXqc hZ hXqs
    T hT hTc

/-- **GL26 Lemma A.9** (`lem:preferred_eq_class`), **preferred-class clause**, unconditional:
for a quasi-compact quasi-separated algebraic space `X` and a closed `T ⊆ |X|` with
quasi-compact complement, the standard `t`-structure of `D_{qc,T}(X)` is equivalent (Neeman
2024, Definition 2.9) to every `t`-structure `tG` with
`tG^{≥ 1} = {Y | Hom(G[n], Y) = 0, n ≥ 0}`, for every compact generator `G` of `D_{qc,T}(X)`
(`Spaces.Supported.lemma_A_9_preferred` with its inputs proved).  **Difference from the
paper** (as there): the existence of the compactly generated `tG` is not part of the
statement. -/
theorem lemma_A_9_preferred_unconditional (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (G : DqcZ X T) (hGc : IsCompactObject.{u} G) (hGg : IsPaperGenerator G)
    (tG : TStructure (DqcZ X T)) (htG : ∀ Y : DqcZ X T, tG.ge 1 Y ↔ genCoaisle G Y) :
    NeemanPreferredM6.TStructureEquivalent (stdT X T) tG :=
  lemma_A_9_preferred (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0GFD B S hS)
    (stepInputs B S hS) (perfectQcohSupported B S hS) X hXqc hZ hXqs T hT hTc G hGc hGg tG htG

/-- **GL26 Lemma A.9** (`lem:preferred_eq_class`), preferred-class clause, uniform bound,
unconditional: a compact generator `G` of `D_{qc,T}(X)` detects boundedness below uniformly
for the standard `t`-structure (`Spaces.Supported.lemma_A_9_detectsBelowUniformly`). -/
theorem lemma_A_9_detectsBelowUniformly_unconditional (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (G : DqcZ X T) (hGc : IsCompactObject.{u} G) (hGg : IsPaperGenerator G) :
    DetectsBelowUniformly (stdT X T) G :=
  lemma_A_9_detectsBelowUniformly (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0GFD B S hS)
    (stepInputs B S hS) (perfectQcohSupported B S hS) X hXqc hZ hXqs T hT hTc G hGc hGg

/-- **Non-vacuity of GL26 Lemma A.9, preferred-class clause** (general `T`), unconditional: for
every quasi-compact quasi-separated `X` and closed `T ⊆ |X|` with quasi-compact complement, a
compact generator `G` of `D_{qc,T}(X)` exists and detects boundedness below uniformly
(`Spaces.Supported.nonVacuity_detectsBelowUniformly`). -/
theorem nonVacuity_detectsBelowUniformly_unconditional (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) :
    ∃ G : DqcZ X T, IsCompactObject.{u} G ∧ IsPaperGenerator G ∧
      DetectsBelowUniformly (stdT X T) G :=
  nonVacuity_detectsBelowUniformly (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0AEC B S hS)
    (tag0GFD B S hS) (stepInputs B S hS) (perfectQcohSupported B S hS) X hXqc hZ hXqs T hT hTc

/-- **Non-vacuity, an instance**, unconditional: at `X = h_{T₀}` with `T₀` affine and `T = |X|`,
every hypothesis of `nonVacuity_detectsBelowUniformly_unconditional` is met
(`Spaces.Supported.nonVacuity_detectsBelowUniformly_affine_general`). -/
theorem nonVacuity_detectsBelowUniformly_affine_general_unconditional
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (X : AlgebraicSpaces B S hS) (hX : X = Supported.representedSpace T₀) :
    ∃ G : DqcZ X Set.univ, IsCompactObject.{u} G ∧ IsPaperGenerator G ∧
      DetectsBelowUniformly (stdT X Set.univ) G :=
  nonVacuity_detectsBelowUniformly_affine_general (tag08F3 B S hS) (supportedDirectSums B S hS)
    (tag0AEC B S hS) (tag0GFD B S hS) (stepInputs B S hS) (perfectQcohSupported B S hS)
    (affineQuasiSeparatedYoneda B S hS) containsTerminal T₀ hT₀ X hX

end Headlines

end RelativeFM.SpacesVerified

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
