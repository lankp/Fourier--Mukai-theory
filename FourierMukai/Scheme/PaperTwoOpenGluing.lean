/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.WeakApprox
import FourierMukai.Scheme.SchemeNeemanTransport
import WeakApprox.PaperMainMinimalM2

/-!
# Zero-detection gluing for an open--closed derived recollement

This is the `PaperWeakApproximationData` version of the former
`SchemeGluingReduction.lean` (deleted in wave 7, `results/OPEN_INPUTS.md` row 7.3).  The generator hypothesis is zero detection
(`IsPaperGenerator`), never the strictly stronger `IsGenerator`.

The main theorem produces approximation data on the middle category with the
*prescribed* middle `t`-structure and the normalized LP generator.  This is the
form needed at the next stage of a finite-cover induction.  As in the older
reduction, `CompactHomZeroAtTop` replaces any Stacks 09SR hypothesis in the
reverse gluing direction.

The geometric interface `PaperSchemeOpenClosedDerived` does not assert that its
conclusion holds on the middle category: its approximation data occur only on
the two ends of the recollement.  Constructing its fields for a scheme requires
an open--closed recollement and the three compactly-generated-aisle identities.
Those are geometric inputs, not facts proved in this module.  The contentless
compact/perfect fields (`CompactsArePerfect`), the `D_qc`-specialized
`DqcOpenClosedGluingInput` and the perfect-Ext variants were deleted in wave 6
(`results/OPEN_INPUTS.md` rows 2.11, 5.5).
-/

@[expose] public section

namespace RelativeWeakApprox.SchemeTwoOpenM3

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open RelativeWeakApprox
open RelativeWeakApprox.PaperM2

universe v u uZ uD uU

section PaperAtTStructure

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Zero-detection weak approximation at a prescribed `t`-structure. -/
def SatisfiesPaperWAAt (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : TStructure C) : Prop :=
  ∃ W : PaperWeakApproximationData C, W.t = t

theorem satisfiesPaperWA_of_satisfiesPaperWAAt {t : TStructure C}
    (h : SatisfiesPaperWAAt C t) : SatisfiesPaperWA C := by
  obtain ⟨W, _⟩ := h
  exact ⟨W⟩

end PaperAtTStructure

section EquivalenceTransport

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type uD} [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Bundle the repository's coproduct-free transport theorem as zero-detection
weak approximation data.  No coproduct existence or coproduct-preservation
hypothesis is needed. -/
noncomputable def transportPaperWeakApproximationData
    (F : C ⥤ D) [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (W : PaperWeakApproximationData C) : PaperWeakApproximationData D := by
  let h := SchemeNeemanTransportM5.exists_paper_weakApproximation_of_equivalence
    F W.G W.t W.A W.A_pos W.G_compact W.G_paperGenerates W.G_mem_le
    W.hom_vanishing W.exists_triangle
  let N : ℤ := Classical.choose h
  have hspec := Classical.choose_spec h
  exact
    { G := F.obj W.G
      t := transportTStructure F W.t
      A := N
      A_pos := hspec.1
      G_compact := hspec.2.1
      G_paperGenerates := hspec.2.2.1
      G_mem_le := hspec.2.2.2.1
      hom_vanishing := hspec.2.2.2.2.1
      exists_triangle := hspec.2.2.2.2.2 }

@[simp] theorem transportPaperWeakApproximationData_G
    (F : C ⥤ D) [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (W : PaperWeakApproximationData C) :
    (transportPaperWeakApproximationData F W).G = F.obj W.G := rfl

@[simp] theorem transportPaperWeakApproximationData_t
    (F : C ⥤ D) [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (W : PaperWeakApproximationData C) :
    (transportPaperWeakApproximationData F W).t = transportTStructure F W.t := rfl

/-- Weak approximation at the transported `t`-structure. -/
theorem satisfiesPaperWAAt_transport
    (F : C ⥤ D) [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (W : PaperWeakApproximationData C) :
    SatisfiesPaperWAAt D (transportTStructure F W.t) :=
  ⟨transportPaperWeakApproximationData F W, rfl⟩

/-- Zero-detection weak approximability transports along an equivalence, with
no coproduct hypotheses.  Applied to open--closed excision, this supplies the
supported approximation data on the other side of the equivalence. -/
theorem satisfiesPaperWA_of_equivalence
    (F : C ⥤ D) [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (h : SatisfiesPaperWA C) : SatisfiesPaperWA D := by
  obtain ⟨W⟩ := h
  exact ⟨transportPaperWeakApproximationData F W⟩

end EquivalenceTransport

section GeometryIndependent

variable (DZ : Type uZ) (DX : Type uD) (DU : Type uU)
  [Category.{v} DZ] [Category.{v} DX] [Category.{v} DU]
  [Preadditive DZ] [Preadditive DX] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DX] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DX ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor DX n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DX] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DX]
  [CategoryTheory.IsTriangulated DU]

/-- The zero-detection geometric interface for an open--closed recollement.
The categories are intended to be `D_qc,Z(X)`, `D_qc(X)` and `D_qc(U)`.  In a
relative supported gluing step all three categories acquire a further support
condition.  No middle-category weak-approximation field occurs here. -/
structure PaperSchemeOpenClosedDerived where
  /-- The open immersion and its closed complement, in actual scheme geometry. -/
  geometry : SchemeOpenClosed.{u}
  /-- The minimal LP package, with zero detection on both ends. -/
  setup : PaperSetupMainMinimal DZ DX DU
  /-- Cohomological support on the closed complement. -/
  supportedOnZ : ObjectProperty DX
  /-- Support is exactly the kernel of restriction to the open. -/
  supported_iff : ∀ E : DX, supportedOnZ E ↔ Nonempty (setup.R.jStar.obj E ≅ 0)

/-- The LP setup with approximation data only on the open endpoint.  The
closed endpoint is intentionally absent, so an excision theorem does not need
a dummy closed approximation package merely to discard it afterwards. -/
structure PaperOpenEndpointSetup where
  R : Recollement DZ DX DU
  tD : TStructure DX
  tZ : TStructure DZ
  tU : TStructure DU
  approxU : PaperWeakApproximationData DU
  GU : DU
  G' : DX
  G'_compact : IsCompactAb G'
  G'_paperGenerates : IsPaperGenerator G'
  m : ℤ
  jStar_G'_mem : tU.le m (R.jStar.obj G')
  [normalized_biproduct : HasBinaryBiproduct (G'⟦m⟧) (R.jShriek.obj GU)]
  tD_compactlyGenerated :
    tD.le 0 = Coprod (shiftTail (G'⟦m⟧ ⊞ R.jShriek.obj GU) 0)
  tZ_compactlyGenerated :
    tZ.le 0 = Coprod (shiftTail (R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)) 0)
  tU_compactlyGenerated : tU.le 0 = Coprod (shiftTail GU 0)
  approxU_t : approxU.t = tU
  approxU_G : approxU.G = GU

/-- Supply the supported approximation data on the closed endpoint. -/
def PaperOpenEndpointSetup.toPaperSetupMainMinimal
    (S : PaperOpenEndpointSetup DZ DX DU)
    (WZ : PaperWeakApproximationData DZ) (ht : WZ.t = S.tZ)
    (hG : WZ.G = S.R.iStar.obj (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU)) :
    PaperM2.PaperSetupMainMinimal DZ DX DU where
  R := S.R
  tD := S.tD
  tZ := S.tZ
  tU := S.tU
  approxZ := WZ
  approxU := S.approxU
  GU := S.GU
  G' := S.G'
  G'_compact := S.G'_compact
  G'_paperGenerates := S.G'_paperGenerates
  m := S.m
  jStar_G'_mem := S.jStar_G'_mem
  normalized_biproduct := S.normalized_biproduct
  tD_compactlyGenerated := S.tD_compactlyGenerated
  tZ_compactlyGenerated := S.tZ_compactlyGenerated
  tU_compactlyGenerated := S.tU_compactlyGenerated
  approxZ_t := ht
  approxU_t := S.approxU_t
  approxZ_G := hG
  approxU_G := S.approxU_G

/-- Geometric open--closed data which leave the closed approximation package
to be supplied after supported excision. -/
structure PaperSchemeOpenClosedSeed where
  geometry : SchemeOpenClosed.{u}
  setup : PaperOpenEndpointSetup DZ DX DU
  supportedOnZ : ObjectProperty DX
  supported_iff : ∀ E : DX, supportedOnZ E ↔ Nonempty (setup.R.jStar.obj E ≅ 0)

/-- Complete a seed with supported approximation data. -/
def PaperSchemeOpenClosedSeed.toPaperSchemeOpenClosedDerived
    (I : PaperSchemeOpenClosedSeed DZ DX DU)
    (WZ : PaperWeakApproximationData DZ) (ht : WZ.t = I.setup.tZ)
    (hG : WZ.G = I.setup.R.iStar.obj
      (I.setup.G'⟦I.setup.m⟧ ⊞ I.setup.R.jShriek.obj I.setup.GU)) :
    PaperSchemeOpenClosedDerived DZ DX DU where
  geometry := I.geometry
  setup := PaperOpenEndpointSetup.toPaperSetupMainMinimal
    (DZ := DZ) (DX := DX) (DU := DU) (S := I.setup) (WZ := WZ) ht hG
  supportedOnZ := I.supportedOnZ
  supported_iff := I.supported_iff

end GeometryIndependent

namespace PaperSetupMainMinimal

variable {DZ : Type uZ} {DX : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} DX] [Category.{v} DU]
  [Preadditive DZ] [Preadditive DX] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DX] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DX ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor DX n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DX] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DX]
  [CategoryTheory.IsTriangulated DU]

variable (S : PaperM2.PaperSetupMainMinimal DZ DX DU)

include S

/-- Compactness of the chosen generator on the open end. -/
theorem GU_compact : IsCompactAb S.GU := by
  rw [← S.approxU_G]
  exact S.approxU.G_compact

/-- Build full zero-detection Setup 4.4 using only positive Hom vanishing
between compacts.  In particular, no 09SR finite-thick-generation field and no
old `IsGenerator` field is introduced. -/
noncomputable def toPaperSetup44OfCompactHomZeroAtTop
    (hvan : CompactHomZeroAtTop DX) : PaperSetup44 DZ DX DU := by
  classical
  have hG' : EventuallyHomZero S.G' S.G' :=
    hvan _ _ S.G'_compact S.G'_compact
  have hGUcompact : IsCompactAb S.GU := GU_compact S
  have haisle : S.tD.le 0 =
      Coprod (shiftTail (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) 0) :=
    S.tD_compactlyGenerated
  let hex : ∃ A : ℤ, 0 < A ∧
      (∀ {Y : DX}, S.tD.le (-A) Y →
        ∀ f : (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) ⟶ Y, f = 0) :=
    (exists_setup_4_4_3_of_compactHomZeroAtTop S.R S.tD S.G' S.GU S.m
      S.G'_compact hGUcompact hvan haisle).imp fun A hA => ⟨hA.1, hA.2.2⟩
  let A₀ : ℤ := hex.choose
  have hA₀pos : 0 < A₀ := hex.choose_spec.1
  have hvan₀ : ∀ {Y : DX}, S.tD.le (-A₀) Y →
      ∀ f : (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) ⟶ Y, f = 0 :=
    hex.choose_spec.2
  let A : ℤ := max A₀ (max S.approxZ.A S.approxU.A)
  have hA₀ : A₀ ≤ A := le_max_left _ _
  have hAZ : S.approxZ.A ≤ A :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hAU : S.approxU.A ≤ A :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hpos : 0 < A := lt_of_lt_of_le hA₀pos hA₀
  exact
    { R := S.R
      tD := S.tD
      tZ := S.tZ
      tU := S.tU
      approxZ := S.approxZ.monoBound hAZ
      approxU := S.approxU.monoBound hAU
      GU := S.GU
      G' := S.G'
      G'_compact := S.G'_compact
      G'_paperGenerates := S.G'_paperGenerates
      G'_eventual := hG'
      m := S.m
      jStar_G'_mem := S.jStar_G'_mem
      normalized_biproduct := S.normalized_biproduct
      G_compact := isCompactAb_normalizedGenerator S.R S.G' S.GU S.m
        S.G'_compact hGUcompact
      G_paperGenerates := (lemma_4_3_2_paperGeneration S.R S.G' S.GU S.m
        S.G'_paperGenerates).1
      tD_compactlyGenerated := S.tD_compactlyGenerated
      tZ_compactlyGenerated := S.tZ_compactlyGenerated
      tU_compactlyGenerated := S.tU_compactlyGenerated
      tD_glued := lemma_4_3_3 S.R S.tD S.tZ S.tU S.G' S.GU S.m
        S.jStar_G'_mem S.tD_compactlyGenerated S.tZ_compactlyGenerated
        S.tU_compactlyGenerated
      approxZ_t := S.approxZ_t
      approxU_t := S.approxU_t
      approxZ_G := S.approxZ_G
      approxU_G := S.approxU_G
      A := A
      A_pos := hpos
      approxZ_A := rfl
      approxU_A := rfl
      G_hom_vanishing := fun {Y} hY f =>
        hvan₀ (S.tD.le_monotone (by omega) Y hY) f }

/-- Replace the closed endpoint by equivalent supported approximation data.
This is used with `WZ` transported along open--closed excision.  Only the two
compatibility conditions required by the LP setup are imposed; the middle
category and its conclusion are untouched. -/
def replaceApproxZ (WZ : PaperWeakApproximationData DZ)
    (ht : WZ.t = S.tZ)
    (hG : WZ.G = S.R.iStar.obj (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU)) :
    PaperM2.PaperSetupMainMinimal DZ DX DU where
  R := S.R
  tD := S.tD
  tZ := S.tZ
  tU := S.tU
  approxZ := WZ
  approxU := S.approxU
  GU := S.GU
  G' := S.G'
  G'_compact := S.G'_compact
  G'_paperGenerates := S.G'_paperGenerates
  m := S.m
  jStar_G'_mem := S.jStar_G'_mem
  normalized_biproduct := S.normalized_biproduct
  tD_compactlyGenerated := S.tD_compactlyGenerated
  tZ_compactlyGenerated := S.tZ_compactlyGenerated
  tU_compactlyGenerated := S.tU_compactlyGenerated
  approxZ_t := ht
  approxU_t := S.approxU_t
  approxZ_G := hG
  approxU_G := S.approxU_G

variable [HasCoproducts.{v} DZ] [HasCoproducts.{v} DX] [HasCoproducts.{v} DU]

/-- Reverse LP gluing with zero detection, retaining both the prescribed
middle `t`-structure and the normalized generator. -/
theorem exists_paperData_of_compactHomZeroAtTop
    (hvan : CompactHomZeroAtTop DX) :
    ∃ W : PaperWeakApproximationData DX,
      W.t = S.tD ∧ W.G = (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) := by
  let T := toPaperSetup44OfCompactHomZeroAtTop S hvan
  obtain ⟨W, ht, hG, _⟩ := PaperM2.theorem_1_1_of_setup T
  refine ⟨W, ?_, ?_⟩
  · change W.t = T.tD at ht
    exact ht
  · change W.G = T.G at hG
    exact hG

/-- The middle category is zero-detection weakly approximable at the `t`-
structure supplied by the recollement package. -/
theorem satisfiesPaperWAAt_of_compactHomZeroAtTop
    (hvan : CompactHomZeroAtTop DX) : SatisfiesPaperWAAt DX S.tD := by
  obtain ⟨W, ht, _⟩ := exists_paperData_of_compactHomZeroAtTop S hvan
  exact ⟨W, ht⟩

/-- Bare zero-detection weak approximability is the corresponding projection. -/
theorem satisfiesPaperWA_of_compactHomZeroAtTop
    (hvan : CompactHomZeroAtTop DX) : SatisfiesPaperWA DX :=
  satisfiesPaperWA_of_satisfiesPaperWAAt
    (satisfiesPaperWAAt_of_compactHomZeroAtTop S hvan)

end PaperSetupMainMinimal

section SchemeInterface

variable {DZ : Type uZ} {DX : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} DX] [Category.{v} DU]
  [Preadditive DZ] [Preadditive DX] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DX] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DX ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor DX n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DX] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DX]
  [CategoryTheory.IsTriangulated DU]

namespace PaperSchemeOpenClosedDerived

variable (I : PaperSchemeOpenClosedDerived DZ DX DU)

include I

/-- The open endpoint is an input, not a conclusion restated in the interface. -/
theorem weakApprox_open : SatisfiesPaperWA DU :=
  ⟨PaperM2.PaperSetupMainMinimal.approxU (PaperSchemeOpenClosedDerived.setup I)⟩

/-- The closed-support endpoint is an input, not a conclusion restated in the
interface. -/
theorem weakApprox_closed : SatisfiesPaperWA DZ :=
  ⟨PaperM2.PaperSetupMainMinimal.approxZ (PaperSchemeOpenClosedDerived.setup I)⟩

/-- Replace the closed-support approximation data, for example by data
transported along excision. -/
def replaceApproxZ (WZ : PaperWeakApproximationData DZ)
    (ht : WZ.t = I.setup.tZ)
    (hG : WZ.G = I.setup.R.iStar.obj
      (I.setup.G'⟦I.setup.m⟧ ⊞ I.setup.R.jShriek.obj I.setup.GU)) :
    PaperSchemeOpenClosedDerived DZ DX DU where
  geometry := I.geometry
  setup := PaperSetupMainMinimal.replaceApproxZ I.setup WZ ht hG
  supportedOnZ := I.supportedOnZ
  supported_iff := I.supported_iff

/-- Full gluing output: data at the middle `t`-structure with the normalized
generator.  (Before wave 6 the conclusion also had a conjunct
`I.perfectX.Perf W.G`, read off the deleted contentless field
`CompactsArePerfect`; `results/OPEN_INPUTS.md` row 2.11.) -/
theorem exists_paperData_of_compactHomZeroAtTop
    [HasCoproducts.{v} DZ] [HasCoproducts.{v} DX] [HasCoproducts.{v} DU]
    (hvan : CompactHomZeroAtTop DX) :
    ∃ W : PaperWeakApproximationData DX,
      W.t = I.setup.tD ∧
      W.G = (I.setup.G'⟦I.setup.m⟧ ⊞ I.setup.R.jShriek.obj I.setup.GU) :=
  PaperSetupMainMinimal.exists_paperData_of_compactHomZeroAtTop I.setup hvan

end PaperSchemeOpenClosedDerived
end SchemeInterface

end RelativeWeakApprox.SchemeTwoOpenM3

#print axioms RelativeWeakApprox.SchemeTwoOpenM3.PaperSetupMainMinimal.toPaperSetup44OfCompactHomZeroAtTop
#print axioms RelativeWeakApprox.SchemeTwoOpenM3.PaperSetupMainMinimal.exists_paperData_of_compactHomZeroAtTop
#print axioms RelativeWeakApprox.SchemeTwoOpenM3.PaperSetupMainMinimal.satisfiesPaperWAAt_of_compactHomZeroAtTop
#print axioms RelativeWeakApprox.SchemeTwoOpenM3.transportPaperWeakApproximationData
#print axioms RelativeWeakApprox.SchemeTwoOpenM3.satisfiesPaperWA_of_equivalence
#print axioms RelativeWeakApprox.SchemeTwoOpenM3.PaperSetupMainMinimal.replaceApproxZ
#print axioms RelativeWeakApprox.SchemeTwoOpenM3.PaperOpenEndpointSetup.toPaperSetupMainMinimal
#print axioms RelativeWeakApprox.SchemeTwoOpenM3.PaperSchemeOpenClosedSeed.toPaperSchemeOpenClosedDerived
