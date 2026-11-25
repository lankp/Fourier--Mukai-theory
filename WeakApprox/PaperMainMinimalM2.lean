/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.PaperTwoStageM2

/-!
# LP Theorem 1.1 with zero-detection generation

The remaining parameter `h09SR` is the classical compact-generation theorem
(Ravenel--Neeman, Stacks Tag 09SR), stated with the paper's zero-detection
notion of generator. It is not a weak-approximability assumption. Everything
else in Setup 4.4 and in the two-stage construction is proved in the preceding
modules.
-/

@[expose] public section

namespace RelativeWeakApprox.PaperM2

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox

universe v uZ uD uU

section Declarations

variable (DZ : Type uZ) (D : Type uD) (DU : Type uU)
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- Minimal Setup 4.4, including the eventual self-vanishing used in the
reverse implication. All generation fields use zero detection. -/
structure PaperSetup44Minimal where
  R : Recollement DZ D DU
  tD : TStructure D
  tZ : TStructure DZ
  tU : TStructure DU
  approxZ : PaperWeakApproximationData DZ
  approxU : PaperWeakApproximationData DU
  GU : DU
  G' : D
  G'_compact : IsCompactAb G'
  G'_paperGenerates : IsPaperGenerator G'
  G'_eventual : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∀ f : G' ⟶ G'⟦n⟧, f = 0
  m : ℤ
  jStar_G'_mem : tU.le m (R.jStar.obj G')
  [normalized_biproduct : HasBinaryBiproduct (G'⟦m⟧) (R.jShriek.obj GU)]
  tD_compactlyGenerated :
    tD.le 0 = Coprod (shiftTail (G'⟦m⟧ ⊞ R.jShriek.obj GU) 0)
  tZ_compactlyGenerated :
    tZ.le 0 = Coprod (shiftTail (R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)) 0)
  tU_compactlyGenerated : tU.le 0 = Coprod (shiftTail GU 0)
  approxZ_t : approxZ.t = tZ
  approxU_t : approxU.t = tU
  approxZ_G : approxZ.G = R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)
  approxU_G : approxU.G = GU

/-- The setup for Theorem 1.1, without assuming the right-hand side. -/
structure PaperSetupMainMinimal where
  R : Recollement DZ D DU
  tD : TStructure D
  tZ : TStructure DZ
  tU : TStructure DU
  approxZ : PaperWeakApproximationData DZ
  approxU : PaperWeakApproximationData DU
  GU : DU
  G' : D
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
  approxZ_t : approxZ.t = tZ
  approxU_t : approxU.t = tU
  approxZ_G : approxZ.G = R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)
  approxU_G : approxU.G = GU

end Declarations

section RecollementGeneration

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- Lemma 4.3(2), generation part, with zero detection. The proof is the
same retract/left-adjoint transport as the original, but at no point is a
nonzero ghost excluded. -/
theorem lemma_4_3_2_paperGeneration (R : Recollement DZ D DU)
    (G' : D) (GU : DU) (m : ℤ) (hG' : IsPaperGenerator G') :
    IsPaperGenerator (G'⟦m⟧ ⊞ R.jShriek.obj GU) ∧
      IsPaperGenerator (R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)) := by
  have hG : IsPaperGenerator (G'⟦m⟧ ⊞ R.jShriek.obj GU) :=
    isPaperGenerator_of_retract
      (BinaryBiproduct.bicone (G'⟦m⟧) (R.jShriek.obj GU)).retract_left
      (isPaperGenerator_shift G' m hG')
  exact ⟨hG, isPaperGenerator_leftAdjoint_obj R.iStarAdj hG⟩

end RecollementGeneration

namespace PaperSetup44Minimal

variable {DZ D DU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

variable (S : PaperSetup44Minimal DZ D DU)

/-- Compactness of `GU`, transported from the data on `D_U`. -/
theorem GU_compact : IsCompactAb S.GU := by
  rw [← S.approxU_G]
  exact S.approxU.G_compact

/-- Construct full Setup 4.4 from 09SR's finite-thick-generation input.
No separator field is reconstructed: the normalized object is shown to
satisfy zero detection directly by Lemma 4.3(2). -/
noncomputable def toPaperSetup44 (hgen : IsClassicalGeneratorOnCompacts S.G') :
    PaperSetup44 DZ D DU := by
  classical
  have hG' : EventuallyHomZero S.G' S.G' := S.G'_eventual
  let hex : ∃ A : ℤ, 0 < A ∧
      (∀ {Y : D}, S.tD.le (-A) Y →
        ∀ f : (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) ⟶ Y, f = 0) :=
    (exists_setup_4_4_3 S.R S.tD S.G' S.GU S.m S.G'_compact S.GU_compact hG'
      hgen S.tD_compactlyGenerated).imp fun A hA => ⟨hA.1, hA.2.2⟩
  let A₀ : ℤ := hex.choose
  have hA₀pos : 0 < A₀ := hex.choose_spec.1
  have hvan₀ : ∀ {Y : D}, S.tD.le (-A₀) Y →
      ∀ f : (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) ⟶ Y, f = 0 :=
    hex.choose_spec.2
  let A : ℤ := max A₀ (max S.approxZ.A S.approxU.A)
  have hA₀ : A₀ ≤ A := le_max_left _ _
  have hAZ : S.approxZ.A ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hAU : S.approxU.A ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
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
      G'_eventual := S.G'_eventual
      m := S.m
      jStar_G'_mem := S.jStar_G'_mem
      normalized_biproduct := S.normalized_biproduct
      G_compact := isCompactAb_normalizedGenerator S.R S.G' S.GU S.m
        S.G'_compact S.GU_compact
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

end PaperSetup44Minimal

namespace PaperSetupMainMinimal

variable {DZ D DU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

variable (S : PaperSetupMainMinimal DZ D DU)

/-- Adjoin the eventual vanishing only for the reverse implication. -/
def withEventual
    (hG' : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∀ f : S.G' ⟶ S.G'⟦n⟧, f = 0) :
    PaperSetup44Minimal DZ D DU where
  R := S.R
  tD := S.tD
  tZ := S.tZ
  tU := S.tU
  approxZ := S.approxZ
  approxU := S.approxU
  GU := S.GU
  G' := S.G'
  G'_compact := S.G'_compact
  G'_paperGenerates := S.G'_paperGenerates
  G'_eventual := hG'
  m := S.m
  jStar_G'_mem := S.jStar_G'_mem
  normalized_biproduct := S.normalized_biproduct
  tD_compactlyGenerated := S.tD_compactlyGenerated
  tZ_compactlyGenerated := S.tZ_compactlyGenerated
  tU_compactlyGenerated := S.tU_compactlyGenerated
  approxZ_t := S.approxZ_t
  approxU_t := S.approxU_t
  approxZ_G := S.approxZ_G
  approxU_G := S.approxU_G

variable [HasCoproducts.{v} DZ] [HasCoproducts.{v} D] [HasCoproducts.{v} DU]

/-- Forward direction. The only use of generation is as an input to 09SR,
which places the compact `G'` in the finite thick envelope of `W.G`. -/
theorem theorem_1_1_forward
    (h09SR : ∀ (G : D), IsPaperGenerator G → IsCompactAb G →
      IsClassicalGeneratorOnCompacts G)
    (h : SatisfiesPaperWA D) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∀ f : S.G' ⟶ S.G'⟦n⟧, f = 0 := by
  obtain ⟨W⟩ := h
  have hgen : IsClassicalGeneratorOnCompacts W.G :=
    h09SR W.G W.G_paperGenerates W.G_compact
  have hmem : (ObjectProperty.singleton W.G).triangEnvelope S.G' :=
    hgen S.G' S.G'_compact
  exact eventuallyHomZero_self_of_mem_triangEnvelope W hmem

/-- LP Theorem 1.1 with the paper's zero-detection generation throughout. -/
theorem theorem_1_1
    (h09SR : ∀ (G : D), IsPaperGenerator G → IsCompactAb G →
      IsClassicalGeneratorOnCompacts G) :
    SatisfiesPaperWA D ↔ ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      ∀ f : S.G' ⟶ S.G'⟦n⟧, f = 0 :=
  ⟨S.theorem_1_1_forward h09SR,
    fun h => satisfiesPaperWA_of_setup
      ((S.withEventual h).toPaperSetup44 (h09SR S.G' S.G'_paperGenerates S.G'_compact))⟩

end PaperSetupMainMinimal

end RelativeWeakApprox.PaperM2

#print axioms RelativeWeakApprox.PaperM2.lemma_4_3_2_paperGeneration
#print axioms RelativeWeakApprox.PaperM2.PaperSetup44Minimal.toPaperSetup44
#print axioms RelativeWeakApprox.PaperM2.PaperSetupMainMinimal.withEventual
#print axioms RelativeWeakApprox.PaperM2.PaperSetupMainMinimal.theorem_1_1_forward
#print axioms RelativeWeakApprox.PaperM2.PaperSetupMainMinimal.theorem_1_1
