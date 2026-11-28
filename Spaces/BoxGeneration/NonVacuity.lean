/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.BoxGeneration.Lemma54
import Spaces.Supported.CompactGeneration

/-!
# Non-vacuity for GL26 Lemma 5.4 (`lem:neeman2023cor5_10`)

CLAUDE.md, verification step 5: the hypothesis-carrying notions of
`Spaces/BoxGeneration/Lemma54.lean` are satisfiable.

* `exists_isCompactGeneratorQc`: **`IsCompactGeneratorQc` is inhabited**: every quasi-compact
  quasi-separated algebraic space has a compact generator of `D_qc` in that sense.  From GL26
  Lemma A.9 at `Z = |X|` (`Supported.lemma_A_9_generator`, Stacks 0AEC, 0AED) and Stacks 09M8.
* `lemma_5_4_nonVacuity`: at an affine `X = h_{T₀}` (for instance `T₀ = S` for an affine base
  `S`, e.g. `S = Spec ℤ`, `Supported.isAffine_terminal`), with `T = Y₁ = Y₂ = X` and
  `f₁ = f₂ = 𝟙`, every hypothesis of `lemma_5_4_of_isAffineHom` is met (`𝟙` is affine) and the
  lemma applies; so do the hypotheses of `lemma_5_4_of_factorization` (`s = j = 𝟙`, `p = 𝟙`) and,
  through these, of `lemma_5_4_of_conservative`.

## Assumptions

Those of `Lemma54.lean` and of `Supported.lemma_A_9_generator` (`Tag0AECInput`, `Tag0AEDInput`,
with `Tag06UQInput` and `SupportTriangulatedInput` for its instance arguments), and
`AffineQuasiSeparatedInput` (Stacks 03JX) for the affine example.  AxiomMath theorems only.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Space RelativeWeakApprox

namespace RelativeFM.Spaces.BoxGeneration

open RelativeFM.Spaces RelativeFM.Spaces.LP26 RelativeFM.Spaces.Statements
  RelativeFM.Spaces.Supported

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Compact generators of `D_qc(X)` exist** for `X` quasi-compact and quasi-separated
(Stacks 09IY, here from GL26 Lemma A.9 at `Z = |X|`): the perfect generator `P` of
`D_{qc,|X|}(X) = D_qc(X)` of `Supported.lemma_A_9_generator` is compact in `D_qc(X)` (Stacks 09M8)
and every object of `D_qc(X)` receiving only zero maps from its shifts is zero.  So
`IsCompactGeneratorQc` is satisfiable. -/
theorem exists_isCompactGeneratorQc (h06 : Tag06UQInput B S hS)
    (hsuppT : SupportTriangulatedInput B S hS) (h0AEC : Tag0AECInput B S hS)
    (h0AED : Tag0AEDInput B S hS) (h09M8 : Tag09M8Input B S hS)
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ∃ P : Space.QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2, IsCompactGeneratorQc P := by
  have := isTriangulated_qcohDerived h06 X
  have := isTriangulated_support hsuppT X Set.univ
  obtain ⟨P, hP, -, hgen⟩ := lemma_A_9_generator h0AEC h0AED X hXqc hZ hXqs Set.univ isClosed_univ
    (by rw [Set.compl_univ]; exact isCompact_empty)
  refine ⟨P.obj, (h09M8 hZ X hXqc hXqs P.obj).2 hP, fun E hE horth => ?_⟩
  let E' : DqcZ X Set.univ :=
    ⟨⟨E, hE⟩, (cohomologySupportedOn_iff_supp_subset X Set.univ E).2 (Set.subset_univ _)⟩
  let F := ιZ X Set.univ
  have hz : IsZero E' := hgen fun n f => by
    apply F.map_injective
    rw [Functor.map_zero, ← cancel_epi ((F.commShiftIso n).inv.app P), comp_zero]
    exact horth n _
  exact F.map_isZero hz

/-- **Non-vacuity of Lemma 5.4** (`lem:neeman2023cor5_10`): at an affine `X = h_{T₀}`, with
`T = Y₁ = Y₂ = X` and `f₁ = f₂ = 𝟙`, the hypotheses of `lemma_5_4_of_isAffineHom` hold (`X` is
qcqs, `𝟙` is affine, compact generators exist by `exists_isCompactGeneratorQc`), and the lemma
gives a compact generator `Lg₁^*P ⊗^L Lg₂^*P` of `D_qc(X ×_X X)`. -/
theorem lemma_5_4_nonVacuity (hZ : B.Contains (⊤_ Scheme.{u}))
    (h4 : Tag08F4Input B S hS) (h08FA : Tag08FAInput B S hS) (h0A8A : Tag0A8AInput B S hS)
    (h08I3 : Tag08I3PerfectInput B S hS) (hpp : PerfectPullbackInput B S hS)
    (hbc : EtaleBaseChangeInput B S hS)
    (hex : Conservative.FlatPullbackExactInput B S hS)
    (hsupp : Conservative.FlatPullbackSupportInput B S hS) (hempty : LP26.SupportEmptyInput B S hS)
    (h073B : Tag073BInput B S hS) (h073B2 : Tag073BTwoInput B S hS)
    (hsrc : QuasiCompactSourceInput B S hS) (h09M8 : Tag09M8Input B S hS)
    (h09JB : QuasiPerfect.Tag09JBInput B S hS) (hPq : LP26.PerfectQcohInput B S hS)
    (haff : Conservative.AffinePushforwardConservativeInput B S hS)
    (h06 : Tag06UQInput B S hS) (hsuppT : SupportTriangulatedInput B S hS)
    (h0AEC : Tag0AECInput B S hS) (h0AED : Tag0AEDInput B S hS)
    (hqs : AffineQuasiSeparatedInput B S hS)
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ∃ P : Space.QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T₀).1
        (representedSpace T₀).2, IsCompactGeneratorQc P ∧
      ∃ hG : Dqc (pullback (𝟙 (representedSpace T₀)) (𝟙 (representedSpace T₀)))
          (boxObj (𝟙 _) (𝟙 _) (qcObj P) (qcObj P)),
        IsCompactGeneratorQc (⟨_, hG⟩ : Space.QuasicoherentDerivedCategory.{u, u} B S hS
          (pullback (𝟙 (representedSpace T₀)) (𝟙 (representedSpace T₀))).1
          (pullback (𝟙 (representedSpace T₀)) (𝟙 (representedSpace T₀))).2) := by
  set X := representedSpace T₀
  obtain ⟨hXqc, hXqs, -, -⟩ := nonVacuity_affine_univ hqs hZ T₀ hT₀
  obtain ⟨P, hP⟩ := exists_isCompactGeneratorQc h06 hsuppT h0AEC h0AED h09M8 X hXqc hZ hXqs
  exact ⟨P, hP, lemma_5_4_of_isAffineHom hZ h4 h08FA h0A8A h08I3 hpp hbc hex hsupp hempty h073B
    h073B2 hsrc h09M8 h09JB hPq haff (𝟙 X) (𝟙 X) (isAffineHom_id X.1) hXqs hXqc hXqs hXqc
    hXqs P P hP hP⟩

/-- **Non-vacuity of `lemma_5_4_of_factorization`**: at an affine `X = h_{T₀}`, with
`T = Y₁ = Y₂ = U = P = X` and `f₁ = f₂ = s = j = p = 𝟙`, every hypothesis is met (`𝟙` is étale,
surjective, a quasi-compact open immersion and affine), and the lemma applies. -/
theorem lemma_5_4_of_factorization_nonVacuity (hZ : B.Contains (⊤_ Scheme.{u}))
    (h4 : Tag08F4Input B S hS) (h08FA : Tag08FAInput B S hS) (h0A8A : Tag0A8AInput B S hS)
    (h08I3 : Tag08I3PerfectInput B S hS) (hpp : PerfectPullbackInput B S hS)
    (hbc : EtaleBaseChangeInput B S hS)
    (hex : Conservative.FlatPullbackExactInput B S hS)
    (hsupp : Conservative.FlatPullbackSupportInput B S hS) (hempty : LP26.SupportEmptyInput B S hS)
    (h073B : Tag073BInput B S hS) (h073B2 : Tag073BTwoInput B S hS)
    (hsrc : QuasiCompactSourceInput B S hS) (h09M8 : Tag09M8Input B S hS)
    (h09JB : QuasiPerfect.Tag09JBInput B S hS) (hPq : LP26.PerfectQcohInput B S hS)
    (haff : Conservative.AffinePushforwardConservativeInput B S hS)
    (hcounit : LP26.OpenImmersionCounitInput B S hS)
    (h06 : Tag06UQInput B S hS) (hsuppT : SupportTriangulatedInput B S hS)
    (h0AEC : Tag0AECInput B S hS) (h0AED : Tag0AEDInput B S hS)
    (hqs : AffineQuasiSeparatedInput B S hS)
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ∃ P : Space.QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T₀).1
        (representedSpace T₀).2, IsCompactGeneratorQc P ∧
      ∃ hG : Dqc (pullback (𝟙 (representedSpace T₀)) (𝟙 (representedSpace T₀)))
          (boxObj (𝟙 _) (𝟙 _) (qcObj P) (qcObj P)),
        IsCompactGeneratorQc (⟨_, hG⟩ : Space.QuasicoherentDerivedCategory.{u, u} B S hS
          (pullback (𝟙 (representedSpace T₀)) (𝟙 (representedSpace T₀))).1
          (pullback (𝟙 (representedSpace T₀)) (𝟙 (representedSpace T₀))).2) := by
  set X := representedSpace T₀
  obtain ⟨hXqc, hXqs, -, -⟩ := nonVacuity_affine_univ hqs hZ T₀ hT₀
  obtain ⟨P, hP⟩ := exists_isCompactGeneratorQc h06 hsuppT h0AEC h0AED h09M8 X hXqc hZ hXqs
  have hsurj : IsSurjective B S hS (𝟙 X : X ⟶ X).hom := by
    change Function.Surjective (pointsMap B S hS X.1 (𝟙 X.1))
    rw [pointsMap_id]
    exact Function.surjective_id
  exact ⟨P, hP, lemma_5_4_of_factorization hZ h4 h08FA h0A8A h08I3 hpp hbc hex hsupp hempty
    h073B h073B2 hsrc h09M8 h09JB hPq haff hcounit (𝟙 X) (𝟙 X) hXqs hXqc hXqs hXqc hXqs P P hP hP
    (𝟙 X) (isEtale_id B S hS X.1) hsurj hXqc hXqs (𝟙 X) (𝟙 X)
    (isOpenImmersion_of_isIso B S hS (𝟙 X.1)) (h073B hZ X.2 hXqs hXqc _)
    (isAffineHom_id X.1) rfl⟩

/-- **Non-vacuity of `isZero_of_orthogonal_box_unit_iff`**: at an affine `X = h_{T₀}` with
`a = f₂ = 𝟙` and `P₂` a compact generator of `D_qc(X)`, the hypotheses hold (the projection
`X ×_X X ⟶ X` is quasi-compact and quasi-separated), so the equivalence holds there. -/
theorem isZero_of_orthogonal_box_unit_iff_nonVacuity (hZ : B.Contains (⊤_ Scheme.{u}))
    (h08FA : Tag08FAInput B S hS) (h073B : Tag073BInput B S hS) (h073B2 : Tag073BTwoInput B S hS)
    (hsrc : QuasiCompactSourceInput B S hS) (h09M8 : Tag09M8Input B S hS)
    (h06 : Tag06UQInput B S hS) (hsuppT : SupportTriangulatedInput B S hS)
    (h0AEC : Tag0AECInput B S hS) (h0AED : Tag0AEDInput B S hS)
    (hqs : AffineQuasiSeparatedInput B S hS)
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ∃ P : Space.QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T₀).1
        (representedSpace T₀).2, IsCompactGeneratorQc P ∧
      ((∀ N : D B S hS (pullback (𝟙 (representedSpace T₀)) (𝟙 (representedSpace T₀))), Dqc _ N →
        (∀ (n : ℤ) (g : (boxObj (𝟙 _) (𝟙 _) (unitD (representedSpace T₀)) (qcObj P))⟦n⟧ ⟶ N),
          g = 0) → IsZero N) ↔
      (∀ N : D B S hS (pullback (𝟙 (representedSpace T₀)) (𝟙 (representedSpace T₀))), Dqc _ N →
        IsZero ((push (pullback.snd (𝟙 (representedSpace T₀)) (𝟙 (representedSpace T₀)))).obj N) →
          IsZero N)) := by
  set X := representedSpace T₀
  obtain ⟨hXqc, hXqs, -, -⟩ := nonVacuity_affine_univ hqs hZ T₀ hT₀
  obtain ⟨P, hP⟩ := exists_isCompactGeneratorQc h06 hsuppT h0AEC h0AED h09M8 X hXqc hZ hXqs
  obtain ⟨hWqc, hWqs⟩ := pullback_isQcqs (𝟙 X) (𝟙 X) hZ h073B h073B2 hsrc hXqs hXqc hXqs hXqc hXqs
  exact ⟨P, hP, isZero_of_orthogonal_box_unit_iff h08FA (𝟙 X) (𝟙 X) (qcObj P) hP.2
    (h073B hZ X.2 hXqs hWqc _) (h073B2 hZ (pullback (𝟙 X) (𝟙 X)).2 hWqs _)⟩

end RelativeFM.Spaces.BoxGeneration
