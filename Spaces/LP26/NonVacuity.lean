/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.LP26.HomVanishing
import Spaces.LP26.OpenPushforward

/-!
# Non-vacuity of LP26 Lemmas 5.5, 5.6 and 5.7 over algebraic spaces

CLAUDE.md, verification step 5: the hypotheses of `lemma_5_5`, `lemma_5_6` and `lemma_5_7`
(`Spaces/LP26/HomVanishing.lean`, `Spaces/LP26/OpenPushforward.lean`) are satisfiable.  The
witness is an affine object `T₀` of the big fppf site (for instance the identity of an affine base
`S`, e.g. `S = Spec ℤ`, see `Supported.nonVacuity_base` and `Supported.isAffine_terminal`) and the
algebraic space `h_{T₀}` it represents, which is quasi-compact and quasi-separated
(`Supported.nonVacuity_affine_univ`):

* `nonVacuity_lemma_5_5`: `D_qc(h_{T₀})` has a compact object (a perfect generator of
  `D_{qc,|X|}(X) = D_qc(X)`, Stacks 0AEC, compact by 09M8), and Lemma 5.5 applies to it;
* `nonVacuity_lemma_5_6`: for every quasi-compact quasi-separated `X` (such as `h_{T₀}`) and
  `Z = |X|` (closed, with empty complement), `D_{qc,Z}(X)` has a compact generator (GL26 Lemma
  A.9, `Supported.lemma_A_9`), and Lemma 5.6 applies to it; its two instance arguments hold for
  every `X` (`nonVacuity_lemma_5_6_instances`);
* `nonVacuity_lemma_5_7`: the identity of `h_{T₀}` is a quasi-compact open immersion into a
  quasi-compact space, so Lemma 5.7 applies (for every open `V`).

The inputs are tagged AxiomMath theorems (`Spaces/LP26/Inputs.lean`,
`Spaces/Supported/Inputs.lean`, `Spaces.Tag06UQInput`, `Spaces.Tag08FAInput`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.LP26

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

open Supported

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Non-vacuity of Lemma 5.5**: on the affine space `X = h_{T₀}` (quasi-compact and
quasi-separated), `D_qc(X)` has a compact object `G`, and `lemma_5_5` gives
`Hom(G, G[n]) = 0` for `n ≫ 0`. -/
theorem nonVacuity_lemma_5_5 (h06 : Tag06UQInput B S hS)
    (hsupp : SupportTriangulatedInput B S hS) (h08F3 : Tag08F3Input B S hS)
    (hsum : SupportedDirectSumsInput B S hS) (h0AEC : Tag0AECInput B S hS)
    (h0AED : Tag0AEDInput B S hS) (h0GFD : Tag0GFDInput B S hS)
    (hqs : AffineQuasiSeparatedInput B S hS) (hterm : ContainsTerminalInput.{u})
    (h09M8 : Tag09M8Input B S hS) (hbd : PerfectBoundedAboveInput B S hS)
    (h09MB : Tag09MBInput B S hS)
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    IsQuasiCompactSpace B S hS (representedSpace T₀).1 ∧
      IsAbsolutelyQuasiSeparated B S hS (hterm B) (representedSpace T₀).1 ∧
      ∃ G : QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T₀).1
          (representedSpace T₀).2,
        IsCompactObject.{u} G ∧
          ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G.obj ⟶ G.obj⟦n⟧, f = 0 := by
  obtain ⟨hqc, hqs', -, -⟩ := nonVacuity_affine_univ hqs (hterm B) T₀ hT₀
  obtain ⟨-, P, hP, -⟩ :=
    lemma_A_9_affine_univ h06 hsupp h08F3 hsum h0AEC h0AED h0GFD hqs hterm T₀ hT₀
  have hG := (h09M8 (hterm B) _ hqc hqs' P.obj).2 hP
  exact ⟨hqc, hqs', P.obj, hG, lemma_5_5 h09M8 hbd h09MB (hterm B) _ hqc hqs' P.obj hG⟩

/-- **Non-vacuity of Lemma 5.6**: for every quasi-compact quasi-separated algebraic space `X`
(for instance `X = h_{T₀}` with `T₀` affine, `Supported.nonVacuity_affine_univ`) and `Z = |X|`
(closed, with empty hence quasi-compact complement), `D_{qc,Z}(X)` has a compact generator `G'`
(GL26 Lemma A.9, `Supported.lemma_A_9`), and `lemma_5_6` gives `Hom(G', G'[n]) = 0` for
`n ≫ 0`.  The two instance arguments (the triangulated structure of `D_{qc,Z}(X)`) hold for every
`X` (`nonVacuity_lemma_5_6_instances`). -/
theorem nonVacuity_lemma_5_6 (h08F3 : Tag08F3Input B S hS)
    (hsum : SupportedDirectSumsInput B S hS) (h0AEC : Tag0AECInput B S hS)
    (h0AED : Tag0AEDInput B S hS) (h0GFD : Tag0GFDInput B S hS)
    (h09M8 : Tag09M8Input B S hS) (hbd : PerfectBoundedAboveInput B S hS)
    (h09MB : Tag09MBInput B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) [(qcohDerived X).IsTriangulated]
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 Set.univ)] :
    _root_.IsClosed (Set.univ : Set (points B S hS X.1)) ∧
      _root_.IsCompact (Set.univ : Set (points B S hS X.1))ᶜ ∧
      ∃ G' : DqcZ X Set.univ, IsCompactObject.{u} G' ∧ RelativeWeakApprox.IsPaperGenerator G' ∧
        ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G'.obj.obj ⟶ G'.obj.obj⟦n⟧, f = 0 := by
  have hcl : _root_.IsClosed (Set.univ : Set (points B S hS X.1)) := isClosed_univ
  have hco : _root_.IsCompact (Set.univ : Set (points B S hS X.1))ᶜ := by
    rw [Set.compl_univ]; exact isCompact_empty
  obtain ⟨-, ⟨P, -, hPc, hPg, -⟩, -⟩ :=
    lemma_A_9 h08F3 hsum h0AEC h0AED h0GFD X hqc hZ hqs Set.univ hcl hco
  exact ⟨hcl, hco, P, hPc, hPg,
    lemma_5_6 h09M8 hbd h09MB h0AED hZ X hqc hqs Set.univ hcl hco P hPc hPg⟩

/-- The instance arguments of `nonVacuity_lemma_5_6` (and of `lemma_5_6`) hold for every `X` and
`T`, from Stacks 06UQ and `SupportTriangulatedInput`. -/
theorem nonVacuity_lemma_5_6_instances (h06 : Tag06UQInput B S hS)
    (hsupp : SupportTriangulatedInput B S hS) (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) :
    (qcohDerived X).IsTriangulated ∧
      ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T) :=
  ⟨isTriangulated_qcohDerived h06 _, isTriangulated_support hsupp _ _⟩

/-- The identity of an algebraic space is an open immersion. -/
theorem isOpenImmersion_id (X : AlgebraicSpaces B S hS) :
    IsOpenImmersion B S hS (𝟙 X.1) := by
  have : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsMultiplicative := inferInstance
  have : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso := inferInstance
  change MorphismProperty.presheaf _ (𝟙 X.1)
  exact MorphismProperty.id_mem _ _

/-- **Non-vacuity of Lemma 5.7**: the identity of the affine space `X = h_{T₀}` is a quasi-compact
open immersion into a quasi-compact space, so `lemma_5_7` applies to it. -/
theorem nonVacuity_lemma_5_7 (h08FA : Tag08FAInput B S hS) (h08FB : Tag08FBInput B S hS)
    (h08FAb : Tag08FABoundInput B S hS) (h0AFJ : Tag0AFJInput B S hS)
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ∃ j : representedSpace T₀ ⟶ representedSpace T₀,
      IsOpenImmersion B S hS j.hom ∧ IsQuasiCompact B S hS j.hom ∧
      IsQuasiCompactSpace B S hS (representedSpace T₀).1 ∧
      ∃ r : ℤ, 0 ≤ r ∧ ∀ E : D B S hS (representedSpace T₀), Dqc _ E → E.IsLE 0 →
        ((push j).obj E).IsLE r := by
  let j : representedSpace T₀ ⟶ representedSpace T₀ := 𝟙 _
  have hj : IsOpenImmersion B S hS j.hom := isOpenImmersion_id (representedSpace T₀)
  have hjqc : IsQuasiCompact B S hS j.hom := isQuasiCompact_of_isIso' (𝟙 (representedSpace T₀).1)
  have hX := isQuasiCompact_yoneda_of_compact B S hS T₀ inferInstance
  exact ⟨j, hj, hjqc, hX, (lemma_5_7 h08FA h08FB h08FAb h0AFJ j hj hjqc hX).2.2.1⟩

end RelativeFM.Spaces.LP26
