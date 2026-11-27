/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces
import SpacesVerified.Affine
import SpacesVerified.Discharge
import SpacesVerified.Statements
import SpacesVerified.Supported
import SpacesVerified.LP26Inputs

/-!
# LP26 §5, Corollary 1.2 and GL26 Lemmas A.4, A.6, A.9 (preferred class), unconditional

The results of `Spaces/LP26/` and `Spaces/Supported/Preferred.lean`, with every tagged AxiomMath
input proved (`SpacesVerified/Discharge.lean`, `Statements.lean`, `Affine.lean`,
`Supported.lean`, `LP26Inputs.lean`), so that they hold with axioms `propext`,
`Classical.choice`, `Quot.sound` only:

* **LP26 Lemma 5.5** (`lem:compact_ext_vanishing`): `lemma_5_5_unconditional`,
  `lemma_5_5_dqc_unconditional`;
* **LP26 Lemma 5.6** (`lem:perf_vanishing`): `lemma_5_6_unconditional`,
  `lemma_5_6_dqcZ_unconditional`;
* **LP26 Lemma 5.7** (`lem:qcqs_open_pushforward`): `lemma_5_7_unconditional`,
  `lemma_5_7_supported_unconditional`;
* **LP26 Lemma 5.9** (`lem:characterize_T-_c`): `lemma_5_9_unconditional` and the Noetherian
  forms `lemma_5_9_minus_noetherian_unconditional`, `lemma_5_9_bounded_noetherian_unconditional`,
  `lemma_5_9_minus_eq_unconditional`, `lemma_5_9_bounded_eq_unconditional`;
* **LP26 Proposition 5.8** (`prop:A8`), weak-approximability part: `proposition_5_8_unconditional`;
* **LP26 Corollary 1.2** (`cor:weak_approx_spaces`), weak-approximability and `D_qc` parts:
  `corollary_1_2_unconditional`,
  `corollary_1_2_dqc_unconditional`;
* **GL26 Lemma A.4** (`lem:spacey_recollement`): `lemma_A_4_unconditional`;
* **GL26 Lemma A.6** (`lem:etale_nbhd_preferred_class_equivalences`): `lemma_A_6_unconditional`,
  `lemma_A_6_bounded_unconditional`;
* **GL26 Lemma A.9** (`lem:preferred_eq_class`), preferred-class clause for `Z = |X|`:
  `lemma_A_9_preferred_univ_unconditional`.

The instance hypotheses of the `Spaces` statements that `D_QCoh(𝒪_X)` and `D_T(𝒪_X)` are
triangulated (Stacks 06UQ and `SupportTriangulatedInput`, both proved) are supplied by the local
instances `isTriangulated_qcohDerived'`, `isTriangulated_support'` and are not hypotheses here.
The statements are otherwise those of the `Spaces` theorems cited in each docstring, with the
differences from the papers recorded there.  Non-vacuity: the `…_nonVacuity_unconditional`
theorems below.

The labels are those recorded in `results/COVERAGE.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry AlgebraicGeometry.Space RelativeWeakApprox

namespace RelativeFM.SpacesVerified

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify
  AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] isTriangulated_qcohDerived' isTriangulated_support'

open RelativeFM.Spaces RelativeFM.Spaces.Supported RelativeFM.Spaces.LP26

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! The instances `isTriangulated_qcohDerived'`, `isTriangulated_support'` at the concrete
spaces of the non-vacuity statements (instance search does not see through their reducible
definitions). -/

theorem isTriangulated_qcohDerived_represented (T₀ : BigFppfOver B S hS) :
    (qcohDerived (Supported.representedSpace T₀)).IsTriangulated :=
  isTriangulated_qcohDerived' _

theorem isTriangulated_support_represented (T₀ : BigFppfOver B S hS)
    (T : Set (points B S hS (Supported.representedSpace T₀).1)) :
    ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS
      (Supported.representedSpace T₀).1 (Supported.representedSpace T₀).2 T) :=
  isTriangulated_support' _ T

theorem isTriangulated_qcohDerived_affineSpace (T₀ : BigFppfOver B S hS) :
    (qcohDerived (Affine.space T₀)).IsTriangulated :=
  isTriangulated_qcohDerived' _

theorem isTriangulated_support_affineSpace (T₀ : BigFppfOver B S hS)
    (T : Set (points B S hS (Affine.space T₀).1)) :
    ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS
      (Affine.space T₀).1 (Affine.space T₀).2 T) :=
  isTriangulated_support' _ T

theorem isTriangulated_qcohDerived_base : (qcohDerived (baseSpace B S hS)).IsTriangulated :=
  isTriangulated_qcohDerived' _

theorem isTriangulated_support_base (T : Set (points B S hS (baseSpace B S hS).1)) :
    ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS
      (baseSpace B S hS).1 (baseSpace B S hS).2 T) :=
  isTriangulated_support' _ T

attribute [local instance] isTriangulated_qcohDerived_represented
  isTriangulated_support_represented isTriangulated_qcohDerived_affineSpace
  isTriangulated_support_affineSpace isTriangulated_qcohDerived_base isTriangulated_support_base

/-! ### LP26 Lemmas 5.5, 5.6 -/

/-- **LP26 Lemma 5.5** (`lem:compact_ext_vanishing`), unconditional: for `X` quasi-compact and
quasi-separated and `G` compact in `D_qc(X)`, `Hom(G, G[n]) = 0` for `n ≫ 0`
(`Spaces.LP26.lemma_5_5`). -/
theorem lemma_5_5_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (G : AlgebraicGeometry.Space.QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (hG : IsCompactObject.{u} G) :
    ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G.obj ⟶ G.obj⟦n⟧, f = 0 :=
  lemma_5_5 (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS) hZ X hqc hqs G hG

/-- **LP26 Lemma 5.5** (`lem:compact_ext_vanishing`) in `D_qc(X)` itself, unconditional
(`Spaces.LP26.lemma_5_5_dqc`). -/
theorem lemma_5_5_dqc_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (G : AlgebraicGeometry.Space.QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (hG : IsCompactObject.{u} G) :
    ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G ⟶ G⟦n⟧, f = 0 :=
  lemma_5_5_dqc (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS) hZ X hqc hqs G hG

/-- **LP26 Lemma 5.6** (`lem:perf_vanishing`), unconditional: for `X` quasi-compact and
quasi-separated, `T ⊆ |X|` closed with quasi-compact complement and `G'` a compact generator of
`D_{qc,T}(X)`, `Hom(G', G'[n]) = 0` for `n ≫ 0` (`Spaces.LP26.lemma_5_6`). -/
theorem lemma_5_6_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (T : Set (points B S hS X.1))
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (G' : DqcZ X T) (hG' : IsCompactObject.{u} G') (hgen : RelativeWeakApprox.IsPaperGenerator G') :
    ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G'.obj.obj ⟶ G'.obj.obj⟦n⟧, f = 0 :=
  lemma_5_6 (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS) (tag0AED B S hS) hZ X
    hqc hqs T hT hTc G' hG' hgen

/-- **LP26 Lemma 5.6** (`lem:perf_vanishing`) in `D_{qc,T}(X)` itself, unconditional
(`Spaces.LP26.lemma_5_6_dqcZ`). -/
theorem lemma_5_6_dqcZ_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (T : Set (points B S hS X.1))
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (G' : DqcZ X T) (hG' : IsCompactObject.{u} G') (hgen : RelativeWeakApprox.IsPaperGenerator G') :
    ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G' ⟶ G'⟦n⟧, f = 0 :=
  lemma_5_6_dqcZ (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS) (tag0AED B S hS)
    hZ X hqc hqs T hT hTc G' hG' hgen

/-! ### LP26 Lemma 5.7 -/

/-- **LP26 Lemma 5.7** (`lem:qcqs_open_pushforward`), unconditional
(`Spaces.LP26.lemma_5_7`). -/
theorem lemma_5_7_unconditional {U X : AlgebraicSpaces B S hS} (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (hjqc : IsQuasiCompact B S hS j.hom)
    (hX : IsQuasiCompactSpace B S hS X.1) :
    (∀ E : Spaces.D B S hS U, Spaces.Dqc U E → Spaces.Dqc X ((Spaces.push j).obj E)) ∧
      (∀ {I : Type u} (E : I → Spaces.D B S hS U), (∀ i, Spaces.Dqc U (E i)) →
        PreservesColimit (Discrete.functor E) (Spaces.push j)) ∧
      (∃ r : ℤ, 0 ≤ r ∧ ∀ E : Spaces.D B S hS U, Spaces.Dqc U E → E.IsLE 0 → ((Spaces.push j).obj E).IsLE r) ∧
      (∀ V : Set (points B S hS U.1), IsOpen V → ∀ E : Spaces.D B S hS U, Spaces.DqcSupported U Vᶜ E →
        Spaces.DqcSupported X (pointsMap B S hS U.1 j.hom '' V)ᶜ ((Spaces.push j).obj E)) :=
  lemma_5_7 (tag08FA B S hS) (tag08FB B S hS) (tag08FABound B S hS) (tag0AFJ B S hS) j hj hjqc hX

/-- **LP26 Lemma 5.7** (`lem:qcqs_open_pushforward`), the supported form, unconditional
(`Spaces.LP26.lemma_5_7_supported`). -/
theorem lemma_5_7_supported_unconditional {U X : AlgebraicSpaces B S hS} (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (hjqc : IsQuasiCompact B S hS j.hom)
    (hX : IsQuasiCompactSpace B S hS X.1) (V : Set (points B S hS U.1)) (hV : IsOpen V) :
    (∀ E : Spaces.D B S hS U, Spaces.DqcSupported U Vᶜ E →
        Spaces.DqcSupported X (pointsMap B S hS U.1 j.hom '' V)ᶜ ((Spaces.push j).obj E)) ∧
      (∀ {I : Type u} (E : I → Spaces.D B S hS U), (∀ i, Spaces.DqcSupported U Vᶜ (E i)) →
        PreservesColimit (Discrete.functor E) (Spaces.push j)) ∧
      (∃ r : ℤ, 0 ≤ r ∧ ∀ E : Spaces.D B S hS U, Spaces.DqcSupported U Vᶜ E → E.IsLE 0 →
        Spaces.DqcSupported X (pointsMap B S hS U.1 j.hom '' V)ᶜ ((Spaces.push j).obj E) ∧
          ((Spaces.push j).obj E).IsLE r) :=
  lemma_5_7_supported (tag08FA B S hS) (tag08FB B S hS) (tag08FABound B S hS) (tag0AFJ B S hS) j
    hj hjqc hX V hV

/-! ### LP26 Lemma 5.9 -/

/-- **LP26 Lemma 5.9** (`lem:characterize_T-_c`), unconditional: for `X` quasi-compact and
quasi-separated and `T ⊆ |X|` closed with quasi-compact complement, an object of `D_{qc,T}(X)`
lies in `T^-_c` iff it is pseudo-coherent (`Spaces.LP26.lemma_5_9`). -/
theorem lemma_5_9_unconditional (X : AlgebraicSpaces B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) (E : DqcZ X T) :
    standardMinusC X T E ↔ (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E.obj.obj :=
  lemma_5_9 X (tag0AED B S hS) (perfectPseudoCoherent B S hS) (tag08FVTwo B S hS)
    (pseudoCoherentFromOfIsLE B S hS) (tag08FU2 B S hS) (perfectQcoh B S hS) (tag08HP B S hS)
    (tag073B B S hS) (openSubspaceQuasiCompact B S hS) hZ hqc hqs T hT hTc E

/-- **LP26 Lemma 5.9** (`lem:characterize_T-_c`), Noetherian form, unconditional
(`Spaces.LP26.lemma_5_9_minus_noetherian`). -/
theorem lemma_5_9_minus_noetherian_unconditional (X : AlgebraicSpaces B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) (E : DqcZ X T) :
    standardMinusC X T E ↔
      DerivedCategoryB.IsBoundedAbove E.obj.obj ∧
        ∀ i : ℤ, SheafOfModules.IsCoherentOnSite
          ((DerivedCategory.homologyFunctor (AlgebraicGeometry.Space.Modules.{u, u} B S hS X.1 X.2) i).obj E.obj.obj) :=
  lemma_5_9_minus_noetherian X (tag0AED B S hS) (perfectPseudoCoherent B S hS)
    (tag08FVTwo B S hS) (pseudoCoherentFromOfIsLE B S hS) (tag08FU2 B S hS) (perfectQcoh B S hS)
    (tag08HP B S hS) (tag073B B S hS) (openSubspaceQuasiCompact B S hS) (tag08IK B S hS) hZ hN T
    hT hTc E

/-- **LP26 Lemma 5.9** (`lem:characterize_T-_c`), bounded Noetherian form, unconditional
(`Spaces.LP26.lemma_5_9_bounded_noetherian`). -/
theorem lemma_5_9_bounded_noetherian_unconditional (X : AlgebraicSpaces B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) (E : DqcZ X T) :
    standardBoundedC X T E ↔
      DerivedCategoryB.IsBounded E.obj.obj ∧
        ∀ i : ℤ, SheafOfModules.IsCoherentOnSite
          ((DerivedCategory.homologyFunctor (AlgebraicGeometry.Space.Modules.{u, u} B S hS X.1 X.2) i).obj E.obj.obj) :=
  lemma_5_9_bounded_noetherian X (tag0AED B S hS) (perfectPseudoCoherent B S hS)
    (tag08FVTwo B S hS) (pseudoCoherentFromOfIsLE B S hS) (tag08FU2 B S hS) (perfectQcoh B S hS)
    (tag08HP B S hS) (tag073B B S hS) (openSubspaceQuasiCompact B S hS) (tag08IK B S hS) hZ hN T
    hT hTc E

/-- **LP26 Lemma 5.9** (`lem:characterize_T-_c`): `T^-_c = D^-_{coh,T}(X)` for `X` Noetherian,
unconditional (`Spaces.LP26.lemma_5_9_minus_eq`). -/
theorem lemma_5_9_minus_eq_unconditional (X : AlgebraicSpaces B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (E : DerivedCategory (AlgebraicGeometry.Space.Modules.{u, u} B S hS X.1 X.2)) :
    (∃ E' : DqcZ X T, (ιZ X T).obj E' = E ∧ standardMinusC X T E') ↔
      DerivedCategoryB.derivedCategoryBMinus (coh X) E ∧
        CohomologySupportedOn B S hS X.1 X.2 T E :=
  lemma_5_9_minus_eq X (tag0AED B S hS) (perfectPseudoCoherent B S hS)
    (tag08FVTwo B S hS) (pseudoCoherentFromOfIsLE B S hS) (tag08FU2 B S hS) (perfectQcoh B S hS)
    (tag08HP B S hS) (tag073B B S hS) (openSubspaceQuasiCompact B S hS) (tag08IK B S hS) hZ hN T
    hT hTc E

/-- **LP26 Lemma 5.9** (`lem:characterize_T-_c`): `T^b_c = D^b_{coh,T}(X)` for `X` Noetherian,
unconditional (`Spaces.LP26.lemma_5_9_bounded_eq`). -/
theorem lemma_5_9_bounded_eq_unconditional (X : AlgebraicSpaces B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (E : DerivedCategory (AlgebraicGeometry.Space.Modules.{u, u} B S hS X.1 X.2)) :
    (∃ E' : DqcZ X T, (ιZ X T).obj E' = E ∧ standardBoundedC X T E') ↔
      DerivedCategoryB.derivedCategoryBBounded (coh X) E ∧
        CohomologySupportedOn B S hS X.1 X.2 T E :=
  lemma_5_9_bounded_eq X (tag0AED B S hS) (perfectPseudoCoherent B S hS)
    (tag08FVTwo B S hS) (pseudoCoherentFromOfIsLE B S hS) (tag08FU2 B S hS) (perfectQcoh B S hS)
    (tag08HP B S hS) (tag073B B S hS) (openSubspaceQuasiCompact B S hS) (tag08IK B S hS) hZ hN T
    hT hTc E

/-! ### LP26 Proposition 5.8 and Corollary 1.2 -/

/-- **LP26 Proposition 5.8** (`prop:A8`), unconditional: for an elementary
distinguished square `(U ⊆ X, V ⟶ X)` of quasi-compact quasi-separated algebraic spaces, if `U`
and `V` satisfy weak approximability (with support), so does `X`
(`Spaces.LP26.proposition_5_8`).  Weak-approximability part only; the standard-W.A. part is
open (`results/COVERAGE.md`). -/
theorem proposition_5_8_unconditional {X : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor X.1} {fV : V ⟶ X.1}
    (hsq : IsElementaryDistinguishedSquare B S hS X.2 Uo fV)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hVqc : IsQuasiCompactSpace B S hS V) (hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V)
    (hU : Spaces.LP26.SatisfiesWA (edsOpenSpace hsq))
    (hY : Spaces.LP26.SatisfiesWA (edsEtaleSpace hsq)) :
    Spaces.LP26.SatisfiesWA X :=
  proposition_5_8 (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS) (pullbackSupport B S hS)
    (pullbackDisjoint B S hS) (etaleRestrictionSupport B S hS) (openImmersionCounit B S hS)
    (perfectPullback B S hS) (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0AEC B S hS)
    (tag0AED B S hS) tag079Q tag0A8G rightAdjointCoproducts (quasiCompactSource B S hS)
    (compactComplPreimage B S hS) (tag08GGUnit B S hS) (tag08GGCounit B S hS) (tag073B B S hS)
    (tag073BTwo B S hS) (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS) hsq hZ hXqc
    hXqs hUqc hVqc hVqs hU hY

/-- **LP26 Corollary 1.2** (`cor:weak_approx_spaces`), unconditional: a quasi-compact
quasi-separated algebraic space satisfies weak approximability with support
(`Spaces.LP26.corollary_1_2`).  The standard-W.A. and coherence parts are open
(`results/COVERAGE.md`). -/
theorem corollary_1_2_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    Spaces.LP26.SatisfiesWA X :=
  corollary_1_2 (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS) (pullbackSupport B S hS)
    (pullbackDisjoint B S hS) (etaleRestrictionSupport B S hS) (openImmersionCounit B S hS)
    (perfectPullback B S hS) (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0AEC B S hS)
    (tag0AED B S hS) tag079Q tag0A8G rightAdjointCoproducts (quasiCompactSource B S hS)
    (compactComplPreimage B S hS) (tag08GGUnit B S hS) (tag08GGCounit B S hS) (tag073B B S hS)
    (tag073BTwo B S hS) (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS)
    (edsOfComplSubset B S hS) (supportEmpty B S hS) (openSubspaceQuasiCompact B S hS)
    (tag09IT B S hS) (affineQuasiSeparatedYoneda B S hS) (tag06Z0Exact B S hS)
    (tag06Z0Qcoh B S hS) (tag06Z0 B S hS) (tag07TY B S hS) hZ X hXqc hXqs

/-- **LP26 Corollary 1.2** (`cor:weak_approx_spaces`), the case `Z = |X|`, unconditional:
`D_qc(X)` is weakly approximable for `X` quasi-compact and quasi-separated
(`Spaces.LP26.corollary_1_2_dqc`). -/
theorem corollary_1_2_dqc_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    SumUniverse.SatisfiesPaperWA.{u} (AlgebraicGeometry.Space.QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :=
  corollary_1_2_dqc (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS) (pullbackSupport B S hS)
    (pullbackDisjoint B S hS) (etaleRestrictionSupport B S hS) (openImmersionCounit B S hS)
    (perfectPullback B S hS) (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0AEC B S hS)
    (tag0AED B S hS) tag079Q tag0A8G rightAdjointCoproducts (quasiCompactSource B S hS)
    (compactComplPreimage B S hS) (tag08GGUnit B S hS) (tag08GGCounit B S hS) (tag073B B S hS)
    (tag073BTwo B S hS) (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS)
    (edsOfComplSubset B S hS) (supportEmpty B S hS) (openSubspaceQuasiCompact B S hS)
    (tag09IT B S hS) (affineQuasiSeparatedYoneda B S hS) (tag06Z0Exact B S hS)
    (tag06Z0Qcoh B S hS) (tag06Z0 B S hS) (tag07TY B S hS) hZ X hXqc hXqs

/-! ### GL26 Lemmas A.4, A.6 -/

/-- **GL26 Lemma A.4** (`lem:spacey_recollement`), unconditional: for `j : U ⟶ X` a
quasi-compact open immersion into a quasi-compact quasi-separated algebraic space and
`W ⊆ |X|` closed with quasi-compact complement, `D_{qc,W ∩ (X∖U)}(X) → D_{qc,W}(X) → D_{qc,j⁻¹W}(U)`
is a recollement whose functors are the restrictions of `Rj_*`, `Lj^*` and the inclusion
(`Spaces.LP26.lemma_A_4`). -/
theorem lemma_A_4_unconditional {U X : AlgebraicSpaces B S hS}
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom) (hjqc : IsQuasiCompact B S hS j.hom)
    (W : Set (points B S hS X.1)) (hW : IsClosed W) (hWc : _root_.IsCompact Wᶜ) :
    ∃ R : Recollement (DqcZ U (pointsMap B S hS U.1 j.hom ⁻¹' W)) (DqcZ X W)
        (DqcZ X (W ∩ (Set.range (pointsMap B S hS U.1 j.hom))ᶜ)),
      Nonempty (R.iLower ⋙ ιZ X W ≅ ιZ U _ ⋙ Spaces.push j) ∧
      Nonempty (R.iStar ⋙ ιZ U _ ≅ ιZ X W ⋙ Spaces.pull j) ∧
      Nonempty (R.jShriek ⋙ ιZ X W ≅ ιZ X _) :=
  lemma_A_4 (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS) (pullbackSupport B S hS)
    (pullbackDisjoint B S hS) (etaleRestrictionSupport B S hS) (openImmersionCounit B S hS)
    (perfectPullback B S hS) (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0AEC B S hS)
    (tag0AED B S hS) tag079Q tag0A8G rightAdjointCoproducts (quasiCompactSource B S hS)
    (compactComplPreimage B S hS) hZ hXqc hXqs j hj hjqc W hW hWc

section LemmaA6

variable {X : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor X.1} {fV : V ⟶ X.1}

/-- **GL26 Lemma A.6** (`lem:etale_nbhd_preferred_class_equivalences`), unconditional: for an elementary
distinguished square `(U ⊆ X, f : V ⟶ X)` with `X` quasi-separated and `V` quasi-compact
quasi-separated, and `W ⊆ |X| ∖ |U|` closed, `Lf^* ⊣ Rf_*` restricts to an adjoint equivalence
`D_{qc,W}(X) ≃ D_{qc,f⁻¹W}(V)` of `t`-exact functors for the standard `t`-structures
(`Spaces.LP26.lemma_A_6`). -/
theorem lemma_A_6_unconditional (hsq : IsElementaryDistinguishedSquare B S hS X.2 Uo fV)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hVqc : IsQuasiCompactSpace B S hS V) (hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V)
    (W : Set (points B S hS X.1)) (hW : IsClosed W)
    (hWZ : W ⊆ (Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ) :
    IsIso (edsAdj (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS) (pullbackSupport B S hS)
        (tag073B B S hS) (tag073BTwo B S hS) hsq hZ hXqs hVqc hVqs W hW).unit ∧
      IsIso (edsAdj (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS) (pullbackSupport B S hS)
        (tag073B B S hS) (tag073BTwo B S hS) hsq hZ hXqs hVqc hVqs W hW).counit ∧
      (pullZ (tag08F4 B S hS) (pullbackSupport B S hS) (edsEtaleMap hsq) W).TExact
        (standardTStructure X W) (standardTStructure (edsEtaleSpace hsq) (edsW hsq W)) ∧
      (pushZ (tag08FA B S hS) (tag0AFJ B S hS) (edsEtaleMap hsq) W
        (isQuasiCompact_edsEtaleMap (tag073B B S hS) hsq hZ hXqs hVqc)
        (isQuasiSeparated_edsEtaleMap (tag073BTwo B S hS) hsq hZ hVqs) hW).TExact
        (standardTStructure (edsEtaleSpace hsq) (edsW hsq W)) (standardTStructure X W) :=
  lemma_A_6 (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS) (pullbackSupport B S hS)
    (tag08GGUnit B S hS) (tag08GGCounit B S hS) (tag073B B S hS) (tag073BTwo B S hS) hsq hZ hXqs
    hVqc hVqs W hW hWZ

/-- **GL26 Lemma A.6** (`lem:etale_nbhd_preferred_class_equivalences`), boundedness, unconditional: the
equivalence of `lemma_A_6_unconditional` preserves and reflects bounded objects
(`Spaces.LP26.lemma_A_6_bounded`). -/
theorem lemma_A_6_bounded_unconditional (hsq : IsElementaryDistinguishedSquare B S hS X.2 Uo fV)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hVqc : IsQuasiCompactSpace B S hS V) (hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V)
    (W : Set (points B S hS X.1)) (hW : IsClosed W)
    (hWZ : W ⊆ (Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ) :
    (∀ E : DqcZ X W, (∃ a b : ℤ, (standardTStructure X W).IsGE E a ∧
        (standardTStructure X W).IsLE E b) ↔
      ∃ a b : ℤ, (standardTStructure (edsEtaleSpace hsq) (edsW hsq W)).IsGE
          ((pullZ (tag08F4 B S hS) (pullbackSupport B S hS) (edsEtaleMap hsq) W).obj E) a ∧
        (standardTStructure (edsEtaleSpace hsq) (edsW hsq W)).IsLE
          ((pullZ (tag08F4 B S hS) (pullbackSupport B S hS) (edsEtaleMap hsq) W).obj E) b) ∧
      ∀ F : DqcZ (edsEtaleSpace hsq) (edsW hsq W),
        (∃ a b : ℤ, (standardTStructure (edsEtaleSpace hsq) (edsW hsq W)).IsGE F a ∧
          (standardTStructure (edsEtaleSpace hsq) (edsW hsq W)).IsLE F b) →
        ∃ a b : ℤ, (standardTStructure X W).IsGE ((pushZ (tag08FA B S hS) (tag0AFJ B S hS)
            (edsEtaleMap hsq) W
            (isQuasiCompact_edsEtaleMap (tag073B B S hS) hsq hZ hXqs hVqc)
            (isQuasiSeparated_edsEtaleMap (tag073BTwo B S hS) hsq hZ hVqs) hW).obj F) a ∧
          (standardTStructure X W).IsLE ((pushZ (tag08FA B S hS) (tag0AFJ B S hS)
            (edsEtaleMap hsq) W
            (isQuasiCompact_edsEtaleMap (tag073B B S hS) hsq hZ hXqs hVqc)
            (isQuasiSeparated_edsEtaleMap (tag073BTwo B S hS) hsq hZ hVqs) hW).obj F) b :=
  lemma_A_6_bounded (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS) (pullbackSupport B S hS)
    (tag08GGUnit B S hS) (tag08GGCounit B S hS) (tag073B B S hS) (tag073BTwo B S hS) hsq hZ hXqs
    hVqc hVqs W hW hWZ

end LemmaA6

/-! ### GL26 Lemma A.9, preferred class -/

/-- **GL26 Lemma A.9** (`lem:preferred_eq_class`), preferred-class clause for `Z = |X|`,
unconditional: for `X` quasi-compact quasi-separated and `G` a compact generator of `D_qc(X)`,
the standard `t`-structure is equivalent to the one generated by `G`
(`Spaces.Supported.lemma_A_9_preferred_univ`; the differences from the paper are recorded
there). -/
theorem lemma_A_9_preferred_univ_unconditional (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (G : DqcZ X Set.univ) (hGc : IsCompactObject.{u} G) (hGg : IsPaperGenerator G)
    (tG : TStructure (DqcZ X Set.univ))
    (htG : ∀ Y : DqcZ X Set.univ, tG.ge 1 Y ↔ genCoaisle G Y) :
    NeemanPreferredM6.TStructureEquivalent (stdT X Set.univ) tG :=
  lemma_A_9_preferred_univ (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0AED B S hS)
    (tag0GFD B S hS) (tag0GFI B S hS) (perfectBoundedAboveSupported B S hS) X hXqc hZ hXqs G hGc
    hGg tG htG

/-! ### Non-vacuity -/

/-- Non-vacuity of LP26 Lemma 5.5, unconditional (`Spaces.LP26.nonVacuity_lemma_5_5`). -/
theorem nonVacuity_lemma_5_5_unconditional
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    IsQuasiCompactSpace B S hS (Supported.representedSpace T₀).1 ∧
      IsAbsolutelyQuasiSeparated B S hS (containsTerminal B) (Supported.representedSpace T₀).1 ∧
      ∃ G : AlgebraicGeometry.Space.QuasicoherentDerivedCategory.{u, u} B S hS (Supported.representedSpace T₀).1
          (Supported.representedSpace T₀).2,
        IsCompactObject.{u} G ∧
          ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G.obj ⟶ G.obj⟦n⟧, f = 0 :=
  nonVacuity_lemma_5_5 (tag06UQ B S hS) (supportTriangulated B S hS) (tag08F3 B S hS)
    (supportedDirectSums B S hS) (tag0AEC B S hS) (tag0AED B S hS) (tag0GFD B S hS)
    (affineQuasiSeparatedYoneda B S hS) containsTerminal (tag09M8 B S hS)
    (perfectBoundedAbove B S hS) (tag09MB B S hS) T₀ hT₀

/-- Non-vacuity of LP26 Lemma 5.6, unconditional (`Spaces.LP26.nonVacuity_lemma_5_6`). -/
theorem nonVacuity_lemma_5_6_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    _root_.IsClosed (Set.univ : Set (points B S hS X.1)) ∧
      _root_.IsCompact (Set.univ : Set (points B S hS X.1))ᶜ ∧
      ∃ G' : DqcZ X Set.univ, IsCompactObject.{u} G' ∧ RelativeWeakApprox.IsPaperGenerator G' ∧
        ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G'.obj.obj ⟶ G'.obj.obj⟦n⟧, f = 0 :=
  nonVacuity_lemma_5_6 (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0AEC B S hS)
    (tag0AED B S hS) (tag0GFD B S hS) (tag09M8 B S hS) (perfectBoundedAbove B S hS)
    (tag09MB B S hS) hZ X hqc hqs

/-- Non-vacuity of LP26 Lemma 5.7, unconditional (`Spaces.LP26.nonVacuity_lemma_5_7`). -/
theorem nonVacuity_lemma_5_7_unconditional
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ∃ j : Supported.representedSpace T₀ ⟶ Supported.representedSpace T₀,
      IsOpenImmersion B S hS j.hom ∧ IsQuasiCompact B S hS j.hom ∧
      IsQuasiCompactSpace B S hS (Supported.representedSpace T₀).1 ∧
      ∃ r : ℤ, 0 ≤ r ∧ ∀ E : Spaces.D B S hS (Supported.representedSpace T₀), Spaces.Dqc _ E → E.IsLE 0 →
        ((Spaces.push j).obj E).IsLE r :=
  nonVacuity_lemma_5_7 (tag08FA B S hS) (tag08FB B S hS) (tag08FABound B S hS) (tag0AFJ B S hS)
    T₀ hT₀

/-- Non-vacuity of LP26 Lemma 5.9, unconditional (`Spaces.LP26.nonVacuity_lemma_5_9`). -/
theorem nonVacuity_lemma_5_9_unconditional (X : AlgebraicSpaces B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    _root_.IsClosed (Set.univ : Set (points B S hS X.1)) ∧
      _root_.IsCompact (Set.univ : Set (points B S hS X.1))ᶜ ∧
      ∃ E : DqcZ X Set.univ, standardMinusC X Set.univ E ∧
        (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E.obj.obj :=
  nonVacuity_lemma_5_9 X (tag0AEC B S hS) (tag0AED B S hS) (perfectPseudoCoherent B S hS)
    (tag08FVTwo B S hS) (pseudoCoherentFromOfIsLE B S hS) (tag08FU2 B S hS) (perfectQcoh B S hS)
    (tag08HP B S hS) (tag073B B S hS) (openSubspaceQuasiCompact B S hS) hZ hqc hqs

/-- Non-vacuity of the Noetherian forms of LP26 Lemma 5.9, unconditional: an affine locally
Noetherian base is Noetherian, and `T^-_c` over it has a member
(`Spaces.LP26.nonVacuity_lemma_5_9_noetherian`). -/
theorem nonVacuity_lemma_5_9_noetherian_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    [IsAffine S] [IsLocallyNoetherian S] :
    IsNoetherian B S hS hZ (baseSpace B S hS).1 ∧
      ∃ E : DqcZ (baseSpace B S hS) Set.univ, standardMinusC (baseSpace B S hS) Set.univ E ∧
        DerivedCategoryB.IsBoundedAbove E.obj.obj ∧
        ∀ i : ℤ, SheafOfModules.IsCoherentOnSite
          ((DerivedCategory.homologyFunctor
            (AlgebraicGeometry.Space.Modules.{u, u} B S hS (baseSpace B S hS).1 (baseSpace B S hS).2) i).obj
              E.obj.obj) :=
  nonVacuity_lemma_5_9_noetherian (affineQuasiSeparated B S hS) (tag0AEC B S hS)
    (tag0AED B S hS) (perfectPseudoCoherent B S hS) (tag08FVTwo B S hS)
    (pseudoCoherentFromOfIsLE B S hS) (tag08FU2 B S hS) (perfectQcoh B S hS) (tag08HP B S hS)
    (tag073B B S hS) (openSubspaceQuasiCompact B S hS) (tag08IK B S hS) hZ

/-- Non-vacuity of LP26 Proposition 5.8, unconditional (`Spaces.LP26.proposition_5_8_nonVacuity`):
every hypothesis of `proposition_5_8_unconditional` holds for some square. -/
theorem proposition_5_8_nonVacuity_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X₀ : AlgebraicSpaces B S hS) (hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀.1) :
    ∃ (X : AlgebraicSpaces B S hS) (hsq : IsElementaryDistinguishedSquare B S hS X.2
        (⊤ : Subfunctor X.1) (⊤ : Subfunctor X.1).ι),
      IsQuasiCompactSpace B S hS X.1 ∧ IsAbsolutelyQuasiSeparated B S hS hZ X.1 ∧
      IsQuasiCompactSpace B S hS (⊤ : Subfunctor X.1).toFunctor ∧
      IsAbsolutelyQuasiSeparated B S hS hZ (⊤ : Subfunctor X.1).toFunctor ∧
      Spaces.LP26.SatisfiesWA (edsOpenSpace hsq) ∧ Spaces.LP26.SatisfiesWA (edsEtaleSpace hsq) :=
  proposition_5_8_nonVacuity (supportEmpty B S hS) (edsTop B S hS)
    (openSubspaceQuasiCompact B S hS) hZ X₀ hX₀qs

/-- Non-vacuity of LP26 Corollary 1.2, unconditional: a non-empty affine object of the site
represents a non-empty quasi-compact quasi-separated algebraic space, which satisfies weak
approximability (`Spaces.LP26.corollary_1_2_nonVacuity`); such objects exist over `Spec ℤ`
(`Spaces.LP26.corollary_1_2_int_witness` with `tag021R`). -/
theorem corollary_1_2_nonVacuity_unconditional
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (hne : Nonempty ((BigFppfOver.toScheme B S hS).obj T₀)) :
    Nonempty (points B S hS (Affine.space T₀).1) ∧
      IsQuasiCompactSpace B S hS (Affine.space T₀).1 ∧
      IsAbsolutelyQuasiSeparated B S hS (containsTerminal B) (Affine.space T₀).1 ∧
      Spaces.LP26.SatisfiesWA (Affine.space T₀) :=
  corollary_1_2_nonVacuity (tag06UQ B S hS) (supportTriangulated B S hS) containsTerminal
    (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS) (pullbackSupport B S hS)
    (pullbackDisjoint B S hS) (etaleRestrictionSupport B S hS) (openImmersionCounit B S hS)
    (perfectPullback B S hS) (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0AEC B S hS)
    (tag0AED B S hS) tag079Q tag0A8G rightAdjointCoproducts (quasiCompactSource B S hS)
    (compactComplPreimage B S hS) (tag08GGUnit B S hS) (tag08GGCounit B S hS) (tag073B B S hS)
    (tag073BTwo B S hS) (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS)
    (edsOfComplSubset B S hS) (supportEmpty B S hS) (openSubspaceQuasiCompact B S hS)
    (tag09IT B S hS) (affineQuasiSeparatedYoneda B S hS) (tag06Z0Exact B S hS)
    (tag06Z0Qcoh B S hS) (tag06Z0 B S hS) (tag07TY B S hS) T₀ hT₀ hne

/-- A witness for `corollary_1_2_nonVacuity_unconditional`, unconditional: some big fppf site
contains `Spec ℤ`, whose object `Spec ℤ` is affine and non-empty
(`Spaces.LP26.corollary_1_2_int_witness` with `tag021R`). -/
theorem corollary_1_2_int_witness_unconditional :
    ∃ (B : BigFppfSite.{0}) (hS : B.Contains (Spec (.of ℤ))),
      IsAffine ((BigFppfOver.toScheme B _ hS).obj (Affine.intObject B hS)) ∧
      Nonempty ((BigFppfOver.toScheme B _ hS).obj (Affine.intObject B hS)) :=
  corollary_1_2_int_witness tag021R.{0}

/-- Non-vacuity of GL26 Lemma A.4, unconditional (`Spaces.LP26.lemma_A_4_nonVacuity`). -/
theorem lemma_A_4_nonVacuity_unconditional
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    (qcohDerived (Supported.representedSpace T₀)).IsTriangulated ∧
      (∀ T, ObjectProperty.IsTriangulated
        (CohomologySupportedOn B S hS (Supported.representedSpace T₀).1 (Supported.representedSpace T₀).2 T)) ∧
      IsQuasiCompactSpace B S hS (Supported.representedSpace T₀).1 ∧
      IsAbsolutelyQuasiSeparated B S hS (containsTerminal B) (Supported.representedSpace T₀).1 ∧
      IsOpenImmersion B S hS
        (𝟙 (Supported.representedSpace T₀) : Supported.representedSpace T₀ ⟶ Supported.representedSpace T₀).hom ∧
      IsQuasiCompact B S hS
        (𝟙 (Supported.representedSpace T₀) : Supported.representedSpace T₀ ⟶ Supported.representedSpace T₀).hom ∧
      IsClosed (Set.univ : Set (points B S hS (Supported.representedSpace T₀).1)) ∧
      _root_.IsCompact (Set.univ : Set (points B S hS (Supported.representedSpace T₀).1))ᶜ :=
  lemma_A_4_nonVacuity (tag06UQ B S hS) (supportTriangulated B S hS)
    (affineQuasiSeparatedYoneda B S hS) containsTerminal T₀ hT₀

/-- Non-vacuity of GL26 Lemma A.6, unconditional (`Spaces.LP26.lemma_A_6_nonVacuity`). -/
theorem lemma_A_6_nonVacuity_unconditional
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ∃ hsq : IsElementaryDistinguishedSquare B S hS (Supported.representedSpace T₀).2
        (⊤ : Subfunctor (Supported.representedSpace T₀).1) (⊤ : Subfunctor (Supported.representedSpace T₀).1).ι,
      IsAbsolutelyQuasiSeparated B S hS (containsTerminal B) (Supported.representedSpace T₀).1 ∧
      IsQuasiCompactSpace B S hS (⊤ : Subfunctor (Supported.representedSpace T₀).1).toFunctor ∧
      IsAbsolutelyQuasiSeparated B S hS (containsTerminal B)
        (⊤ : Subfunctor (Supported.representedSpace T₀).1).toFunctor ∧
      IsClosed (∅ : Set (points B S hS (Supported.representedSpace T₀).1)) ∧
      (∅ : Set (points B S hS (Supported.representedSpace T₀).1)) ⊆
        (Set.range (pointsMap B S hS _ (⊤ : Subfunctor (Supported.representedSpace T₀).1).ι))ᶜ := by
  obtain ⟨hsq, -, -, -, -, h⟩ := lemma_A_6_nonVacuity (tag06UQ B S hS) (supportTriangulated B S hS)
    (affineQuasiSeparatedYoneda B S hS) containsTerminal (edsTop B S hS) T₀ hT₀
  exact ⟨hsq, h⟩

/-- Non-vacuity of the preferred-class clause of GL26 Lemma A.9, unconditional: at an affine
`X = h_{T₀}` a compact generator detecting objects bounded below uniformly exists
(`Spaces.Supported.nonVacuity_detectsBelowUniformly_affine`). -/
theorem nonVacuity_detectsBelowUniformly_affine_unconditional
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (X : AlgebraicSpaces B S hS) (hX : X = Supported.representedSpace T₀) :
    ∃ G : DqcZ X Set.univ, IsCompactObject.{u} G ∧ IsPaperGenerator G ∧
      DetectsBelowUniformly (stdT X Set.univ) G :=
  nonVacuity_detectsBelowUniformly_affine (tag08F3 B S hS) (supportedDirectSums B S hS)
    (tag0AEC B S hS) (tag0AED B S hS) (tag0GFD B S hS) (tag0GFI B S hS)
    (affineQuasiSeparatedYoneda B S hS) containsTerminal T₀ hT₀ X hX

end RelativeFM.SpacesVerified

#print axioms RelativeFM.SpacesVerified.lemma_5_5_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_5_dqc_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_6_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_6_dqcZ_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_7_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_7_supported_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_9_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_9_minus_noetherian_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_9_bounded_noetherian_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_9_minus_eq_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_5_9_bounded_eq_unconditional
#print axioms RelativeFM.SpacesVerified.proposition_5_8_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_dqc_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_4_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_6_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_6_bounded_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_9_preferred_univ_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_lemma_5_5_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_lemma_5_6_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_lemma_5_7_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_lemma_5_9_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_lemma_5_9_noetherian_unconditional
#print axioms RelativeFM.SpacesVerified.proposition_5_8_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_int_witness_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_4_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_A_6_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.nonVacuity_detectsBelowUniformly_affine_unconditional
