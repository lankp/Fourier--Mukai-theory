/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces
import SpacesVerified.Affine
import SpacesVerified.Discharge
import SpacesVerified.Supported
import SpacesVerified.LP26Inputs
import SpacesVerified.LP26

/-!
# LP26 Proposition 5.8 and Corollary 1.2, standard W.A., unconditional

The results of `Spaces/LP26/StandardWA.lean` with every tagged AxiomMath input proved
(`SpacesVerified/Discharge.lean`, `Affine.lean`, `Supported.lean`, `LP26Inputs.lean`), so that
they hold with axioms `propext`, `Classical.choice`, `Quot.sound` only:

* **LP26 Proposition 5.8** (`prop:A8`), standard-W.A. part:
  `proposition_5_8_standard_unconditional`;
* **LP26 Corollary 1.2** (`cor:weak_approx_spaces`), first claim in LP26's stronger form
  (standard W.A., Definition 5.3): `corollary_1_2_standard_unconditional`;
* non-vacuity: `proposition_5_8_standard_nonVacuity_unconditional`,
  `corollary_1_2_standard_nonVacuity_unconditional` (a witness: `Spec ℤ`,
  `corollary_1_2_int_witness_unconditional`).

`Spaces/LP26/StandardWA.lean` adds no tagged input: its inputs are those of
`Spaces.LP26.proposition_5_8` and `corollary_1_2`, and Stacks 08FA (2) (`Tag08FABoundInput`,
`tag08FABound`), all proved in `SpacesVerified/LP26Inputs.lean`.  The instance hypotheses that
`D_QCoh(𝒪_X)` and `D_T(𝒪_X)` are triangulated (Stacks 06UQ and `SupportTriangulatedInput`, both
proved) are supplied by the local instances `isTriangulated_qcohDerived'`,
`isTriangulated_support'`.  The statements are otherwise those of the `Spaces` theorems cited in
each docstring, with the differences from the paper recorded there (for Corollary 1.2: LP26's
hypothesis of quasi-finite separated diagonal is not needed, so the statement is stronger).
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

attribute [local instance] isTriangulated_qcohDerived_affineSpace
  isTriangulated_support_affineSpace

open RelativeFM.Spaces RelativeFM.Spaces.Supported RelativeFM.Spaces.LP26

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **LP26 Proposition 5.8** (`prop:A8`), standard-W.A. part, unconditional: for an elementary
distinguished square `(U ⊆ X, V ⟶ X)` of quasi-compact quasi-separated algebraic spaces, if `U`
and `V` satisfy standard W.A. (Definition 5.3), so does `X`: for every closed `S ⊆ |X|` with
quasi-compact complement there are weak approximation data on `D_{qc,S}(X)` whose `t`-structure
is the standard one (`Spaces.LP26.proposition_5_8_standard` with its inputs proved). -/
theorem proposition_5_8_standard_unconditional {X : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor X.1} {fV : V ⟶ X.1}
    (hsq : IsElementaryDistinguishedSquare B S hS X.2 Uo fV)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hVqc : IsQuasiCompactSpace B S hS V) (hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V)
    (hU : SatisfiesStandardWA (edsOpenSpace hsq))
    (hY : SatisfiesStandardWA (edsEtaleSpace hsq)) :
    SatisfiesStandardWA X :=
  proposition_5_8_standard (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS)
    (pullbackSupport B S hS) (pullbackDisjoint B S hS) (etaleRestrictionSupport B S hS)
    (openImmersionCounit B S hS) (perfectPullback B S hS) (tag08F3 B S hS)
    (supportedDirectSums B S hS) (tag0AEC B S hS) (tag0AED B S hS) tag079Q tag0A8G
    rightAdjointCoproducts (quasiCompactSource B S hS) (compactComplPreimage B S hS)
    (tag08GGUnit B S hS) (tag08GGCounit B S hS) (tag073B B S hS) (tag073BTwo B S hS)
    (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS) (tag08FABound B S hS) hsq hZ
    hXqc hXqs hUqc hVqc hVqs hU hY

/-- **LP26 Corollary 1.2** (`cor:weak_approx_spaces`), first claim in LP26's stronger form,
unconditional: a quasi-compact quasi-separated algebraic space `X` satisfies **standard W.A.**
(Definition 5.3): for every closed `S ⊆ |X|` with quasi-compact complement there are weak
approximation data on `D_{qc,S}(X)` whose `t`-structure is the standard one
(`Spaces.LP26.corollary_1_2_standard` with its inputs proved).  As there, LP26's hypothesis of
quasi-finite separated diagonal is not needed. -/
theorem corollary_1_2_standard_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    SatisfiesStandardWA X :=
  corollary_1_2_standard (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS)
    (pullbackSupport B S hS) (pullbackDisjoint B S hS) (etaleRestrictionSupport B S hS)
    (openImmersionCounit B S hS) (perfectPullback B S hS) (tag08F3 B S hS)
    (supportedDirectSums B S hS) (tag0AEC B S hS) (tag0AED B S hS) tag079Q tag0A8G
    rightAdjointCoproducts (quasiCompactSource B S hS) (compactComplPreimage B S hS)
    (tag08GGUnit B S hS) (tag08GGCounit B S hS) (tag073B B S hS) (tag073BTwo B S hS)
    (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS) (tag08FABound B S hS)
    (edsOfComplSubset B S hS) (supportEmpty B S hS) (openSubspaceQuasiCompact B S hS)
    (tag09IT B S hS) (affineQuasiSeparatedYoneda B S hS) (tag06Z0Exact B S hS)
    (tag06Z0Qcoh B S hS) (tag06Z0 B S hS) (tag07TY B S hS) hZ X hXqc hXqs

/-- Non-vacuity of `proposition_5_8_standard_unconditional`
(`Spaces.LP26.proposition_5_8_standard_nonVacuity`): for every quasi-separated `X₀` the square
`(⊤ ⊆ X, ⊤.ι)` on the empty open subspace `X` of `X₀` meets every hypothesis. -/
theorem proposition_5_8_standard_nonVacuity_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X₀ : AlgebraicSpaces B S hS) (hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀.1) :
    ∃ (X : AlgebraicSpaces B S hS) (hsq : IsElementaryDistinguishedSquare B S hS X.2
        (⊤ : Subfunctor X.1) (⊤ : Subfunctor X.1).ι),
      IsQuasiCompactSpace B S hS X.1 ∧ IsAbsolutelyQuasiSeparated B S hS hZ X.1 ∧
      IsQuasiCompactSpace B S hS (⊤ : Subfunctor X.1).toFunctor ∧
      IsAbsolutelyQuasiSeparated B S hS hZ (⊤ : Subfunctor X.1).toFunctor ∧
      SatisfiesStandardWA (edsOpenSpace hsq) ∧ SatisfiesStandardWA (edsEtaleSpace hsq) :=
  proposition_5_8_standard_nonVacuity (supportEmpty B S hS) (edsTop B S hS)
    (openSubspaceQuasiCompact B S hS) hZ X₀ hX₀qs

/-- Non-vacuity of `corollary_1_2_standard_unconditional`
(`Spaces.LP26.corollary_1_2_standard_nonVacuity`): a non-empty affine object `T₀` of the site
represents a non-empty quasi-compact quasi-separated algebraic space satisfying standard W.A.;
such objects exist over `Spec ℤ` (`corollary_1_2_int_witness_unconditional`). -/
theorem corollary_1_2_standard_nonVacuity_unconditional
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (hne : Nonempty ((BigFppfOver.toScheme B S hS).obj T₀)) :
    Nonempty (points B S hS (Affine.space T₀).1) ∧
      IsQuasiCompactSpace B S hS (Affine.space T₀).1 ∧
      IsAbsolutelyQuasiSeparated B S hS (containsTerminal B) (Affine.space T₀).1 ∧
      SatisfiesStandardWA (Affine.space T₀) :=
  corollary_1_2_standard_nonVacuity (tag06UQ B S hS) (supportTriangulated B S hS) containsTerminal
    (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS) (pullbackSupport B S hS)
    (pullbackDisjoint B S hS) (etaleRestrictionSupport B S hS) (openImmersionCounit B S hS)
    (perfectPullback B S hS) (tag08F3 B S hS) (supportedDirectSums B S hS) (tag0AEC B S hS)
    (tag0AED B S hS) tag079Q tag0A8G rightAdjointCoproducts (quasiCompactSource B S hS)
    (compactComplPreimage B S hS) (tag08GGUnit B S hS) (tag08GGCounit B S hS) (tag073B B S hS)
    (tag073BTwo B S hS) (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS)
    (tag08FABound B S hS) (edsOfComplSubset B S hS) (supportEmpty B S hS)
    (openSubspaceQuasiCompact B S hS) (tag09IT B S hS) (affineQuasiSeparatedYoneda B S hS)
    (tag06Z0Exact B S hS) (tag06Z0Qcoh B S hS) (tag06Z0 B S hS) (tag07TY B S hS) T₀ hT₀ hne

end RelativeFM.SpacesVerified

#print axioms RelativeFM.SpacesVerified.proposition_5_8_standard_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_standard_unconditional
#print axioms RelativeFM.SpacesVerified.proposition_5_8_standard_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_standard_nonVacuity_unconditional
