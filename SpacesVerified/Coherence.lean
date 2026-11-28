/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces
import SpacesVerified.Affine
import SpacesVerified.Discharge
import SpacesVerified.Supported
import SpacesVerified.LP26Inputs
import SpacesVerified.LP26
import SpacesVerified.StandardWA
import SpacesVerified.Statements
import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies

/-!
# LP26 Corollary 1.2, coherence clause, unconditional

The two tagged AxiomMath inputs added to `Spaces/LP26/Inputs.lean` by `Spaces/LP26/Coherence.lean`
are proved here by the AxiomMath/Stacks declarations they name (commit `f56a316`):

| input | Stacks | proved by |
|---|---|---|
| `CoherentOfIsoInput` | (03DL, invariance) | `Stacks.SheafOfModules.isCoherentOnSite_of_iso` |
| `CoherentOfIsZeroInput` | (03DL, the zero sheaf) | `Stacks.SheafOfModules.isCoherentOnSite_zero` |

With every other input of `Spaces.LP26.corollary_1_2_coherent` already proved
(`SpacesVerified/Discharge.lean`, `Affine.lean`, `Supported.lean`, `LP26Inputs.lean`,
`Statements.lean`), **LP26 Corollary 1.2** (`cor:weak_approx_spaces`), last clause, holds with
nothing assumed: `corollary_1_2_coherent_unconditional` (for `X` Noetherian and `T ⊆ |X|` closed
with quasi-compact complement, `D_{qc,T}(X)` is coherent), with non-vacuity
`corollary_1_2_coherent_nonVacuity_unconditional` (over an affine locally Noetherian base `S`)
and the concrete instance `corollary_1_2_coherent_int_unconditional` (`S = Spec ℤ`).  The two
steps of LP26's proof of Lemma 5.9 on the preferred class are unconditional too:
`inPreferredClass_standardTStructure_unconditional` (the standard `t`-structure lies in the
preferred class) and `minusC_boundedC_eq_standard_unconditional` (`𝒯^-_c`, `𝒯^b_c` computed for
it), for `X` qcqs; the `…_of_standardWA_unconditional` forms keep standard W.A. as hypothesis.  The statements are those of
`Spaces/LP26/Coherence.lean`, with the differences from the paper recorded there (LP26's
hypothesis of quasi-finite separated diagonal is not needed).  The instance hypotheses that
`D_QCoh(𝒪_X)` and `D_T(𝒪_X)` are triangulated (Stacks 06UQ and `SupportTriangulatedInput`,
proved) are supplied by the local instances `isTriangulated_qcohDerived'`,
`isTriangulated_support'`.  The instance context is that of `Spaces/LP26/Coherence.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry AlgebraicGeometry.Space RelativeWeakApprox

namespace RelativeFM.SpacesVerified

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify
  AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] isTriangulated_qcohDerived' isTriangulated_support'

open RelativeFM.Spaces RelativeFM.Spaces.Supported RelativeFM.Spaces.LP26

section Inputs

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Coherence is invariant under isomorphism (Stacks 03DL), proved. -/
theorem coherentOfIso : CoherentOfIsoInput B S hS := by
  intro X M N e hM
  exact Stacks.SheafOfModules.isCoherentOnSite_of_iso e hM

/-- A zero sheaf of modules is coherent (Stacks 03DL), proved. -/
theorem coherentOfIsZero : CoherentOfIsZeroInput B S hS := by
  intro X Z hZ
  exact Stacks.SheafOfModules.isCoherentOnSite_zero hZ

end Inputs

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **LP26 Corollary 1.2** (`cor:weak_approx_spaces`), last clause, unconditional: if `X` is a
Noetherian algebraic space and `T ⊆ |X|` is closed with quasi-compact complement, then
`D_{qc,T}(X)` is coherent (`IsCoherent.{u}`, LP26 §2 and CHNS, Definition 10.1.1)
(`Spaces.LP26.corollary_1_2_coherent` with its inputs proved).  As there, LP26's hypothesis of
quasi-finite separated diagonal is not needed. -/
theorem corollary_1_2_coherent_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) :
    IsCoherent.{u} (DqcZ X T) :=
  corollary_1_2_coherent (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS)
    (pullbackSupport B S hS) (pullbackDisjoint B S hS) (etaleRestrictionSupport B S hS)
    (openImmersionCounit B S hS) (perfectPullback B S hS) (tag08F3 B S hS)
    (supportedDirectSums B S hS) (tag0AEC B S hS) (tag0AED B S hS) tag079Q tag0A8G
    rightAdjointCoproducts (quasiCompactSource B S hS) (compactComplPreimage B S hS)
    (tag08GGUnit B S hS) (tag08GGCounit B S hS) (tag073B B S hS) (tag073BTwo B S hS)
    (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS) (tag08FABound B S hS)
    (edsOfComplSubset B S hS) (supportEmpty B S hS) (openSubspaceQuasiCompact B S hS)
    (tag09IT B S hS) (affineQuasiSeparatedYoneda B S hS) (tag06Z0Exact B S hS)
    (tag06Z0Qcoh B S hS) (tag06Z0 B S hS) (tag07TY B S hS) (perfectPseudoCoherent B S hS)
    (tag08FVTwo B S hS) (pseudoCoherentFromOfIsLE B S hS) (tag08FU2 B S hS) (perfectQcoh B S hS)
    (tag08HP B S hS) (tag08IK B S hS) (coherentOfIso B S hS) (coherentOfIsZero B S hS) hZ X hN T
    hT hTc

/-- **Non-vacuity of `corollary_1_2_coherent_unconditional`**
(`Spaces.LP26.corollary_1_2_coherent_nonVacuity` with its inputs proved): over an affine, locally
Noetherian base scheme `S` (for instance `S = Spec ℤ`, contained in some big fppf site:
`corollary_1_2_int_witness_unconditional`), the base `X = S` is a Noetherian algebraic space,
`T = |S|` is closed with empty complement, the instance arguments hold, and `D_{qc,T}(S)` is
coherent, with the standard `t`-structure in its preferred class (so the quantifier in
`IsCoherent` is not vacuous). -/
theorem corollary_1_2_coherent_nonVacuity_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    [IsAffine S] [IsLocallyNoetherian S] :
    ∃ X : AlgebraicSpaces B S hS, X = baseSpace B S hS ∧ IsNoetherian B S hS hZ X.1 ∧
      IsClosed (Set.univ : Set (points B S hS X.1)) ∧
      _root_.IsCompact (Set.univ : Set (points B S hS X.1))ᶜ ∧
      (qcohDerived X).IsTriangulated ∧
      ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 Set.univ) ∧
      ∀ [(qcohDerived X).IsTriangulated]
        [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 Set.univ)],
        IsCoherent.{u} (DqcZ X Set.univ) ∧
          SumUniverse.InPreferredClass.{u} (standardTStructure X Set.univ) :=
  corollary_1_2_coherent_nonVacuity (tag06UQ B S hS) (supportTriangulated B S hS)
    (tag08FA B S hS) (tag08F4 B S hS) (tag0AFJ B S hS)
    (pullbackSupport B S hS) (pullbackDisjoint B S hS) (etaleRestrictionSupport B S hS)
    (openImmersionCounit B S hS) (perfectPullback B S hS) (tag08F3 B S hS)
    (supportedDirectSums B S hS) (tag0AEC B S hS) (tag0AED B S hS) tag079Q tag0A8G
    rightAdjointCoproducts (quasiCompactSource B S hS) (compactComplPreimage B S hS)
    (tag08GGUnit B S hS) (tag08GGCounit B S hS) (tag073B B S hS) (tag073BTwo B S hS)
    (tag09M8 B S hS) (perfectBoundedAbove B S hS) (tag09MB B S hS) (tag08FABound B S hS)
    (edsOfComplSubset B S hS) (supportEmpty B S hS) (openSubspaceQuasiCompact B S hS)
    (tag09IT B S hS) (affineQuasiSeparatedYoneda B S hS) (tag06Z0Exact B S hS)
    (tag06Z0Qcoh B S hS) (tag06Z0 B S hS) (tag07TY B S hS) (perfectPseudoCoherent B S hS)
    (tag08FVTwo B S hS) (pseudoCoherentFromOfIsLE B S hS) (tag08FU2 B S hS) (perfectQcoh B S hS)
    (tag08HP B S hS) (tag08IK B S hS) (coherentOfIso B S hS) (coherentOfIsZero B S hS)
    (affineQuasiSeparated B S hS) hZ

/-! ### The preferred class (LP26, proof of Lemma 5.9) -/

/-- **The standard `t`-structure of `D_{qc,T}(X)` lies in the preferred equivalence class**
(LP26, proof of Lemma 5.9, `lem:characterize_T-_c`), unconditional, under standard W.A.
(`Spaces.LP26.inPreferredClass_standardTStructure` with Stacks 079Q, 08F3 and the direct-sum
remark preceding 0AED proved). -/
theorem inPreferredClass_standardTStructure_of_standardWA_unconditional
    (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) (h : SatisfiesStandardWA X)
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) :
    SumUniverse.InPreferredClass.{u} (standardTStructure X T) :=
  inPreferredClass_standardTStructure X T tag079Q (tag08F3 B S hS) (supportedDirectSums B S hS) h
    hT hTc

/-- **The standard `t`-structure of `D_{qc,T}(X)` lies in the preferred equivalence class**,
unconditional, for every quasi-compact quasi-separated `X` and closed `T ⊆ |X|` with
quasi-compact complement: standard W.A. holds by LP26 Corollary 1.2
(`corollary_1_2_standard_unconditional`). -/
theorem inPreferredClass_standardTStructure_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) :
    SumUniverse.InPreferredClass.{u} (standardTStructure X T) :=
  inPreferredClass_standardTStructure_of_standardWA_unconditional X T
    (corollary_1_2_standard_unconditional hZ X hXqc hXqs) hT hTc

/-- **`𝒯^-_c` and `𝒯^b_c` may be computed for the standard `t`-structure** (LP26, proof of
Lemma 5.9), unconditional, under standard W.A. (`Spaces.LP26.minusC_boundedC_eq_standard` with
Stacks 079Q, 08F3 and the direct-sum remark proved). -/
theorem minusC_boundedC_eq_standard_of_standardWA_unconditional
    (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) (h : SatisfiesStandardWA X)
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (t : TStructure (DqcZ X T)) (ht : SumUniverse.InPreferredClass.{u} t) :
    minusC t (fun D => IsCompactObject.{u} D) = standardMinusC X T ∧
      boundedC t (fun D => IsCompactObject.{u} D) = standardBoundedC X T :=
  minusC_boundedC_eq_standard X T tag079Q (tag08F3 B S hS) (supportedDirectSums B S hS) h hT hTc
    t ht

/-- **`𝒯^-_c` and `𝒯^b_c` may be computed for the standard `t`-structure**, unconditional, for
every quasi-compact quasi-separated `X` and closed `T ⊆ |X|` with quasi-compact complement, and
every `t`-structure `t` of the preferred class of `D_{qc,T}(X)` (standard W.A. by LP26
Corollary 1.2).  Non-vacuity of the preferred class: `inPreferredClass_standardTStructure_unconditional`. -/
theorem minusC_boundedC_eq_standard_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (t : TStructure (DqcZ X T)) (ht : SumUniverse.InPreferredClass.{u} t) :
    minusC t (fun D => IsCompactObject.{u} D) = standardMinusC X T ∧
      boundedC t (fun D => IsCompactObject.{u} D) = standardBoundedC X T :=
  minusC_boundedC_eq_standard_of_standardWA_unconditional X T
    (corollary_1_2_standard_unconditional hZ X hXqc hXqs) hT hTc t ht

/-- **A concrete instance of `corollary_1_2_coherent_unconditional`**: some big fppf site contains
`Spec ℤ` (`corollary_1_2_int_witness_unconditional`), and over the base `S = Spec ℤ` (affine,
locally Noetherian) the base space `X = S` is a Noetherian algebraic space with `D_qc(X)`
coherent. -/
theorem corollary_1_2_coherent_int_unconditional :
    ∃ (B : BigFppfSite.{0}) (hS : B.Contains (Spec (.of ℤ))) (X : AlgebraicSpaces B _ hS),
      IsNoetherian B _ hS (containsTerminal B) X.1 ∧ IsCoherent.{0} (DqcZ X Set.univ) := by
  obtain ⟨B, hS, -, -⟩ := corollary_1_2_int_witness_unconditional
  obtain ⟨X, -, hN, hcl, hco, -⟩ :=
    corollary_1_2_coherent_nonVacuity_unconditional (hS := hS) (containsTerminal B)
  exact ⟨B, hS, X, hN, corollary_1_2_coherent_unconditional _ X hN _ hcl hco⟩

end RelativeFM.SpacesVerified

#print axioms RelativeFM.SpacesVerified.coherentOfIso
#print axioms RelativeFM.SpacesVerified.coherentOfIsZero
#print axioms RelativeFM.SpacesVerified.corollary_1_2_coherent_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_coherent_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.corollary_1_2_coherent_int_unconditional
#print axioms RelativeFM.SpacesVerified.inPreferredClass_standardTStructure_of_standardWA_unconditional
#print axioms RelativeFM.SpacesVerified.inPreferredClass_standardTStructure_unconditional
#print axioms RelativeFM.SpacesVerified.minusC_boundedC_eq_standard_of_standardWA_unconditional
#print axioms RelativeFM.SpacesVerified.minusC_boundedC_eq_standard_unconditional
