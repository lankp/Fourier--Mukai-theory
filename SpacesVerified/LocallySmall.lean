/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces
import SpacesVerified.Discharge
import SpacesVerified.Supported
import SpacesVerified.LP26Inputs
import SpacesVerified.LP26

/-!
# `D(𝒪_X)` is locally `u`-small; LP26 Theorem 1.1 on algebraic spaces

AxiomMath's derived category `D(𝒪_X)` of an algebraic space (`Spaces.D`) has morphisms in
`Type (u + 1)` and direct sums indexed by `Type u`.  LP26 Theorem 1.1 (`thm:glueing_weak_approx`)
in the form that fits it, `Spaces.Stacks.theorem_1_1_univ` at `w = u`, asks the three categories
of the recollement to be locally `u`-small ("Hom sets are sets").  This is Stacks 079Q
(`Tag079QInput`, proved in `SpacesVerified/LP26Inputs.lean` by AxiomMath's
`Stacks.ModulesOnACategory.CartesianSubcategory.locallySmall_derivedCategory`):

* `locallySmall_D`: `LocallySmall.{u} (Spaces.D B S hS X)`, an instance;
* `locallySmall_qcohDerived`: `LocallySmall.{u}` for `D_qc(X)`, an instance;
* `locallySmall_dqcZ_unconditional`: `LocallySmall.{u}` for `D_{qc,T}(X)`, an instance.

With these and the direct sums of `D_{qc,T}(X)` for `T` closed (Stacks 08F3 and the remark
preceding 0AED, proved in `SpacesVerified/Supported.lean`), `theorem_1_1_univ` applies to every
recollement of supported categories over algebraic spaces with nothing assumed:

* `theorem_1_1_dqcZ_unconditional`: **LP26 Theorem 1.1** for a recollement
  `D_{qc,T₁}(X₁) → D_{qc,T}(X) → D_{qc,T₂}(X₂)` with `T₁, T, T₂` closed;
* `theorem_1_1_dqcZ_nonVacuity_unconditional`: for every quasi-compact quasi-separated `X`
  (for instance `X = h_{T₀}` with `T₀` affine, `theorem_1_1_dqcZ_nonVacuity_affine_unconditional`),
  the recollement of GL26 Lemma A.4 (`lem:spacey_recollement`) along `𝟙 : X ⟶ X` with `W = |X|`
  meets every hypothesis (its outer terms are weakly approximable by LP26 Corollary 1.2, the middle term has
  a compact generator by GL26 Lemma A.9).

The statement of `theorem_1_1_dqcZ_unconditional` is that of `Spaces.Stacks.theorem_1_1_univ`
at `w = u` with compactness written `IsCompactObject.{u}` (AxiomMath's, equivalent to
`SumUniverse.IsCompactAb.{u}`: `Stacks.isCompactObject_iff_sumUniverse_isCompactAb`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry AlgebraicGeometry.Space RelativeWeakApprox

namespace RelativeFM.SpacesVerified

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Local smallness, in the instance context of `Spaces/Categories.lean` -/

section D

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

/-- **`D(𝒪_X)` is locally `u`-small** (Stacks 079Q, `tag079Q`): AxiomMath's derived category of
an algebraic space, whose morphisms are in `Type (u + 1)`, has `u`-small morphism types. -/
instance locallySmall_D (X : AlgebraicSpaces B S hS) : LocallySmall.{u} (Spaces.D B S hS X) :=
  have := isGrothendieckAbelian_modules B S hS X.1 X.2
  tag079Q _

end D

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify
  AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

attribute [local instance] isTriangulated_qcohDerived' isTriangulated_support'

attribute [local instance] isTriangulated_qcohDerived_represented
  isTriangulated_support_represented

open RelativeFM.Spaces RelativeFM.Spaces.Supported RelativeFM.Spaces.LP26

/-- **`D_{qc,T}(X)` is locally `u`-small** (Stacks 079Q, `Spaces.LP26.locallySmall_dqcZ` with
`tag079Q`). -/
instance locallySmall_dqcZ_unconditional (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) : LocallySmall.{u} (DqcZ X T) :=
  locallySmall_dqcZ tag079Q X T

/-- **`D_qc(X)` is locally `u`-small** (Stacks 079Q, `tag079Q`; a full subcategory of
`D(𝒪_X)`). -/
instance locallySmall_qcohDerived (X : AlgebraicSpaces B S hS) :
    LocallySmall.{u} (AlgebraicGeometry.Space.QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :=
  have := isGrothendieckAbelian_modules B S hS X.1 X.2
  have : LocallySmall.{u} (DerivedCategory (Space.Modules.{u, u} B S hS X.1 X.2)) := tag079Q _
  inferInstance

/-- **LP26 Theorem 1.1** (`thm:glueing_weak_approx`) on algebraic spaces, unconditional.  Let
`D_{qc,T₁}(X₁) → D_{qc,T}(X) → D_{qc,T₂}(X₂)` be a recollement of supported derived categories
of algebraic spaces, `T₁, T, T₂` closed, with the outer terms weakly approximable, and let `G'`
be a compact generator of `D_{qc,T}(X)`.  Then `D_{qc,T}(X)` is weakly approximable if and only
if `Hom(G', G'[n]) = 0` for `n ≫ 0`.  `Spaces.Stacks.theorem_1_1_univ` at `w = u`, with local
smallness (Stacks 079Q, `locallySmall_dqcZ_unconditional`), direct sums (Stacks 08F3 and the
remark preceding 0AED) and the triangulated structures (Stacks 06UQ,
`SupportTriangulatedInput`) proved. -/
theorem theorem_1_1_dqcZ_unconditional {X₁ X X₂ : AlgebraicSpaces B S hS}
    {T₁ : Set (points B S hS X₁.1)} {T : Set (points B S hS X.1)}
    {T₂ : Set (points B S hS X₂.1)} (hT₁ : IsClosed T₁) (hT : IsClosed T) (hT₂ : IsClosed T₂)
    (R : Recollement (DqcZ X₁ T₁) (DqcZ X T) (DqcZ X₂ T₂))
    (hZ : SumUniverse.SatisfiesPaperWA.{u} (DqcZ X₁ T₁))
    (hU : SumUniverse.SatisfiesPaperWA.{u} (DqcZ X₂ T₂))
    (G' : DqcZ X T) (hG'c : IsCompactObject.{u} G') (hG'g : IsPaperGenerator G') :
    SumUniverse.SatisfiesPaperWA.{u} (DqcZ X T) ↔
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∀ f : G' ⟶ G'⟦n⟧, f = 0 := by
  have : HasCoproducts.{u} (DqcZ X₁ T₁) :=
    hasCoproducts (tag08F3 B S hS) (supportedDirectSums B S hS) X₁ T₁ hT₁
  have : HasCoproducts.{u} (DqcZ X T) :=
    hasCoproducts (tag08F3 B S hS) (supportedDirectSums B S hS) X T hT
  have : HasCoproducts.{u} (DqcZ X₂ T₂) :=
    hasCoproducts (tag08F3 B S hS) (supportedDirectSums B S hS) X₂ T₂ hT₂
  exact Stacks.theorem_1_1_univ.{u} R hZ hU G'
    ((Stacks.isCompactObject_iff_sumUniverse_isCompactAb G').1 hG'c) hG'g

/-- **Non-vacuity of `theorem_1_1_dqcZ_unconditional`**: for every quasi-compact
quasi-separated algebraic space `X`, the recollement of GL26 Lemma A.4
(`lemma_A_4_unconditional`) along `𝟙 : X ⟶ X` with `W = |X|` has closed supports, its outer
terms are weakly approximable (LP26 Corollary 1.2, `corollary_1_2_unconditional`), and its middle
term `D_qc(X)` has a compact generator (GL26 Lemma A.9, `lemma_A_9_unconditional`).  Such `X`
exist: `theorem_1_1_dqcZ_nonVacuity_affine_unconditional`. -/
theorem theorem_1_1_dqcZ_nonVacuity_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ∃ (T₁ T₂ : Set (points B S hS X.1))
      (_ : Recollement (DqcZ X T₁) (DqcZ X Set.univ) (DqcZ X T₂)),
      IsClosed T₁ ∧ IsClosed T₂ ∧
      SumUniverse.SatisfiesPaperWA.{u} (DqcZ X T₁) ∧
      SumUniverse.SatisfiesPaperWA.{u} (DqcZ X T₂) ∧
      ∃ G' : DqcZ X Set.univ, IsCompactObject.{u} G' ∧ IsPaperGenerator G' := by
  have := compactSpace_points_of_isQuasiCompactSpace B S hS X.2 hqc
  have hcl : IsClosed (Set.univ : Set (points B S hS X.1)) := isClosed_univ
  have hco : _root_.IsCompact (Set.univ : Set (points B S hS X.1))ᶜ := by
    rw [Set.compl_univ]; exact isCompact_empty
  have hoi : IsOpenImmersion B S hS (𝟙 X : X ⟶ X).hom := isOpenImmersion_id X
  have hjqc : IsQuasiCompact B S hS (𝟙 X : X ⟶ X).hom := isQuasiCompact_of_isIso' (𝟙 X.1)
  obtain ⟨R, -⟩ := lemma_A_4_unconditional hZ hqc hqs (𝟙 X) hoi hjqc Set.univ hcl hco
  have hWA := corollary_1_2_unconditional hZ X hqc hqs
  have hid : pointsMap B S hS X.1 (𝟙 X : X ⟶ X).hom = id := by
    change pointsMap B S hS _ (𝟙 X.1) = id
    rw [pointsMap_id]
  have h₁ : pointsMap B S hS X.1 (𝟙 X : X ⟶ X).hom ⁻¹' (Set.univ : Set (points B S hS X.1)) =
      Set.univ := Set.preimage_univ
  have h₂ : (Set.univ : Set (points B S hS X.1)) ∩
      (Set.range (pointsMap B S hS X.1 (𝟙 X : X ⟶ X).hom))ᶜ = ∅ := by
    rw [hid, Set.range_id, Set.compl_univ, Set.inter_empty]
  obtain ⟨-, ⟨G', -, hG'c, hG'g, -⟩, -⟩ := lemma_A_9_unconditional X hqc hZ hqs Set.univ hcl hco
  refine ⟨_, _, R, ?_, ?_, hWA _ ?_ ?_, hWA _ ?_ ?_, G', hG'c, hG'g⟩
  · rw [h₁]; exact isClosed_univ
  · rw [h₂]; exact isClosed_empty
  · rw [h₁]; exact isClosed_univ
  · rw [h₁, Set.compl_univ]; exact isCompact_empty
  · rw [h₂]; exact isClosed_empty
  · rw [h₂, Set.compl_empty]; exact isCompact_univ

/-- **Non-vacuity, an instance**: at `X = h_{T₀}` with `T₀` affine (`hX`, satisfied by `rfl`),
`X` is quasi-compact and quasi-separated, so `theorem_1_1_dqcZ_nonVacuity_unconditional` applies;
such `T₀` exist over `Spec ℤ` (`corollary_1_2_int_witness_unconditional`). -/
theorem theorem_1_1_dqcZ_nonVacuity_affine_unconditional
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (X : AlgebraicSpaces B S hS) (hX : X = Supported.representedSpace T₀) :
    ∃ (T₁ T₂ : Set (points B S hS X.1))
      (_ : Recollement (DqcZ X T₁) (DqcZ X Set.univ) (DqcZ X T₂)),
      IsClosed T₁ ∧ IsClosed T₂ ∧
      SumUniverse.SatisfiesPaperWA.{u} (DqcZ X T₁) ∧
      SumUniverse.SatisfiesPaperWA.{u} (DqcZ X T₂) ∧
      ∃ G' : DqcZ X Set.univ, IsCompactObject.{u} G' ∧ IsPaperGenerator G' := by
  obtain ⟨hqc, hqs, -, -⟩ :=
    nonVacuity_affine_univ (affineQuasiSeparatedYoneda B S hS) (containsTerminal B) T₀ hT₀
  rw [← hX] at hqc hqs
  exact theorem_1_1_dqcZ_nonVacuity_unconditional (containsTerminal B) X hqc hqs

end RelativeFM.SpacesVerified

#print axioms RelativeFM.SpacesVerified.locallySmall_D
#print axioms RelativeFM.SpacesVerified.locallySmall_dqcZ_unconditional
#print axioms RelativeFM.SpacesVerified.locallySmall_qcohDerived
#print axioms RelativeFM.SpacesVerified.theorem_1_1_dqcZ_unconditional
#print axioms RelativeFM.SpacesVerified.theorem_1_1_dqcZ_nonVacuity_unconditional
#print axioms RelativeFM.SpacesVerified.theorem_1_1_dqcZ_nonVacuity_affine_unconditional
