/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Categories
import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# The affine algebraic space `Spec R` and the functor `Φ : D(R) ⥤ D(𝒪_{Spec R})`

Lank–Pauwels, *Gluing weak approximability along recollements* (LP26), Corollary 1.2
(`cor:weak_approx_spaces`), affine base case: the setting.

Let `U` be an object of the big fppf site over `S` whose underlying scheme `X_U` is affine,
with ring of global functions `R = Γ(X_U, 𝒪)`, and let `h_U = yoneda.obj U` be the algebraic
space it represents (the algebraic space `Spec R` of LP26 and GL26 §2.2).  Every affine scheme
of the site over `S` is of this form, so this is LP26's affine base case in AxiomMath's model.

This file only makes definitions; nothing is assumed.

## Main definitions

* `RelativeFM.Spaces.Affine.space U`: the algebraic space `h_U`.
* `RelativeFM.Spaces.Affine.associated U`: the associated-module functor
  `Mod(R) ⥤ Mod(𝒪_{h_U})`, `M ↦ M^~`, pulled back along `X_U ≅ Spec R`, made a module on the
  small étale site of `X_U` (Stacks 03DU (4)) and transported to the small étale site of `h_U`.
  It is, verbatim, the body of AxiomMath's
  `AlgebraicGeometry.Space.representedAffineAssociated`
  (`StacksFrontier/AlgebraicGeometry/Spaces/AffineQuasicoherentDerivedEquivalence.lean`), with
  AxiomMath's `representedSmallEtaleModuleEquivalence B S hS U` written out by its body
  `Stacks.SheafOfModules.reindexEquivalence (representedSmallEtaleEquivalence B S hS U)
  (representedSchemeStructureSheaf B S hS U)` and `representedSchemeStructureSheaf` by its body
  (`Spaces/RepresentedQuasicoherent.lean`, outside the `Spaces` import list).  The continuity
  instances of the site equivalence come from `Spaces/RepresentedModuleComparison.lean`; they
  are propositions, so the functor is AxiomMath's.
* `RelativeFM.Spaces.Affine.zeroLocusPoints U I`: for an ideal `I ⊆ R`, the set
  `|V(I)| ⊆ |h_U|` of points whose image in `Spec R` (under `|h_U| ≃ₜ X_U ≅ Spec R`,
  Stacks 03BX) lies in `V(I)`.

## The exactness instances

`associated U` is left adjoint to the sections functor `sections U` (`associatedAdjunction`, the
composite of four adjunctions, as AxiomMath's `representedAffineAssociatedAdjunction`), hence
additive and preserving finite colimits; both are proved here.  That it preserves finite limits (flatness of the étale structure sheaf
over the Zariski one) is the tagged input `Tag06Z0ExactInput` of `Spaces/Affine/Inputs.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Affine

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The algebraic space `h_U = yoneda.obj U` represented by an object `U` of the big fppf site
over `S` (Stacks 025Z). -/
abbrev space (U : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩

/-- **The associated-module functor** `Mod(R) ⥤ Mod(𝒪_{h_U})`, `R = Γ(U, 𝒪)`: the body of
AxiomMath's `AlgebraicGeometry.Space.representedAffineAssociated B S hS U`, written out (see
the module docstring). -/
def associated (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⥤
      Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⋙
    Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ⋙
    _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    (Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B S hS (yoneda.obj U))
      (J := _root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      (representedSmallEtaleEquivalence B S hS U)
      (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).functor

/-- The sections functor `Mod(𝒪_{h_U}) ⥤ Mod(R)`, right adjoint of `associated U` (the body
of AxiomMath's `representedAffineSections`). -/
def sections (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] :
    Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
      ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  (Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B S hS (yoneda.obj U))
        (J := _root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (representedSmallEtaleEquivalence B S hS U)
        (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ⋙
    moduleSpecΓFunctor

/-- The associated-module functor is left adjoint to the sections functor: the composite of the
adjunctions `M ↦ M^~ ⊣ Γ` (Mathlib), `f^* ⊣ f_*` (Mathlib), Stacks 03DU (4) (AxiomMath's
`associatedModuleAdjunction`) and the equivalence of sites (as AxiomMath's
`representedAffineAssociatedAdjunction`). -/
def associatedAdjunction (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] :
    associated U ⊣ sections U :=
  (tilde.adjunction).comp ((Scheme.Modules.pullbackPushforwardAdjunction _).comp
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction _ _ _).comp
      (Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B S hS (yoneda.obj U))
        (J := _root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (representedSmallEtaleEquivalence B S hS U)
        (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).toAdjunction))

/-- The sections functor is additive, being a right adjoint. -/
instance additive_sections (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] : (sections U).Additive :=
  have := (associatedAdjunction U).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- The associated-module functor is additive, being a left adjoint. -/
instance additive_associated (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] : (associated U).Additive :=
  (associatedAdjunction U).left_adjoint_additive

/-- The associated-module functor preserves finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_associated (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] :
    PreservesFiniteColimits (associated U) :=
  have := (associatedAdjunction U).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- **`|V(I)| ⊆ |h_U|`**: the points of the algebraic space `h_U` whose image in
`Spec R`, under the homeomorphism `|h_U| ≃ₜ X_U` (Stacks 03BX, AxiomMath's
`schemePointsHomeomorph`) followed by `X_U ≅ Spec R`, lies in the zero locus of `I`. -/
def zeroLocusPoints (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    Set (points B S hS (yoneda.obj U)) :=
  {p | ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom (schemePointsHomeomorph B S hS U p) ∈
    PrimeSpectrum.zeroLocus (I : Set Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))}

end RelativeFM.Spaces.Affine
