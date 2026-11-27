/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Affine.Basic

/-!
# Tagged AxiomMath inputs of the affine base case

CLAUDE.md rule 2 and `results/STACKS_POLICY.md`, with the conventions of
`Spaces/AxiomMathInputs.lean`: an AxiomMath *theorem* outside the `Spaces` import list
(`scripts/axiommath/spaces-imports.txt`) is used through a `Prop` below whose statement is the
AxiomMath statement verbatim (same binders, same hypotheses, same conclusion; a definition of
an AxiomMath module outside the import list is written out by its body, which is said in the
docstring), and which `SpacesVerified` discharges by the AxiomMath declaration it names.  A
result that takes one of these as a hypothesis is conditional on it until then.

| input | Stacks | AxiomMath declaration | AxiomMath file |
|---|---|---|---|
| `Tag06Z0ExactInput` | 06Z0 (exactness of `M ↦ M^~`) | `AlgebraicGeometry.Space.preservesFiniteLimits_representedAffineAssociated` | `Spaces/AffineQuasicoherentDerivedEquivalence.lean` |
| `Tag06Z0QcohInput` | 06Z0 / 03DX (2) (`M^~` is quasi-coherent) | `AlgebraicGeometry.Space.isQuasicoherentOnSite_representedAffineAssociated_obj` | `Spaces/AffineQuasicoherentDerivedEquivalence.lean` |
| `Tag06Z0Input` | 06Z0 (`D(R) ≃ D_QCoh(𝒪_{Spec R})`) | `AlgebraicGeometry.Space.isEquivalence_representedAffineDerivedAssociatedQcoh` | `Spaces/AffineQuasicoherentDerivedEquivalence.lean` |
| `Tag07TYInput` | 04KA, 07TY (support of an associated module) | `AlgebraicGeometry.Space.mem_supportOfSheaf_representedAssociatedModule_iff` | `Spaces/RepresentedAssociatedModuleSupport.lean` |
| `Tag021RInput` | 021R, 000J (big fppf sites exist) | `AlgebraicGeometry.BigFppfSite.exists_contains` | `Topologies/Fppf/ContainingSet.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, AxiomMath commit `f56a316`.)

How the AxiomMath abbreviations are written out:

* `representedAffineAssociated B S hS U` is `RelativeFM.Spaces.Affine.associated U`
  (`Spaces/Affine/Basic.lean`), its body;
* `representedAffineDerivedAssociated B S hS U` is its body
  `(representedAffineAssociated B S hS U).mapDerivedCategory`, so
  `(associated U).mapDerivedCategory`; the exactness instances it needs are AxiomMath's
  `additive_…`, `preservesFiniteColimits_…`, `preservesFiniteLimits_representedAffineAssociated`,
  here `additive_associated`, `preservesFiniteColimits_associated` (`Spaces/Affine/Basic.lean`,
  proved) and an instance binder for `PreservesFiniteLimits` (all three are propositions, so
  the functor is AxiomMath's whichever proofs are used);
* `representedAffineDerivedAssociatedQcoh B S hS U` is its body
  `ObjectProperty.lift _ (representedAffineDerivedAssociated B S hS U)
  (qcohDerived_representedAffineDerivedAssociated_obj B S hS U)`; the proof argument
  `qcohDerived_…` (an AxiomMath theorem) is a binder `h` of `Tag06Z0Input` (proof
  irrelevance makes the lift independent of it), and the property `_` is
  `QcohDerived B S hS ⟨yoneda.obj U, _⟩`, written out as `Dqc (space U)`
  (`Spaces/Categories.lean`, which records `Dqc_fullSubcategory_eq` by `rfl`).

The local instances are AxiomMath's: `HasDerivedCategory.standard` (priority 10000),
`SheafOfModules.instAbelian` (priority 5000), and the two `Stacks.Cohomology.SiteModules`
instances AxiomMath removes in `AffineQuasicoherentDerivedEquivalence.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Affine

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06Z0, exactness of the associated module**: for `U` with affine underlying
scheme, `M ↦ M^~ : Mod(R) ⥤ Mod(𝒪_{h_U})` preserves finite limits.  AxiomMath: the instance
`AlgebraicGeometry.Space.preservesFiniteLimits_representedAffineAssociated B S hS U`
(`Spaces/AffineQuasicoherentDerivedEquivalence.lean`), verbatim, with
`representedAffineAssociated` written out by its body (`associated`). -/
def Tag06Z0ExactInput : Prop :=
  ∀ (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)],
    PreservesFiniteLimits (associated U)

/-- **Stacks 06Z0 / 03DX (2), quasi-coherence of the associated module**: `M^~` is a
quasi-coherent `𝒪_{h_U}`-module.  AxiomMath:
`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U M`
(`Spaces/AffineQuasicoherentDerivedEquivalence.lean`), verbatim, with
`representedAffineAssociated` written out by its body (`associated`). -/
def Tag06Z0QcohInput : Prop :=
  ∀ (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)),
    ((associated U).obj M).IsQuasicoherentOnSite

/-- **Stacks 06Z0 for the affine algebraic space `h_U = Spec R`**: the derived associated-module
functor `Φ : D(R) ⥤ D_QCoh(𝒪_{h_U})` is an equivalence.  AxiomMath: the instance
`AlgebraicGeometry.Space.isEquivalence_representedAffineDerivedAssociatedQcoh B S hS U`
(`Spaces/AffineQuasicoherentDerivedEquivalence.lean`), verbatim, with
`representedAffineDerivedAssociatedQcoh` written out by its body (see the module docstring:
the AxiomMath proofs inside the body, of `PreservesFiniteLimits` and of the lift condition,
are binders). -/
def Tag06Z0Input : Prop :=
  ∀ (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [PreservesFiniteLimits (associated U)]
    (h : ∀ M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)),
      Dqc (space U) ((associated U).mapDerivedCategory.obj M)),
    (ObjectProperty.lift (Dqc (space U)) (associated U).mapDerivedCategory h).IsEquivalence

/-- **Stacks 04KA and 07TY for the module associated to a quasi-coherent module on a
represented space**: a point `p` of `h_U` lies in the support of `ε^* G₀` exactly when the
stalk of `G₀` at the corresponding point of the scheme underlying `U` is nonzero.  AxiomMath:
`AlgebraicGeometry.Space.mem_supportOfSheaf_representedAssociatedModule_iff`
(`Spaces/RepresentedAssociatedModuleSupport.lean`), verbatim; every definition it mentions is
in the import list. -/
def Tag07TYInput : Prop :=
  ∀ (U : BigFppfOver B S hS) (G₀ : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (_hG₀ : G₀.IsQuasicoherent) (p : points B S hS (yoneda.obj U)),
    p ∈ supportOfSheaf B S hS (yoneda.obj U)
        ((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O)).obj
          ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj G₀)) ↔
      ¬ IsZero (TopCat.Presheaf.stalk (X := (BigFppfOver.toScheme B S hS).obj U)
          G₀.val.presheaf (schemePointsHomeomorph B S hS U p))

/-- **Stacks 021R (with the size cutoff of 000J)**: every scheme lies in some big fppf site.
AxiomMath: `AlgebraicGeometry.BigFppfSite.exists_contains`
(`Topologies/Fppf/ContainingSet.lean`), verbatim.  Used only for the non-vacuity witness. -/
def Tag021RInput : Prop :=
  ∀ (X : Scheme.{u}), ∃ B : BigFppfSite.{u}, B.Contains X

end RelativeFM.Spaces.Affine
