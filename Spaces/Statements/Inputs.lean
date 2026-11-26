/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Statements.Notions

/-!
# Tagged AxiomMath inputs for the non-vacuity of the statements

CLAUDE.md rule 2, with the conventions of `Spaces/AxiomMathInputs.lean`: an AxiomMath theorem
outside the `Spaces` import list is used through a `Prop` whose statement is the AxiomMath
statement verbatim (a definition of a module outside the import list is written out by its
body, which is said), discharged by the orchestrator in `SpacesVerified` by the declaration it
names.

These inputs are used **only** in `Spaces/Statements/NonVacuity.lean`, to show that the
hypotheses of the statements of `Spaces/Statements/Main.lean` (Noetherian base, proper flat
structure morphisms) can be met; no statement depends on them.  All five AxiomMath modules lie
in the import closure of `SpacesVerified` as merged (checked with
`scripts/axiommath/closure.py`: no new AxiomMath module is needed to discharge them).

| input | Stacks | AxiomMath declaration | AxiomMath file |
|---|---|---|---|
| `Tag06LTInput` | 06LT | `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isEtale'` | `Spaces/FiniteTypePermanence.lean` |
| `IsQuasiCompactOfIsIsoInput` | — | `AlgebraicGeometry.Space.isQuasiCompact_of_isIso` | `Stacks/QuasiSeparatedDiagonal.lean` |
| `UniversallyClosedOfIsIsoInput` | — | `AlgebraicGeometry.Space.universallyClosed_of_isIso` | `Spaces/Support/SelfProduct.lean` |
| `IsFlatIdInput` | — | `AlgebraicGeometry.Space.isFlat_id` | `Spaces/IdentityMorphismProperties.lean` |
| `AffineQuasiSeparatedInput` | (03JX) | `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isAffineSpace` | `Spaces/FiniteTypeQuasicoherentSubobjectExtensionAffine.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, AxiomMath commit `f56a316`; "—": the
AxiomMath declaration carries no Stacks tag.)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Statements

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06LT**: an étale morphism of presheaves on the big fppf site of `S` is locally of
finite type.  AxiomMath: `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isEtale'`
(`Spaces/FiniteTypePermanence.lean`), verbatim. -/
def Tag06LTInput : Prop :=
  ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (_hf : IsEtale B S hS f),
    IsLocallyOfFiniteType B S hS f

/-- An isomorphism of algebraic spaces over `S` is quasi-compact.  AxiomMath:
`AlgebraicGeometry.Space.isQuasiCompact_of_isIso` (`Stacks/QuasiSeparatedDiagonal.lean`),
verbatim. -/
def IsQuasiCompactOfIsIsoInput : Prop :=
  ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G) [IsIso e], IsQuasiCompact B S hS e

/-- An isomorphism of presheaves on the big fppf site of `S` is universally closed.  AxiomMath:
`AlgebraicGeometry.Space.universallyClosed_of_isIso` (`Spaces/Support/SelfProduct.lean`),
verbatim. -/
def UniversallyClosedOfIsIsoInput : Prop :=
  ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G) [IsIso e],
    UniversallyClosed B S hS e

/-- An identity morphism of algebraic spaces over `S` is flat.  AxiomMath:
`AlgebraicGeometry.Space.isFlat_id` (`Spaces/IdentityMorphismProperties.lean`), verbatim. -/
def IsFlatIdInput : Prop :=
  ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hX : IsAlgebraicSpace B S hS X),
    IsFlat B S hS (𝟙 X)

/-- An affine algebraic space is quasi-separated (in the absolute sense, Stacks 03BS(3); its
proof uses Stacks 03JX).  AxiomMath:
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isAffineSpace`
(`Spaces/FiniteTypeQuasicoherentSubobjectExtensionAffine.lean`), verbatim, with AxiomMath's
abbreviation `IsAffineSpace B S hS V` written out by its body
`∃ T, IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧ Nonempty (V ≅ yoneda.obj T)`
(`Spaces/Affine.lean`, outside the import list). -/
def AffineQuasiSeparatedInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hV : ∃ T : BigFppfOver B S hS,
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧ Nonempty (V ≅ yoneda.obj T)),
    IsAbsolutelyQuasiSeparated B S hS hZ V

end RelativeFM.Spaces.Statements
