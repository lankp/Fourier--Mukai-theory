/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Spaces
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine

/-!
# Discharge of the tagged inputs of `Spaces/Statements/`

The five tagged AxiomMath inputs of `Spaces/Statements/Inputs.lean`, used only to show that
the hypotheses of GL26's headline statements (`Spaces/Statements/Main.lean`) can all hold,
are proved here by the AxiomMath theorems they name (commit `f56a316`).  Consequently
`setup_hypotheses_satisfiable_unconditional`: for an affine locally Noetherian base `S`,
every hypothesis of those statements holds at once (identity maps, `K = 0`), with nothing
assumed.

| input | proved by |
|---|---|
| `Tag06LTInput` (Stacks 06LT) | `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isEtale'` |
| `IsQuasiCompactOfIsIsoInput` | `AlgebraicGeometry.Space.isQuasiCompact_of_isIso` |
| `UniversallyClosedOfIsIsoInput` | `AlgebraicGeometry.Space.universallyClosed_of_isIso` |
| `IsFlatIdInput` | `AlgebraicGeometry.Space.isFlat_id` |
| `AffineQuasiSeparatedInput` | `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isAffineSpace` |
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.SpacesVerified

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

open RelativeFM.Spaces.Statements

/-- **Stacks 06LT**, proved: an étale morphism is locally of finite type. -/
theorem tag06LT : Tag06LTInput B S hS := fun f hf =>
  isLocallyOfFiniteType_of_isEtale' B S hS f hf

/-- An isomorphism is quasi-compact, proved. -/
theorem isQuasiCompactOfIsIso : IsQuasiCompactOfIsIsoInput B S hS := fun e _ =>
  isQuasiCompact_of_isIso B S hS e

/-- An isomorphism is universally closed, proved. -/
theorem universallyClosedOfIsIso : UniversallyClosedOfIsIsoInput B S hS := fun e _ =>
  universallyClosed_of_isIso B S hS e

/-- An identity morphism of algebraic spaces is flat, proved. -/
theorem isFlatId : IsFlatIdInput B S hS := fun hX => isFlat_id B S hS hX

/-- An affine algebraic space is quasi-separated, proved (Stacks 03BS(3)). -/
theorem affineQuasiSeparated : AffineQuasiSeparatedInput B S hS := fun hZ _ hV =>
  isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hV

/-- Non-vacuity of the hypotheses of GL26's headline statements over algebraic spaces, with
nothing assumed: `Spaces.Statements.setup_hypotheses_satisfiable` with its five inputs
proved. -/
theorem setup_hypotheses_satisfiable_unconditional (hZ : B.Contains (⊤_ Scheme.{u}))
    [IsAffine S] [IsLocallyNoetherian S] :
    IsNoetherianSpace hZ (Spaces.baseSpace B S hS) ∧ IsProperHom (𝟙 (Spaces.baseSpace B S hS)) ∧
      IsFlatHom (𝟙 (Spaces.baseSpace B S hS)) ∧ IsFiniteTypeHom (𝟙 (Spaces.baseSpace B S hS)) ∧
      IsQuasiAffineHom (𝟙 (Spaces.baseSpace B S hS)) ∧
      ∀ K : Spaces.D B S hS (pullback (𝟙 (Spaces.baseSpace B S hS)) (𝟙 (Spaces.baseSpace B S hS))), IsZero K →
        Spaces.Dqc _ K ∧ Spaces.IsPseudoCoherent _ K ∧ Spaces.DbCoh _ K ∧
          IsRelPerfOverFst (𝟙 (Spaces.baseSpace B S hS)) (𝟙 (Spaces.baseSpace B S hS)) K ∧
          IsRelPerfOverSnd (𝟙 (Spaces.baseSpace B S hS)) (𝟙 (Spaces.baseSpace B S hS)) K :=
  setup_hypotheses_satisfiable B S hS (tag06LT B S hS) (isQuasiCompactOfIsIso B S hS)
    (universallyClosedOfIsIso B S hS) (isFlatId B S hS) (affineQuasiSeparated B S hS) hZ

end RelativeFM.SpacesVerified

#print axioms RelativeFM.SpacesVerified.tag06LT
#print axioms RelativeFM.SpacesVerified.isQuasiCompactOfIsIso
#print axioms RelativeFM.SpacesVerified.universallyClosedOfIsIso
#print axioms RelativeFM.SpacesVerified.isFlatId
#print axioms RelativeFM.SpacesVerified.affineQuasiSeparated
#print axioms RelativeFM.SpacesVerified.setup_hypotheses_satisfiable_unconditional
