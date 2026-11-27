/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces
import SpacesVerified.Discharge
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionAgree
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso

/-!
# Discharge of the tagged inputs for base change; GL26 Lemmas 6.11 and 10.1 over spaces

The three tagged AxiomMath inputs of `Spaces/BaseChange/Inputs.lean` are proved here by the
AxiomMath/Stacks declarations they name (commit `f56a316`).

| input | Stacks | proved by |
|---|---|---|
| `CompIsoAgreeInput` | 0D6D | `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_eq` |
| `FlatBaseChangeInput` | 0A1K, 08IR | `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isFlat` |
| `Tag08INInput` | 08IN | `AlgebraicGeometry.Space.isIso_smallEtaleProjectionFormulaMap` |

Consequences, with the inputs of `Spaces/AxiomMathInputs.lean` proved in
`SpacesVerified/Discharge.lean`:

* **GL26 Lemma 6.11** (`lem:fm_cube_flat_base_change_natural_isomorphism`) over algebraic spaces,
  unconditional: `lemma_6_11_unconditional` (`Spaces.BaseChange.lemma_6_11_of_isFlat`).
* **GL26 Lemma 10.1** (`lem:fm_cube_pullback_natural_isomorphism`) over algebraic spaces:
  `lemma_10_1_of_flatBaseChange` (`Spaces.BaseChange.lemma_10_1_of`), with the tagged inputs
  (08IN, 08F4) proved.  **Not unconditional**: it keeps the hypothesis `h`, flat base change on
  `D_qc` for the face `Y₁₂T = Y₁₂ ×_{Y₁} Y₁T` (Stacks 08IR for a flat *pulled* morphism), which is
  an open item of `Spaces/BaseChange/Cube.lean` (module docstring there: AxiomMath states it
  through `TorIndependent`, outside the `Spaces` import list), not a tagged input.

The differences from the paper are those recorded in `Spaces/BaseChange/Cube.lean`
(objectwise on `D_qc`; flatness and quasi-compactness of the individual morphisms the proofs use
in place of Setup 2.20's hypotheses).  The instance context is that of
`Spaces/BaseChange/Inputs.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space
  RelativeFM.FMCube

namespace RelativeFM.SpacesVerified

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open RelativeFM.Spaces.BaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0D6D, the two spellings agree**, proved. -/
theorem compIsoAgree : CompIsoAgreeInput B S hS := fun f g =>
  smallEtaleDerivedModulePullbackCompIso_eq B S hS f g

/-- **Stacks 0A1K / 08IR** (flat base change, pushed morphism flat), proved. -/
theorem flatBaseChange : FlatBaseChangeInput B S hS := fun sq hfqc hfqs hfl E hE =>
  isIso_smallEtaleDerivedBaseChangeMap_of_isFlat sq hfqc hfqs hfl E hE

/-- **Stacks 08IN** (the projection formula), proved. -/
theorem tag08IN : Tag08INInput B S hS := fun f hfqc hfqs E hE K hK =>
  isIso_smallEtaleProjectionFormulaMap B S hS f hfqc hfqs E hE K hK

variable {B S hS}

/-- **GL26 Lemma 6.11** (`lem:fm_cube_flat_base_change_natural_isomorphism`) for algebraic spaces,
unconditional: in a cube of algebraic spaces (Setup 2.20, `FMCube`) with
`f'₁ : Y₁ ×_S Y₂ ⟶ Y₂` flat, quasi-compact and quasi-separated, for `K ∈ D_qc(Y₁ ×_S Y₂)` the
natural transformation `α^K : L t₂^* ∘ Φ_K ⟶ Φ_{L(t')^*K} ∘ L t₁^*` is invertible at every object
of `D_qc(Y₁)`.  `Spaces.BaseChange.lemma_6_11_of_isFlat` with its tagged inputs (0A1K/08IR, 0D6D,
08F4, 08F5) proved. -/
theorem lemma_6_11_unconditional (C : FMCube (AlgebraicSpaces B S hS))
    (hfl : IsFlat B S hS C.f'₁.hom) (hqc : IsQuasiCompact B S hS C.f'₁.hom)
    (hqs : IsQuasiSeparated B S hS C.f'₁.hom) {K : Spaces.D B S hS C.Y₁₂}
    (hK : Spaces.Dqc C.Y₁₂ K) :
    ∀ E : Spaces.D B S hS C.Y₁, Spaces.Dqc C.Y₁ E →
      IsIso ((C.alpha (tensorPullPushData B S hS) K).app E) :=
  lemma_6_11_of_isFlat C (flatBaseChange B S hS) (compIsoAgree B S hS) (tag08F4 B S hS)
    (tag08F5 B S hS) hfl hqc hqs hK

/-- **GL26 Lemma 10.1** (`lem:fm_cube_pullback_natural_isomorphism`) for algebraic spaces, with
every tagged input proved (08IN, 08F4): for `t'` quasi-compact and quasi-separated and
`K ∈ D_qc(Y₁ ×_S Y₂)`, `β^K : Φ_K ∘ R(t₁)_* ⟶ R(t₂)_* ∘ Φ_{L(t')^*K}` is invertible at every
object of `D_qc(Y₁ ×_S T)`, **given** flat base change on `D_qc` for the face
`Y₁₂T = Y₁₂ ×_{Y₁} Y₁T` (hypothesis `h`; an open item, see the module docstring).
`Spaces.BaseChange.lemma_10_1_of` with its tagged inputs proved. -/
theorem lemma_10_1_of_flatBaseChange (C : FMCube (AlgebraicSpaces B S hS))
    (h : ∀ E : Spaces.D B S hS C.Y₁T, Spaces.Dqc C.Y₁T E →
      IsIso (((tensorPullPushData B S hS).theta C.sq₁).app E))
    (hqc : IsQuasiCompact B S hS C.t'.hom) (hqs : IsQuasiSeparated B S hS C.t'.hom)
    {K : Spaces.D B S hS C.Y₁₂} (hK : Spaces.Dqc C.Y₁₂ K) :
    ∀ E : Spaces.D B S hS C.Y₁T, Spaces.Dqc C.Y₁T E →
      IsIso ((C.beta (tensorPullPushData B S hS) K).app E) :=
  lemma_10_1_of C h (tag08IN B S hS) (tag08F4 B S hS) hqc hqs hK

/-- Non-vacuity of Lemma 6.11, unconditional: the identity cube on any algebraic space, at a zero
kernel (`Spaces.BaseChange.lemma_6_11_id` with 08F4, 08F5 proved). -/
theorem lemma_6_11_id_unconditional (X : AlgebraicSpaces B S hS) :
    ∀ E : Spaces.D B S hS X, Spaces.Dqc X E → IsIso (((constFMCube (AlgebraicSpaces B S hS) X).alpha
      (tensorPullPushData B S hS) (zeroObj X)).app E) :=
  lemma_6_11_id X (tag08F4 B S hS) (tag08F5 B S hS)

/-- Non-vacuity of Lemma 10.1, unconditional: the identity cube on any algebraic space, at a zero
kernel (`Spaces.BaseChange.lemma_10_1_id` with 08F4 proved). -/
theorem lemma_10_1_id_unconditional (X : AlgebraicSpaces B S hS) :
    ∀ E : Spaces.D B S hS X, Spaces.Dqc X E → IsIso (((constFMCube (AlgebraicSpaces B S hS) X).beta
      (tensorPullPushData B S hS) (zeroObj X)).app E) :=
  lemma_10_1_id X (tag08F4 B S hS)

end RelativeFM.SpacesVerified

#print axioms RelativeFM.SpacesVerified.compIsoAgree
#print axioms RelativeFM.SpacesVerified.flatBaseChange
#print axioms RelativeFM.SpacesVerified.tag08IN
#print axioms RelativeFM.SpacesVerified.lemma_6_11_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_10_1_of_flatBaseChange
#print axioms RelativeFM.SpacesVerified.lemma_6_11_id_unconditional
#print axioms RelativeFM.SpacesVerified.lemma_10_1_id_unconditional
