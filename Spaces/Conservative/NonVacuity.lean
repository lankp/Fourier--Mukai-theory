/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Conservative.Flat
import Spaces.Conservative.QuasiAffine
import Spaces.LP26.Corollary12
import Spaces.NonVacuity
import Spaces.Statements.NonVacuity

/-!
# Non-vacuity of GL26 Lemmas 2.14, 2.15, 2.18 and 3.2 over algebraic spaces

CLAUDE.md, verification step 5: the hypotheses of `lemma_2_14`, `lemma_2_14_isIso`,
`lemma_2_15`, `lemma_2_15_homology` (`Spaces/Conservative/Flat.lean`), `lemma_2_18` and
`lemma_3_2_of_factorization` (`Spaces/Conservative/QuasiAffine.lean`) are satisfiable, for every
algebraic space `X` (for instance the base `baseSpace B S hS`, `Spaces.NonVacuity`):

* `nonVacuity_faithfullyFlat`: `𝟙 X` is flat and surjective (flat: smooth by AxiomMath's
  `isSmooth_id`, and `FlatOfSmoothInput`; surjective: `|𝟙 X| = id`), and `0 ∈ D_qc(X)`; so the
  hypotheses of Lemmas 2.14 and 2.15 hold, and `nonVacuity_lemma_2_15` exhibits the smooth
  surjective cover of condition (3);
* `nonVacuity_lemma_2_18`: `g = f = h = 𝟙 X`; `𝟙 X` is quasi-affine
  (`Statements.isQuasiAffineHom_id`) and so is the diagonal of `𝟙 X`, an isomorphism
  (`isQuasiAffineHom_of_isIso`, by base change of `𝟙` along an isomorphism, Stacks 03WO);
* `nonVacuity_lemma_3_2`: `j = p = 𝟙 X`; the identity is an open immersion
  (`LP26.isOpenImmersion_of_isIso'`), quasi-compact (`LP26.isQuasiCompact_of_isIso'`) and affine
  (AxiomMath's `isAffineHom_id`), and `0 ∈ D_qc(X)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space
open ZeroObject

namespace RelativeFM.Spaces.Conservative

open RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The identity of an algebraic space is surjective. -/
theorem isSurjective_id (X : AlgebraicSpaces B S hS) :
    IsSurjective B S hS (𝟙 X : X ⟶ X).hom := by
  change Function.Surjective (pointsMap B S hS X.1 (𝟙 X.1))
  rw [pointsMap_id]
  exact Function.surjective_id

/-- **Non-vacuity of Lemmas 2.14 and 2.15**: `𝟙 X` is faithfully flat (flat and surjective),
and `D_qc(X)` contains the zero object. -/
theorem nonVacuity_faithfullyFlat (hsm : FlatOfSmoothInput B S hS) (X : AlgebraicSpaces B S hS) :
    Statements.IsFlatHom (𝟙 X) ∧ IsSurjective B S hS (𝟙 X : X ⟶ X).hom ∧
      Dqc X (0 : D B S hS X) :=
  ⟨hsm _ (isSmooth_id B S hS X.2), isSurjective_id X, Dqc_of_isZero (isZero_zero _)⟩

/-- **Non-vacuity of condition (3) of Lemma 2.15**: `𝟙 X` is smooth and surjective. -/
theorem nonVacuity_lemma_2_15 (X : AlgebraicSpaces B S hS) :
    IsSmooth B S hS (𝟙 X : X ⟶ X).hom ∧ IsSurjective B S hS (𝟙 X : X ⟶ X).hom :=
  ⟨isSmooth_id B S hS X.2, isSurjective_id X⟩

/-- An isomorphism of algebraic spaces is quasi-affine: it is the base change of `𝟙` along an
isomorphism (Stacks 03WO, AxiomMath's `IsQuasiAffineHom.of_isPullback`). -/
theorem isQuasiAffineHom_of_isIso {X Y : AlgebraicSpaces B S hS} (e : X ⟶ Y) [IsIso e] :
    Statements.IsQuasiAffineHom e := by
  have : IsIso e.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map e))
  have sq : IsPullback e.hom e.hom (𝟙 Y.1) (𝟙 Y.1) := IsPullback.of_horiz_isIso ⟨rfl⟩
  exact IsQuasiAffineHom.of_isPullback sq (Statements.isQuasiAffineHom_id Y)

/-- **Non-vacuity of Lemma 2.18**: `g = f = h = 𝟙 X` satisfy its hypotheses. -/
theorem nonVacuity_lemma_2_18 (X : AlgebraicSpaces B S hS) :
    (𝟙 X ≫ 𝟙 X = 𝟙 X) ∧ Statements.IsQuasiAffineHom (𝟙 X) ∧
      Statements.IsQuasiAffineHom (pullback.diagonal (𝟙 X)) :=
  ⟨Category.id_comp _, Statements.isQuasiAffineHom_id X, isQuasiAffineHom_of_isIso _⟩

/-- **Non-vacuity of `lemma_3_2_of_factorization`**: `j = p = 𝟙 X` is a quasi-compact open
immersion followed by an affine morphism, and `D_qc(X)` contains the zero object. -/
theorem nonVacuity_lemma_3_2 (X : AlgebraicSpaces B S hS) :
    IsOpenImmersion B S hS (𝟙 X : X ⟶ X).hom ∧ IsQuasiCompact B S hS (𝟙 X : X ⟶ X).hom ∧
      IsAffineHom B S hS (𝟙 X : X ⟶ X).hom ∧ Dqc X (0 : D B S hS X) := by
  have : IsIso (𝟙 X : X ⟶ X).hom := (inferInstance : IsIso (𝟙 X.1))
  exact ⟨LP26.isOpenImmersion_of_isIso' _, LP26.isQuasiCompact_of_isIso' _, isAffineHom_id X.1,
    Dqc_of_isZero (isZero_zero _)⟩

/-- The base `S` is an algebraic space to which all of the above applies. -/
example (hsm : FlatOfSmoothInput B S hS) :
    Statements.IsFlatHom (𝟙 (baseSpace B S hS)) ∧
      Statements.IsQuasiAffineHom (pullback.diagonal (𝟙 (baseSpace B S hS))) :=
  ⟨(nonVacuity_faithfullyFlat hsm _).1, (nonVacuity_lemma_2_18 _).2.2⟩

end RelativeFM.Spaces.Conservative
