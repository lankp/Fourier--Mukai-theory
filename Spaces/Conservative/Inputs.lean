/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.LP26.OpenPushforward
import Spaces.LP26.Recollement
import Spaces.Statements.Notions

/-!
# Tagged AxiomMath inputs for GL26 §2–3 conservativity

The AxiomMath/Stacks theorems that `Spaces/Conservative/Flat.lean` (GL26 Lemmas 2.14
`lem:faithfully_flat_is_conservative` and 2.15 `lem:zero_object_via_covers`) and
`Spaces/Conservative/QuasiAffine.lean` (GL26 Lemmas 2.18 `lem:quasi-affine_via_diagonal` and
3.2 `lem:quasi-affine_is_conservative`) use.  Each is a `Prop` whose statement is AxiomMath's
verbatim, with the conventions of `Spaces/AxiomMathInputs.lean` (CLAUDE.md rule 2,
`results/STACKS_POLICY.md`): the AxiomMath modules below are theorem modules outside
`scripts/axiommath/spaces-imports.txt`, and `SpacesVerified` discharges each input by the
AxiomMath declaration named in its docstring.

| input | Stacks | AxiomMath declaration | AxiomMath file |
|---|---|---|---|
| `FlatPullbackExactInput` | 05VQ, 03LU | `AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat_hom` | `Spaces/ModulePullbackFlatExact.lean` |
| `FlatPullbackSupportInput` | 07TZ (3), 03MK | `AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq_of_isFlat` | `Spaces/ModulePullbackFlatReflection.lean` |
| `FlatOfSmoothInput` | 04TA | `AlgebraicGeometry.Space.isFlat_of_isSmooth` | `Spaces/SmoothFlat.lean` |
| `QuasiAffineCompInput` | 03WN | `AlgebraicGeometry.Space.IsQuasiAffineHom.comp` | `Spaces/QuasiAffineComposition.lean` |
| `AffinePushforwardConservativeInput` | — (GL26 cites 0E4R) | `AlgebraicGeometry.Space.isZero_of_isZero_derivedModulePushforward_of_isAffineHom` | `Spaces/QuasicoherentDerivedPushforwardAffineConservative.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, AxiomMath commit `f56a316`; "—": the
AxiomMath declaration carries no Stacks tag.)

Also used, from earlier waves: `Spaces.Tag06UQInput` and `Spaces.Tag08FAInput`
(`Spaces/AxiomMathInputs.lean`), `LP26.OpenImmersionCounitInput` and `LP26.SupportEmptyInput`
(Stacks 04K5, `Spaces/LP26/Inputs.lean`).

Not inputs, because the import closure provides them: AxiomMath's `IsQuasiAffineHom` (03WL),
its stability under base change `IsQuasiAffineHom.of_isPullback` (03WO), `isSmooth_id`,
`pointsMap_id`, `isAffineHom_id`, the triangulated structure of `Lf^*`,
and `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` (0D6E, `smallEtaleDerivedPushforwardCompIso`).

## Spelling

* AxiomMath's abbreviation `QcohDerived B S hS W` (`Spaces/QuasicoherentDerivedPushforward.lean`,
  outside the import list) is written out by its body
  `DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} …)`,
  and AxiomMath's abbreviation `derivedModulePushforward B S hS g`
  (`Spaces/QuasicoherentDerivedDirectImage.lean`, outside the import list) by its body
  `derivedPushforward (smallEtaleRingedToposHom B S hS g)`, as in `Spaces.Tag08FAInput`.
* The section variables `B S hS` of the AxiomMath files are bound by the `variable` line below;
  the morphism and object variables are bound in each statement, in AxiomMath's order.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Conservative

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inverse image of modules along a flat morphism of algebraic spaces is left exact**
(Stacks 05VQ, 03LU).  AxiomMath:
`AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS g hg`
(`Spaces/ModulePullbackFlatExact.lean`), verbatim. -/
def FlatPullbackExactInput : Prop :=
  ∀ {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X) (_hg : IsFlat B S hS g.hom),
    PreservesFiniteLimits (modulePullback B S hS g)

/-- **The support of a flat pullback of a quasi-coherent module is the inverse image of the
support** (Stacks 07TZ (3) with flatness in place of finite type, 03MK).  AxiomMath:
`AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq_of_isFlat B S hS g hg F hqc`
(`Spaces/ModulePullbackFlatReflection.lean`), verbatim. -/
def FlatPullbackSupportInput : Prop :=
  ∀ {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X) (_hg : IsFlat B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (_hqc : F.IsQuasicoherentOnSite),
    supportOfSheaf B S hS X'.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj F)) =
      pointsMap B S hS X'.1 g.hom ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)

/-- **A smooth morphism of algebraic spaces is flat** (Stacks 04TA).  AxiomMath:
`AlgebraicGeometry.Space.isFlat_of_isSmooth B S hS f hf` (`Spaces/SmoothFlat.lean`),
verbatim. -/
def FlatOfSmoothInput : Prop :=
  ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (_hf : IsSmooth B S hS f),
    IsFlat B S hS f

/-- **Stacks 03WN**: a composite of quasi-affine morphisms of algebraic spaces is quasi-affine.
AxiomMath: `AlgebraicGeometry.Space.IsQuasiAffineHom.comp hX hY hZ hf hg`
(`Spaces/QuasiAffineComposition.lean`), verbatim. -/
def QuasiAffineCompInput : Prop :=
  ∀ {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hX : IsAlgebraicSpace B S hS X)
    (_hY : IsAlgebraicSpace B S hS Y) (_hZ : IsAlgebraicSpace B S hS Z) {f : X ⟶ Y} {g : Y ⟶ Z}
    (_hf : IsQuasiAffineHom B S hS f) (_hg : IsQuasiAffineHom B S hS g),
    IsQuasiAffineHom B S hS (f ≫ g)

/-- **The derived direct image along an affine morphism of algebraic spaces is conservative on
`D_QCoh`** (GL26 cites Stacks 0E4R; the AxiomMath declaration carries no tag).  AxiomMath:
`AlgebraicGeometry.Space.isZero_of_isZero_derivedModulePushforward_of_isAffineHom B S hS g hg E hE h`
(`Spaces/QuasicoherentDerivedPushforwardAffineConservative.lean`), verbatim, with `QcohDerived`
and `derivedModulePushforward` written out by their bodies (see "Spelling"). -/
def AffinePushforwardConservativeInput : Prop :=
  ∀ {W Y : AlgebraicSpaces B S hS} (g : W ⟶ Y) (_hg : IsAffineHom B S hS g.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (_hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))) E)
    (_h : IsZero ((Stacks.Cohomology.DerivedPushforward.derivedPushforward
      (X := smallEtaleRingedTopos B S hS W) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS g)).obj E)),
    IsZero E

end RelativeFM.Spaces.Conservative
