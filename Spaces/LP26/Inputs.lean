/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Supported.Inputs

/-!
# Tagged AxiomMath inputs for LP26 §5 (`sec:proof_of_results`)

The AxiomMath/Stacks theorems that `Spaces/LP26/HomVanishing.lean` (LP26 Lemmas 5.5
`lem:compact_ext_vanishing` and 5.6 `lem:perf_vanishing`) and
`Spaces/LP26/OpenPushforward.lean` (LP26 Lemma 5.7 `lem:qcqs_open_pushforward`) use.  Each is a
`Prop` whose statement is AxiomMath's verbatim, with the conventions of
`Spaces/AxiomMathInputs.lean` and `Spaces/Supported/Inputs.lean` (CLAUDE.md rule 2,
`results/STACKS_POLICY.md`): the AxiomMath modules below are theorem modules outside
`scripts/axiommath/spaces-imports.txt`, and `SpacesVerified` discharges each input by the
AxiomMath declaration named in its docstring.

| input | Stacks | AxiomMath declaration | AxiomMath file |
|---|---|---|---|
| `Tag09M8Input` | 09M8 | `AlgebraicGeometry.Space.isCompactObject_iff_isPerfect` | `Spaces/Perfect/PerfectCompactQcqs.lean` |
| `PerfectBoundedAboveInput` | (none in AxiomMath; perfect objects are bounded, cf. 08G8) | `AlgebraicGeometry.Space.exists_isLE_of_isPerfect` | `Spaces/Perfect/DetectingBoundedBelow.lean` |
| `Tag09MBInput` | 09MB (1), half | `AlgebraicGeometry.Space.exists_hom_eq_zero_of_isCompactObject` | `Spaces/Perfect/CompactHomVanishing.lean` |
| `Tag08FBInput` | 08FB | `AlgebraicGeometry.Space.preservesColimit_derivedModulePushforward` | `Spaces/QuasicoherentDerivedPushforwardDirectSums.lean` |
| `Tag08FABoundInput` | 08FA (2) | `AlgebraicGeometry.Space.exists_isLE_derivedModulePushforward_obj` | `Spaces/DualityRightAdjointBoundedBelow.lean` |
| `Tag0AFJInput` | 0AFJ | `AlgebraicGeometry.Space.derivedCategoryB_supportedModules_derivedPushforward` | `Spaces/DerivedPushforwardSupport.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, AxiomMath commit `f56a316`.)

## Spelling

* AxiomMath's abbreviation `QcohDerived B S hS X` (`Spaces/QuasicoherentDerivedPushforward.lean`,
  outside the import list) is written out by its body, `Supported.qcohDerived X`.
* AxiomMath's abbreviation `derivedModulePushforward B S hS f`
  (`Spaces/QuasicoherentDerivedDirectImage.lean`, outside the import list) is written out by its
  body `derivedPushforward (smallEtaleRingedToposHom B S hS f)`, as in `Spaces.Tag08FAInput`;
  it is also the body of `smallEtaleDerivedModulePushforward B S hS f` (`Spaces.push f`).
* AxiomMath's definition `HomVanishingFarLeft X hX K` (`Spaces/Perfect/CompactHomVanishing.lean`)
  is written out by its body in `Tag09MBInput`.
* AxiomMath's definition `supportedModules B S hS X T` (`Spaces/DerivedSupportTriangulated.lean`)
  is written out by its body `fun F ↦ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)
  ⊆ T` in `Tag0AFJInput`.
* AxiomMath writes `B.contains_terminal` for the proof that the site contains `Spec ℤ`; the inputs
  bind it as `hZ : B.Contains (⊤_ Scheme.{u})`, as in `Spaces/Supported/Inputs.lean` (any two
  proofs of a `Prop` are equal, and `ContainsTerminalInput` says the hypothesis always holds).
* The instance context is that of `Spaces/Supported/Inputs.lean` (AxiomMath's, the two
  `Stacks.Cohomology.SiteModules` abelian instances removed).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.LP26

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

open Supported

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 09M8**: for `X` quasi-compact and quasi-separated, an object of `D_QCoh(𝒪_X)` is
compact (`IsCompactObject.{u}`, direct sums indexed by `Type u`) iff it is perfect.  AxiomMath:
`AlgebraicGeometry.Space.isCompactObject_iff_isPerfect X hqc hqs E`
(`Spaces/Perfect/PerfectCompactQcqs.lean`), verbatim, with `B.contains_terminal` bound as `hZ`. -/
def Tag09M8Input : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (_hqc : IsQuasiCompactSpace B S hS X.1)
    (_hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2),
    IsCompactObject.{u} E ↔ (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E.obj

/-- **A perfect object of `D(𝒪_X)` is bounded above** when `X` is quasi-compact (AxiomMath gives
no tag; a perfect complex is locally bounded, cf. Stacks 08G8).  AxiomMath:
`AlgebraicGeometry.Space.exists_isLE_of_isPerfect hX E hE`
(`Spaces/Perfect/DetectingBoundedBelow.lean`), verbatim. -/
def PerfectBoundedAboveInput : Prop :=
  ∀ {X : AlgebraicSpaces B S hS} (_hX : IsQuasiCompactSpace B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (_hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E),
    ∃ m : ℤ, E.IsLE m

/-- **Half of Stacks 09MB (1)**: for `X` quasi-compact and quasi-separated and `K` a compact
object of `D_QCoh(𝒪_X)`, there is `N` such that every morphism from `K` to an object `L` of
`D_QCoh(𝒪_X)` with `L ∈ D^{≤ -N}` is zero.  AxiomMath:
`AlgebraicGeometry.Space.exists_hom_eq_zero_of_isCompactObject X hqc hqs K hK`
(`Spaces/Perfect/CompactHomVanishing.lean`), verbatim, with `HomVanishingFarLeft X.1 X.2 K.obj`
and `QcohDerived` written out and `B.contains_terminal` bound as `hZ`. -/
def Tag09MBInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (_hqc : IsQuasiCompactSpace B S hS X.1)
    (_hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (_hK : IsCompactObject.{u} K),
    ∃ N : ℤ, ∀ L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), qcohDerived X L →
      L.IsLE (-N) → ∀ f : K.obj ⟶ L, f = 0

/-- **Stacks 08FB**: for `f : X ⟶ Y` quasi-compact and quasi-separated, `Rf_*` commutes with
(`Type u`-indexed) direct sums of objects of `D_QCoh(𝒪_X)`, in `D(𝒪_Y)`.  AxiomMath:
`AlgebraicGeometry.Space.preservesColimit_derivedModulePushforward f hfqc hfqs E hE`
(`Spaces/QuasicoherentDerivedPushforwardDirectSums.lean`), verbatim, with `QcohDerived` and
`derivedModulePushforward` written out. -/
def Tag08FBInput : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (_hfqc : IsQuasiCompact B S hS f.hom)
    (_hfqs : IsQuasiSeparated B S hS f.hom) {I : Type u}
    (E : I → DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (_hE : ∀ i, qcohDerived X (E i)),
    PreservesColimit (Discrete.functor E)
      (Stacks.Cohomology.DerivedPushforward.derivedPushforward
        (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f))

/-- **The uniform bound of Stacks 08FA (2)**: for `f : X ⟶ Y` quasi-compact and quasi-separated
with `Y` quasi-compact, there is `N` such that `Rf_*E ∈ D^{≤ c + N}` for every `E ∈ D_QCoh(𝒪_X)`
with `E ∈ D^{≤ c}`.  AxiomMath:
`AlgebraicGeometry.Space.exists_isLE_derivedModulePushforward_obj f hfqc hfqs hY`
(`Spaces/DualityRightAdjointBoundedBelow.lean`), verbatim, with `QcohDerived` and
`derivedModulePushforward` written out. -/
def Tag08FABoundInput : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (_hfqc : IsQuasiCompact B S hS f.hom)
    (_hfqs : IsQuasiSeparated B S hS f.hom) (_hY : IsQuasiCompactSpace B S hS Y.1),
    ∃ N : ℤ, ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), qcohDerived X E →
      ∀ c : ℤ, E.IsLE c →
        ((Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f)).obj E).IsLE (c + N)

/-- **Stacks 0AFJ**: for `f : Y ⟶ X` a morphism of algebraic spaces, `T ⊆ |X|` closed and `Rf` a
right derived functor of the direct image of modules (any models of the derived categories), if
every cohomology sheaf of `E ∈ D(𝒪_Y)` is supported on `|f|⁻¹ T` then every cohomology sheaf of
`Rf E` is supported on `T`.  AxiomMath:
`AlgebraicGeometry.Space.derivedCategoryB_supportedModules_derivedPushforward B S hS f T hT Rf αf
E hE` (`Spaces/DerivedPushforwardSupport.lean`), verbatim, with `supportedModules` written out. -/
def Tag0AFJInput : Prop :=
  ∀ {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y.1 Y.2)]
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X.1 X.2)]
    (T : Set (points B S hS X.1)) (_hT : IsClosed T)
    (Rf : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (αf : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (_hE : DerivedCategoryB.derivedCategoryB
      (fun F : Modules.{u, u} B S hS Y.1 Y.2 => supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf _).obj F) ⊆ pointsMap B S hS Y.1 f.hom ⁻¹' T) E),
    DerivedCategoryB.derivedCategoryB
      (fun F : Modules.{u, u} B S hS X.1 X.2 => supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj F) ⊆ T) (Rf.obj E)

end RelativeFM.Spaces.LP26
