/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Supported.Inputs
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare

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
| `PerfectPseudoCoherentInput` | 08G8, (1) ⇒ (2), first clause | `AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isPerfect_general` | `CategoryTheory/Sites/Cohomology/Perfect/PseudoCoherenceAndTorAmplitudeGeneral.lean` † |
| `Tag08FVTwoInput` | 08FV (2) | `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_two_general` | `CategoryTheory/Sites/Cohomology/PseudoCoherent/DistinguishedTriangles.lean` † |
| `PseudoCoherentFromOfIsLEInput` | (none; the zero complex approximates, cf. 08FT) | `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isLE_sub_one` | `CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean` † |
| `Tag08FU2Input` | 08FU (2) | `AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom` | `CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean` † |
| `PerfectQcohInput` | (none; perfect ⇒ pseudo-coherent ⇒ `D_QCoh`, cf. 08G8, 08DM) | `AlgebraicGeometry.Space.qcohDerived_of_isPerfect_derivedCategoryB` | `Spaces/Perfect/PerfectRetract.lean` |
| `Tag08HPInput` | 08HP | `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_qcqs` | `Spaces/Perfect/ApproximationQcqs.lean` |
| `Tag073BInput` | 073B (1) | `AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace` | `Spaces/QuasiCompactSupport.lean` |
| `OpenSubspaceQuasiCompactInput` | 06RV, 03IR, 03E4 | `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isCompact_range` | `Spaces/SpectralPoints.lean` |
| `Tag08IKInput` | 08IK, final statement | `AlgebraicGeometry.Space.isPseudoCoherent_iff_of_isNoetherian` | `Spaces/PseudoCoherent/CoherentCohomologyEquivalence.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, or to `StacksFrontier/` when marked †,
AxiomMath commit `f56a316`.)  The inputs from `PerfectPseudoCoherentInput` on are used by
`Spaces/LP26/Lemma59.lean` (LP26 Lemma 5.9, `lem:characterize_T-_c`).

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
  `Stacks.Cohomology.SiteModules` abelian instances removed).  These two instances do not apply
  to `Modules.{u, u} B S hS X.1 X.2` anyway (their module universe is `max` of the site's
  universes, here `u + 1`), so AxiomMath files that keep them (`CoherentCohomologyEquivalence`)
  state the same thing.
* The inputs marked † above are AxiomMath theorems about an arbitrary ringed site
  `X : RingedSite.{u, v, w}` (with sheafification instances); each input is that statement
  **instantiated** at the small étale ringed site `smallEtaleRingedSite B S hS X.1 X.2` of an
  algebraic space `X` (`RingedSite.{u + 1, u, u}`), the only site LP26 uses, with the
  instances found in the context above (all `Prop`-valued except `HasDerivedCategory`, which is
  `HasDerivedCategory.standard` on both sides).  The discharge is
  `fun X … => AxiomMath's theorem (smallEtaleRingedSite B S hS X.1 X.2) …`.
* AxiomMath's abbreviations `ApproximationByPerfectComplexes` and `ApproximationHolds`
  (`Spaces/Perfect/Approximation.lean`, outside the import list) are written out by their bodies
  in `Tag08HPInput`; the `letI` of the topology of `|X|` in the body is the local instance
  `pointTopology` here.
* AxiomMath's `qcohDerived_of_isPerfect_derivedCategoryB` states its object in the spelling
  `DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))`, kept verbatim in
  `PerfectQcohInput`; it is definitionally `DerivedCategory (Modules.{u, u} B S hS X.1 X.2)`
  (`Spaces.D_eq_derivedModules`).
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

/-! ### Inputs of LP26 Lemma 5.9 (`lem:characterize_T-_c`) -/

/-- **A perfect object of `D(𝒪_X)` is pseudo-coherent** (Stacks 08G8, the first clause of the
implication (1) ⇒ (2)).  AxiomMath:
`AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isPerfect_general X hE` (`StacksFrontier/`
`CategoryTheory/Sites/Cohomology/Perfect/PseudoCoherenceAndTorAmplitudeGeneral.lean`), verbatim, instantiated at `X := smallEtaleRingedSite B S hS X.1 X.2` (module docstring). -/
def PerfectPseudoCoherentInput : Prop :=
  ∀ (X : AlgebraicSpaces B S hS) {E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    (_hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E),
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E

/-- **Stacks 08FV, part (2)**: if the first and third vertices of a distinguished triangle of
`D(𝒪_X)` are `m`-pseudo-coherent, so is the second.  AxiomMath:
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_two_general X m T hT hK hM`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/DistinguishedTriangles.lean`),
verbatim, instantiated at `X := smallEtaleRingedSite B S hS X.1 X.2`. -/
def Tag08FVTwoInput : Prop :=
  ∀ (X : AlgebraicSpaces B S hS) (m : ℤ)
    (T : Pretriangulated.Triangle (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)))
    (_hT : T ∈ Pretriangulated.distinguishedTriangles)
    (_hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom T.obj₁ m)
    (_hM : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom T.obj₃ m),
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom T.obj₂ m

/-- **An object of `D^{≤ t - 1}(𝒪_X)` is `t`-pseudo-coherent** (the zero complex approximates it;
no Stacks tag, cf. 08FT).  AxiomMath:
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isLE_sub_one X E t hE`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean`), verbatim,
instantiated at `X := smallEtaleRingedSite B S hS X.1 X.2`. -/
def PseudoCoherentFromOfIsLEInput : Prop :=
  ∀ (X : AlgebraicSpaces B S hS) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (t : ℤ)
    (_hE : E.IsLE (t - 1)),
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E t

/-- **Stacks 08FU (2), the degree-free criterion**: an object of `D(𝒪_X)` is pseudo-coherent iff
it is `n`-pseudo-coherent for every `n`.  AxiomMath:
`AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom X E` (an alias,
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean`), verbatim,
instantiated at `X := smallEtaleRingedSite B S hS X.1 X.2`. -/
def Tag08FU2Input : Prop :=
  ∀ (X : AlgebraicSpaces B S hS) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)),
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E ↔
      ∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E n

/-- **A perfect object of `D(𝒪_X)` lies in `D_QCoh(𝒪_X)`** (no Stacks tag; it is pseudo-coherent,
cf. 08G8).  AxiomMath: `AlgebraicGeometry.Space.qcohDerived_of_isPerfect_derivedCategoryB X E hE`
(`Spaces/Perfect/PerfectRetract.lean`), verbatim. -/
def PerfectQcohInput : Prop :=
  ∀ (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (_hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E),
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E

/-- **Stacks 08HP**: on a quasi-compact quasi-separated algebraic space `X`, approximation by
perfect complexes holds: for every closed `T ⊆ |X|` whose open complement has quasi-compact
inclusion there is `r` such that every `E ∈ D_QCoh(𝒪_X)` which is `(m - r)`-pseudo-coherent with
`Hⁱ(E)` supported on `T` for `i ≥ m - r` receives a map `P ⟶ E` from a perfect `P` supported on
`T`, an isomorphism on `Hⁱ` for `i > m` and surjective on `Hᵐ`.  AxiomMath:
`AlgebraicGeometry.Space.approximationByPerfectComplexes_of_qcqs B S hS hZ X hX hXqc hXqs`
(`Spaces/Perfect/ApproximationQcqs.lean`), verbatim, with `ApproximationByPerfectComplexes.{u, u}`
and `ApproximationHolds` (Stacks 08HJ, 08HI) written out by their bodies. -/
def Tag08HPInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (_hXqc : IsQuasiCompactSpace B S hS X)
    (_hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (T : Set (points B S hS X)) (hT : IsClosed T),
    IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι →
    ∃ r : ℤ, ∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ),
      (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentFrom E.obj (m - r) →
      (∀ i : ℤ, m - r ≤ i →
        supportOfSheaf B S hS X
          ((SheafOfModules.toSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).obj
            ((DerivedCategory.homologyFunctor
              (Modules.{u, u} B S hS X hX) i).obj E.obj)) ⊆ T) →
      ∃ P : DerivedCategory (Modules.{u, u} B S hS X hX),
        (smallEtaleRingedSite B S hS X hX).IsPerfect P ∧
          CohomologySupportedOn B S hS X hX T P ∧
          ∃ α : P ⟶ E.obj,
            (∀ i : ℤ, m < i →
              IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).map α)) ∧
            Epi ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) m).map α)

/-- **Stacks 073B, part (1)**: a morphism from a quasi-compact algebraic space into a
quasi-separated algebraic space is quasi-compact.  AxiomMath:
`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hX hXqs hUqc ι`
(`Spaces/QuasiCompactSupport.lean`), verbatim. -/
def Tag073BInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X) (_hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (_hUqc : IsQuasiCompactSpace B S hS U) (ι : U ⟶ X),
    IsQuasiCompact B S hS ι

/-- **An open subspace whose set of points is compact is quasi-compact** (Stacks 06RV, 03IR,
03E4).  AxiomMath: `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isCompact_range B S hS hX hG
hcompact` (`Spaces/SpectralPoints.lean`), verbatim. -/
def OpenSubspaceQuasiCompactInput : Prop :=
  ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hX : IsAlgebraicSpace B S hS X)
    {G : Subfunctor X} (_hG : IsOpenSubspace B S hS G)
    (_hcompact : IsCompact (Set.range (pointsMap B S hS G.toFunctor G.ι))),
    IsQuasiCompactSpace B S hS G.toFunctor

/-- **Stacks 08IK, the final statement**: on a Noetherian algebraic space `F`, an object `E` of
`D_QCoh(𝒪_F)` is pseudo-coherent iff it is bounded above with coherent cohomology sheaves
(`E ∈ D^-_Coh(𝒪_F)`).  AxiomMath:
`AlgebraicGeometry.Space.isPseudoCoherent_iff_of_isNoetherian B S hS F hF hZ hFN E hE`
(`Spaces/PseudoCoherent/CoherentCohomologyEquivalence.lean`), verbatim. -/
def Tag08IKInput : Prop :=
  ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hZ : B.Contains (⊤_ Scheme.{u})) (_hFN : IsNoetherian B S hS hZ F)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (_hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) E),
    (smallEtaleRingedSite B S hS F hF).IsPseudoCoherent E ↔
      (DerivedCategoryB.IsBoundedAbove E ∧
        ∀ i : ℤ, SheafOfModules.IsCoherentOnSite
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E))

/-! ### Inputs of the open–closed recollement (GL26 Lemmas A.4, A.6) and of LP26 Proposition 5.8

These are used by `Spaces/LP26/Recollement.lean` and `Spaces/LP26/Proposition58.lean`.  Two
AxiomMath **definition** modules are imported for their statements (module imports above, both
built, free of `MilnorPatching.Relative`): `Spaces/SmallEtaleDerivedModulePullbackEtale.lean`
(the étale restriction adjunction `etaleDerivedModuleAdjunction`, the identification
`smallEtaleDerivedModulePullbackIsoEtale`) and `Spaces/Perfect/ElementaryDistinguishedSquare.lean`
(`IsElementaryDistinguishedSquare`, Stacks 08GM).

| input | Stacks | AxiomMath declaration | AxiomMath file |
|---|---|---|---|
| `Tag079QInput` | 079Q | `Stacks.ModulesOnACategory.CartesianSubcategory.locallySmall_derivedCategory` | `CategoryTheory/Sites/Cohomology/ModulesOnACategory/CartesianObjectsTriangulatedSubcategory.lean` † |
| `Tag0A8GInput` | 0A8G | `CategoryTheory.Pretriangulated.isLeftAdjoint_of_compact_generator` | `CategoryTheory/Triangulated/BrownRepresentabilityShrinkHoms.lean` † |
| `RightAdjointCoproductsInput` | (08DZ, the formal step) | `CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map` | `CategoryTheory/Triangulated/RightAdjointCoproducts.lean` † |
| `PullbackSupportInput` | 08GF | `AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedModulePullback` | `Spaces/DerivedPullbackSupport.lean` |
| `PullbackDisjointInput` | 08GF, 04K5 | `AlgebraicGeometry.Space.isZero_smallEtaleDerivedModulePullback_of_disjoint` | `Spaces/Deformations/DerivedExistenceSupportedVanishing.lean` |
| `EtaleRestrictionSupportInput` | 08GF, 04K5 | `AlgebraicGeometry.Space.cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback` | `Spaces/DerivedSupportEtaleRestriction.lean` |
| `OpenImmersionCounitInput` | (08GE for `U ×_X U = U`) | `AlgebraicGeometry.Space.isIso_etaleDerivedModuleAdjunction_counit_of_mono` | `Spaces/DerivedPushforwardEtaleBaseChange.lean` |
| `QuasiCompactSourceInput` | (none; base change along `𝟙`) | `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isQuasiCompact` | `Spaces/HigherDirectImageUniformBound.lean` |
| `Tag073BTwoInput` | 073B (2) | `AlgebraicGeometry.Space.isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source` | `Spaces/Morphisms/QuasiCompact.lean` |
| `CompactComplPreimageInput` | (0EMK, 06RV) | `AlgebraicGeometry.Space.isCompact_compl_preimage_of_isQuasiCompact` | `Spaces/Perfect/SupportedAffinePullbackGenerator.lean` |
| `PerfectPullbackInput` | 08H6 | `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback` | `Spaces/Perfect/DerivedPullbackPerfect.lean` |
| `SupportEmptyInput` | 04K5 | `AlgebraicGeometry.Space.supportOfSheaf_eq_empty_iff_isZero` | `Spaces/WeaklyAssociatedVanishingConverse.lean` |
| `EDSTopInput` | 08GM (an example) | `AlgebraicGeometry.Space.isElementaryDistinguishedSquare_top` | `Spaces/ModuleSectionsWithSupport.lean` |
| `Tag08GGUnitInput` | 08GG (1)(a) | `AlgebraicGeometry.Space.isIso_unit_derivedRestrict_of_cohomologySupportedOn` | `Spaces/Perfect/SupportedOnComplementClauses.lean` |
| `Tag08GGCounitInput` | 08GG (2)(b) | `AlgebraicGeometry.Space.isIso_counit_derivedPushforward_of_cohomologySupportedOn` | `Spaces/Perfect/SupportedOnComplementClauses.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, or to `StacksFrontier/` when marked †.)

Spelling:

* The categorical theorems (†) are universe-polymorphic; each input is the statement at the
  universes where it is used: categories `Type (u + 1)` with morphisms in `Type (u + 1)` (the
  models `D(𝒪_X)`, `D_{qc,T}(X)` at `HasDerivedCategory.standard`) and coproducts indexed by
  `Type u`; for 079Q, `A : Type (u + 1)` with morphisms in `Type (u + 1)`, a derived category with
  morphisms in `Type (u + 1)`, Grothendieck universe `u` (the module categories
  `Modules.{u, u} B S hS X.1 X.2`).
* In the two 08GG inputs, AxiomMath's section variables `{W} {V} {Uo} {fV} (hsq)` are bound, and
  its definitions `edsEtale B S hS hsq` (`⟨V, hsq.isAlgebraicSpace⟩`), `edsEtaleHom B S hS hsq`
  (`ObjectProperty.homMk fV`) and `isEtale_edsEtaleHom B S hS hsq` (`hsq.isEtale`)
  (`Spaces/Perfect/MayerVietoris.lean`, outside the import list) are restated here with the same
  bodies as the definitions `edsEtaleSpace`, `edsEtaleMap` and the theorem
  `isEtale_edsEtaleMap` (`edsOpenSpace`, `edsOpenMap` likewise for `edsOpen`, `edsOpenHom`), and
  `edsComplementPoints B S hS Uo` (`(Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ`) and
  `edsEtalePreimageComplementPoints B S hS hsq` (its preimage under the points map of `fV`)
  (`Spaces/Perfect/SupportedOnComplement.lean`) are written out by their bodies.
* `isCompact_compl_preimage_of_isQuasiCompact` writes `B.contains_terminal`; it is bound as `hZ`.
-/

section RecollementInputs

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- **Stacks 079Q**: the derived category of a Grothendieck abelian category is locally small in
the universe in which the category is, whatever model of the derived category is used.  AxiomMath:
the instance `Stacks.ModulesOnACategory.CartesianSubcategory.locallySmall_derivedCategory A`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/ModulesOnACategory/`
`CartesianObjectsTriangulatedSubcategory.lean`), verbatim, at `A : Type (u + 1)` with morphisms in
`Type (u + 1)`, the derived category's morphisms in `Type (u + 1)` and the Grothendieck universe
`u`. -/
def Tag079QInput : Prop :=
  ∀ (A : Type (u + 1)) [Category.{u + 1} A] [Abelian A] [HasDerivedCategory.{u + 1} A]
    [IsGrothendieckAbelian.{u} A], LocallySmall.{u} (DerivedCategory A)

/-- **Stacks 0A8G** (Brown representability, without smallness of the morphism types): an exact
functor preserving `Type u`-indexed coproducts out of a triangulated category which is locally
`u`-small, has `Type u`-indexed coproducts and a compact weak generator, into a locally `u`-small
pretriangulated category, is a left adjoint.  AxiomMath:
`CategoryTheory.Pretriangulated.isLeftAdjoint_of_compact_generator`
(`StacksFrontier/CategoryTheory/Triangulated/BrownRepresentabilityShrinkHoms.lean`), verbatim, at
`C D : Type (u + 1)` with morphisms in `Type (u + 1)` and `u₃ = u`. -/
def Tag0A8GInput : Prop :=
  ∀ {C : Type (u + 1)} {D : Type (u + 1)} [Category.{u + 1} C] [Category.{u + 1} D]
    [LocallySmall.{u} C] [LocallySmall.{u} D]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [HasCoproducts.{u} C]
    (functor : C ⥤ D) (functorShift : functor.CommShift ℤ)
    (_functorTriangulated : @Functor.IsTriangulated _ _ _ _ _ _ functor functorShift
      _ _ _ _ _ _ _ _)
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) functor]
    (generator : C) [IsCompactObject.{u} generator]
    (_hgenerator : (ObjectProperty.singleton generator).IsWeakTriangulatedGenerator),
    functor.IsLeftAdjoint

/-- **A right adjoint commutes with direct sums as soon as its left adjoint preserves the
compactness of a weak generator** (the formal step behind Stacks 08DZ).  AxiomMath:
`CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map adj E hE hcompact hmap`
(`StacksFrontier/CategoryTheory/Triangulated/RightAdjointCoproducts.lean`), verbatim with its
section variables bound, at `C D : Type (u + 1)` with morphisms in `Type (u + 1)` and `w = u`. -/
def RightAdjointCoproductsInput : Prop :=
  ∀ {C : Type (u + 1)} {D : Type (u + 1)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [HasCoproducts.{u} C] [HasCoproducts.{u} D]
    {L : D ⥤ C} {R : C ⥤ D} [L.Additive] [R.Additive] [L.CommShift ℤ]
    (_adj : L ⊣ R) (E : D)
    (_hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (_hcompact : IsCompactObject.{u} E) (_hmap : IsCompactObject.{u} (L.obj E)),
    ∀ I : Type u, PreservesColimitsOfShape (Discrete I) R

/-- **Supports and derived pullbacks** (Stacks 08GF): if `E ∈ D(𝒪_X)` is supported on `Y ⊆ |X|`,
then `Lg^*E` is supported on `|g|⁻¹ Y`.  AxiomMath:
`AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedModulePullback g E hE`
(`Spaces/DerivedPullbackSupport.lean`), verbatim.  (GL26 Lemma A.2, `lem:support_for_pullback`,
is the case of a closed `Y`.) -/
def PullbackSupportInput : Prop :=
  ∀ {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X) {Y : Set (points B S hS X.1)}
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (_hE : CohomologySupportedOn B S hS X.1 X.2 Y E),
    CohomologySupportedOn B S hS X'.1 X'.2 (pointsMap B S hS X'.1 g.hom ⁻¹' Y)
      ((smallEtaleDerivedModulePullback B S hS g).obj E)

/-- **The derived pullback of an object supported on `Q` along a morphism missing `Q` vanishes**
(Stacks 08GF, 04K5).  AxiomMath:
`AlgebraicGeometry.Space.isZero_smallEtaleDerivedModulePullback_of_disjoint g Q E hE hdisj`
(`Spaces/Deformations/DerivedExistenceSupportedVanishing.lean`), verbatim. -/
def PullbackDisjointInput : Prop :=
  ∀ {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (Q : Set (points B S hS X.1)) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (_hE : CohomologySupportedOn B S hS X.1 X.2 Q E)
    (_hdisj : Disjoint (Set.range (pointsMap B S hS X'.1 g.hom)) Q),
    IsZero ((smallEtaleDerivedModulePullback B S hS g).obj E)

/-- **An object whose restriction along an étale `g : Y ⟶ X` vanishes is supported off the image
of `|Y|`** (Stacks 08GF, 04K5).  AxiomMath:
`AlgebraicGeometry.Space.cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback B S hS g hg
E hE` (`Spaces/DerivedSupportEtaleRestriction.lean`), verbatim. -/
def EtaleRestrictionSupportInput : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (_hE : IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E)),
    CohomologySupportedOn B S hS X.1 X.2
      (Set.range (pointsMap B S hS Y.1 g.hom))ᶜ E

/-- **The counit of `(-)|_U ⊣ Rj_*` is invertible for an étale monomorphism `j`** (an open
immersion; base change, Stacks 08GE, along `U ×_X U = U`).  AxiomMath:
`AlgebraicGeometry.Space.isIso_etaleDerivedModuleAdjunction_counit_of_mono B S hS j hj`
(`Spaces/DerivedPushforwardEtaleBaseChange.lean`), verbatim. -/
def OpenImmersionCounitInput : Prop :=
  ∀ {U X : AlgebraicSpaces B S hS} (j : U ⟶ X) (hj : IsEtale B S hS j.hom) [Mono j],
    IsIso (etaleDerivedModuleAdjunction B S hS j hj).counit

/-- **The source of a quasi-compact morphism to a quasi-compact algebraic space is
quasi-compact.**  AxiomMath: `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isQuasiCompact B S hS
hY hYqc f hf` (`Spaces/HigherDirectImageUniformBound.lean`), verbatim. -/
def QuasiCompactSourceInput : Prop :=
  ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hY : IsAlgebraicSpace B S hS Y) (_hYqc : IsQuasiCompactSpace B S hS Y) (f : X ⟶ Y)
    (_hf : IsQuasiCompact B S hS f), IsQuasiCompactSpace B S hS X

/-- **Stacks 073B, part (2)**: every morphism out of a quasi-separated algebraic space is
quasi-separated.  AxiomMath:
`AlgebraicGeometry.Space.isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ hF hFqs f`
(`Spaces/Morphisms/QuasiCompact.lean`), verbatim. -/
def Tag073BTwoInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : IsAlgebraicSpace B S hS F)
    (_hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F) (f : F ⟶ G),
    IsQuasiSeparated B S hS f

/-- **The complement of the preimage of a closed set with quasi-compact complement, along a
morphism from a quasi-compact space into a quasi-separated one, is quasi-compact** (Stacks 0EMK
and 06RV).  AxiomMath:
`AlgebraicGeometry.Space.isCompact_compl_preimage_of_isQuasiCompact g hXqc hX₀qs T₀ hT₀ hT₀c`
(`Spaces/Perfect/SupportedAffinePullbackGenerator.lean`), verbatim, with `B.contains_terminal`
bound as `hZ`. -/
def CompactComplPreimageInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {X X₀ : AlgebraicSpaces B S hS} (g : X ⟶ X₀)
    (_hXqc : IsQuasiCompactSpace B S hS X.1)
    (_hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀.1)
    (T₀ : Set (points B S hS X₀.1)) (_hT₀ : IsClosed T₀) (_hT₀c : IsCompact T₀ᶜ),
    IsCompact (pointsMap B S hS X.1 g.hom ⁻¹' T₀)ᶜ

/-- **Stacks 08H6**: the derived pullback of a perfect object along a morphism of algebraic spaces
is perfect.  AxiomMath: `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback f E hE`
(`Spaces/Perfect/DerivedPullbackPerfect.lean`), verbatim. -/
def PerfectPullbackInput : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (_hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) E),
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2)
      ((smallEtaleDerivedModulePullback B S hS f).obj E)

section EDS

variable {B S hS} {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}

/-- The étale algebraic space `V` of an elementary distinguished square `(U ⊆ W, fV : V ⟶ W)`:
the body of AxiomMath's `edsEtale B S hS hsq` (`Spaces/Perfect/MayerVietoris.lean`). -/
def edsEtaleSpace (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) :
    AlgebraicSpaces B S hS :=
  ⟨V, hsq.isAlgebraicSpace⟩

/-- The étale morphism `V ⟶ W` of an elementary distinguished square: the body of AxiomMath's
`edsEtaleHom B S hS hsq`. -/
def edsEtaleMap (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) :
    edsEtaleSpace hsq ⟶ W :=
  ObjectProperty.homMk fV

/-- The étale morphism of an elementary distinguished square is étale (AxiomMath's
`isEtale_edsEtaleHom`, whose proof is `hsq.isEtale`). -/
theorem isEtale_edsEtaleMap (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) :
    IsEtale B S hS (edsEtaleMap hsq).hom :=
  hsq.isEtale

/-- The open subspace `U` of an elementary distinguished square, as an algebraic space: the body
of AxiomMath's `edsOpen B S hS hsq`. -/
def edsOpenSpace (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) :
    AlgebraicSpaces B S hS :=
  ⟨Uo.toFunctor, hsq.isOpenSubspace.1⟩

/-- The open immersion `U ⟶ W` of an elementary distinguished square: the body of AxiomMath's
`edsOpenHom B S hS hsq`. -/
def edsOpenMap (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) :
    edsOpenSpace hsq ⟶ W :=
  ObjectProperty.homMk Uo.ι

end EDS

/-- **Stacks 08GG, clause (1)(a)**: let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square
and `T = |X| ∖ |U|`.  For `Rj_*` any right adjoint of derived restriction
`(-)|_V : D(𝒪_X) ⥤ D(𝒪_V)` and `E ∈ D(𝒪_X)` supported on `T`, the unit `E ⟶ Rj_*(E|_V)` is an
isomorphism.  AxiomMath:
`AlgebraicGeometry.Space.isIso_unit_derivedRestrict_of_cohomologySupportedOn B S hS hsq adjPush E
hE` (`Spaces/Perfect/SupportedOnComplementClauses.lean`), verbatim, with the section variables
bound and `edsEtale`, `edsEtaleHom`, `isEtale_edsEtaleHom` spelled `edsEtaleSpace`, `edsEtaleMap`,
`isEtale_edsEtaleMap` (their bodies, above) and `edsComplementPoints` written out. -/
def Tag08GGUnitInput : Prop :=
  ∀ {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    {RpushD : DerivedCategory
        (Modules.{u, u} B S hS (edsEtaleSpace hsq).1 (edsEtaleSpace hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
    (adjPush : (etaleModulePullback.{u, u} B S hS (edsEtaleMap hsq)
      (isEtale_edsEtaleMap hsq)).mapDerivedCategory ⊣ RpushD)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (_hE : CohomologySupportedOn B S hS W.1 W.2
      (Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ E),
    IsIso (adjPush.unit.app E)

/-- **Stacks 08GG, clause (2)(b)**: let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square
and `T = |X| ∖ |U|`.  For `Rj_*` any right adjoint of derived restriction and `F ∈ D(𝒪_V)`
supported on `j⁻¹T`, the counit `(Rj_*F)|_V ⟶ F` is an isomorphism.  AxiomMath:
`AlgebraicGeometry.Space.isIso_counit_derivedPushforward_of_cohomologySupportedOn B S hS hsq
adjPush F hF` (`Spaces/Perfect/SupportedOnComplementClauses.lean`), verbatim, with the section
variables bound, `edsEtale`, `edsEtaleHom`, `isEtale_edsEtaleHom` spelled `edsEtaleSpace`,
`edsEtaleMap`, `isEtale_edsEtaleMap` (their bodies, above) and `edsEtalePreimageComplementPoints`
written out. -/
def Tag08GGCounitInput : Prop :=
  ∀ {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    {RpushD : DerivedCategory
        (Modules.{u, u} B S hS (edsEtaleSpace hsq).1 (edsEtaleSpace hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
    (adjPush : (etaleModulePullback.{u, u} B S hS (edsEtaleMap hsq)
      (isEtale_edsEtaleMap hsq)).mapDerivedCategory ⊣ RpushD)
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtaleSpace hsq).1 (edsEtaleSpace hsq).2))
    (_hF : CohomologySupportedOn B S hS (edsEtaleSpace hsq).1 (edsEtaleSpace hsq).2
      (pointsMap B S hS (edsEtaleSpace hsq).1 (edsEtaleMap hsq).hom ⁻¹'
        (Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ) F),
    IsIso (adjPush.counit.app F)

/-- **An open subspace and the identity form an elementary distinguished square** (Stacks 08GM):
for `U` an open subspace of `X`, `(U ⊆ X, ⊤.ι : ⊤ ⟶ X)` is an elementary distinguished square.
AxiomMath: `AlgebraicGeometry.Space.isElementaryDistinguishedSquare_top B S hS hX hU`
(`Spaces/ModuleSectionsWithSupport.lean`), verbatim.  Used only for non-vacuity. -/
def EDSTopInput : Prop :=
  ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {U : Subfunctor X} (_hU : IsOpenSubspace B S hS U),
    IsElementaryDistinguishedSquare B S hS hX U (⊤ : Subfunctor X).ι

/-- **A module with empty support is zero** (Stacks 04K5): the support of the abelian sheaf
underlying an `𝒪_X`-module is empty iff the module is zero.  AxiomMath:
`AlgebraicGeometry.Space.supportOfSheaf_eq_empty_iff_isZero B S hS X F`
(`Spaces/WeaklyAssociatedVanishingConverse.lean`), verbatim at the module universe `m = u`.  Used
only for non-vacuity. -/
def SupportEmptyInput : Prop :=
  ∀ (X : AlgebraicSpaces B S hS) (F : Modules.{u, u} B S hS X.1 X.2),
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) = ∅ ↔ IsZero F

end RecollementInputs

end RelativeFM.Spaces.LP26
