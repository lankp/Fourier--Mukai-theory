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

end RelativeFM.Spaces.LP26
