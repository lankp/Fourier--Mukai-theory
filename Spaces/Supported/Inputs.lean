/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.AxiomMathInputs
import StacksFrontier.CategoryTheory.Triangulated.CompactObjects.ThickSubcategory

/-!
# Tagged AxiomMath inputs for `D_{qc,Z}(X)` (GL26 Lemma A.9, `lem:preferred_eq_class`)

The AxiomMath/Stacks theorems that `Spaces/Supported/CompactGeneration.lean` and
`Spaces/Supported/Preferred.lean` use, for a
quasi-compact quasi-separated algebraic space `X` and a closed `T ⊆ |X|` with quasi-compact
complement.  Each is a `Prop` whose statement is AxiomMath's verbatim, with the conventions of
`Spaces/AxiomMathInputs.lean` (CLAUDE.md rule 2, `results/STACKS_POLICY.md`): the AxiomMath
modules below are theorem modules outside `scripts/axiommath/spaces-imports.txt`, and
`SpacesVerified` discharges each input by the AxiomMath declaration named in its docstring.

| input | Stacks | AxiomMath declaration | AxiomMath file |
|---|---|---|---|
| `Tag08F3Input` | 08F3 | `AlgebraicGeometry.Space.hasCoproducts_quasicoherentDerivedCategory_ringUniverse` | `Spaces/QuasicoherentDerivedDirectSums.lean` |
| `SupportTriangulatedInput` | 0AED (remark preceding it), 08GF | `AlgebraicGeometry.Space.isTriangulated_cohomologySupportedOn` (instance) | `Spaces/Perfect/SupportedQuasicoherentDerived.lean` |
| `SupportedDirectSumsInput` | 0AED (remark preceding it) | `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentDerivedSupportedOn` | `Spaces/Perfect/SupportedQuasicoherentDerived.lean` |
| `Tag0AECInput` | 0AEC | `AlgebraicGeometry.Space.exists_isPerfect_generator_of_supported` | `Spaces/Perfect/SupportedPerfectGenerator.lean` |
| `Tag0AEDInput` | 0AED | `AlgebraicGeometry.Space.isCompactObject_iff_isPerfect_of_supported` | `Spaces/Perfect/SupportedCompactPerfect.lean` |
| `Tag0GFDInput` | 0GFD | `AlgebraicGeometry.Space.triangEnvelope_singleton_eq_isPerfect_of_supported` | `Spaces/Perfect/SupportedPerfectClassicalGenerator.lean` |
| `AffineQuasiSeparatedInput` | 03JX (ι), 03BS (3) | `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_yoneda_of_isAffine` | `Spaces/AbsolutelyQuasiSeparatedAffine.lean` |
| `ContainsTerminalInput` | (none; 021R's site contains `Spec ℤ`) | `AlgebraicGeometry.BigFppfSite.contains_terminal` | `Spaces/FiniteEtaleAtlasQuasiSeparated.lean` |
| `Tag0GFIInput` | 0GFI ((7) ⇒ (1)) | `AlgebraicGeometry.Space.exists_isGE_of_lowHomVanishingOnCompact` | `Spaces/Perfect/DetectingBoundedBelow.lean` |
| `PerfectBoundedAboveInput` | (none; 08G5 with 08GP, a step of 0GFI) | `AlgebraicGeometry.Space.exists_isLE_of_isPerfect` | `Spaces/Perfect/DetectingBoundedBelow.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, AxiomMath commit `f56a316`.)

## Spelling

* AxiomMath's abbreviation `quasicoherentDerivedSupportedOn X T`
  (`Spaces/Perfect/SupportedQuasicoherentDerived.lean`, outside the import list) is written out
  by its body as `qcSupportedOn X T` below
  (`ObjectProperty.inverseImage (CohomologySupportedOn B S hS X.1 X.2 T) (ObjectProperty.ι _)`).
  Its full subcategory is `D_{QCoh,T}(𝒪_X)`.
* The instance context is AxiomMath's, copied from the AxiomMath files (the two
  `Stacks.Cohomology.SiteModules` abelian instances removed; `HasDerivedCategory.standard`,
  the sheafification instances of the small étale site and `pointTopology`, the topology of
  `|X|`, as local instances).  With the repository's context of `Spaces/Categories.lean`
  (`SheafOfModules.instAbelian` at priority 5000) the hidden instance arguments of
  AxiomMath's `QuasicoherentDerivedCategory` are not those of `Spaces.Dqc X`, and instance
  search does not see the triangulated structure; in AxiomMath's context it does.
* AxiomMath writes `B.contains_terminal` (`BigFppfSite.contains_terminal`, a theorem of
  `Spaces/FiniteEtaleAtlasQuasiSeparated.lean`, outside the import list) for the proof that
  the site contains `Spec ℤ`, on which absolute quasi-separatedness depends.  The inputs bind
  that proof as `hZ : B.Contains (⊤_ Scheme.{u})`; being a proof of a `Prop`, any `hZ` is
  definitionally `B.contains_terminal`, and the discharge is
  `fun _ X … => AxiomMath's theorem X …`.
* `Tag0GFDInput` mentions the triangulated envelope in `D_{QCoh,T}(𝒪_X)`, which needs the
  pretriangulated structure of that category.  AxiomMath obtains it from two global instances
  of theorem modules outside the import list, `isTriangulated_quasicoherentDerivedCategory`
  (06UQ, the repository's `Tag06UQInput`) and `isTriangulated_cohomologySupportedOn`
  (`SupportTriangulatedInput`).  The input therefore binds those two instances as
  instance-implicit hypotheses; they are `Prop`s, so this is AxiomMath's statement (any two
  proofs are equal), and the discharge is `fun _ X _ … T _ … => AxiomMath's theorem X …`.
* `Tag0GFIInput` writes out AxiomMath's two abbreviations of
  `Spaces/Perfect/DetectingBoundedBelow.lean` (outside the import list) by their bodies:
  `LowHomVanishingOnCompact X hX E` is
  `∀ P : QuasicoherentDerivedCategory B S hS X hX, IsCompactObject.{u} P → lowHomVanishing E P.obj`
  and `lowHomVanishing M P` is `∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P⟦-i⟧ ⟶ M)`.  That file's
  instance context (`SheafOfModules.instAbelian` at priority 5000, `HasDerivedCategory.standard`)
  selects the same instances as the context below.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Supported

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

section Spelling

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`D_QCoh(𝒪_X)`** as a property of objects of `D(𝒪_X)`, in AxiomMath's spelling (the
body of AxiomMath's `QcohDerived`, and the property whose full subcategory is
`QuasicoherentDerivedCategory`). -/
abbrev qcohDerived (X : AlgebraicSpaces B S hS) :
    ObjectProperty (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :=
  DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))

/-- **`D_{QCoh,T}(𝒪_X)`** as a property of objects of `D_QCoh(𝒪_X)`: all cohomology sheaves
supported on `T` (Stacks 08GF).  This is the body of AxiomMath's abbreviation
`AlgebraicGeometry.Space.quasicoherentDerivedSupportedOn X T`
(`Spaces/Perfect/SupportedQuasicoherentDerived.lean`, outside the import list). -/
abbrev qcSupportedOn (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) :
    ObjectProperty (QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :=
  ObjectProperty.inverseImage (CohomologySupportedOn B S hS X.1 X.2 T) (ObjectProperty.ι _)

/-- Support on `T` is invariant under isomorphism in `D(𝒪_X)` (proved here; AxiomMath's
instance `isClosedUnderIsomorphisms_cohomologySupportedOn` lives in a module outside the import
list).  It is needed to state `Tag0GFDInput`: the triangulated structure of
`D_{QCoh,T}(𝒪_X)` is that of an inverse image. -/
instance isClosedUnderIsomorphisms_cohomologySupportedOn' (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) :
    ObjectProperty.IsClosedUnderIsomorphisms (CohomologySupportedOn B S hS X.1 X.2 T) where
  of_iso e h := fun i => by
    let φ := (SheafOfModules.toSheaf _).mapIso
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).mapIso e)
    have : Mono φ.inv := ⟨fun g k w => by simpa using congrArg (· ≫ φ.hom) w⟩
    exact (@supportOfSheaf_subset_of_mono B S hS X.1 X.2 _ _ φ.inv this).trans (h i)

end Spelling

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 08F3** (direct sums in `D_QCoh`): `D_QCoh(𝒪_F)` has direct sums indexed by
`Type u`.  AxiomMath:
`AlgebraicGeometry.Space.hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS F hF`
(`Spaces/QuasicoherentDerivedDirectSums.lean`), verbatim. -/
def Tag08F3Input : Prop :=
  ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F),
    HasCoproducts.{u} (QuasicoherentDerivedCategory.{u, u} B S hS F hF)

/-- **`D_T(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`** (the remark preceding
Stacks 0AED; support as in Stacks 08GF).  AxiomMath: the instance
`AlgebraicGeometry.Space.isTriangulated_cohomologySupportedOn X T`
(`Spaces/Perfect/SupportedQuasicoherentDerived.lean`), verbatim. -/
def SupportTriangulatedInput : Prop :=
  ∀ (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)),
    ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)

/-- **`D_{QCoh,T}(𝒪_X)` is closed under direct sums in `D_QCoh(𝒪_X)`**, for `T` closed (the
remark preceding Stacks 0AED).  AxiomMath:
`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentDerivedSupportedOn X T hT J`
(`Spaces/Perfect/SupportedQuasicoherentDerived.lean`), verbatim, with
`quasicoherentDerivedSupportedOn` written out (`qcSupportedOn`). -/
def SupportedDirectSumsInput : Prop :=
  ∀ (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) (_hT : IsClosed T)
    (J : Type u), (qcSupportedOn X T).IsClosedUnderColimitsOfShape (Discrete J)

/-- **Stacks 0AEC**: for `X` quasi-compact and quasi-separated and `T ⊆ |X|` closed with
`|X| ∖ T` quasi-compact, `D_{QCoh,T}(𝒪_X)` is generated by a single perfect object `P`:
`P` is perfect, has quasi-coherent cohomology supported on `T`, and an object `E` of
`D_QCoh(𝒪_X)` supported on `T` is zero iff `Hom(P[n], E) = 0` for all `n`.  AxiomMath:
`AlgebraicGeometry.Space.exists_isPerfect_generator_of_supported X hXqc hXqs T hT hTc`
(`Spaces/Perfect/SupportedPerfectGenerator.lean`), verbatim. -/
def Tag0AECInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (_hXqc : IsQuasiCompactSpace B S hS X.1)
    (_hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (_hT : IsClosed T) (_hTc : IsCompact Tᶜ),
    ∃ P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P ∧
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) P ∧
      CohomologySupportedOn B S hS X.1 X.2 T P ∧
      ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
        CohomologySupportedOn B S hS X.1 X.2 T E.obj →
          (IsZero E.obj ↔ ∀ (n : ℤ) (g : P⟦n⟧ ⟶ E.obj), g = 0)

/-- **Stacks 0AED**: for `X` quasi-compact and quasi-separated and `T ⊆ |X|` closed with
`|X| ∖ T` quasi-compact, an object of `D_{QCoh,T}(𝒪_X)` is compact in `D_{QCoh,T}(𝒪_X)`
(`IsCompactObject.{u}`, Stacks 07LS, direct sums indexed by `Type u`) iff it is perfect in
`D(𝒪_X)`.  AxiomMath:
`AlgebraicGeometry.Space.isCompactObject_iff_isPerfect_of_supported X hXqc hXqs T hT hTc E`
(`Spaces/Perfect/SupportedCompactPerfect.lean`), verbatim, with
`quasicoherentDerivedSupportedOn` written out (`qcSupportedOn`). -/
def Tag0AEDInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (_hXqc : IsQuasiCompactSpace B S hS X.1)
    (_hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (_hT : IsClosed T) (_hTc : IsCompact Tᶜ)
    (E : (qcSupportedOn X T).FullSubcategory),
    IsCompactObject.{u} E ↔ (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E.obj.obj

/-- **Stacks 0GFD**: for `X` quasi-compact and quasi-separated, `T ⊆ |X|` closed with
`|X| ∖ T` quasi-compact, and `G` a perfect object of `D_{QCoh,T}(𝒪_X)` generating it (an
object of `D_QCoh(𝒪_X)` supported on `T` receiving only zero maps from the shifts of `G` is
zero), the triangulated envelope of `G` in `D_{QCoh,T}(𝒪_X)` is exactly the property of being
perfect in `D(𝒪_X)`.  AxiomMath:
`AlgebraicGeometry.Space.triangEnvelope_singleton_eq_isPerfect_of_supported X hXqc hXqs T hT hTc
G hG hGq hGs hgen` (`Spaces/Perfect/SupportedPerfectClassicalGenerator.lean`), verbatim, with
`quasicoherentDerivedSupportedOn` written out (`qcSupportedOn`) and the two `Prop` instances
behind the pretriangulated structure of `D_{QCoh,T}(𝒪_X)` bound as instance arguments (module
docstring). -/
def Tag0GFDInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    [(DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)))).IsTriangulated]
    (_hXqc : IsQuasiCompactSpace B S hS X.1)
    (_hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (_hT : IsClosed T) (_hTc : IsCompact Tᶜ)
    (G : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (_hG : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect G)
    (hGq : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) G)
    (hGs : CohomologySupportedOn B S hS X.1 X.2 T G)
    (_hgen : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      CohomologySupportedOn B S hS X.1 X.2 T E.obj →
        (∀ (n : ℤ) (g : G⟦n⟧ ⟶ E.obj), g = 0) → IsZero E.obj),
    (ObjectProperty.singleton
        (⟨⟨G, hGq⟩, hGs⟩ : (qcSupportedOn X T).FullSubcategory)).triangEnvelope =
      fun K => (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K.obj.obj

/-- **An affine object of the site represents an absolutely quasi-separated algebraic space**
(Stacks 03JX, condition (ι), and 03BS (3)).  AxiomMath:
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS hZ T hT`
(`Spaces/AbsolutelyQuasiSeparatedAffine.lean`), verbatim.  Used only for non-vacuity. -/
def AffineQuasiSeparatedInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (T : BigFppfOver B S hS)
    (_hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)),
    IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T)

/-- **A big fppf site contains the terminal scheme `Spec ℤ`.**  AxiomMath:
`AlgebraicGeometry.BigFppfSite.contains_terminal B` (`Spaces/FiniteEtaleAtlasQuasiSeparated.lean`),
verbatim (universally quantified over `B`).  It shows that the hypothesis
`hZ : B.Contains (⊤_ Scheme.{u})` of the inputs and headlines always holds; used only for
non-vacuity. -/
def ContainsTerminalInput : Prop :=
  ∀ B : BigFppfSite.{u}, B.Contains (⊤_ Scheme.{u})

/-- **Stacks 0GFI**, implication (7) ⇒ (1) (detecting boundedness below): for `X`
quasi-compact and quasi-separated, an object `E` of `D_QCoh(𝒪_X)` such that, for every compact
(equivalently perfect) object `P` of `D_QCoh(𝒪_X)`, `Hom(P[-i], E) = 0` for all `i ≪ 0`, is
bounded below.  AxiomMath:
`AlgebraicGeometry.Space.exists_isGE_of_lowHomVanishingOnCompact X hqc hqs E hE`
(`Spaces/Perfect/DetectingBoundedBelow.lean`), verbatim, with `LowHomVanishingOnCompact` and
`lowHomVanishing` written out (module docstring). -/
def Tag0GFIInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (_hqc : IsQuasiCompactSpace B S hS X.1)
    (_hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (_hE : ∀ P : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2, IsCompactObject.{u} P →
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P.obj⟦-i⟧ ⟶ E.obj)),
    ∃ a : ℤ, E.obj.IsGE a

/-- **A perfect object of `D(𝒪_X)` is bounded above** when `X` is quasi-compact (perfectness,
Stacks 08G5, checked on an affine étale cover; a step of the proof of Stacks 0GFI).  AxiomMath:
`AlgebraicGeometry.Space.exists_isLE_of_isPerfect hX E hE`
(`Spaces/Perfect/DetectingBoundedBelow.lean`), verbatim. -/
def PerfectBoundedAboveInput : Prop :=
  ∀ {X : AlgebraicSpaces B S hS} (_hX : IsQuasiCompactSpace B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (_hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E),
    ∃ m : ℤ, E.IsLE m

end RelativeFM.Spaces.Supported
