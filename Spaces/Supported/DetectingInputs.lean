/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Supported.Inputs
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZero
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupportEtaleRestriction
import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.SquareLocality
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplement
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.QcqsInduction
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
import StacksFrontier.AlgebraicGeometry.Spaces.Affine
import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
import StacksFrontier.AlgebraicGeometry.Duality.KoszulTruncatedOrthogonality
import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.Abstract
import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale

/-!
# Koszul objects and tagged AxiomMath inputs for the supported Stacks 0GFI

Inputs of `Spaces/Supported/Detecting.lean`, which proves the supported form of Stacks 0GFI
((7) ⇒ (1)) on `D_{QCoh,T}(𝒪_X)` (GL26 Lemma A.9, `lem:preferred_eq_class`, preferred-class
clause) by the induction of AxiomMath's proof of 0GFI
(`AlgebraicGeometry.Space.exists_isGE_of_lowHomVanishingOnCompact`,
`Spaces/Perfect/DetectingBoundedBelow.lean`) over elementary distinguished squares (Stacks 08GP).

## Written-out definitions

AxiomMath's Koszul objects (`AlgebraicGeometry.Space.koszul`), the vanishing condition
`AlgebraicGeometry.Space.VanishesWhereUnit` (`Spaces/CompactGeneration/KoszulDetection.lean`) and
the sieve `AlgebraicGeometry.Space.unitLocusSieve` (`Spaces/CompactGeneration/UnitLocus.lean`)
live in modules whose import closure contains `StacksFrontier.RingTheory.MilnorPatching.Relative`,
which `scripts/axiommath/spaces-imports.txt` keeps out of `Spaces`.  They are written out below
by their bodies, copied from AxiomMath (`koszulSp`, `VanishesWhereUnitSp`, `unitLocusSieveSp`,
`isMulCommutative_ringSheaf_smallEtaleSp`), and the inputs state AxiomMath's theorems with these
spellings; the discharge in `SpacesVerified` identifies each with AxiomMath's definition
(`koszulSp hX l = koszul hX l` by induction on `l`, each step `rfl`; the two others by `rfl`).
AxiomMath's `structureModule Z` (an `abbrev` for `SheafOfModules.unit _`) and
`QcohDerived B S hS Y` (an `abbrev`, written `qcohDerived Y` here) are written out by their
bodies, as in `Spaces/Supported/Inputs.lean`.  `koszulQuasicoherent hX l` is
`⟨koszul hX l, qcohDerived_koszul l⟩`; `KoszulCompactInput` quantifies over the proof of the
second component (a `Prop`), so its discharge is AxiomMath's theorem itself.

## Inputs

| input | AxiomMath declaration | AxiomMath file |
|---|---|---|
| `KoszulTorsionInput` | `exists_pow_smul_eq_zero_of_koszul` | `Spaces/CompactGeneration/KoszulDetection.lean` |
| `KoszulDetectionInput` | `isZero_homology_of_hom_koszul_eq_zero` | same |
| `KoszulQcohInput` | `qcohDerived_koszul` | same |
| `KoszulCompactInput` | `isCompactObject_koszulQuasicoherent` | same |
| `UnitLocusInput` | `exists_list_globalRing_unitLocus` | `Spaces/CompactGeneration/UnitLocus.lean` |
| `KoszulRestrictInput` | `isZero_restrictSnd_koszul` | `Spaces/CompactGeneration/GenerationStep.lean` |
| `VanishesWhereUnitInput` | `vanishesWhereUnit_of_isZero_restrict` | `Spaces/CompactGeneration/AffineLift.lean` |
| `EdsOpenQcInput` | `isQuasiCompact_edsOpenHom` | `Spaces/CompactGeneration/SquareQcqs.lean` |
| `EdsOpenQsInput` | `isQuasiSeparated_edsOpenHom` | same |
| `OpenCounitInput` | `isIso_etaleDerivedModuleAdjunction_counit_of_mono` | `Spaces/DerivedPushforwardEtaleBaseChange.lean` |
| `PushforwardQcohInput` | `qcohDerived_derivedModulePushforward_obj` (Stacks 08DW) | `Spaces/QuasicoherentDerivedDirectImage.lean` |
| `PerfectQcohInput` | `qcohDerived_of_isPerfect_derivedCategoryB` | `Spaces/Perfect/PerfectRetract.lean` |
| `RangeOpenInput` | `range_openSubspacesOrderIso_symm` | `Spaces/Perfect/ApproximationSquareGeometry.lean` |
| `PreimageQcInput` | `isQuasiCompact_openSubspacesOrderIso_symm_preimage` (03HF) | same |
| `ShriekSupportInput` | `cohomologySupportedOn_lowerShriek_of_preimage` (08HA) | `Spaces/Perfect/SupportedPerfectGenerator.lean` |
| `ShriekPerfectInput` | `isPerfect_lowerShriek_of_cohomologySupportedOn` (08GG) | `Spaces/Perfect/ApproximationExtensionByZero.lean` |
| `ShriekRestrictOpenInput` | `isZero_restrictOpen_derivedShriekEtale` (08HA) | `Spaces/CompactGeneration/ExcisionDerived.lean` |
| `Tag09IVInput` | `exists_isPerfect_retract_restrict_of_supported` (09IV) | `Spaces/Perfect/PerfectSupportedExtension.lean` |
| `SupportPullbackInput` | `cohomologySupportedOn_etaleModulePullback` | `Spaces/Perfect/SupportedLiftTransport.lean` |

(paths relative to `StacksFrontier/AlgebraicGeometry/`, AxiomMath commit `f56a316`.)  Each
statement is AxiomMath's verbatim up to the spellings above; the instance context is that of
AxiomMath's `Spaces/Perfect/DetectingBoundedBelow.lean` and `Spaces/Perfect/PerfectSupportedExtension.lean`
(`SheafOfModules.instAbelian` at priority 5000, `HasDerivedCategory.standard`, the sheafification
instances of the small étale site), in which AxiomMath's topos-level functors (`Rj_*`, `j_!`) and
the site-level objects carry the same instances.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Space
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

namespace RelativeFM.Spaces.Supported

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

attribute [local instance] pointTopology

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

section Koszul

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}

/-- The rings of sections of the structure sheaf of the small étale site are commutative
(AxiomMath's instance `isMulCommutative_ringSheaf_smallEtale`, written out; a `Prop`). -/
instance isMulCommutative_ringSheaf_smallEtaleSp (U : (smallEtaleRingedSite B S hS X hX).Cᵒᵖ) :
    IsMulCommutative
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj.obj U) :=
  ⟨⟨fun a b => (chartRing_commRing B S hS X hX U.unop).mul_comm a b⟩⟩

/-- The ring of global functions on `X` (AxiomMath's local notation `globalRing hX`). -/
abbrev globalRingSp (hX : IsAlgebraicSpace B S hS X) :=
  Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (AlgebraicGeometry.RingedSite.O (smallEtaleRingedSite _ _ _ _ hX)))

variable (hX) in
/-- **AxiomMath's Koszul object** `AlgebraicGeometry.Space.koszul hX l`, written out: `𝒪_X[0]` for
the empty list, and a cone of multiplication by `a` on the Koszul object of `l` for `a :: l`. -/
def koszulSp : List (globalRingSp hX) → DerivedCategory (Space.Modules.{u, u} B S hS X hX)
  | [] => (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)
  | a :: l => (distinguished_cocone_triangle (a • 𝟙 (koszulSp l))).choose

/-- The distinguished triangle `K(l) ⟶ K(l) ⟶ K(a :: l) ⟶ K(l)⟦1⟧` defining a Koszul object
(AxiomMath's `exists_distTriang_koszul_cons`, proved here from the definition). -/
theorem exists_distTriang_koszulSp_cons (a : globalRingSp hX) (l : List (globalRingSp hX)) :
    ∃ (g : koszulSp hX l ⟶ koszulSp hX (a :: l))
      (h : koszulSp hX (a :: l) ⟶ (koszulSp hX l)⟦(1 : ℤ)⟧),
      Triangle.mk (a • 𝟙 (koszulSp hX l)) g h ∈ distTriang _ :=
  (distinguished_cocone_triangle (a • 𝟙 (koszulSp hX l))).choose_spec

/-- **AxiomMath's `VanishesWhereUnit a M`**, written out: on every chart where `a` becomes a
unit, every cohomology sheaf of `M` has no nonzero section. -/
def VanishesWhereUnitSp (a : globalRingSp hX)
    (M : DerivedCategory (Space.Modules.{u, u} B S hS X hX)) : Prop :=
  ∀ (U : SmallEtale B S hS X), IsUnit (a.1 (op U)) → ∀ q : ℤ,
    Subsingleton (((DerivedCategory.homologyFunctor _ q).obj M).val.obj (op U))

end Koszul

section UnitLocus

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **AxiomMath's `unitLocusSieve hsq l U'`**, written out: the sieve on a chart `U'` of
`U ×_W V` of the charts over `U'` on which one of the global functions of `l` is a unit. -/
def unitLocusSieveSp (l : List (globalRingSp hsq.isAlgebraicSpace))
    (U' : SmallEtale B S hS (edsInter B S hS hsq).1) : Sieve U' where
  arrows Y _ := ∃ a ∈ l, IsUnit (a.1 (op ((smallEtalePostcomp B S hS (edsSnd B S hS hsq)
    (isEtale_edsSnd B S hS hsq)).obj Y)))
  downward_closed := by
    rintro Y Z - ⟨a, ha, hu⟩ g
    refine ⟨a, ha, ?_⟩
    have h := a.2 ((smallEtalePostcomp B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).map
      g).op
    exact h ▸ hu.map (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V
      hsq.isAlgebraicSpace).O)).obj.map ((smallEtalePostcomp B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).map g).op).hom

end UnitLocus

/-- The category of `𝒪_X`-modules in AxiomMath's two spellings is the same (`rfl`). -/
theorem modules_eq_ringedToposModules {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (X : AlgebraicSpaces B S hS) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) =
      Space.Modules.{u, u} B S hS X.1 X.2 := rfl

/-! ### The inputs -/

section Inputs

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Torsion** (the étale-site form of a step of Stacks 09IR): every morphism from a Koszul object
into an object of `D_QCoh(𝒪_X)` vanishing where `a` is a unit is killed by a power of `a`, when
the small étale site of `X` has a final affine chart.  AxiomMath:
`AlgebraicGeometry.Space.exists_pow_smul_eq_zero_of_koszul T hT hTa a l M hM hloc x`, verbatim
(module docstring for the spellings). -/
def KoszulTorsionInput : Prop :=
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : SmallEtale B S hS X) (_hT : IsTerminal T) (_hTa : IsAffineChart B S hS X T)
    (a : globalRingSp hX) (l : List (globalRingSp hX))
    (M : DerivedCategory (Space.Modules.{u, u} B S hS X hX)),
    qcohDerived ⟨X, hX⟩ M → VanishesWhereUnitSp a M →
      ∀ x : koszulSp hX l ⟶ M, ∃ N : ℕ, a ^ N • x = 0

/-- **Graded Koszul detection**: for `M` in `D_QCoh(𝒪_X)` (final affine chart), vanishing where
each member of `l` is a unit, with every `K(l) ⟶ M⟦n⟧` zero for `n` in a set `D` of degrees,
`H^q(M) = 0` for `q ∈ D`.  AxiomMath:
`AlgebraicGeometry.Space.isZero_homology_of_hom_koszul_eq_zero T hT hTa D`, verbatim. -/
def KoszulDetectionInput : Prop :=
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : SmallEtale B S hS X) (_hT : IsTerminal T) (_hTa : IsAffineChart B S hS X T)
    (D : ℤ → Prop) (l : List (globalRingSp hX))
    (M : DerivedCategory (Space.Modules.{u, u} B S hS X hX)),
    qcohDerived ⟨X, hX⟩ M → (∀ b ∈ l, VanishesWhereUnitSp b M) →
      (∀ n : ℤ, D n → ∀ x : koszulSp hX l ⟶ M⟦n⟧, x = 0) →
      ∀ q : ℤ, D q → IsZero ((DerivedCategory.homologyFunctor _ q).obj M)

/-- **Koszul objects have quasi-coherent cohomology.**  AxiomMath:
`AlgebraicGeometry.Space.qcohDerived_koszul l`, verbatim. -/
def KoszulQcohInput : Prop :=
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (l : List (globalRingSp hX)), qcohDerived ⟨X, hX⟩ (koszulSp hX l)

/-- **Koszul objects are compact in `D_QCoh(𝒪_X)`** (final affine chart).  AxiomMath:
`AlgebraicGeometry.Space.isCompactObject_koszulQuasicoherent T hT hTa l`, verbatim, with
`koszulQuasicoherent hX l = ⟨koszul hX l, qcohDerived_koszul l⟩` written out and the proof of
quasi-coherence quantified (a `Prop`; module docstring). -/
def KoszulCompactInput : Prop :=
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : SmallEtale B S hS X) (_hT : IsTerminal T) (_hTa : IsAffineChart B S hS X T)
    (l : List (globalRingSp hX)) (h : qcohDerived ⟨X, hX⟩ (koszulSp hX l)),
    IsCompactObject.{u} (⟨koszulSp hX l, h⟩ : Space.QuasicoherentDerivedCategory.{u, u} B S hS X hX)

/-- **The intersection of an elementary distinguished square is a finite union of unit loci**
(Stacks 0859 (1) on the affine member): there is a list `l` of global functions on `V` such that
(a) a chart of `V` on which a member of `l` is a unit lies over `U ×_W V`, and (b) every chart of
`U ×_W V` is covered by charts on which a member of `l` is a unit.  AxiomMath:
`AlgebraicGeometry.Space.exists_list_globalRing_unitLocus B S hS hsq hZ hV hU hW`, verbatim. -/
def UnitLocusInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {W : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (_hV : IsAffineSpace B S hS V) (_hU : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (_hW : IsAbsolutelyQuasiSeparated B S hS hZ W.1),
    ∃ l : List (globalRingSp hsq.isAlgebraicSpace),
      (∀ U : SmallEtale B S hS V, (∃ a ∈ l, IsUnit (a.1 (op U))) →
        ∃ U' : SmallEtale B S hS (edsInter B S hS hsq).1,
          Nonempty ((smallEtalePostcomp B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)).obj U' ≅ U)) ∧
      ∀ U' : SmallEtale B S hS (edsInter B S hS hsq).1,
        unitLocusSieveSp B S hS hsq l U' ∈
          SmallEtale.topology B S hS (edsInter B S hS hsq).1 U'

/-- **The Koszul object of functions whose unit loci cover `U ×_W V` vanishes there.**
AxiomMath: `AlgebraicGeometry.Space.isZero_restrictSnd_koszul hsq l hb`, verbatim. -/
def KoszulRestrictInput : Prop :=
  ∀ {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1}
    {fV : V ⟶ W.1} (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (l : List (Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS V hsq.isAlgebraicSpace).O))))
    (_hb : ∀ U' : SmallEtale B S hS (edsInter B S hS hsq).1,
      unitLocusSieveSp B S hS hsq l U' ∈ SmallEtale.topology B S hS (edsInter B S hS hsq).1 U'),
    IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).mapDerivedCategory.obj (koszulSp hsq.isAlgebraicSpace l))

/-- **Vanishing where a function is a unit, from vanishing on an étale `Y ⟶ X`** covering the
unit loci.  AxiomMath: `AlgebraicGeometry.Space.vanishesWhereUnit_of_isZero_restrict j hj l hl N
hNY`, verbatim. -/
def VanishesWhereUnitInput : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (j : Y ⟶ X) (hj : IsEtale B S hS j.hom)
    (l : List (Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (_hl : ∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
      ∃ U' : SmallEtale B S hS Y.1, Nonempty ((smallEtalePostcomp B S hS j hj).obj U' ≅ U))
    (N : DerivedCategory (Space.Modules.{u, u} B S hS X.1 X.2))
    (_hNY : IsZero ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj N)),
    ∀ a ∈ l, VanishesWhereUnitSp a N

/-- **The open immersion of an elementary distinguished square is quasi-compact** when `U` is
quasi-compact and `W` quasi-separated.  AxiomMath:
`AlgebraicGeometry.Space.isQuasiCompact_edsOpenHom B S hS hZ hsq hWqs hUqc`, verbatim. -/
def EdsOpenQcInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {W : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (_hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (_hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor),
    IsQuasiCompact B S hS (edsOpenHom B S hS hsq).hom

/-- **The open immersion of an elementary distinguished square is quasi-separated.**
AxiomMath: `AlgebraicGeometry.Space.isQuasiSeparated_edsOpenHom B S hS hsq`, verbatim. -/
def EdsOpenQsInput : Prop :=
  ∀ {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1}
    {fV : V ⟶ W.1} (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV),
    IsQuasiSeparated B S hS (edsOpenHom B S hS hsq).hom

/-- **The counit of `(-)|_U ⊣ Rj_*` is invertible for an open immersion** (an étale
monomorphism).  AxiomMath:
`AlgebraicGeometry.Space.isIso_etaleDerivedModuleAdjunction_counit_of_mono j hj`, verbatim. -/
def OpenCounitInput : Prop :=
  ∀ {U X : AlgebraicSpaces B S hS} (j : U ⟶ X) (hj : IsEtale B S hS j.hom) [Mono j],
    IsIso (etaleDerivedModuleAdjunction B S hS j hj).counit

/-- **Stacks 08DW** for algebraic spaces: for `f` quasi-compact and quasi-separated, `Rf_*`
carries `D_QCoh` into `D_QCoh`.  AxiomMath:
`AlgebraicGeometry.Space.qcohDerived_derivedModulePushforward_obj f hfqc hfqs E hE`, verbatim, with
the abbreviation `derivedModulePushforward B S hS f` written out by its body. -/
def PushforwardQcohInput : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (_hfqc : IsQuasiCompact B S hS f.hom)
    (_hfqs : IsQuasiSeparated B S hS f.hom)
    (E : DerivedCategory (Space.Modules.{u, u} B S hS X.1 X.2)) (_hE : qcohDerived X E),
    qcohDerived Y ((derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj E)

/-- **A perfect object of `D(𝒪_X)` lies in `D_QCoh(𝒪_X)`.**  AxiomMath:
`AlgebraicGeometry.Space.qcohDerived_of_isPerfect_derivedCategoryB X E hE`, verbatim, with
AxiomMath's `SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)` written
`Modules.{u, u} B S hS X.1 X.2` (the same category by `rfl`: `modules_eq_ringedToposModules`;
AxiomMath's spelling does not find `HasDerivedCategory` outside AxiomMath's file). -/
def PerfectQcohInput : Prop :=
  ∀ (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (Space.Modules.{u, u} B S hS X.1 X.2))
    (_hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E),
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E

/-- **The points of the open subspace attached to `|X| ∖ T` form `|X| ∖ T`.**  AxiomMath:
`AlgebraicGeometry.Space.range_openSubspacesOrderIso_symm F hF T hT`, verbatim. -/
def RangeOpenInput : Prop :=
  ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (T : Set (points B S hS F)) (hT : IsClosed T),
    Set.range (pointsMap B S hS
      ((openSubspacesOrderIso B S hS F hF).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.toFunctor
      ((openSubspacesOrderIso B S hS F hF).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) = Tᶜ

/-- **Stacks 03HF** (base change of a quasi-compact open immersion): the complement of the
inverse image of a closed set with quasi-compact complement has quasi-compact inclusion.
AxiomMath: `AlgebraicGeometry.Space.isQuasiCompact_openSubspacesOrderIso_symm_preimage hX hY f T
hT hTqc hT'`, verbatim. -/
def PreimageQcInput : Prop :=
  ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ X)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (_hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (hT' : IsClosed (pointsMap B S hS Y f ⁻¹' T)),
    IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS Y hY).symm ⟨(pointsMap B S hS Y f ⁻¹' T)ᶜ,
        hT'.isOpen_compl⟩).1.ι

/-- **The extension by zero of an object supported over a closed `T` is supported on `T`**
(Stacks 08HA).  AxiomMath:
`AlgebraicGeometry.Space.cohomologySupportedOn_lowerShriek_of_preimage B S hS j hj T hT K hK`,
verbatim. -/
def ShriekSupportInput : Prop :=
  ∀ {X U : AlgebraicSpaces B S hS} (j : U ⟶ X) (hj : IsEtale B S hS j.hom)
    (T : Set (points B S hS X.1)) (_hT : IsClosed T)
    (K : DerivedCategory (Space.Modules.{u, u} B S hS U.1 U.2))
    (_hK : CohomologySupportedOn B S hS U.1 U.2 (pointsMap B S hS U.1 j.hom ⁻¹' T) K),
    CohomologySupportedOn B S hS X.1 X.2 T
      ((etaleModuleLowerShriek B S hS j hj).mapDerivedCategory.obj K)

/-- **The extension by zero of a perfect object supported on `f⁻¹(|W| ∖ |U|)` is perfect**
(Stacks 08GG (2)(a)).  AxiomMath:
`AlgebraicGeometry.Space.isPerfect_lowerShriek_of_cohomologySupportedOn B S hS hsq P hP hPs`,
verbatim. -/
def ShriekPerfectInput : Prop :=
  ∀ {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1}
    {fV : V ⟶ W.1} (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (P : DerivedCategory
      (Space.Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (_hP : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect P)
    (_hPs : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) P),
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect
      ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj P)

/-- **The extension by zero of `K` restricts to zero on `U` when `K` restricts to zero on
`U ×_W V`** (Stacks 08HA).  AxiomMath:
`AlgebraicGeometry.Space.isZero_restrictOpen_derivedShriekEtale B S hS hsq K hK`, verbatim, with the
abbreviations `edsDerivedRestrictSnd` and `edsDerivedShriekEtale` written out by their bodies. -/
def ShriekRestrictOpenInput : Prop :=
  ∀ {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1}
    {fV : V ⟶ W.1} (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (K : DerivedCategory
      (Space.Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (_hK : IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).mapDerivedCategory.obj K)),
    IsZero ((edsDerivedRestrictOpen B S hS hsq).obj
      ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj K))

/-- **Stacks 09IV**: for `X` qcqs, `W ⊆ X` a quasi-compact open, `T ⊆ |X|` closed with `X ∖ T ⟶ X`
quasi-compact, `E` in `D_QCoh(𝒪_X)` and `α : P ⟶ E|_W` with `P` perfect supported on `T ∩ W`,
there are `R` perfect supported on `T` and `β : R ⟶ E` with `P` a direct summand of `R|_W`
compatibly with `α`.  AxiomMath:
`AlgebraicGeometry.Space.exists_isPerfect_retract_restrict_of_supported hZ X hXqc hXqs W hW hWqc
T hT hTqc E P hP hPT α`, verbatim. -/
def Tag09IVInput : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (_hXqc : IsQuasiCompactSpace B S hS X.1) (_hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (_hWqc : IsQuasiCompactSpace B S hS W.toFunctor) (T : Set (points B S hS X.1))
    (hT : IsClosed T)
    (_hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (E : Space.QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (P : DerivedCategory (Space.Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2))
    (_hP : (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2).IsPerfect P)
    (_hPT : CohomologySupportedOn B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2 (pointsMap B S hS W.toFunctor W.ι ⁻¹' T) P)
    (α : P ⟶ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj E.obj),
    ∃ (R : DerivedCategory (Space.Modules.{u, u} B S hS X.1 X.2)) (β : R ⟶ E.obj),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect R ∧
      CohomologySupportedOn B S hS X.1 X.2 T R ∧
      ∃ (s : P ⟶ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R)
        (r : (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R ⟶ P),
        s ≫ r = 𝟙 P ∧
        s ≫ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β = α

/-- **Supports pull back along étale restriction.**  AxiomMath:
`AlgebraicGeometry.Space.cohomologySupportedOn_etaleModulePullback B S hS g hg T E hE`,
verbatim. -/
def SupportPullbackInput : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (T : Set (points B S hS X.1)) (E : DerivedCategory (Space.Modules.{u, u} B S hS X.1 X.2))
    (_hE : CohomologySupportedOn B S hS X.1 X.2 T E),
    CohomologySupportedOn B S hS Y.1 Y.2 (pointsMap B S hS Y.1 g.hom ⁻¹' T)
      ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E)

end Inputs

end RelativeFM.Spaces.Supported
