/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.M6Transport
import FourierMukai.Scheme.SmallHomTransportM5
import FourierMukai.Scheme.OpenClosedCompletion
import FourierMukai.Scheme.AffineMain
import FourierMukai.Scheme.PerfectField
import FourierMukai.Scheme.AffineNeemanEndpointM3
import FourierMukai.Scheme.SmallAffineAssembly
import FourierMukai.Scheme.AffineSpaltenstein
import FourierMukai.Scheme.RegularCompact
import FourierMukai.Scheme.M4Unconditional

/-!
# Neeman 2024, Theorem 3.2(i) in the affine models

Neeman, *Bounded `t`-structures on the category of perfect complexes*, Acta
Math. 233 (2024), **Theorem 3.2(i)** says that the compact objects of
`D_qc,Z(X)` are the perfect complexes supported on `Z`.  Since 26 November 2026
the project no longer assumes it (`results/NEEMAN_3_2.md` is the inventory of
where the tree used it).  This file proves the affine case `X = Spec A`, `Z = X`
that the tree's former interfaces `CompactPerfectInput A` (large-Hom model
`AffineD A`) and `SmallNeemanCompactToPerfectInput A H` (small-Hom model
`SmallAffineD A H`) asked for.  Those interfaces were deleted on
`wave5/neeman-prune` (maintainer, 26 November 2026); every declaration that took
one as a hypothesis now lives here (renamed, see below): in the large-Hom model
with **no** hypothesis, in the small-Hom model with the Stacks 09SR hypothesis
`h09`.  Neither GL26 nor LP26 cites 3.2(i) itself: LP26 Corollary 1.2
(`cor:weak_approx_spaces`) cites 3.2(iii, iv) and GL26 Lemma A.9
(`lem:preferred_eq_class`) cites 3.2(iii).  The interfaces discharged here feed the
affine instances of LP26 Theorem 1.1 (`thm:glueing_weak_approx`) in the tree.

## Route (Ravenel--Neeman, via the tagged Stacks input)

* `A[0]` is compact (`NeemanM1.smallRingObject_isCompactAb`,
  `RegularCompact.ringObject_isCompactAb`, proved here before);
* `A[0]` detects zero (`NeemanGeneratorM5.Paper.smallRingObject_isPaperGenerator`,
  proved);
* the small model has `u`-small coproducts (`smallAffineHasCoproducts`, proved);
* **Stacks Tag 09SR** (2) ⇒ (1) for one generator, as the existing `Prop`
  `OpenClosedCompletionW3.Tag09SRPaper` (AxiomMath/Stacks
  `CategoryTheory.Pretriangulated.isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated`;
  row "09SR (open/closed glue, wave 3)" of `results/ASSUMPTIONS.md`), instantiated
  at the category `SmallAffineD A H`, says the compacts are in the thick envelope
  of `A[0]`, which is `SmallPerf A H` by definition.

That is the small-Hom route.  For the large-Hom model `AffineD A` no input is
needed: compact ⇒ `Perf A` is `Stacks07LT.M4.perf_of_compact_unconditional`
(`Scheme/M4Unconditional.lean`: compact ⇒ bounded above, free resolutions with the
07LR factorization, finite-free improvement; all proved).  The converse
(perfect ⇒ compact) is the proved compactness of `A[0]` closed under the thick
envelope, in both models.

## What is assumed

Large-Hom model: nothing.  Small-Hom model: exactly one instance of Stacks 09SR
per statement, the hypothesis `h09`, and no other input.  The small statement does
not follow from the large one by the existing transport: `SmallHomM5` proves only
large ⇒ small for compactness (`isCompactAb_of_equivalence_large_to_small`); the
direction needed here, small-Hom compactness ⇒ large-Hom compactness (coproducts
indexed by `Type (u+1)`), is the unproved `liftCompact` parameter of
`CapstoneM6.perfectToCompactInput_of_small`.  Proving it would remove `h09`.  (The
small-model inputs `SmallHomM5.SmallFilteredFreeModelInput` /
`SmallFiniteFreeImprovementInput`, never inhabited, were deleted in wave 6.)

## Difference from the paper's statement

The paper's 3.2(i) is for `D_qc,Z(X)`, `X` a qcqs scheme; here `X = Spec A`,
`Z = X`, and `D_qc(Spec A)` is modelled by `D(A-Mod)`.  "Perfect" is the thick
envelope of `A[0]` (`Perf`, `SmallPerf`), which is the tree's convention; its
agreement with bounded finite-projective models is the separate 066S question
(not on a GL26/LP26 path; the Neeman-model input that used to carry it,
`AffinePerfect.NeemanAffineCompactModelInput`, was deleted).

## Relocated endpoints (`wave5/neeman-prune`)

Each of the following took `CompactPerfectInput A` or
`SmallNeemanCompactToPerfectInput A H` (old name → new name):

* large model, now with **no** hypothesis (from `AffineMain`, `PerfectField`):
  `affine_theorem_1_1_neeman_only` (pinned; LP26 Theorem 1.1,
  `thm:glueing_weak_approx`) → `affine_theorem_1_1_unconditional`;
  `satisfiesWA_of_neemanCompactPerfectInput` → `affine_satisfiesWA_of_setup` (both
  deleted in wave 6: they took `AffineDerivedCoproducts`, which is uninhabited for
  `A ≠ 0`, `Scheme/RefuteLargeCoproducts.lean`);
  `affineCompactHomZeroAtTop_of_compactPerfectInput` → `affineCompactHomZeroAtTop`;
  `ringObject_isClassicalGeneratorOnCompacts_of_compactPerfectInput` →
  `ringObject_isClassicalGeneratorOnCompacts`;
  `compact_iff_dbcoh_of_input` → `compact_iff_dbcoh`;
* small model, with `h09 : Tag09SRPaper (SmallAffineD A H)` (from
  `SmallAffineAssembly`, `AffineCompactness`, `AffineNeemanEndpointM3`):
  `smallCompactHomZeroAtTop_of_neeman` → `smallCompactHomZeroAtTop_of_tag09SR`;
  `affine_theorem_1_1_small_neeman_only` → `affine_theorem_1_1_small_of_tag09SR`;
  `affine_theorem_1_1_small_standard_neeman_only` →
  `affine_theorem_1_1_small_standard_of_tag09SR`;
  `NeemanM1.isCompactAb_iff_smallPerf_of_neeman` →
  `NeemanM1.isCompactAb_iff_smallPerf_of_tag09SR`;
  `AffineNeemanEndpointM3.small_compact_iff_smallPerf` and
  `AffineNeemanEndpointM3.small_affine_regularGenerator_package` (names kept).
-/

@[expose] public section

namespace RelativeFM.Neeman32Inputs

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open OpenClosedCompletionW3

universe u uZ uU

noncomputable section

/-! ### The small-Hom model -/

/-- **Neeman 2024, Theorem 3.2(i)**, compact ⇒ perfect, in the small-Hom affine
model `SmallAffineD A H` (affine case, `Z = X`): every compact object lies in
`SmallPerf A H`, the thick envelope of `A[0]`.  The only input is Stacks 09SR
(`h09`) for this category; compactness and zero detection of `A[0]` and the
coproducts are proved. -/
theorem smallPerf_of_isCompactAb (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H))
    {X : SmallAffineD A H} (hX : IsCompactAb X) : SmallPerf A H X :=
  h09 (smallAffineHasCoproducts A H) (smallRingObject A H)
    (NeemanM1.smallRingObject_isCompactAb A H)
    (NeemanGeneratorM5.Paper.smallRingObject_isPaperGenerator A H) X hX

/-- **Neeman 2024, Theorem 3.2(i)**, small-Hom affine model, both directions:
compact ⇔ `SmallPerf A H`.  Compact ⇒ perfect from Stacks 09SR
(`smallPerf_of_isCompactAb`); perfect ⇒ compact is proved
(`NeemanM1.isCompactAb_of_smallPerf`). -/
theorem smallAffine_neeman_3_2_i (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H)) :
    ∀ X : SmallAffineD A H, IsCompactAb X ↔ SmallPerf A H X :=
  fun _ => ⟨smallPerf_of_isCompactAb A H h09, NeemanM1.isCompactAb_of_smallPerf A H⟩

/-! ### The large-Hom model -/

/-- The canonical small-Hom model of `D(A-Mod)`, built from the proved
Spaltenstein replacements. -/
abbrev CanonicalSmallAffineD (A : Type u) [CommRing A] : Type (u + 1) :=
  SmallAffineD A (Spaltenstein.affineSpaltensteinInput A)

section Large

/-- **Neeman 2024, Theorem 3.2(i)**, compact ⇒ perfect, in the standard
(large-Hom) model `AffineD A = D(A-Mod)`, **with no input**: this is
`Stacks07LT.M4.perf_of_compact_unconditional` (`Scheme/M4Unconditional.lean`:
compact ⇒ bounded above, free resolutions with the 07LR factorization, finite-free
improvement).  Until the second round of `wave5/neeman-prune` it was proved from
Stacks 09SR for the canonical small model via the large-to-small transport. -/
theorem perf_of_isCompactAb (A : Type u) [CommRing A]
    {X : AffineD A} (hX : IsCompactAb X) : Perf A X :=
  Stacks07LT.M4.perf_of_compact_unconditional A hX

/-- The directed half as the (proved) interface `CompactToPerfectInput A`, with no
input. -/
theorem compactToPerfectInput (A : Type u) [CommRing A] : CompactToPerfectInput A where
  perfect_of_compact _ hX := perf_of_isCompactAb A hX

/-- **Neeman 2024, Theorem 3.2(i)**, affine case, large-Hom model: compact ⇔
`Perf A`, with no input.  Perfect ⇒ compact is `RegularCompact.ringObject_isCompactAb`
through the thick envelope. -/
theorem affine_neeman_3_2_i (A : Type u) [CommRing A] :
    ∀ X : AffineD A, IsCompactAb X ↔ Perf A X :=
  fun _ => ⟨perf_of_isCompactAb A,
    isCompactAb_of_perf A (RegularCompact.ringObject_isCompactAb A)⟩

/-- **Neeman 2024, Theorem 3.2(ii)**, affine case, large-Hom model: `A[0]` is a
compact object detecting zero by its shifts.  No hypothesis.  (The deleted
template `Neeman_3_2_ii` used the stronger `IsGenerator`, which is false for
`A[0]` over `ℤ`, see `GeneratorCounterexampleM5`; the paper's notion is
`IsPaperGenerator`.) -/
theorem affine_neeman_3_2_ii (A : Type u) [CommRing A] :
    IsCompactAb (ringObject A) ∧ IsPaperGenerator (ringObject A) :=
  ⟨RegularCompact.ringObject_isCompactAb A,
    NeemanGeneratorM5.Paper.Modules.ringObject_isPaperGenerator A⟩

/-- The affine package of `RegularCompact.affine_regularGenerator_package`
(paper weak approximability, preferred class, compact ⇔ perfect) with its
`CompactToPerfectInput` supplied with no input. -/
theorem affine_regularGenerator_package (A : Type u) [CommRing A] :
    PaperM2.SatisfiesPaperWA (AffineD A) ∧
      NeemanPreferredM6.InPreferredClass (AffineD.standardTStructure A) ∧
      ∀ X : AffineD A, IsCompactAb X ↔ Perf A X :=
  AffineNeemanEndpointM3.affine_regularGenerator_package A
    (RegularCompact.ringObject_isCompactAb A) (compactToPerfectInput A)

end Large

end

end RelativeFM.Neeman32Inputs

/-! ### Large-model endpoints, unconditional (formerly in `AffineMain`, `PerfectField`) -/

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open Neeman32Inputs

universe u uZ uU

noncomputable section

/-- Neeman 2024, Theorem 3.2(ii) in `D(A-Mod)`: the regular module classically
generates the compact objects (they lie in `Perf A`, the thick envelope of
`A[0]`).  No hypothesis.  Formerly
`ringObject_isClassicalGeneratorOnCompacts_of_compactPerfectInput`, which took
`CompactPerfectInput A`. -/
theorem ringObject_isClassicalGeneratorOnCompacts (A : Type u) [CommRing A] :
    IsClassicalGeneratorOnCompacts (ringObject A) :=
  fun _ hX => perf_of_isCompactAb A hX

/-- Every pair of compact objects of `D(A-Mod)` has eventually vanishing
positive Homs; no hypothesis.  Compact ⇒ `Perf A` is `perf_of_isCompactAb`, the
vanishing is `perf_eventuallyHomZero` (the ring form of Stacks 09MB).  Formerly
`affineCompactHomZeroAtTop_of_compactPerfectInput`. -/
theorem affineCompactHomZeroAtTop (A : Type u) [CommRing A] :
    AffineCompactHomZeroAtTop A := by
  intro X Y hX hY
  exact perf_eventuallyHomZero A (perf_of_isCompactAb A hX) (perf_of_isCompactAb A hY)

/-- Over a field, compact objects of `D(k-Mod)` are exactly those with bounded,
degreewise finite-dimensional cohomology; no hypothesis (`affine_neeman_3_2_i`
and `perf_iff_dbcoh`).  Formerly `compact_iff_dbcoh_of_input`, which took
`CompactPerfectInput k`. -/
theorem compact_iff_dbcoh (k : Type u) [Field k] (X : AffineD k) :
    IsCompactAb.{u + 1} X ↔ Dbcoh k X :=
  (affine_neeman_3_2_i k X).trans (perf_iff_dbcoh k X)

end

end RelativeFM

/-! ### Relocated small-model endpoints (formerly in `SmallAffineAssembly`,
`AffineCompactness`, `AffineNeemanEndpointM3`) -/

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open OpenClosedCompletionW3

universe u uZ uU

noncomputable section

/-- Compact objects of the small model have eventually vanishing positive Homs:
compact ⇒ `SmallPerf` by Stacks 09SR (`h09`), then the proved
`smallPerf_eventuallyHomZero`.  Formerly took `SmallNeemanCompactToPerfectInput A H`. -/
theorem smallCompactHomZeroAtTop_of_tag09SR (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H)) :
    CompactHomZeroAtTop (SmallAffineD A H) := by
  intro X Y hX hY
  exact smallPerf_eventuallyHomZero A H
    (Neeman32Inputs.smallPerf_of_isCompactAb A H h09 hX)
    (Neeman32Inputs.smallPerf_of_isCompactAb A H h09 hY)

/-- Compact objects of the small model are exactly `SmallPerf`, from Stacks 09SR
(`h09`); formerly took `SmallNeemanCompactToPerfectInput A H`. -/
theorem NeemanM1.isCompactAb_iff_smallPerf_of_tag09SR (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H))
    (X : SmallAffineD A H) : IsCompactAb X ↔ SmallPerf A H X :=
  Neeman32Inputs.smallAffine_neeman_3_2_i A H h09 X

/-- Compact objects are exactly `SmallPerf`, from Stacks 09SR (`h09`); the
converse uses the proved compactness of `A[0]`.  Formerly took
`SmallNeemanCompactToPerfectInput A H`. -/
theorem AffineNeemanEndpointM3.small_compact_iff_smallPerf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H))
    (X : SmallAffineD A H) : IsCompactAb X ↔ SmallPerf A H X :=
  NeemanM1.isCompactAb_iff_smallPerf_of_tag09SR A H h09 X

/-- Weak approximability and preferred-class membership (both unconditional)
and compact ⇔ `SmallPerf` (from Stacks 09SR, `h09`) in the small-Hom model.
Formerly took `SmallNeemanCompactToPerfectInput A H`. -/
theorem AffineNeemanEndpointM3.small_affine_regularGenerator_package (A : Type u)
    [CommRing A] (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H)) :
    PaperM2.SatisfiesPaperWA (SmallAffineD A H) ∧
      NeemanPreferredM6.InPreferredClass (NeemanGeneratorM5.smallStandardTStructure A H) ∧
      ∀ X : SmallAffineD A H, IsCompactAb X ↔ SmallPerf A H X :=
  ⟨AffineNeemanEndpointM3.smallRegularModule_satisfiesPaperWA A H,
    AffineNeemanEndpointM3.smallRegularModule_preferred A H,
    AffineNeemanEndpointM3.small_compact_iff_smallPerf A H h09⟩

section Endpoint

variable (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
  (DZ : Type uZ) (DU : Type uU)
  [Category.{u} DZ] [Category.{u} DU]
  [Preadditive DZ] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DU]

/-- **LP26 Theorem 1.1** (`thm:glueing_weak_approx`), affine middle term in the
universe-correct small-Hom model, with `hT` identifying the middle `t`-structure
with the standard one.  The only input beyond `S` and `hT` is Stacks 09SR for
`SmallAffineD A H` (`h09`), replacing the former Neeman 2024, Theorem 3.2(i)
interface `SmallNeemanCompactToPerfectInput A H`.  No coproduct package. -/
theorem affine_theorem_1_1_small_of_tag09SR
    (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hT : S.tD = @DerivedCategory.TStructure.t (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H))
    (h09 : Tag09SRPaper (SmallAffineD A H)) :
    SatisfiesWA (SmallAffineD A H) ↔ EventuallyHomZero S.G' S.G' := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  letI : HasAisleCoproducts S.tD := by
    rw [hT]
    exact KProjectiveResolution.hasAisleCoproducts_standard (C := ModuleCat.{u} A)
  exact S.theorem_1_1_of_middleAisleCoproducts_of_compactHomZeroAtTop
    (smallCompactHomZeroAtTop_of_tag09SR A H h09)

/-- **LP26 Theorem 1.1** (`thm:glueing_weak_approx`), small-Hom affine middle
term with the standard middle `t`-structure (`hgen` is the one Setup 4.4 field
to be stated for it).  The only other input is Stacks 09SR (`h09`), replacing
the former `SmallNeemanCompactToPerfectInput A H`. -/
theorem affine_theorem_1_1_small_standard_of_tag09SR
    (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hgen : (@DerivedCategory.TStructure.t (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)).le 0 =
        Coprod (shiftTail (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) 0))
    (h09 : Tag09SRPaper (SmallAffineD A H)) :
    SatisfiesWA (SmallAffineD A H) ↔ EventuallyHomZero S.G' S.G' :=
  affine_theorem_1_1_small_of_tag09SR A H DZ DU
    (S.replaceMiddleTStructure
      (@DerivedCategory.TStructure.t (ModuleCat.{u} A) _ _
        (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)) hgen)
    rfl h09

end Endpoint

end

end RelativeFM

/-! ### Non-vacuity

The large-model statements have no hypothesis.  The only hypothesis of the
small-model ones is the Stacks 09SR instance `h09`, a theorem of AxiomMath/Stacks
(not provable in this tree without it); they apply over `ℤ`, where every other
ingredient is a proved instance. -/

namespace RelativeFM.Neeman32Inputs

open RelativeWeakApprox CategoryTheory CategoryTheory.Limits OpenClosedCompletionW3

example : ∀ X : AffineD ℤ, IsCompactAb X ↔ Perf ℤ X :=
  affine_neeman_3_2_i ℤ

example (h09 : Tag09SRPaper (CanonicalSmallAffineD ℤ)) :
    ∀ X : CanonicalSmallAffineD ℤ,
      IsCompactAb X ↔ SmallPerf ℤ (Spaltenstein.affineSpaltensteinInput ℤ) X :=
  smallAffine_neeman_3_2_i ℤ _ h09

/-- The hypothesis is not vacuous in the sense that its antecedent holds:
the canonical small model has `u`-small coproducts and `A[0]` there is compact and
detects zero, so `h09` is used at a genuine instance. -/
example : Nonempty (HasCoproducts.{0} (CanonicalSmallAffineD ℤ)) ∧
    IsCompactAb (smallRingObject ℤ (Spaltenstein.affineSpaltensteinInput ℤ)) ∧
    IsPaperGenerator (smallRingObject ℤ (Spaltenstein.affineSpaltensteinInput ℤ)) :=
  ⟨⟨smallAffineHasCoproducts ℤ _⟩, NeemanM1.smallRingObject_isCompactAb ℤ _,
    NeemanGeneratorM5.Paper.smallRingObject_isPaperGenerator ℤ _⟩

end RelativeFM.Neeman32Inputs

#print axioms RelativeFM.Neeman32Inputs.smallAffine_neeman_3_2_i
#print axioms RelativeFM.Neeman32Inputs.affine_neeman_3_2_i
#print axioms RelativeFM.Neeman32Inputs.affine_neeman_3_2_ii
#print axioms RelativeFM.Neeman32Inputs.compactToPerfectInput
#print axioms RelativeFM.Neeman32Inputs.affine_regularGenerator_package
#print axioms RelativeFM.ringObject_isClassicalGeneratorOnCompacts
#print axioms RelativeFM.affineCompactHomZeroAtTop
#print axioms RelativeFM.compact_iff_dbcoh
#print axioms RelativeFM.smallCompactHomZeroAtTop_of_tag09SR
#print axioms RelativeFM.NeemanM1.isCompactAb_iff_smallPerf_of_tag09SR
#print axioms RelativeFM.AffineNeemanEndpointM3.small_compact_iff_smallPerf
#print axioms RelativeFM.AffineNeemanEndpointM3.small_affine_regularGenerator_package
#print axioms RelativeFM.affine_theorem_1_1_small_of_tag09SR
#print axioms RelativeFM.affine_theorem_1_1_small_standard_of_tag09SR
