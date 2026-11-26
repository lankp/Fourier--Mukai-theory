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

/-!
# Neeman 2024, Theorem 3.2(i) in the affine models, from Stacks 09SR

Neeman, *Bounded `t`-structures on the category of perfect complexes*, Acta
Math. 233 (2024), **Theorem 3.2(i)** says that the compact objects of
`D_qc,Z(X)` are the perfect complexes supported on `Z`.  Since 26 November 2026
the project no longer assumes it (`results/NEEMAN_3_2.md` is the inventory of
where the tree used it).  This file proves the affine case `X = Spec A`, `Z = X`
that the tree's former interfaces `CompactPerfectInput A` (large-Hom model
`AffineD A`) and `SmallNeemanCompactToPerfectInput A H` (small-Hom model
`SmallAffineD A H`) asked for.  Those interfaces were deleted on
`wave5/neeman-prune` (maintainer, 26 November 2026); every declaration that took
one as a hypothesis now lives here, under its old name, with the Stacks 09SR
hypothesis `h09` in its place.  Neither GL26 nor LP26 cites 3.2(i) itself: LP26 Corollary 1.2
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

For the large-Hom model `AffineD A` the tag cannot be applied directly: its
antecedent `HasCoproducts.{u+1} (AffineD A)` asks for coproducts indexed by
`Type (u+1)`, which are not available.  Instead a compact object of `AffineD A`
is moved to the small model by `SmallHomM5.isCompactAb_of_equivalence_large_to_small`
(proved; large-Hom compactness controls the shrunken small index types), where
the small result applies, and `Perf` is transported back by
`CapstoneM6.smallPerf_affineQhComparison_iff` (proved).  So the large result uses
09SR only at the canonical small model `SmallAffineD A (affineSpaltensteinInput A)`.
The converse (perfect ⇒ compact) is the proved compactness of `A[0]` closed under
the thick envelope.

## What is assumed

Exactly one instance of Stacks 09SR per statement, the hypothesis `h09`.  No
Neeman input, no other Stacks tag.  A direct proof of compact ⇒ perfect (retract
of a finite stage of a K-projective cell replacement) would remove `h09`; the
tree's packages for that route (`SmallHomM5.SmallFilteredFreeModelInput`,
`SmallHomM5.SmallFiniteFreeImprovementInput`) are not inhabited, so it was not taken.

## Difference from the paper's statement

The paper's 3.2(i) is for `D_qc,Z(X)`, `X` a qcqs scheme; here `X = Spec A`,
`Z = X`, and `D_qc(Spec A)` is modelled by `D(A-Mod)`.  "Perfect" is the thick
envelope of `A[0]` (`Perf`, `SmallPerf`), which is the tree's convention; its
agreement with bounded finite-projective models is the separate 066S question
(not on a GL26/LP26 path; the Neeman-model input that used to carry it,
`AffinePerfect.NeemanAffineCompactModelInput`, was deleted).

## Relocated endpoints (`wave5/neeman-prune`)

Each of the following took `CompactPerfectInput A` or
`SmallNeemanCompactToPerfectInput A H`; each keeps its name and now takes `h09`
(`Tag09SRPaper (CanonicalSmallAffineD A)` in the large model,
`Tag09SRPaper (SmallAffineD A H)` in the small one):

* from `Scheme/AffineMain.lean`: `ringObject_isClassicalGeneratorOnCompacts_of_compactPerfectInput`,
  `affineCompactHomZeroAtTop_of_compactPerfectInput`,
  `satisfiesWA_of_neemanCompactPerfectInput` and the pinned
  `affine_theorem_1_1_neeman_only` (LP26 Theorem 1.1, `thm:glueing_weak_approx`,
  affine middle term);
* from `Scheme/PerfectField.lean`: `compact_iff_dbcoh_of_input`;
* from `Scheme/SmallAffineAssembly.lean`: `smallCompactHomZeroAtTop_of_neeman`,
  `affine_theorem_1_1_small_neeman_only`,
  `affine_theorem_1_1_small_standard_neeman_only`;
* from `Scheme/AffineCompactness.lean`: `NeemanM1.isCompactAb_iff_smallPerf_of_neeman`;
* from `Scheme/AffineNeemanEndpointM3.lean`:
  `AffineNeemanEndpointM3.small_compact_iff_smallPerf`,
  `AffineNeemanEndpointM3.small_affine_regularGenerator_package`.

The names still mention "Neeman"/"input"; renaming is left to the orchestrator.

In the large model `h09` is not needed for compact ⇒ `Perf`: the tree proves it
with no input (`Stacks07LT.M4.compactToPerfectInput_unconditional`,
`Scheme/M4Unconditional.lean`).  The large-model endpoints take `h09` here because
that is the hypothesis the maintainer authorized for the pinned
`affine_theorem_1_1_neeman_only`; dropping it is a one-line change per declaration.
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
(large-Hom) model `AffineD A = D(A-Mod)`.  Input: Stacks 09SR for the canonical
small model only.  Compactness is moved to the small model (only the
large-to-small direction is needed, and it is proved), and `Perf` back. -/
theorem perf_of_isCompactAb (A : Type u) [CommRing A]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A))
    {X : AffineD A} (hX : IsCompactAb X) : Perf A X := by
  let H := Spaltenstein.affineSpaltensteinInput A
  let E := CapstoneM6.affineQhComparison A H
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have hX' : IsCompactAb (E.functor.obj X) :=
    SmallHomM5.isCompactAb_of_equivalence_large_to_small E.functor hX
  exact (CapstoneM6.smallPerf_affineQhComparison_iff A H X).mp
    (smallPerf_of_isCompactAb A H h09 hX')

/-- The directed half as the (proved) interface `CompactToPerfectInput A`.  It is
also inhabited with no input by `Stacks07LT.M4.compactToPerfectInput_unconditional`. -/
theorem compactToPerfectInput (A : Type u) [CommRing A]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) : CompactToPerfectInput A where
  perfect_of_compact _ hX := perf_of_isCompactAb A h09 hX

/-- **Neeman 2024, Theorem 3.2(i)**, affine case, large-Hom model: compact ⇔
`Perf A`.  Perfect ⇒ compact is `RegularCompact.ringObject_isCompactAb` through
the thick envelope (no input). -/
theorem affine_neeman_3_2_i (A : Type u) [CommRing A]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) :
    ∀ X : AffineD A, IsCompactAb X ↔ Perf A X :=
  fun _ => ⟨perf_of_isCompactAb A h09,
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
`CompactToPerfectInput` supplied from Stacks 09SR. -/
theorem affine_regularGenerator_package (A : Type u) [CommRing A]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) :
    PaperM2.SatisfiesPaperWA (AffineD A) ∧
      NeemanPreferredM6.InPreferredClass (AffineD.standardTStructure A) ∧
      ∀ X : AffineD A, IsCompactAb X ↔ Perf A X :=
  AffineNeemanEndpointM3.affine_regularGenerator_package A
    (RegularCompact.ringObject_isCompactAb A) (compactToPerfectInput A h09)

end Large

end

end RelativeFM.Neeman32Inputs

/-! ### Relocated large-model endpoints (formerly in `AffineMain`, `PerfectField`) -/

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open OpenClosedCompletionW3 Neeman32Inputs

universe u uZ uU

noncomputable section

/-- Neeman 2024, Theorem 3.2(ii) with Stacks 09SR: the regular module classically
generates the compact objects of `D(A-Mod)`; compact objects lie in `Perf A`,
the thick envelope of `A[0]`.  Formerly took `CompactPerfectInput A`; now Stacks
09SR (`h09`) for the canonical small model. -/
theorem ringObject_isClassicalGeneratorOnCompacts_of_compactPerfectInput
    (A : Type u) [CommRing A] (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) :
    IsClassicalGeneratorOnCompacts (ringObject A) :=
  fun _ hX => perf_of_isCompactAb A h09 hX

/-- Every pair of compact objects of `D(A-Mod)` has eventually vanishing
positive Homs.  Compactness is turned into `Perf A` by Stacks 09SR (`h09`,
`perf_of_isCompactAb`); the vanishing itself is the proved
`perf_eventuallyHomZero` (the ring form of Stacks 09MB).  Formerly took
`CompactPerfectInput A`. -/
theorem affineCompactHomZeroAtTop_of_compactPerfectInput
    (A : Type u) [CommRing A] (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) :
    AffineCompactHomZeroAtTop A := by
  intro X Y hX hY
  exact perf_eventuallyHomZero A
    (perf_of_isCompactAb A h09 hX) (perf_of_isCompactAb A h09 hY)

section NeemanOnlyGluing

variable (A : Type u) [CommRing A]
  (DZ : Type uZ) (DU : Type uU)
  [Category.{u + 1} DZ] [Category.{u + 1} DU]
  [Preadditive DZ] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DU]

/-- **LP26 Theorem 1.1** (`thm:glueing_weak_approx`), reverse direction, affine
middle term `D(A-Mod)`.  The recollement, coproduct, normalization and
preferred-aisle fields are those of `SetupMainMinimal` and the coproduct package
`C`; the only other hypothesis is Stacks 09SR for the canonical small model
(`h09`), which replaces the former Neeman 2024, Theorem 3.2(i) interface
`CompactPerfectInput A`.  No eventual-vanishing hypothesis is used. -/
theorem satisfiesWA_of_neemanCompactPerfectInput
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) : SatisfiesWA (AffineD A) := by
  let _ : HasCoproducts.{u + 1} DZ := C.hasCoproductsZ
  let _ : HasCoproducts.{u + 1} (AffineD A) := C.hasCoproductsA
  let _ : HasCoproducts.{u + 1} DU := C.hasCoproductsU
  exact S.satisfiesWA_of_compactHomZeroAtTop
    (affineCompactHomZeroAtTop_of_compactPerfectInput A h09)

/-- **LP26 Theorem 1.1** (`thm:glueing_weak_approx`), affine middle term
`D(A-Mod)`: `D(A-Mod)` is weakly approximable iff the chosen compact generator
`G'` has eventually vanishing positive self-Homs.  Hypotheses: the setup `S`
(Setup 4.4), the coproduct package `C`, and Stacks 09SR for the canonical small
model (`h09`).  Neeman 2024, Theorem 3.2(i) is no longer a hypothesis: until
`wave5/neeman-prune` this theorem took `CompactPerfectInput A` in place of `h09`
(change authorized by the orchestrator).  The middle category's weak
approximability is not assumed.  In fact `h09` is dispensable here, since
compact ⇒ `Perf` is proved with no input
(`Stacks07LT.M4.compactToPerfectInput_unconditional`). -/
theorem affine_theorem_1_1_neeman_only
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) :
    SatisfiesWA (AffineD A) ↔ AffineEventualSelfVanishing S.G' := by
  have hvan := affineCompactHomZeroAtTop_of_compactPerfectInput A h09
  constructor
  · intro _
    exact hvan S.G' S.G' S.G'_compact S.G'_compact
  · intro _
    exact satisfiesWA_of_neemanCompactPerfectInput A DZ DU S C h09

end NeemanOnlyGluing

/-- Over a field, compact objects of `D(k-Mod)` are exactly those with bounded,
degreewise finite-dimensional cohomology: compact ⇔ `Perf k` from Stacks 09SR
(`affine_neeman_3_2_i`) and `Perf k = Dbcoh k` (`perf_iff_dbcoh`, proved).
Formerly took `CompactPerfectInput k`. -/
theorem compact_iff_dbcoh_of_input (k : Type u) [Field k]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD k))
    (X : AffineD k) : IsCompactAb.{u + 1} X ↔ Dbcoh k X :=
  (affine_neeman_3_2_i k h09 X).trans (perf_iff_dbcoh k X)

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
theorem smallCompactHomZeroAtTop_of_neeman (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H)) :
    CompactHomZeroAtTop (SmallAffineD A H) := by
  intro X Y hX hY
  exact smallPerf_eventuallyHomZero A H
    (Neeman32Inputs.smallPerf_of_isCompactAb A H h09 hX)
    (Neeman32Inputs.smallPerf_of_isCompactAb A H h09 hY)

/-- Compact objects of the small model are exactly `SmallPerf`, from Stacks 09SR
(`h09`); formerly took `SmallNeemanCompactToPerfectInput A H`. -/
theorem NeemanM1.isCompactAb_iff_smallPerf_of_neeman (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H))
    (X : SmallAffineD A H) : IsCompactAb X ↔ SmallPerf A H X :=
  Neeman32Inputs.smallAffine_neeman_3_2_i A H h09 X

/-- Compact objects are exactly `SmallPerf`, from Stacks 09SR (`h09`); the
converse uses the proved compactness of `A[0]`.  Formerly took
`SmallNeemanCompactToPerfectInput A H`. -/
theorem AffineNeemanEndpointM3.small_compact_iff_smallPerf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H))
    (X : SmallAffineD A H) : IsCompactAb X ↔ SmallPerf A H X :=
  NeemanM1.isCompactAb_iff_smallPerf_of_neeman A H h09 X

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
theorem affine_theorem_1_1_small_neeman_only
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
    (smallCompactHomZeroAtTop_of_neeman A H h09)

/-- **LP26 Theorem 1.1** (`thm:glueing_weak_approx`), small-Hom affine middle
term with the standard middle `t`-structure (`hgen` is the one Setup 4.4 field
to be stated for it).  The only other input is Stacks 09SR (`h09`), replacing
the former `SmallNeemanCompactToPerfectInput A H`. -/
theorem affine_theorem_1_1_small_standard_neeman_only
    (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hgen : (@DerivedCategory.TStructure.t (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)).le 0 =
        Coprod (shiftTail (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) 0))
    (h09 : Tag09SRPaper (SmallAffineD A H)) :
    SatisfiesWA (SmallAffineD A H) ↔ EventuallyHomZero S.G' S.G' :=
  affine_theorem_1_1_small_neeman_only A H DZ DU
    (S.replaceMiddleTStructure
      (@DerivedCategory.TStructure.t (ModuleCat.{u} A) _ _
        (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)) hgen)
    rfl h09

end Endpoint

end

end RelativeFM

/-! ### Non-vacuity

The only hypothesis is the Stacks 09SR instance `h09`, a theorem of
AxiomMath/Stacks (not provable in this tree without it).  The statements apply
over `ℤ`, where every other ingredient is a proved instance. -/

namespace RelativeFM.Neeman32Inputs

open RelativeWeakApprox CategoryTheory CategoryTheory.Limits OpenClosedCompletionW3

example (h09 : Tag09SRPaper (CanonicalSmallAffineD ℤ)) :
    ∀ X : AffineD ℤ, IsCompactAb X ↔ Perf ℤ X :=
  affine_neeman_3_2_i ℤ h09

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
#print axioms RelativeFM.ringObject_isClassicalGeneratorOnCompacts_of_compactPerfectInput
#print axioms RelativeFM.affineCompactHomZeroAtTop_of_compactPerfectInput
#print axioms RelativeFM.satisfiesWA_of_neemanCompactPerfectInput
#print axioms RelativeFM.affine_theorem_1_1_neeman_only
#print axioms RelativeFM.compact_iff_dbcoh_of_input
#print axioms RelativeFM.smallCompactHomZeroAtTop_of_neeman
#print axioms RelativeFM.NeemanM1.isCompactAb_iff_smallPerf_of_neeman
#print axioms RelativeFM.AffineNeemanEndpointM3.small_compact_iff_smallPerf
#print axioms RelativeFM.AffineNeemanEndpointM3.small_affine_regularGenerator_package
#print axioms RelativeFM.affine_theorem_1_1_small_neeman_only
#print axioms RelativeFM.affine_theorem_1_1_small_standard_neeman_only
