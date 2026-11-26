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
that the tree's interfaces `CompactPerfectInput A` (large-Hom model `AffineD A`)
and `SmallNeemanCompactToPerfectInput A H` (small-Hom model `SmallAffineD A H`)
ask for.  Neither GL26 nor LP26 cites 3.2(i) itself: LP26 Corollary 1.2
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
(`AffinePerfect.NeemanAffineCompactModelInput`, not addressed here).
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

/-- **Neeman 2024, Theorem 3.2(i)** (compact ⇒ perfect), small-Hom affine model,
as the interface `SmallNeemanCompactToPerfectInput A H`, discharged from Stacks
09SR alone. -/
theorem smallNeemanCompactToPerfectInput (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H)) :
    SmallNeemanCompactToPerfectInput A H where
  perfect_of_compact _ hX := smallPerf_of_isCompactAb A H h09 hX

/-- **Neeman 2024, Theorem 3.2(i)**, small-Hom affine model, both directions, in
the template `Neeman_3_2_i` of `Scheme/Inputs.lean`. -/
theorem smallAffine_neeman_3_2_i (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H)) :
    Neeman_3_2_i (SmallAffineD A H) (SmallPerf A H) :=
  CapstoneM6.smallAffine_neeman_3_2_i A H (smallNeemanCompactToPerfectInput A H h09)

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

/-- **Neeman 2024, Theorem 3.2(i)**, affine case, large-Hom model: the interface
`CompactPerfectInput A` (compact ⇔ `Perf A`), discharged from Stacks 09SR for
the canonical small model.  Perfect ⇒ compact is
`RegularCompact.ringObject_isCompactAb` through the thick envelope (no input). -/
theorem compactPerfectInput (A : Type u) [CommRing A]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) : CompactPerfectInput A where
  compact_iff_perfect _ :=
    ⟨perf_of_isCompactAb A h09,
      isCompactAb_of_perf A (RegularCompact.ringObject_isCompactAb A)⟩

/-- The directed half as the interface `CompactToPerfectInput A`. -/
theorem compactToPerfectInput (A : Type u) [CommRing A]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) : CompactToPerfectInput A where
  perfect_of_compact _ hX := perf_of_isCompactAb A h09 hX

/-- **Neeman 2024, Theorem 3.2(i)**, large-Hom affine model, in the template
`Neeman_3_2_i`. -/
theorem affine_neeman_3_2_i (A : Type u) [CommRing A]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) :
    Neeman_3_2_i (AffineD A) (Perf A) :=
  (compactPerfectInput A h09).compact_iff_perfect

/-- **Neeman 2024, Theorem 3.2(ii)**, affine case, large-Hom model: `A[0]` is a
compact object detecting zero by its shifts.  No hypothesis.  (The template
`Neeman_3_2_ii` of `Scheme/Inputs.lean` uses the stronger `IsGenerator`, which is
false for `A[0]` over `ℤ`, see `AffineNeemanEndpointM3`; the paper's notion is
`IsPaperGenerator`.) -/
theorem affine_neeman_3_2_ii (A : Type u) [CommRing A] :
    IsCompactAb (ringObject A) ∧ IsPaperGenerator (ringObject A) :=
  ⟨RegularCompact.ringObject_isCompactAb A,
    NeemanGeneratorM5.Paper.Modules.ringObject_isPaperGenerator A⟩

/-- **Neeman 2024, Theorem 3.2(ii) with 09SR**: `A[0]` classically generates the
compact objects of `D(A-Mod)`. -/
theorem ringObject_isClassicalGeneratorOnCompacts (A : Type u) [CommRing A]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) :
    IsClassicalGeneratorOnCompacts (ringObject A) :=
  ringObject_isClassicalGeneratorOnCompacts_of_compactPerfectInput A
    (compactPerfectInput A h09)

/-! ### Endpoints that took `CompactPerfectInput A`, with it discharged -/

/-- Compact objects of `D(A-Mod)` have eventually vanishing positive Homs
(`AffineCompactHomZeroAtTop`), from Stacks 09SR only. -/
theorem affineCompactHomZeroAtTop (A : Type u) [CommRing A]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) : AffineCompactHomZeroAtTop A :=
  affineCompactHomZeroAtTop_of_compactPerfectInput A (compactPerfectInput A h09)

section Gluing

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

/-- **LP26 Theorem 1.1** (`thm:glueing_weak_approx`), affine middle term
`D(A-Mod)`: `affine_theorem_1_1_neeman_only` with its Neeman 3.2(i) argument
`CompactPerfectInput A` discharged by `compactPerfectInput`; the remaining
hypotheses are the setup `S`, the coproduct package `C` (as in the original),
and Stacks 09SR for the canonical small model. -/
theorem affine_theorem_1_1_of_tag09SR
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) :
    SatisfiesWA (AffineD A) ↔ AffineEventualSelfVanishing S.G' :=
  affine_theorem_1_1_neeman_only A DZ DU S C (compactPerfectInput A h09)

/-- The reverse direction of the preceding theorem
(`satisfiesWA_of_neemanCompactPerfectInput` with its input discharged). -/
theorem satisfiesWA_of_tag09SR
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) : SatisfiesWA (AffineD A) :=
  satisfiesWA_of_neemanCompactPerfectInput A DZ DU S C (compactPerfectInput A h09)

end Gluing

/-- The affine package of `RegularCompact.affine_regularGenerator_package`
(paper weak approximability, preferred class, compact ⇔ perfect) with its
`CompactToPerfectInput` discharged. -/
theorem affine_regularGenerator_package (A : Type u) [CommRing A]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD A)) :
    PaperM2.SatisfiesPaperWA (AffineD A) ∧
      NeemanPreferredM6.InPreferredClass (AffineD.standardTStructure A) ∧
      ∀ X : AffineD A, IsCompactAb X ↔ Perf A X :=
  AffineNeemanEndpointM3.affine_regularGenerator_package A
    (RegularCompact.ringObject_isCompactAb A) (compactToPerfectInput A h09)

/-- Over a field, compact objects of `D(k-Mod)` are exactly those with bounded,
degreewise finite-dimensional cohomology (`compact_iff_dbcoh_of_input` with its
input discharged). -/
theorem compact_iff_dbcoh (k : Type u) [Field k]
    (h09 : Tag09SRPaper (CanonicalSmallAffineD k))
    (X : AffineD k) : IsCompactAb.{u + 1} X ↔ Dbcoh k X :=
  compact_iff_dbcoh_of_input k (compactPerfectInput k h09) X

end Large

/-! ### Endpoints that took `SmallNeemanCompactToPerfectInput A H` -/

/-- Compact objects of the small model have eventually vanishing positive Homs,
from Stacks 09SR only. -/
theorem smallCompactHomZeroAtTop (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H)) :
    CompactHomZeroAtTop (SmallAffineD A H) :=
  smallCompactHomZeroAtTop_of_neeman A H (smallNeemanCompactToPerfectInput A H h09)

/-- Weak approximability, preferred class, and compact ⇔ `SmallPerf` in the
small-Hom model (`AffineNeemanEndpointM3.small_affine_regularGenerator_package`
with its input discharged). -/
theorem small_affine_regularGenerator_package (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (h09 : Tag09SRPaper (SmallAffineD A H)) :
    PaperM2.SatisfiesPaperWA (SmallAffineD A H) ∧
      NeemanPreferredM6.InPreferredClass (NeemanGeneratorM5.smallStandardTStructure A H) ∧
      ∀ X : SmallAffineD A H, IsCompactAb X ↔ SmallPerf A H X :=
  AffineNeemanEndpointM3.small_affine_regularGenerator_package A H
    (smallNeemanCompactToPerfectInput A H h09)

section SmallGluing

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

/-- **LP26 Theorem 1.1** (`thm:glueing_weak_approx`), small-Hom affine middle
term, with `hT` identifying the middle `t`-structure with the standard one:
`affine_theorem_1_1_small_neeman_only` with its Neeman input discharged. -/
theorem affine_theorem_1_1_small_of_tag09SR
    (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hT : S.tD = @DerivedCategory.TStructure.t (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H))
    (h09 : Tag09SRPaper (SmallAffineD A H)) :
    SatisfiesWA (SmallAffineD A H) ↔ EventuallyHomZero S.G' S.G' :=
  affine_theorem_1_1_small_neeman_only A H DZ DU S hT
    (smallNeemanCompactToPerfectInput A H h09)

/-- **LP26 Theorem 1.1**, small-Hom affine middle term with the standard middle
`t`-structure: `affine_theorem_1_1_small_standard_neeman_only` with its Neeman
input discharged. -/
theorem affine_theorem_1_1_small_standard_of_tag09SR
    (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hgen : (@DerivedCategory.TStructure.t (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)).le 0 =
        Coprod (shiftTail (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) 0))
    (h09 : Tag09SRPaper (SmallAffineD A H)) :
    SatisfiesWA (SmallAffineD A H) ↔ EventuallyHomZero S.G' S.G' :=
  affine_theorem_1_1_small_standard_neeman_only A H DZ DU S hgen
    (smallNeemanCompactToPerfectInput A H h09)

end SmallGluing

/-! ### Non-vacuity

The only hypothesis is the Stacks 09SR instance `h09`, a theorem of
AxiomMath/Stacks (not provable in this tree without it).  The statements apply
over `ℤ`, where every other ingredient is a proved instance. -/

example (h09 : Tag09SRPaper (CanonicalSmallAffineD ℤ)) : CompactPerfectInput ℤ :=
  compactPerfectInput ℤ h09

example (h09 : Tag09SRPaper (CanonicalSmallAffineD ℤ)) :
    SmallNeemanCompactToPerfectInput ℤ (Spaltenstein.affineSpaltensteinInput ℤ) :=
  smallNeemanCompactToPerfectInput ℤ _ h09

/-- The hypothesis is not vacuous in the sense that its antecedent holds:
the canonical small model has `u`-small coproducts and `A[0]` there is compact and
detects zero, so `h09` is used at a genuine instance. -/
example : Nonempty (HasCoproducts.{0} (CanonicalSmallAffineD ℤ)) ∧
    IsCompactAb (smallRingObject ℤ (Spaltenstein.affineSpaltensteinInput ℤ)) ∧
    IsPaperGenerator (smallRingObject ℤ (Spaltenstein.affineSpaltensteinInput ℤ)) :=
  ⟨⟨smallAffineHasCoproducts ℤ _⟩, NeemanM1.smallRingObject_isCompactAb ℤ _,
    NeemanGeneratorM5.Paper.smallRingObject_isPaperGenerator ℤ _⟩

end

end RelativeFM.Neeman32Inputs

#print axioms RelativeFM.Neeman32Inputs.smallNeemanCompactToPerfectInput
#print axioms RelativeFM.Neeman32Inputs.smallAffine_neeman_3_2_i
#print axioms RelativeFM.Neeman32Inputs.compactPerfectInput
#print axioms RelativeFM.Neeman32Inputs.affine_neeman_3_2_i
#print axioms RelativeFM.Neeman32Inputs.affine_neeman_3_2_ii
#print axioms RelativeFM.Neeman32Inputs.affine_theorem_1_1_of_tag09SR
#print axioms RelativeFM.Neeman32Inputs.affine_theorem_1_1_small_standard_of_tag09SR
#print axioms RelativeFM.Neeman32Inputs.affine_regularGenerator_package
