/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.AffineMain
import FourierMukai.Scheme.PerfectModel

/-!
# Affine compact/perfect input in Stacks form

The affine endpoint uses only the implication `compact ⇒ Perf`, not the full
compact ⇔ perfect biconditional.  This file makes that precise.

* `Stacks07LTCompactModelInput` is the compact-to-bounded-finite-projective
  direction of Stacks Tag **07LT** (Proposition 15.80.3).
* `compactToPerfectInput_of_stacks07LT` proves the corresponding implication
  into the thick envelope `Perf A`, using the already proved stupid-filtration
  theorem `AffinePerfect.model_mem_perf`.
* `affineCompactHomZeroAtTop_of_compactToPerfectInput` and
  `affine_theorem_1_1_stacks07LT` replace the old Bondal--Van den Bergh/Neeman
  interface by this one directed Stacks input.  No Stacks 09SR or separate
  Hom-vanishing input is used.
* `affine_perfectHomZero` is the affine form of Stacks Tag **09MB**
  (Lemma 75.17.2(2): `Ext^n(K,L) = 0` for all but finitely many `n` when `K` is
  perfect and `L` bounded); GL26 cites the same vanishing step to Tag **0GFH**.
  It is already a theorem for every commutative ring here, so it is not an
  input.

Stacks **09M1** (Proposition 36.17.1) is the qcqs-scheme compact/perfect
statement — biconditional, whose affine case reduces via **06Z0** to **07LT**;
the supported algebraic-space form is **0AED**.
The local scheme model is **08CM**, equivalently the finite-locally-free model
of **0BCJ**, already represented by `IsPerfectComplex` in `Scheme/Perfect.lean`.
Neither of those geometric definitions is silently identified here with the
ring thick envelope.

The reverse implication `Perf ⇒ IsCompactAb` is deliberately not claimed.  At
this toolchain it would require a derived-coproduct/Hom-coproduct argument in
addition to the model converse isolated elsewhere as Stacks 07LT input.
-/

@[expose] public section

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u uZ uU

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The compact-to-model half of Stacks **07LT**, stated without any
Bondal--Van den Bergh or Neeman input.

Stacks defines a perfect complex of modules by a bounded finite-projective
model.  The repository's `Perf A` is instead the thick envelope of `A[0]`;
the bridge from this model to that thick envelope is proved below, not added
as another hypothesis. -/
structure Stacks07LTCompactModelInput (A : Type u) [CommRing A] where
  /-- Every compact object has a bounded complex of finitely generated
  projective modules representing it (Stacks 07LT, compact ⇒ perfect). -/
  model_of_compact : ∀ X : AffineD A,
    IsCompactAb X → Nonempty (BoundedFiniteProjectiveModel A X)

/-- Only the implication actually consumed by the affine gluing theorem
(compact ⇒ `Perf A`, the forward half of Neeman 2024, Theorem 3.2(i) for
`D(A-Mod)`).

**This is a proved interface, not an assumption.**  It is inhabited for every
commutative ring with no input by `Stacks07LT.M4.compactToPerfectInput_unconditional`
(`Scheme/M4Unconditional.lean`; also `CapstoneM6.compactToPerfectInput_unconditional`),
restated as `Neeman32Inputs.compactToPerfectInput`.  Declarations
taking it as an argument are reductions; it is kept as a structure because the
proof of compact ⇒ `Perf` (`CompactToPerfect*.lean`, `M4Unconditional.lean`)
lies downstream of those reductions in the import graph. -/
structure CompactToPerfectInput (A : Type u) [CommRing A] where
  /-- Compact objects belong to the thick triangulated envelope of `A[0]`. -/
  perfect_of_compact : ∀ X : DerivedCategory (ModuleCat A),
    IsCompactAb X → Perf A X

/-- The other half of the old compact/perfect biconditional.  It is kept
separate because no theorem in this file proves it and the affine endpoint
never uses it. -/
structure PerfectToCompactInput (A : Type u) [CommRing A] where
  /-- Perfect complexes are compact (Stacks 07LT; for qcqs schemes also 09M1). -/
  compact_of_perfect : ∀ X : DerivedCategory (ModuleCat A),
    Perf A X → IsCompactAb X

/-- Stacks 07LT followed by the proved bounded-projective filtration gives the
precise compact-to-`Perf` implication. -/
theorem compactToPerfectInput_of_stacks07LT (A : Type u) [CommRing A]
    (I : Stacks07LTCompactModelInput A) : CompactToPerfectInput A where
  perfect_of_compact X hX :=
    AffinePerfect.model_mem_perf A X (I.model_of_compact X hX)

/-- The affine form of Stacks **09MB(2)** (and of the vanishing step that GL26
cites to **0GFH**): all but finitely many `Ext^n` from a perfect object to a
bounded one vanish.  This is a theorem, not a hypothesis: projective self-Ext
vanishing for `A` transports along the defining thick envelope of `Perf A`. -/
theorem affine_perfectHomZero (A : Type u) [CommRing A]
    {X Y : AffineD A} (hX : Perf A X) (hY : Perf A Y) :
    EventuallyHomZero X Y :=
  perf_eventuallyHomZero A hX hY

/-- The compact Hom-vanishing needed by LP follows from the single directed
compact-to-perfect input and the proved perfect Hom-vanishing. -/
theorem affineCompactHomZeroAtTop_of_compactToPerfectInput
    (A : Type u) [CommRing A] (I : CompactToPerfectInput A) :
    AffineCompactHomZeroAtTop A := by
  intro X Y hX hY
  exact affine_perfectHomZero A (I.perfect_of_compact X hX)
    (I.perfect_of_compact Y hY)

/-- The same vanishing with the literal compact-to-model Stacks 07LT input. -/
theorem affineCompactHomZeroAtTop_of_stacks07LT
    (A : Type u) [CommRing A] (I : Stacks07LTCompactModelInput A) :
    AffineCompactHomZeroAtTop A :=
  affineCompactHomZeroAtTop_of_compactToPerfectInput A
    (compactToPerfectInput_of_stacks07LT A I)

/-- With only compact ⇒ perfect, the regular module classically generates all
compacts: this is just the definition of `Perf A`. -/
theorem ringObject_isClassicalGeneratorOnCompacts_of_compactToPerfectInput
    (A : Type u) [CommRing A] (I : CompactToPerfectInput A) :
    IsClassicalGeneratorOnCompacts (ringObject A) := by
  intro X hX
  exact I.perfect_of_compact X hX

end

namespace StacksGluing

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

/-- Reverse affine LP gluing from the single compact-to-perfect implication.
The coproduct and minimal recollement fields remain explicit in `C` and `S`. -/
theorem satisfiesWA_of_compactToPerfectInput
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (I : CompactToPerfectInput A) : SatisfiesWA (AffineD A) := by
  let _ : HasCoproducts.{u + 1} DZ := C.hasCoproductsZ
  let _ : HasCoproducts.{u + 1} (AffineD A) := C.hasCoproductsA
  let _ : HasCoproducts.{u + 1} DU := C.hasCoproductsU
  exact S.satisfiesWA_of_compactHomZeroAtTop
    (affineCompactHomZeroAtTop_of_compactToPerfectInput A I)

/-- Affine LP Theorem 1.1 using only compact ⇒ perfect.  Neither the reverse
compactness implication nor Bondal--Van den Bergh nor Neeman is a hypothesis. -/
theorem affine_theorem_1_1_of_compactToPerfectInput
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (I : CompactToPerfectInput A) :
    SatisfiesWA (AffineD A) ↔ AffineEventualSelfVanishing S.G' := by
  have hvan := affineCompactHomZeroAtTop_of_compactToPerfectInput A I
  constructor
  · intro _
    exact hvan S.G' S.G' S.G'_compact S.G'_compact
  · intro _
    exact satisfiesWA_of_compactToPerfectInput A DZ DU S C I

/-- The affine endpoint with the literal Stacks **07LT** compact-to-model
input.  On a qcqs scheme this is the affine reduction of **09M1** via 06Z0.
The remaining hypotheses are exactly the coproduct package and Setup 4.4. -/
theorem affine_theorem_1_1_stacks07LT
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (I : Stacks07LTCompactModelInput A) :
    SatisfiesWA (AffineD A) ↔ AffineEventualSelfVanishing S.G' :=
  affine_theorem_1_1_of_compactToPerfectInput A DZ DU S C
    (compactToPerfectInput_of_stacks07LT A I)

end StacksGluing

end RelativeFM

#print axioms RelativeFM.compactToPerfectInput_of_stacks07LT
#print axioms RelativeFM.affine_perfectHomZero
#print axioms RelativeFM.affineCompactHomZeroAtTop_of_compactToPerfectInput
#print axioms RelativeFM.ringObject_isClassicalGeneratorOnCompacts_of_compactToPerfectInput
#print axioms RelativeFM.StacksGluing.satisfiesWA_of_compactToPerfectInput
#print axioms RelativeFM.StacksGluing.affine_theorem_1_1_of_compactToPerfectInput
#print axioms RelativeFM.StacksGluing.affine_theorem_1_1_stacks07LT
