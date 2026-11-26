/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.WeakApprox
import WeakApprox.EquivalenceInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# LP26 Theorem 1.1 for affine schemes

`AffineD A` is `D(A-Mod)`, the affine model of `D_qc(Spec A)`, with its canonical
`t`-structure.  `affine_theorem_1_1` states LP26 Theorem 1.1 in that model:

  `SatisfiesWA (AffineD A) ↔ AffineEventualSelfVanishing S.G'`

from `SetupMainMinimal`, explicit coproducts on the three categories, and Stacks
09SR as the only geometric input.  The two directions are separated
(`eventualSelfVanishing_of_satisfiesWA`, `satisfiesWA_of_affine_eventual`), there
is a version from pairwise compact vanishing
(`satisfiesWA_of_compactHomZeroAtTop`), and `AffineGluingInput` packages the data
so that `AffineGluingInput.satisfiesWA` is a non-vacuous instance; the transport
across the affine dictionary is `satisfiesWA_of_affineDictionary`.

Everything residual is explicit and sourced: weak approximability on the two
ends of the recollement, compact generation, coproducts, 09SR and the eventual
vanishing (Stacks Tag 09MB, proved for rings in `AffineMain`).  No trivial
recollement is manufactured.

Found by a member of the Ultramath run `smwuz1thx` (direction B4).
-/

@[expose] public section

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u uZ uU uQ

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The unbounded derived category of all `A`-modules, with the standard choice
of localization at quasi-isomorphisms.  Under B1's affine dictionary this is
the model for `D_qc(Spec A)`; this abbreviation itself makes no such geometric
claim.  With `A : Type u`, Mathlib places `ModuleCat.{u} A` in `Type (u+1)`;
using `HasDerivedCategory.standard` therefore gives the object and morphism
universe `u+1` below.  No unproved Hovey small-Hom refinement is assumed. -/
abbrev AffineD (A : Type u) [CommRing A] : Type (u + 1) :=
  DerivedCategory (ModuleCat.{u} A)

/-- The canonical cohomological `t`-structure on `D(A-Mod)`. -/
def AffineD.standardTStructure (A : Type u) [CommRing A] :
    TStructure (AffineD A) :=
  DerivedCategory.TStructure.t

/-- Stacks Tag 09SR, stated for `D(A-Mod)` in the exact form consumed by
`SetupMainMinimal.theorem_1_1`. -/
def AffineStacks09SR (A : Type u) [CommRing A] : Prop :=
  Stacks09SR (AffineD A)

/-- The eventual positive self-Hom vanishing of an object of `D(A-Mod)`, in the
sign convention of Lank--Pauwels Theorem 1.1. -/
def AffineEventualSelfVanishing {A : Type u} [CommRing A] (G : AffineD A) : Prop :=
  EventuallyHomZero G G

/-- Pairwise eventual positive Hom vanishing for compact objects of
`D(A-Mod)`.  For rings this is *proved* unconditionally
(`AffineMain.perf_eventuallyHomZero`, via the thick envelope of the regular
module); in the Stacks form of the general statement it is Tag 09MB, with
compacts = perfect from Tag 0AED. -/
def AffineCompactHomZeroAtTop (A : Type u) [CommRing A] : Prop :=
  CompactHomZeroAtTop (AffineD A)

section Categories

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

/-- The small-coproduct constructions needed by LP Theorem 1.1.  The middle
field is a real residual implementation obligation for `D(A-Mod)`: it should
be constructed from degree-wise direct sums of module complexes and their
descent through quasi-isomorphism localization. -/
structure AffineDerivedCoproducts where
  /-- Small coproducts on the closed/support end. -/
  hasCoproductsZ : HasCoproducts.{u + 1} DZ
  /-- Small coproducts on `D(A-Mod)`, supplied by the module-complex
  construction; not inferred by Mathlib 4.33.1. -/
  hasCoproductsA : HasCoproducts.{u + 1} (AffineD A)
  /-- Small coproducts on the open/localization end. -/
  hasCoproductsU : HasCoproducts.{u + 1} DU

/-- **Affine form of Lank--Pauwels Theorem 1.1.**  Given the minimal
recollement/`t`-structure setup with middle category `D(A-Mod)`, small
coproducts, and Stacks 09SR, `D(A-Mod)` is weakly approximable exactly when the
chosen middle compact generator has eventually zero positive self-shifts.

The weak approximation data on `DZ` and `DU`, compactness and generation of
`S.G'`, and all compactly generated `t`-structure identities are fields of `S`;
they are hypotheses of this equivalence, not consequences derived here. -/
theorem affine_theorem_1_1
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (h09SR : AffineStacks09SR A) :
    SatisfiesWA (AffineD A) ↔ AffineEventualSelfVanishing S.G' := by
  let _ : HasCoproducts.{u + 1} DZ := C.hasCoproductsZ
  let _ : HasCoproducts.{u + 1} (AffineD A) := C.hasCoproductsA
  let _ : HasCoproducts.{u + 1} DU := C.hasCoproductsU
  exact S.theorem_1_1 h09SR

/-- Forward direction of affine Theorem 1.1: weak approximability forces the
chosen compact generator's positive self-Hom to vanish eventually. -/
theorem eventualSelfVanishing_of_satisfiesWA
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (h09SR : AffineStacks09SR A)
    (hWA : SatisfiesWA (AffineD A)) : AffineEventualSelfVanishing S.G' :=
  (affine_theorem_1_1 A DZ DU S C h09SR).mp hWA

/-- Reverse direction of affine Theorem 1.1, with the exact self-vanishing
cutoff displayed. -/
theorem satisfiesWA_of_affine_eventual
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (h09SR : AffineStacks09SR A)
    (hG' : AffineEventualSelfVanishing S.G') : SatisfiesWA (AffineD A) :=
  (affine_theorem_1_1 A DZ DU S C h09SR).mpr hG'

/-- Reverse direction using the published pairwise compact boundedness input
instead of assuming self-vanishing separately.  For a ring,
`AffineCompactHomZeroAtTop A` is supplied by
`affineCompactHomZeroAtTop` (`Scheme/Neeman32Inputs.lean`) with no input:
compact ⇒ `Perf` is `Stacks07LT.M4.perf_of_compact_unconditional` and the
vanishing is `perf_eventuallyHomZero`.  The Stacks form of the general statement is
Tag 09MB. -/
theorem satisfiesWA_of_compactHomZeroAtTop
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (h09SR : AffineStacks09SR A)
    (hvan : AffineCompactHomZeroAtTop A) : SatisfiesWA (AffineD A) :=
  satisfiesWA_of_affine_eventual A DZ DU S C h09SR
    (hvan S.G' S.G' S.G'_compact S.G'_compact)

/-- Complete input for the reverse, gluing half of affine Theorem 1.1.  No
field is vacuous and no field asserts the desired weak approximability of the
middle category. -/
structure AffineGluingInput where
  /-- The coproduct constructions on all three categories. -/
  coproducts : AffineDerivedCoproducts A DZ DU
  /-- Minimal Setup 4.4, including the six-functor recollement, weak
  approximation on both ends, the middle compact generator, its normalization,
  and the three compact-generated aisle identifications. -/
  setup : SetupMainMinimal DZ (AffineD A) DU
  /-- Stacks Tag 09SR for the affine middle category. -/
  h09SR : AffineStacks09SR A
  /-- Eventual positive self-Hom vanishing of the selected middle generator:
  for a ring this holds with no input at all (`AffineMain.perf_eventuallyHomZero`);
  in the Stacks form of the general statement it is Tag 09MB. -/
  eventual : AffineEventualSelfVanishing setup.G'

namespace AffineGluingInput

variable {A DZ DU}
variable (I : AffineGluingInput A DZ DU)

include I

/-- The selected compact generator in `D(A-Mod)`. -/
abbrev generator : AffineD A := I.setup.G'

/-- Compactness of the selected generator; this is a field of Setup 4.4, not a
new assertion proved from its name. -/
theorem generator_compact : IsCompactAb I.generator := I.setup.G'_compact

/-- Generation by the shifts of the selected generator. -/
theorem generator_generates : IsGenerator I.generator := I.setup.G'_generates

/-- **Affine weak approximability by gluing.**  This is the reverse implication
of LP Theorem 1.1 specialized to `D(A-Mod)`, and therefore supplies the weak
approximability input used by GL26 Remark 2.6 once B1 identifies the latter's
`D_qc(Spec A)` with `AffineD A`. -/
theorem satisfiesWA : SatisfiesWA (AffineD A) :=
  satisfiesWA_of_affine_eventual A DZ DU I.setup I.coproducts I.h09SR I.eventual

end AffineGluingInput

/-- Transport the affine gluing conclusion across an affine derived dictionary.
Here `F` is the functor supplied by B1's comparison
`D(A-Mod) ≃ D_qc(Spec A)`, and `DQ` is its chosen scheme-side model.  Exactness
(`F.IsTriangulated`), shift compatibility, additivity, being an equivalence, and
small coproducts on `DQ` are explicit inputs.  Equivalences preserve all existing
colimits, so no separate coproduct-preservation field is needed.

The conclusion is the categorical weak approximability used by GL26 Remark 2.6;
standard/preferred `t`-structure transport, if wanted, is separately available
as `satisfiesStandardWA_of_equivalence`. -/
theorem satisfiesWA_of_affineDictionary
    {DQ : Type uQ} [Category.{u + 1} DQ] [Preadditive DQ]
    [HasZeroObject DQ] [HasShift DQ ℤ]
    [∀ n : ℤ, (shiftFunctor DQ n).Additive]
    [Pretriangulated DQ] [CategoryTheory.IsTriangulated DQ]
    (I : AffineGluingInput A DZ DU)
    (F : AffineD A ⥤ DQ) [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (hF : F.IsEquivalence) (coproductsQ : HasCoproducts.{u + 1} DQ) :
    SatisfiesWA DQ := by
  let _ : HasCoproducts.{u + 1} (AffineD A) := I.coproducts.hasCoproductsA
  let _ : HasCoproducts.{u + 1} DQ := coproductsQ
  exact satisfiesWA_of_equivalence F hF I.satisfiesWA

end Categories

end

end RelativeFM
