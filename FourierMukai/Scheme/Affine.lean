/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.WeakApprox
import WeakApprox.EquivalenceInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The affine model `D(A-Mod)` of LP26 Theorem 1.1

`AffineD A` is `D(A-Mod)`, the affine model of `D_qc(Spec A)`, with its canonical
`t`-structure, together with the two vanishing predicates of LP26 Theorem 1.1
(`thm:weak_approx_via_gluing`) in that model (`AffineEventualSelfVanishing`,
`AffineCompactHomZeroAtTop`).

`AffineDerivedCoproducts` is kept only as the object of the refutation
`VacuityF1.isEmpty_affineDerivedCoproducts` (`Scheme/RefuteLargeCoproducts.lean`):
`HasCoproducts.{u+1} (AffineD A)` is false for every nonzero ring.  The affine
Theorem 1.1 endpoints that took it (`affine_theorem_1_1`, its two directions,
`satisfiesWA_of_compactHomZeroAtTop`, `AffineGluingInput`,
`satisfiesWA_of_affineDictionary`) and the `IsGenerator` form of 09SR they used
(`AffineStacks09SR`) were deleted in wave 6 (`results/OPEN_INPUTS.md` rows 1.15,
4.3, 4.5).  The paper forms are the `Paper*` endpoints.
-/
@[expose] public section

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u uZ uU

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

/-- Small coproducts, indexed by `Type (u+1)`, on the three categories of a
recollement with middle `D(A-Mod)`.  **Uninhabited for every nonzero ring `A`**
(`VacuityF1.isEmpty_affineDerivedCoproducts`, `Scheme/RefuteLargeCoproducts.lean`):
the field `hasCoproductsA` is false.  Kept only as the object of that refutation;
its consumers were deleted in wave 6. -/
structure AffineDerivedCoproducts where
  /-- Small coproducts on the closed/support end. -/
  hasCoproductsZ : HasCoproducts.{u + 1} DZ
  /-- Small coproducts on `D(A-Mod)`, supplied by the module-complex
  construction; not inferred by Mathlib 4.33.1. -/
  hasCoproductsA : HasCoproducts.{u + 1} (AffineD A)
  /-- Small coproducts on the open/localization end. -/
  hasCoproductsU : HasCoproducts.{u + 1} DU

end Categories

end

end RelativeFM
