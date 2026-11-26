/-
Unconditional affine compact-to-perfect in the large-Hom derived category.

Dependencies, all proved in this campaign:
* `CompactBoundedAbove`: compactness forces bounded-above cohomology;
* `CompactToPerfectBoundedFree`: free bounded-above resolutions and 07LR
  factorization;
* `M4Improvement`: finite-free one-degree improvements.

No 066S retract-closure, Neeman input, Stacks interface or large-coproduct
assumption is used for compact-to-`Perf`.
-/
import FourierMukai.Scheme.M6LargeInputs
import FourierMukai.Scheme.M4Improvement

@[expose] public section

namespace RelativeFM.CapstoneM6

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- **Unconditional affine compact-to-perfect.**  Every compact object of the
unbounded derived category of a commutative ring lies in the thick triangulated
envelope of the regular module. -/
def compactToPerfectInput_unconditional (A : Type u) [CommRing A] :
    CompactToPerfectInput A :=
  compactToPerfectInput_of_finiteFreeImprovement A
    (Stacks07LT.M4.finiteFreeImprovementInputM4 A)

/-- Objectwise form of the unconditional theorem. -/
theorem isCompactAb_perf_unconditional (A : Type u) [CommRing A]
    (X : AffineD A) (hX : IsCompactAb X) : Perf A X :=
  (compactToPerfectInput_unconditional A).perfect_of_compact X hX

/-- Every compact object is a retract of an object represented by a bounded
complex of finitely generated projectives.  This is stronger than membership
in `Perf`, and does not use 066S. -/
def stacks07LTBoundedFactorizationInput_unconditional (A : Type u) [CommRing A] :
    Stacks07LT.Stacks07LTBoundedFactorizationInput A :=
  stacks07LTBoundedFactorizationInput_of_finiteFreeImprovement A
    (Stacks07LT.M4.finiteFreeImprovementInputM4 A)

/-- Compact-to-bounded-model needs exactly the independent 066S retract input.
No part of the forward `Perf` theorem above depends on this argument. -/
theorem stacks07LTCompactModelInput_of_retracts_unconditional
    (A : Type u) [CommRing A]
    (hR : (AffinePerfect.HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts) :
    Stacks07LTCompactModelInput A :=
  stacks07LTCompactModelInput_of_finiteFreeImprovement A
    (Stacks07LT.M4.finiteFreeImprovementInputM4 A) hR

end

end RelativeFM.CapstoneM6

#print axioms RelativeFM.CapstoneM6.compactToPerfectInput_unconditional
#print axioms RelativeFM.CapstoneM6.isCompactAb_perf_unconditional
#print axioms RelativeFM.CapstoneM6.stacks07LTBoundedFactorizationInput_unconditional
#print axioms RelativeFM.CapstoneM6.stacks07LTCompactModelInput_of_retracts_unconditional
