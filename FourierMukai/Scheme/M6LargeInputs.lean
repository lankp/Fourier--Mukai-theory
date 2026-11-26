/-
Large-Hom capstone after bounded-above and free-resolution/factorization.

Boundedness is `Scheme/CompactBoundedAbove`.  Free resolutions and bounded-free
factorizations are `CompactToPerfectBoundedFree`.  Thus compact-to-`Perf`
has exactly the
one-degree finite-free improvement left; compact-to-bounded-model additionally
uses the separately provided retract-closure theorem.
-/
import FourierMukai.Scheme.CompactToPerfectBoundedFree
import FourierMukai.Scheme.CompactBoundedAbove

@[expose] public section

namespace RelativeFM.CapstoneM6

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The bounded-above proof and the free-resolution/factorization package give
`BoundedFreeInductionInput` as soon as the one-degree improvement is supplied. -/
def boundedFreeInductionInput_of_finiteFreeImprovement
    (A : Type u) [CommRing A] (I : Stacks07LT.FiniteFreeImprovementInput A) :
    Stacks07LT.BoundedFreeInductionInput A :=
  Stacks07LT.M2.boundedFreeInductionInput_of_boundedAbove A
    (fun X hX => by
      obtain ⟨d, hd⟩ := Stacks07LT.BoundedAboveM1.exists_isLE_of_isCompactAb A X hX
      exact ⟨d, hd⟩) I

/-- Compact-to-`Perf`, with only finite-free improvement remaining. -/
theorem compactToPerfectInput_of_finiteFreeImprovement
    (A : Type u) [CommRing A] (I : Stacks07LT.FiniteFreeImprovementInput A) :
    CompactToPerfectInput A :=
  Stacks07LT.compactToPerfectInput_of_freeInduction A
    (boundedFreeInductionInput_of_finiteFreeImprovement A I)

/-- The stronger bounded finite-projective retract factorization, before the
066S/model-retract step. -/
def stacks07LTBoundedFactorizationInput_of_finiteFreeImprovement
    (A : Type u) [CommRing A] (I : Stacks07LT.FiniteFreeImprovementInput A) :
    Stacks07LT.Stacks07LTBoundedFactorizationInput A :=
  Stacks07LT.stacks07LTBoundedFactorizationInput_of_freeInduction A
    (boundedFreeInductionInput_of_finiteFreeImprovement A I)

/-- Full compact-to-bounded-finite-projective-model, with finite-free
improvement and model retract closure as the two remaining inputs. -/
theorem stacks07LTCompactModelInput_of_finiteFreeImprovement
    (A : Type u) [CommRing A] (I : Stacks07LT.FiniteFreeImprovementInput A)
    (hR : (AffinePerfect.HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts) :
    Stacks07LTCompactModelInput A :=
  Stacks07LT.stacks07LTCompactModelInput_of_freeInduction A
    (boundedFreeInductionInput_of_finiteFreeImprovement A I) hR

end

end RelativeFM.CapstoneM6

#print axioms RelativeFM.CapstoneM6.boundedFreeInductionInput_of_finiteFreeImprovement
#print axioms RelativeFM.CapstoneM6.compactToPerfectInput_of_finiteFreeImprovement
#print axioms RelativeFM.CapstoneM6.stacks07LTBoundedFactorizationInput_of_finiteFreeImprovement
#print axioms RelativeFM.CapstoneM6.stacks07LTCompactModelInput_of_finiteFreeImprovement
