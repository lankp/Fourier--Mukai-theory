import FourierMukai.Scheme.M4Improvement
import FourierMukai.Scheme.CompactBoundedAbove
import FourierMukai.Scheme.CompactToPerfectBoundedFree

@[expose] public section

namespace RelativeFM.Stacks07LT.M4

open CategoryTheory CategoryTheory.Limits
open RelativeFM RelativeWeakApprox

universe uA

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable (A : Type uA) [CommRing A]

/-- Every compact object is bounded above, by the completed truncation
argument. -/
lemma exists_isLE_unconditional (X : AffineD A) (hX : IsCompactAb X) :
    ∃ d : ℤ, X.IsLE d := by
  exact RelativeFM.Stacks07LT.BoundedAboveM1.exists_isLE_of_isCompactAb A X hX

/-- The bounded finite-projective identity factorization of a compact object,
with all resolution, truncation, telescope and finite-free steps proved. -/
def stacks07LTBoundedFactorizationInput_unconditional :
    RelativeFM.Stacks07LT.Stacks07LTBoundedFactorizationInput A :=
  RelativeFM.Stacks07LT.M2.stacks07LTBoundedFactorizationInput_of_boundedAbove A
    (exists_isLE_unconditional A) (finiteFreeImprovementInputM4 A)

/-- **Compact objects are perfect, unconditionally, in the affine derived
category of every commutative ring.** -/
def compactToPerfectInput_unconditional : CompactToPerfectInput A :=
  RelativeFM.Stacks07LT.M2.compactToPerfectInput_of_boundedAbove A
    (exists_isLE_unconditional A) (finiteFreeImprovementInputM4 A)

/-- Every compact derived object lies in the thick triangulated envelope of the
regular module. -/
lemma perf_of_compact_unconditional {X : AffineD A} (hX : IsCompactAb X) :
    Perf A X :=
  (compactToPerfectInput_unconditional A).perfect_of_compact X hX

/-- Every compact derived object is a retract of an object with a bounded
finite-projective representative. This gives the model form immediately as
soon as Stacks 066S (retract closure of the strict model class) is supplied. -/
theorem model_of_compact_of_stableUnderRetracts_unconditional
    (hR : (AffinePerfect.HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts)
    {X : AffineD A} (hX : IsCompactAb X) :
    Nonempty (BoundedFiniteProjectiveModel A X) :=
  (AffinePerfect.model_of_perf_of_stableUnderRetracts A hR X
    (perf_of_compact_unconditional A hX))

/-- The strict-model compactness input, conditional only on the separately
named retract-closure theorem 066S. -/
def stacks07LTCompactModelInput_of_stableUnderRetracts_unconditional
    (hR : (AffinePerfect.HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts) :
    Stacks07LTCompactModelInput A :=
  RelativeFM.Stacks07LT.stacks07LTCompactModelInput_of_boundedFactorization A
    (stacks07LTBoundedFactorizationInput_unconditional A) hR

end
end RelativeFM.Stacks07LT.M4

#print axioms RelativeFM.Stacks07LT.M4.exists_isLE_unconditional
#print axioms RelativeFM.Stacks07LT.M4.stacks07LTBoundedFactorizationInput_unconditional
#print axioms RelativeFM.Stacks07LT.M4.compactToPerfectInput_unconditional
#print axioms RelativeFM.Stacks07LT.M4.perf_of_compact_unconditional
#print axioms RelativeFM.Stacks07LT.M4.model_of_compact_of_stableUnderRetracts_unconditional
#print axioms RelativeFM.Stacks07LT.M4.stacks07LTCompactModelInput_of_stableUnderRetracts_unconditional
