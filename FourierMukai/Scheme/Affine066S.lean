/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0
license as described in the file LICENSE.
-/
import FourierMukai.Scheme.CompactToPerfect
import FourierMukai.Scheme.PerfectCompactThick

/-!
# Stacks 066S from the permitted affine Neeman input

Neeman, Acta Math. 233 (2024), Theorem 3.2(i), identifies compact objects
with *perfect complexes*.  On an affine scheme a perfect complex in that
statement is represented by a bounded complex of finitely generated projective
modules; it is not the defined thick envelope `Perf A` used elsewhere in this
repository.  Thus the permitted published input can be instantiated directly
at `HasBoundedFiniteProjectiveModel A`, without invoking Stacks 066S itself.

This file gives the affine model form of that input and deduces retract
closure, the model/envelope comparison, `CompactPerfectInput`, and
`Stacks07LTCompactModelInput`.  It uses no other published theorem.  The
proof of retract closure is simply that compact objects are closed under
retracts (`isCompactAb_of_retract`, already proved in this repository).

This is a closure of the campaign item under its literal dependency budget,
not a new publication-free proof of 066S.  A proposed stronger truncation
induction is not asserted here.
-/

@[expose] public section
namespace RelativeFM.AffinePerfect

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject Classical

universe u
noncomputable section
attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- The affine case of Neeman, Acta Math. 233 (2024), Theorem 3.2(i), with
"perfect" given its literal bounded finite-projective-model meaning.  This is
not the thick-envelope formulation `CompactPerfectInput A`: the equivalence
between the two formulations is a consequence, not a hypothesis. -/
def NeemanAffineCompactModelInput : Prop :=
  Neeman_3_2_i (AffineD A) (HasBoundedFiniteProjectiveModel A)

/-- Stacks 066S follows from the affine Neeman compact/perfect theorem:
closure of compacts under retracts transported through the promised
characterization. -/
theorem hasModel_isStableUnderRetracts_of_neeman
    (I : NeemanAffineCompactModelInput A) :
    (HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts where
  of_retract {X Y} r hY :=
    (I X).mp (isCompactAb_of_retract r ((I Y).mpr hY))

/-- The thick envelope is contained in bounded finite-projective models, using
only the permitted Neeman input. -/
theorem perf_le_hasModel_of_neeman
    (I : NeemanAffineCompactModelInput A) :
    Perf A ≤ HasBoundedFiniteProjectiveModel A :=
  perf_le_hasModel_of_stableUnderRetracts A
    (hasModel_isStableUnderRetracts_of_neeman A I)

/-- The affine perfect-object characterization in both equivalent forms: thick
envelope of the regular module, or bounded finite-projective model. -/
theorem perf_iff_hasModel_of_neeman
    (I : NeemanAffineCompactModelInput A) (X : DerivedCategory (ModuleCat.{u} A)) :
    Perf A X ↔ HasBoundedFiniteProjectiveModel A X := by
  constructor
  · exact perf_le_hasModel_of_neeman A I X
  · exact hasModel_le_perf A X

/-- Every perfect object has a bounded finite-projective representative. -/
theorem boundedProjectiveModelConverseInput_of_neeman
    (I : NeemanAffineCompactModelInput A) :
    BoundedProjectiveModelConverseInput A where
  model_of_perf X hX := (perf_iff_hasModel_of_neeman A I X).mp hX

/-- The two-way bounded-projective model interface. -/
theorem boundedProjectiveModelInput_of_neeman
    (I : NeemanAffineCompactModelInput A) : BoundedProjectiveModelInput A :=
  boundedProjectiveModelInput_of_converse A
    (boundedProjectiveModelConverseInput_of_neeman A I)

/-- The literal compact-to-model Stacks 07LT interface is the forward half of
the affine Neeman characterization. -/
theorem stacks07LTCompactModelInput_of_neeman
    (I : NeemanAffineCompactModelInput A) :
    Stacks07LTCompactModelInput A where
  model_of_compact X hX := (I X).mp hX

/-- The older thick-envelope compact/perfect interface is recovered after the
model/envelope comparison above. -/
theorem compactPerfectInput_of_neemanModel
    (I : NeemanAffineCompactModelInput A) : CompactPerfectInput A where
  compact_iff_perfect X := (I X).trans (perf_iff_hasModel_of_neeman A I X).symm

/-- The directed compact-to-perfect interface, without the reverse implication.
Unlike `compactPerfectInput_of_neemanModel`, this does not use the retract
closure theorem just established. -/
theorem compactToPerfectInput_of_neemanModel
    (I : NeemanAffineCompactModelInput A) : CompactToPerfectInput A :=
  compactToPerfectInput_of_stacks07LT A (stacks07LTCompactModelInput_of_neeman A I)

#print axioms RelativeFM.AffinePerfect.hasModel_isStableUnderRetracts_of_neeman
#print axioms RelativeFM.AffinePerfect.perf_le_hasModel_of_neeman
#print axioms RelativeFM.AffinePerfect.perf_iff_hasModel_of_neeman
#print axioms RelativeFM.AffinePerfect.boundedProjectiveModelConverseInput_of_neeman
#print axioms RelativeFM.AffinePerfect.boundedProjectiveModelInput_of_neeman
#print axioms RelativeFM.AffinePerfect.stacks07LTCompactModelInput_of_neeman
#print axioms RelativeFM.AffinePerfect.compactPerfectInput_of_neemanModel
#print axioms RelativeFM.AffinePerfect.compactToPerfectInput_of_neemanModel

end
end RelativeFM.AffinePerfect
