/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.AffineMain
import WeakApprox.StatementAudit

/-! # Generation of the standard aisle for a ring (direction dD) -/

@[expose] public section

namespace RelativeFM.AisleGeneration.Ring

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The closure inclusion for a generator lying in the degree-zero aisle. -/
theorem coprod_shiftTail_le (t : TStructure C) (H : C) (hH : t.le 0 H) :
    Coprod (shiftTail H 0) ≤ t.le 0 := by
  letI (J : Type v) : (t.le 0).IsClosedUnderColimitsOfShape (Discrete J) :=
    TStructure.le_isClosedUnderColimitsOfShape t 0 (Discrete J)
  letI : (t.le 0).IsTriangulatedClosed₂ :=
    TStructure.le_isTriangulatedClosed₂ t 0
  apply Coprod.le
  rintro X ⟨n, hn, ⟨e⟩⟩
  have hshift : t.le (-n) (H⟦n⟧) := t.le_shift 0 n (-n) (by omega) H hH
  exact (t.le 0).prop_of_iso e.symm (t.le_monotone (by omega) _ hshift)

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- In the standard derived t-structure, the coproduct/extension closure of the
regular module's nonnegative shifts is contained in the aisle. -/
theorem standard_coprod_le (A : Type u) [CommRing A] :
    Coprod (shiftTail (ringObject A) 0) ≤ (AffineD.standardTStructure A).le 0 :=
  coprod_shiftTail_le _ _ (ringObject_mem_standard_le_zero A)

end

end RelativeFM.AisleGeneration.Ring

#print axioms RelativeFM.AisleGeneration.Ring.coprod_shiftTail_le
#print axioms RelativeFM.AisleGeneration.Ring.standard_coprod_le
