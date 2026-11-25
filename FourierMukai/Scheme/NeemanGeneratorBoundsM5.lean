/-
Generator bounds for the regular module in the affine derived category.

The large-Hom assertions at bound one are already in `AffineMain`.  This module
provides the general positive-bound forms and, more importantly, proves the
same assertions directly in the small-Hom model.  We do not use equivalence
invariance: `AffineD A` has Hom universe `u + 1`, while `SmallAffineD A H` has
Hom universe `u`, so `transportWeakApproximationData` does not apply.
-/
import FourierMukai.Scheme.SmallAffineAssembly

@[expose] public section

namespace RelativeFM.NeemanGeneratorM5

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u

noncomputable section

/-- The canonical `t`-structure on the small-Hom affine derived category. -/
noncomputable def smallStandardTStructure (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) : TStructure (SmallAffineD A H) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact DerivedCategory.TStructure.t

/-- The regular module belongs to every nonnegative standard aisle. -/
theorem ringObject_mem_standard_le_of_nonneg (A : Type u) [CommRing A]
    {n : ℤ} (hn : 0 ≤ n) :
    (AffineD.standardTStructure A).le n (ringObject A) :=
  (AffineD.standardTStructure A).le_monotone hn _
    (ringObject_mem_standard_le_zero A)

/-- Maps from the regular module to `D(A-Mod)^{≤ -n}` vanish for `n > 0`. -/
theorem ringObject_hom_zero_of_standard_le_neg_of_pos (A : Type u) [CommRing A]
    {n : ℤ} (hn : 0 < n) {Y : AffineD A}
    (hY : (AffineD.standardTStructure A).le (-n) Y)
    (f : ringObject A ⟶ Y) : f = 0 :=
  ringObject_hom_zero_of_standard_le_neg_one A
    ((AffineD.standardTStructure A).le_monotone (by omega) Y hY) f

/-- The regular module in the small-Hom model belongs to the standard aisle
in degree zero. -/
theorem smallRingObject_mem_standard_le_zero (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    (smallStandardTStructure A H).le 0 (smallRingObject A H) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  change DerivedCategory.TStructure.t.le 0 (smallRingObject A H)
  unfold smallRingObject
  rw [DerivedCategory.TStructure.t.le_iff_isLE]
  infer_instance

/-- The regular module in the small-Hom model belongs to every nonnegative
standard aisle. -/
theorem smallRingObject_mem_standard_le_of_nonneg (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {n : ℤ} (hn : 0 ≤ n) :
    (smallStandardTStructure A H).le n (smallRingObject A H) :=
  (smallStandardTStructure A H).le_monotone hn _
    (smallRingObject_mem_standard_le_zero A H)

/-- Projective-source vanishing against the strictly negative standard aisle,
directly in the small-Hom localization. -/
theorem smallRingObject_hom_zero_of_standard_le_neg_one
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    {Y : SmallAffineD A H}
    (hY : (smallStandardTStructure A H).le (-1) Y)
    (f : smallRingObject A H ⟶ Y) : f = 0 := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  change DerivedCategory.TStructure.t.le (-1) Y at hY
  let _ : Y.IsLE (-1) :=
    (DerivedCategory.TStructure.t.le_iff_isLE Y (-1)).mp hY
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE Y (-1)
  let _ : K.IsStrictlyLE (-1) := hK
  have hf : f ≫ e.hom = 0 :=
    DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
      (P := ModuleCat.of A A) (L := K) (i := 0) (f ≫ e.hom) (-1) (by omega)
  rw [← cancel_mono e.hom, hf, Limits.zero_comp]

/-- Maps from the small-Hom regular module to the `(-n)`-th standard aisle
vanish for every positive integer `n`. -/
theorem smallRingObject_hom_zero_of_standard_le_neg_of_pos
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    {n : ℤ} (hn : 0 < n) {Y : SmallAffineD A H}
    (hY : (smallStandardTStructure A H).le (-n) Y)
    (f : smallRingObject A H ⟶ Y) : f = 0 :=
  smallRingObject_hom_zero_of_standard_le_neg_one A H
    ((smallStandardTStructure A H).le_monotone (by omega) Y hY) f

/-- The two non-triangular generator fields of `WeakApproximationData`, at
the admissible bound `A = 1`, in the large-Hom model. -/
theorem ringObject_standard_bounds_at_one (A : Type u) [CommRing A] :
    (AffineD.standardTStructure A).le 1 (ringObject A) ∧
      ∀ {Y : AffineD A}, (AffineD.standardTStructure A).le (-1) Y →
        ∀ f : ringObject A ⟶ Y, f = 0 :=
  ⟨ringObject_mem_standard_le_of_nonneg A (by omega),
    fun hY f => ringObject_hom_zero_of_standard_le_neg_of_pos A (by omega) hY f⟩

/-- The two non-triangular generator fields of `WeakApproximationData`, at
the admissible bound `A = 1`, in the small-Hom model. -/
theorem smallRingObject_standard_bounds_at_one (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    (smallStandardTStructure A H).le 1 (smallRingObject A H) ∧
      ∀ {Y : SmallAffineD A H}, (smallStandardTStructure A H).le (-1) Y →
        ∀ f : smallRingObject A H ⟶ Y, f = 0 :=
  ⟨smallRingObject_mem_standard_le_of_nonneg A H (by omega),
    fun hY f => smallRingObject_hom_zero_of_standard_le_neg_of_pos A H (by omega) hY f⟩

end

end RelativeFM.NeemanGeneratorM5

#print axioms RelativeFM.NeemanGeneratorM5.ringObject_mem_standard_le_of_nonneg
#print axioms RelativeFM.NeemanGeneratorM5.ringObject_hom_zero_of_standard_le_neg_of_pos
#print axioms RelativeFM.NeemanGeneratorM5.smallRingObject_mem_standard_le_zero
#print axioms RelativeFM.NeemanGeneratorM5.smallRingObject_mem_standard_le_of_nonneg
#print axioms RelativeFM.NeemanGeneratorM5.smallRingObject_hom_zero_of_standard_le_neg_one
#print axioms RelativeFM.NeemanGeneratorM5.smallRingObject_hom_zero_of_standard_le_neg_of_pos
#print axioms RelativeFM.NeemanGeneratorM5.ringObject_standard_bounds_at_one
#print axioms RelativeFM.NeemanGeneratorM5.smallRingObject_standard_bounds_at_one
