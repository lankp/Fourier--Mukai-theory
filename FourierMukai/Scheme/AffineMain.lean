/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.Affine
import FourierMukai.Scheme.PerfectRing
import FourierMukai.Scheme.Inputs
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-!
# Affine ingredients of LP26 Theorem 1.1 for `D(A-Mod)`

The vanishing half of the affine instance of LP26 Theorem 1.1
(`thm:glueing_weak_approx`) with middle term `D(A-Mod)`, proved with no input:

* `ringObject_eventuallyHomZero_self`: `Hom(A, A⟦n⟧) = 0` for `n ≥ 1`;
* `perf_eventuallyHomZero`: every pair of perfect complexes has eventually
  vanishing positive Homs, with no input at all — this is the ring form of
  Stacks Tag 09MB, proved from the thick-envelope transport
  (`eventuallyHomZero_of_mem_triangEnvelope`).

Also proved: the standard-`t`-structure bounds for the ring object
(`ringObject_mem_standard_le_zero`, `..._ge_zero`, `..._le_one`) and
`ringObject_hom_zero_of_standard_le_neg_one`.

The endpoint `affine_theorem_1_1_neeman_only` and the other declarations that
used to take the Neeman 2024, Theorem 3.2(i) interface `CompactPerfectInput A`
here were moved on `wave5/neeman-prune` to `Scheme/Neeman32Inputs.lean` and
renamed (the endpoint became `affine_theorem_1_1_unconditional`, since compact ⇒
`Perf` is proved in `Scheme/M4Unconditional.lean`); that endpoint was deleted in
wave 6, its coproduct hypothesis being uninhabited for `A ≠ 0`.  `CompactPerfectInput` was deleted
(`results/NEEMAN_3_2.md`).

Found by a member of the Ultramath run `smwv1bkrk` (direction AF6).
-/

@[expose] public section

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u uZ uU

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Positive self-extension groups of the regular module vanish. This is the
elementary affine computation behind the eventual-vanishing side of LP Theorem
1.1 for the ring generator; it uses projectivity of `A`, not Neeman's theorem. -/
theorem ringObject_eventuallyHomZero_self (A : Type u) [CommRing A] :
    EventuallyHomZero (ringObject A) (ringObject A) := by
  let _ : HasExt.{u + 1} (ModuleCat.{u} A) :=
    HasExt.standard (ModuleCat.{u} A)
  refine ⟨1, fun n hn f => ?_⟩
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n by omega)
  cases k with
  | zero => omega
  | succ k =>
      let e : Abelian.Ext.{u + 1} (ModuleCat.of A A) (ModuleCat.of A A) (k + 1) :=
        Abelian.Ext.homEquiv.symm f
      have he : e = 0 := Abelian.Ext.eq_zero_of_projective e
      have hz : Abelian.Ext.homEquiv e = 0 := by
        rw [he]
        exact Abelian.Ext.zero_hom (ModuleCat.of A A) (ModuleCat.of A A) (k + 1)
      exact (Abelian.Ext.homEquiv.apply_symm_apply f).symm.trans hz

end

end RelativeFM

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Every pair of perfect complexes of `A`-modules has eventually vanishing
positive Homs.  This is entirely proved: it transports the regular module's
projective self-Ext vanishing along the defining thick triangulated envelope of
`Perf A`.  No compact/perfect theorem, Stacks tag, or Noetherian hypothesis is
used. -/
theorem perf_eventuallyHomZero (A : Type u) [CommRing A]
    {X Y : AffineD A} (hX : Perf A X) (hY : Perf A Y) :
    EventuallyHomZero X Y := by
  exact eventuallyHomZero_of_mem_triangEnvelope
    (ringObject_eventuallyHomZero_self A) hX hY

end

end RelativeFM

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The regular module in cohomological degree zero belongs to the standard
aisle `D(A-Mod)^{≤0}`.  Proved from Mathlib's single-complex `t`-structure
instances. -/
theorem ringObject_mem_standard_le_zero (A : Type u) [CommRing A] :
    (AffineD.standardTStructure A).le 0 (ringObject A) := by
  change DerivedCategory.TStructure.t.le 0 (ringObject A)
  unfold ringObject
  rw [DerivedCategory.TStructure.t.le_iff_isLE]
  infer_instance

/-- The regular module in degree zero also belongs to `D(A-Mod)^{≥0}`. -/
theorem ringObject_mem_standard_ge_zero (A : Type u) [CommRing A] :
    (AffineD.standardTStructure A).ge 0 (ringObject A) := by
  change DerivedCategory.TStructure.t.ge 0 (ringObject A)
  unfold ringObject
  rw [DerivedCategory.TStructure.t.ge_iff_isGE]
  infer_instance

/-- Projective-source vanishing against the strictly negative standard aisle:
every map `A[0] ⟶ Y` is zero when `Y ∈ D(A-Mod)^{≤-1}`.  This is an elementary
module-complex proof, not an external approximation or compactness input. -/
theorem ringObject_hom_zero_of_standard_le_neg_one
    (A : Type u) [CommRing A] {Y : AffineD A}
    (hY : (AffineD.standardTStructure A).le (-1) Y)
    (f : ringObject A ⟶ Y) : f = 0 := by
  change DerivedCategory.TStructure.t.le (-1) Y at hY
  let _ : Y.IsLE (-1) :=
    (DerivedCategory.TStructure.t.le_iff_isLE Y (-1)).mp hY
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE Y (-1)
  let _ : K.IsStrictlyLE (-1) := hK
  have hf : f ≫ e.hom = 0 :=
    DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
      (P := ModuleCat.of A A) (L := K) (i := 0) (f ≫ e.hom) (-1) (by omega)
  rw [← cancel_mono e.hom, hf, Limits.zero_comp]

/-- The bound `A = 1` works for the regular module's standard aisle field in
LP Definition 2.1. -/
theorem ringObject_mem_standard_le_one (A : Type u) [CommRing A] :
    (AffineD.standardTStructure A).le 1 (ringObject A) :=
  (AffineD.standardTStructure A).le_monotone (by omega) _
    (ringObject_mem_standard_le_zero A)

end

end RelativeFM
