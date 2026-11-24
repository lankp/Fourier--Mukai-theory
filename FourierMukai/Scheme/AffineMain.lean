/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.Affine
import FourierMukai.Scheme.PerfectRing
import FourierMukai.Scheme.Inputs
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-!
# The affine Theorem 1.1 with Neeman as the only citation

`affine_theorem_1_1_neeman_only`: for a setup `S : SetupMainMinimal DZ (AffineD A) DU`,
a coproduct package and `CompactPerfectInput A`,

  `SatisfiesWA (AffineD A) ↔ AffineEventualSelfVanishing S.G'`.

What this removes is the point of the file.  The earlier affine theorem carried
Stacks 09SR and Bondal--Van den Bergh; here both are gone.  The cited input is
Neeman, Acta Math. 233 (2024), Theorem 3.2(i), through `CompactPerfectInput`,
used **only** to turn compactness into `Perf A`.  The vanishing itself is proved:

* `ringObject_eventuallyHomZero_self`: `Hom(A, A⟦n⟧) = 0` for `n ≥ 1`;
* `perf_eventuallyHomZero`: every pair of perfect complexes has eventually
  vanishing positive Homs, with no input at all — this is Bondal--Van den Bergh's
  Lemma 3.3.8 for rings, proved from the thick-envelope transport
  (`eventuallyHomZero_of_mem_triangEnvelope`).

Also proved: the standard-`t`-structure bounds for the ring object
(`ringObject_mem_standard_le_zero`, `..._ge_zero`, `..._le_one`),
`ringObject_hom_zero_of_standard_le_neg_one`, and classical generation and
compactness of `A[0]` from `CompactPerfectInput`.

What remains explicit in `S` and `C`: the recollement, the coproducts, the
preferred aisle identities, the normalization, and weak approximation data on the
two ends.  No argument-free unconditional theorem is claimed.

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

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Neeman 2024, Theorem 3.2(i), in the existing `CompactPerfectInput`
interface, makes the regular module a classical generator on compacts.  The
proof is only unfolding `Perf A`, which is already the thick envelope of the
regular module; no separate Stacks 09SR hypothesis is needed. -/
theorem ringObject_isClassicalGeneratorOnCompacts_of_compactPerfectInput
    (A : Type u) [CommRing A] (I : CompactPerfectInput A) :
    IsClassicalGeneratorOnCompacts (ringObject A) := by
  intro X hX
  exact (I.compact_iff_perfect X).mp hX

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

/-- **Published input used:** Neeman, Acta Math. 233 (2024), Theorem 3.2(i),
through `CompactPerfectInput`.  Every pair of compact objects of `D(A-Mod)` has
eventually vanishing positive Homs.  The geometric input is used only to turn
compactness into `Perf A`; the vanishing itself is `perf_eventuallyHomZero`.
It does not use Bondal--Van den Bergh or Stacks 09SR. -/
theorem affineCompactHomZeroAtTop_of_compactPerfectInput
    (A : Type u) [CommRing A] (I : CompactPerfectInput A) :
    AffineCompactHomZeroAtTop A := by
  intro X Y hX hY
  exact perf_eventuallyHomZero A
    ((I.compact_iff_perfect X).mp hX) ((I.compact_iff_perfect Y).mp hY)

end

end RelativeFM

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u uZ uU

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section NeemanOnlyGluing

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

/-- **LP Theorem 1.1, reverse affine gluing direction, with Neeman as the only
published residue.**  `CompactPerfectInput` is Neeman 2024, Theorem 3.2(i).
The recollement, coproduct, normalization and preferred-aisle fields remain
exactly those in `SetupMainMinimal`; this theorem supplies no invented geometry.
Neither Stacks 09SR nor a separate Bondal--Van den Bergh vanishing hypothesis is
used. -/
theorem satisfiesWA_of_neemanCompactPerfectInput
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (I : CompactPerfectInput A) : SatisfiesWA (AffineD A) := by
  let _ : HasCoproducts.{u + 1} DZ := C.hasCoproductsZ
  let _ : HasCoproducts.{u + 1} (AffineD A) := C.hasCoproductsA
  let _ : HasCoproducts.{u + 1} DU := C.hasCoproductsU
  exact S.satisfiesWA_of_compactHomZeroAtTop
    (affineCompactHomZeroAtTop_of_compactPerfectInput A I)

/-- **Affine LP Theorem 1.1 with Neeman's published compact/perfect theorem as
its only external homological input.**  Both directions use the proved compact
Hom-vanishing consequence of Neeman 2024, Theorem 3.2(i); the reverse direction
then invokes the repository's 09SR-free gluing theorem.  In particular, the
middle category's weak approximability is not assumed. -/
theorem affine_theorem_1_1_neeman_only
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (I : CompactPerfectInput A) :
    SatisfiesWA (AffineD A) ↔ AffineEventualSelfVanishing S.G' := by
  have hvan := affineCompactHomZeroAtTop_of_compactPerfectInput A I
  constructor
  · intro _
    exact hvan S.G' S.G' S.G'_compact S.G'_compact
  · intro _
    exact satisfiesWA_of_neemanCompactPerfectInput A DZ DU S C I

end NeemanOnlyGluing

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

/-- Neeman 2024, Theorem 3.2(i), through `CompactPerfectInput`, implies
compactness of the regular module.  No bounded-projective model is needed. -/
theorem ringObject_compact_of_compactPerfectInput
    (A : Type u) [CommRing A] (I : CompactPerfectInput A) :
    IsCompactAb (ringObject A) :=
  (I.compact_iff_perfect (ringObject A)).mpr (ringObject_mem_perf A)

end

end RelativeFM
