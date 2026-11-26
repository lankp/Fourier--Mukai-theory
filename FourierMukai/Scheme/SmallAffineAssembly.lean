/-
Endgame assembly for the affine LP theorem in the small-Hom derived model.

This file is self-contained apart from the repository imports. In particular,
it does not add axioms or use `sorry`.

The small-Hom endpoints `affine_theorem_1_1_small_neeman_only` and
`affine_theorem_1_1_small_standard_neeman_only` (and
`smallCompactHomZeroAtTop_of_neeman`) moved to `Scheme/Neeman32Inputs.lean` on
`wave5/neeman-prune`, renamed `…_of_tag09SR`: they took the Neeman 2024,
Theorem 3.2(i) interface `SmallNeemanCompactToPerfectInput`, which was deleted,
and now take Stacks 09SR.
-/
import FourierMukai.Scheme.AisleCoproducts
import FourierMukai.Scheme.AffineMain

@[expose] public section

namespace RelativeWeakApprox.SetupMainMinimal

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v uZ uD uU

noncomputable section

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- LP Theorem 1.1 with aisle-local coproducts and uniform positive compact
Hom-vanishing. Neither Stacks 09SR nor a coproduct package is needed. -/
theorem theorem_1_1_of_middleAisleCoproducts_of_compactHomZeroAtTop
    (S : SetupMainMinimal DZ D DU) [HasAisleCoproducts S.tD]
    (hvan : CompactHomZeroAtTop D) :
    SatisfiesWA D ↔ EventuallyHomZero S.G' S.G' := by
  have hglue : S.tD.le 0 = gluedLe S.R.iStar S.R.jStar S.tZ S.tU 0 :=
    lemma_4_3_3 S.R S.tD S.tZ S.tU S.G' S.GU S.m S.jStar_G'_mem
      S.tD_compactlyGenerated S.tZ_compactlyGenerated S.tU_compactlyGenerated
  letI : HasAisleCoproducts S.tZ :=
    hasAisleCoproductsClosedOfMiddle S.R S.tD S.tZ S.tU hglue
  constructor
  · intro _
    exact hvan S.G' S.G' S.G'_compact S.G'_compact
  · intro _
    let S44 := (S.toSetup44ReducedOfCompactHomZeroAtTop hvan).toSetup44
    letI : HasAisleCoproducts S44.tD := by
      change HasAisleCoproducts S.tD
      infer_instance
    letI : HasAisleCoproducts S44.tZ := by
      change HasAisleCoproducts S.tZ
      infer_instance
    exact satisfiesWA_of_aisleCoproducts S44

end

end RelativeWeakApprox.SetupMainMinimal

#print axioms RelativeWeakApprox.SetupMainMinimal.theorem_1_1_of_middleAisleCoproducts_of_compactHomZeroAtTop

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u uZ uU

noncomputable section

/-- The regular module, concentrated in degree zero in the small-Hom affine
derived category. -/
noncomputable def smallRingObject (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) : SmallAffineD A H := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)

/-- Perfect complexes in the small-Hom affine derived model: the thick
triangulated envelope of the regular module. -/
noncomputable def SmallPerf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) : ObjectProperty (SmallAffineD A H) :=
  (ObjectProperty.singleton (smallRingObject A H)).triangEnvelope

theorem smallRingObject_mem_smallPerf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) : SmallPerf A H (smallRingObject A H) := by
  apply ObjectProperty.le_triangEnvelope
  exact ObjectProperty.ofObj_apply _ Unit.unit

/-- Positive self-extensions of the regular module vanish in the small-Hom
model. The proof is projectivity of the regular module; it uses no geometric
or compactness input. -/
theorem smallRingObject_eventuallyHomZero_self (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    EventuallyHomZero (smallRingObject A H) (smallRingObject A H) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  let _ : HasExt.{u} (ModuleCat.{u} A) :=
    hasExt_of_hasDerivedCategory (ModuleCat.{u} A)
  refine ⟨1, fun n hn f => ?_⟩
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n by omega)
  cases k with
  | zero => omega
  | succ k =>
      let e : Abelian.Ext.{u} (ModuleCat.of A A) (ModuleCat.of A A) (k + 1) :=
        Abelian.Ext.homEquiv.symm f
      have he : e = 0 := Abelian.Ext.eq_zero_of_projective e
      have hz : Abelian.Ext.homEquiv e = 0 := by
        rw [he]
        exact Abelian.Ext.zero_hom (ModuleCat.of A A) (ModuleCat.of A A) (k + 1)
      exact (Abelian.Ext.homEquiv.apply_symm_apply f).symm.trans hz

/-- Eventual positive Hom-vanishing for perfect complexes in the small-Hom
model, by transport around the defining thick triangulated envelope. -/
theorem smallPerf_eventuallyHomZero (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X Y : SmallAffineD A H}
    (hX : SmallPerf A H X) (hY : SmallPerf A H Y) : EventuallyHomZero X Y :=
  eventuallyHomZero_of_mem_triangEnvelope
    (smallRingObject_eventuallyHomZero_self A H) hX hY

end

end RelativeFM

#print axioms RelativeFM.smallRingObject_eventuallyHomZero_self
#print axioms RelativeFM.smallPerf_eventuallyHomZero

namespace RelativeWeakApprox.SetupMainMinimal

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v uZ uD uU

noncomputable section

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- Replace only the middle t-structure. The only field that has to be
reproved is its compact-generation identity; every other field is independent
of `tD`. -/
def replaceMiddleTStructure (S : SetupMainMinimal DZ D DU)
    (t : TStructure D)
    (hgen : t.le 0 = Coprod
      (shiftTail (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) 0)) :
    SetupMainMinimal DZ D DU where
  R := S.R
  tD := t
  tZ := S.tZ
  tU := S.tU
  approxZ := S.approxZ
  approxU := S.approxU
  GU := S.GU
  G' := S.G'
  G'_compact := S.G'_compact
  G'_generates := S.G'_generates
  m := S.m
  jStar_G'_mem := S.jStar_G'_mem
  normalized_biproduct := S.normalized_biproduct
  tD_compactlyGenerated := hgen
  tZ_compactlyGenerated := S.tZ_compactlyGenerated
  tU_compactlyGenerated := S.tU_compactlyGenerated
  approxZ_t := S.approxZ_t
  approxU_t := S.approxU_t
  approxZ_G := S.approxZ_G
  approxU_G := S.approxU_G

end

end RelativeWeakApprox.SetupMainMinimal

#print axioms RelativeWeakApprox.SetupMainMinimal.replaceMiddleTStructure
