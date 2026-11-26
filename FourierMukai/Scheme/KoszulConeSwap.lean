/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.Linear

/-!
# Iterated scalar mapping cones commute

Source: LP26, Corollary 1.2 (`cor:weak_approx_spaces`), affine base case, via
Neeman, *Acta Math.* 233 (2024), Construction 7.3: the finite-power Koszul
objects.  This file proves the chain-level fact behind the reordering of a finite
Koszul object: for a cochain complex `K` over an `R`-linear category and scalars
`b c : R`,

`cone(c • 𝟙, cone(b • 𝟙, K)) ≅ cone(b • 𝟙, cone(c • 𝟙, K))`

(`coneSwapIso`).  Both are the total complex of the square of `b`, `c` on `K`;
the isomorphism swaps the two middle summands, with a sign on the top summand.
It is built from Mathlib's `CochainComplex.mappingCone.desc`; its inverse is the
same construction with `b` and `c` exchanged.

Nothing is assumed.
-/

@[expose] public section

namespace RelativeFM.KoszulConeSwap

open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex

variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
  [HasBinaryBiproducts C]

/-- The mapping cone of scalar multiplication by `b`. -/
noncomputable abbrev cone (b : R) (K : CochainComplex C ℤ) : CochainComplex C ℤ :=
  mappingCone (b • 𝟙 K)

variable (K : CochainComplex C ℤ) (b c : R)

/-- The map `cone(b, K) ⟶ cone(b, cone(c, K))` induced by `inr : K ⟶ cone(c, K)`. -/
noncomputable def innerMap : cone b K ⟶ cone b (cone c K) :=
  mappingCone.desc (b • 𝟙 K)
    ((Cochain.ofHom (mappingCone.inr (c • 𝟙 K))).comp (mappingCone.inl (b • 𝟙 (cone c K)))
      (zero_add _))
    (mappingCone.inr (c • 𝟙 K) ≫ mappingCone.inr (b • 𝟙 (cone c K))) (by
      rw [δ_ofHom_comp, mappingCone.δ_inl, Cochain.ofHom_comp, ← Cochain.ofHom_comp]
      congr 1
      simp [Linear.smul_comp])

/-- The cochain `cone(b, K) ⟶ cone(b, cone(c, K))` of degree `-1` used to build the swap. -/
noncomputable def swapCochain : Cochain (cone b K) (cone b (cone c K)) (-1) :=
  -(mappingCone.fst (b • 𝟙 K)).1.comp ((mappingCone.inl (c • 𝟙 K)).comp
      (mappingCone.inl (b • 𝟙 (cone c K))) (show (-1 : ℤ) + -1 = -2 by norm_num))
      (show (1 : ℤ) + -2 = -1 by norm_num) +
    (mappingCone.snd (b • 𝟙 K)).comp ((mappingCone.inl (c • 𝟙 K)).comp
      (Cochain.ofHom (mappingCone.inr (b • 𝟙 (cone c K)))) (add_zero _)) (zero_add _)

lemma δ_swapCochain :
    δ (-1) 0 (swapCochain K b c) = Cochain.ofHom ((c • 𝟙 (cone b K)) ≫ innerMap K b c) := by
  simp only [swapCochain, δ_add, δ_neg]
  rw [δ_comp _ _ _ 2 (-1) 0 (by norm_num) (by norm_num) (by norm_num),
    δ_comp _ _ _ 0 0 (-1) (by norm_num) (by norm_num) (by norm_num),
    δ_zero_cochain_comp _ _ 0 (by norm_num),
    δ_comp_zero_cochain _ _ 0 (by norm_num)]
  simp only [Cocycle.δ_eq_zero, mappingCone.δ_inl, mappingCone.δ_snd, δ_ofHom, Cochain.zero_comp,
    Cochain.comp_zero, smul_zero, add_zero, zero_add]
  rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (by norm_num)]
  constructor
  · simp [innerMap, Cochain.comp_add, Cochain.comp_neg, Cochain.comp_smul]
  · simp [innerMap, Cochain.comp_add, Cochain.comp_neg, Cochain.comp_smul]

/-- The swap `cone(c, cone(b, K)) ⟶ cone(b, cone(c, K))`. -/
noncomputable def swapHom : cone c (cone b K) ⟶ cone b (cone c K) :=
  mappingCone.desc (c • 𝟙 (cone b K)) (swapCochain K b c) (innerMap K b c) (δ_swapCochain K b c)

lemma innerMap_swapHom :
    innerMap K b c ≫ swapHom K c b = mappingCone.inr (c • 𝟙 (cone b K)) := by
  apply Cochain.ofHom_injective
  rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (by norm_num)]
  constructor
  · rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain, innerMap,
      mappingCone.inl_desc, Cochain.comp_assoc_of_first_is_zero_cochain, swapHom,
      mappingCone.inl_desc]
    simp [swapCochain]
  · rw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
    congr 1
    simp [innerMap, swapHom]

lemma swapHom_swapHom : swapHom K b c ≫ swapHom K c b = 𝟙 _ := by
  apply Cochain.ofHom_injective
  rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (by norm_num)]
  constructor
  · rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain]
    simp only [swapHom, mappingCone.inl_desc]
    rw [mappingCone.ext_cochain_from_iff _ (-2) (-1) (by norm_num)]
    constructor
    · simp [swapCochain, innerMap, Cochain.comp_add, Cochain.comp_neg]
    · simp [swapCochain, innerMap, Cochain.comp_add, Cochain.comp_neg]
  · rw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
    congr 1
    rw [swapHom, mappingCone.inr_desc_assoc, innerMap_swapHom, Category.comp_id]

/-- **Iterated scalar cones commute** (chain level):
`cone(c • 𝟙, cone(b • 𝟙, K)) ≅ cone(b • 𝟙, cone(c • 𝟙, K))`. -/
noncomputable def coneSwapIso : cone c (cone b K) ≅ cone b (cone c K) where
  hom := swapHom K b c
  inv := swapHom K c b
  hom_inv_id := swapHom_swapHom K b c
  inv_hom_id := swapHom_swapHom K c b

end RelativeFM.KoszulConeSwap

#print axioms RelativeFM.KoszulConeSwap.coneSwapIso
