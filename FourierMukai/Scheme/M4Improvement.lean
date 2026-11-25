import FourierMukai.Scheme.M4CompactM
import FourierMukai.Scheme.DerivedCoproducts

@[expose] public section

namespace RelativeFM.Stacks07LT.M4

open CategoryTheory CategoryTheory.Limits Module
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeFM RelativeFM.DerivedCoproducts RelativeFM.NeemanM1 RelativeWeakApprox
open scoped ZeroObject Classical

universe uA

noncomputable section

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (A : Type uA) [CommRing A]

/-- The explicit one-degree improvement from Stacks 07LT, valid when `c`
lies between the existing bounds. -/
def degreeImprovementDatum_of_bounds {X : AffineD A}
    (F : RelativeFM.Stacks07LT.BoundedFreeFactorization A X) (c : ℤ)
    (hfin : RelativeFM.Stacks07LT.FiniteBelow A F c)
    (hc : c ≤ F.model.upper) (hlow : F.model.lower ≤ c) :
    Nonempty (RelativeFM.Stacks07LT.DegreeImprovementTriangleDatum A F c) := by
  let L := F.model.complex
  letI := F.model.isStrictlyGE
  letI := F.model.isStrictlyLE
  letI : Module.Free A (L.X c) := F.model.free c
  let b := Module.Free.chooseBasis A (L.X c)
  letI : Module.Finite A (L.X (c - 1)) := hfin (c - 1) (by omega)
  obtain ⟨s₀, hs₀⟩ := exists_finset_tailMap_comp_eq_zero b (L.d (c - 1) c).hom
  have hd₀ : L.d (c - 1) c ≫ ModuleCat.ofHom (tailMap b s₀) = 0 := by
    apply ModuleCat.hom_ext
    exact hs₀
  have hπ₀ : L.d (c - 1) c ≫ stageProjectionMap A s₀ L c b = 0 := by
    rw [stageProjectionMap, ← Category.assoc, hd₀, zero_comp]
  let π₀ := stageProjection A s₀ L c b hπ₀
  obtain ⟨s₁, hsub, hzero⟩ := exists_stageTransition_comp_eq_zero A F.compact s₀ c
    ((F.φ ≫ F.model.iso.hom) ≫ DerivedCategory.Q.map π₀)
  have hπ₁ : L.d (c - 1) c ≫ stageProjectionMap A s₁ L c b = 0 := by
    rw [← stageProjectionMap_comp_transition A L c b s₀ s₁ hsub]
    rw [← Category.assoc, hπ₀, zero_comp]
  let π₁ := stageProjection A s₁ L c b hπ₁
  have hcomp : π₀ ≫ stageTransition A s₀ s₁ hsub c = π₁ := by
    dsimp [π₀, π₁]
    exact stageProjection_comp_stageTransition A L c b s₀ s₁ hsub hπ₀ hπ₁
  have hvanq : F.φ ≫ F.model.iso.hom ≫ DerivedCategory.Q.map π₁ = 0 := by
    rw [← hcomp]
    simpa only [Category.assoc, ← DerivedCategory.Q.map_comp] using hzero
  have hvan : F.φ ≫ (F.model.iso.hom ≫ DerivedCategory.Q.map π₁) = 0 := by
    simpa only [Category.assoc] using hvanq
  let model' : RelativeFM.Stacks07LT.BoundedFreeModel A
      (DerivedCategory.Q.obj (kernel π₁)) :=
    { complex := kernel π₁
      lower := F.model.lower
      upper := F.model.upper
      isStrictlyGE := by
        rw [CochainComplex.isStrictlyGE_iff]
        intro n hn
        have hnc : n ≠ c := by omega
        exact IsZero.of_iso (L.isZero_of_isStrictlyGE F.model.lower n hn)
          (kernelStageProjectionXIsoOfNe A s₁ L c b hπ₁ n hnc)
      isStrictlyLE := by
        rw [CochainComplex.isStrictlyLE_iff]
        intro n hn
        have hnc : n ≠ c := by omega
        exact IsZero.of_iso (L.isZero_of_isStrictlyLE F.model.upper n hn)
          (kernelStageProjectionXIsoOfNe A s₁ L c b hπ₁ n hnc)
      bounds := F.model.bounds
      free := by
        intro n
        by_cases hnc : n = c
        · subst n
          exact moduleFree_kernelStageProjection_c A s₁ L c b hπ₁
        · letI := F.model.free n
          exact moduleFree_kernelStageProjection_of_ne A s₁ L c b hπ₁ n hnc
      iso := Iso.refl _ }
  let S := stageProjectionShortComplex A s₁ L c b hπ₁
  have hS : S.ShortExact := stageProjectionShortComplex_shortExact A s₁ L c b hπ₁
  let δ₀ := DerivedCategory.triangleOfSESδ hS
  let ι := DerivedCategory.Q.map (kernel.ι π₁) ≫ F.model.iso.inv
  let π := F.model.iso.hom ≫ DerivedCategory.Q.map π₁
  let T₀ := DerivedCategory.triangleOfSES hS
  let T := Triangle.mk ι π δ₀
  have hdist : T ∈ distTriang (AffineD A) := by
    refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
      (Triangle.isoMk T₀ T (Iso.refl _)
      (show DerivedCategory.Q.obj F.model.complex ≅ F.Y from F.model.iso.symm) (Iso.refl _) ?_ ?_ ?_).symm
    · dsimp [T₀, T, S, stageProjectionShortComplex, ι]
      simp
      rfl
    · change DerivedCategory.Q.map π₁ ≫ 𝟙 _ =
        F.model.iso.inv ≫ F.model.iso.hom ≫ DerivedCategory.Q.map π₁
      simp only [Category.comp_id, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp]
    · change δ₀ ≫ (shiftFunctor (AffineD A) 1).map (𝟙 _) = (𝟙 _) ≫ δ₀
      simp
  exact ⟨
    { Y' := DerivedCategory.Q.obj (kernel π₁)
      model' := model'
      ι := ι
      Z := DerivedCategory.Q.obj (stageCoproduct A s₁ c)
      π := π
      δ := δ₀
      distinguished := hdist
      vanish := hvan
      lower := rfl
      upper := rfl
      finite := by
        intro n hn
        by_cases hnc : n = c
        · subst n
          exact moduleFinite_kernelStageProjection_c A s₁ L c b hπ₁
        · have hnc' : n ≠ c := hnc
          letI : Module.Finite A (L.X n) := hfin n (by omega)
          exact moduleFinite_kernelStageProjection_of_ne A s₁ L c b hπ₁ n hnc' }⟩

/-- The complete one-degree improvement input for Stacks 07LT. -/
def finiteFreeImprovementInputM4 : RelativeFM.Stacks07LT.FiniteFreeImprovementInput A where
  improve F c hfin hc := by
    by_cases hlow : c < F.model.lower
    · refine ⟨F, rfl, rfl, ?_⟩
      intro n hn
      by_cases hnc : n < c
      · exact hfin n hnc
      · have hn' : n = c := by omega
        subst n
        letI := F.model.isStrictlyGE
        exact RelativeFM.AffinePerfect.moduleFinite_of_isZero A
          (F.model.complex.isZero_of_isStrictlyGE F.model.lower c hlow)
    · exact RelativeFM.Stacks07LT.exists_improved_factorization_of_triangleDatum A F c
        (degreeImprovementDatum_of_bounds A F c hfin hc (by omega)).some

end
end RelativeFM.Stacks07LT.M4

#print axioms RelativeFM.Stacks07LT.M4.degreeImprovementDatum_of_bounds
#print axioms RelativeFM.Stacks07LT.M4.finiteFreeImprovementInputM4
