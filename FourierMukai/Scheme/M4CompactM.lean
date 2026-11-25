import FourierMukai.Scheme.M4TransitionFiniteFree
import WeakApprox.CompactAb

@[expose] public section

namespace RelativeFM.Stacks07LT.M4

open CategoryTheory CategoryTheory.Limits Module
open RelativeFM RelativeFM.DerivedCoproducts RelativeFM.NeemanM1 RelativeWeakApprox
open scoped ZeroObject Classical

universe w v u uA

noncomputable section

section UniverseTransfer

variable {C : Type u} [Category.{v} C] [Preadditive C] {X : C}

/-- Reindex a coproduct by `Shrink` and decompose a compact map over the
large indexing universe. -/
lemma exists_shrink_coproduct_decomposition
    {J : Type w} [DecidableEq J] [UnivLE.{w, v}] (hX : IsCompactAb X)
    (f : J → C) {P : C} (g : ∀ j, f j ⟶ P)
    (hc : IsColimit (Cofan.mk P g)) (δ : X ⟶ P) :
    ∃ z : DFinsupp (fun i : Shrink.{v} J => X ⟶ f ((equivShrink J).symm i)),
      (DFinsupp.sumAddHom (fun i =>
        ((RelativeWeakApprox.abCoyoneda X).map (g ((equivShrink J).symm i))).hom)) z = δ := by
  classical
  let e := equivShrink.{v} J
  let c : Cofan (fun i : Shrink.{v} J => f (e.symm i)) :=
    Cofan.mk P (fun i => g (e.symm i))
  have hc' : IsColimit c :=
    (Cofan.isColimitEquivOfEquiv (f := f) e.symm (Cofan.mk (f := f) P g)).1 hc
  exact RelativeFM.Stacks07LT.exists_dfinsupp_coproduct_decomposition hX
    (fun i : Shrink.{v} J => f (e.symm i)) (fun i => g (e.symm i)) hc' δ

end UniverseTransfer

attribute [local instance] HasDerivedCategory.standard

variable (A : Type uA) [CommRing A]
variable {ι : Type uA}

/-- Compactness allows the finite zero set of a coproduct stage to be enlarged
so that a given map dies after the transition. -/
lemma exists_stageTransition_comp_eq_zero {X : AffineD A} (hX : IsCompactAb X)
    (s₀ : Finset ι) (c : ℤ) (δ : X ⟶ DerivedCategory.Q.obj (stageCoproduct A s₀ c)) :
    ∃ s₁ : Finset ι, ∃ h : s₀ ⊆ s₁,
      δ ≫ DerivedCategory.Q.map (stageTransition A s₀ s₁ h c) = 0 := by
  classical
  classical
  let e := equivShrink.{uA + 1} ι
  obtain ⟨z, hz⟩ := exists_shrink_coproduct_decomposition hX
    (fun i => DerivedCategory.Q.obj (stageComplex A s₀ c i))
    (fun i => DerivedCategory.Q.map ((coproductComplexCocone (stageComplex A s₀ c)).ι.app ⟨i⟩))
    (derivedCoproductCofanIsColimit (stageComplex A s₀ c)) δ
  let s₁ := s₀ ∪ z.support.image e.symm
  have h : s₀ ⊆ s₁ := Finset.subset_union_left
  refine ⟨s₁, h, ?_⟩
  have hnat := abCofanSum_homCofan_mapRange_comp X
    (DerivedCategory.Q.obj (stageCoproduct A s₀ c))
    (DerivedCategory.Q.obj (stageCoproduct A s₁ c))
    (fun i : Shrink.{uA + 1} ι => DerivedCategory.Q.map
      ((coproductComplexCocone (stageComplex A s₀ c)).ι.app ⟨e.symm i⟩))
    (fun i : Shrink.{uA + 1} ι => DerivedCategory.Q.map
      ((coproductComplexCocone (stageComplex A s₁ c)).ι.app ⟨e.symm i⟩))
    (fun i => DerivedCategory.Q.map (stageTransitionComponent A s₀ s₁ h c (e.symm i)))
    (DerivedCategory.Q.map (stageTransition A s₀ s₁ h c))
    (fun i : Shrink.{uA + 1} ι => by
      simp only [← DerivedCategory.Q.map_comp, stageTransition_ι]
      rfl) z
  have hzero : DFinsupp.mapRange
      (fun i q => q ≫ DerivedCategory.Q.map (stageTransitionComponent A s₀ s₁ h c (e.symm i)))
      (fun i => zero_comp) z = 0 := by
    apply DFinsupp.ext
    intro i
    simp only [DFinsupp.mapRange_apply]
    by_cases hi : e.symm i ∈ s₁
    · rw [stageTransitionComponent_eq_zero A s₀ s₁ h c (e.symm i) hi,
        DerivedCategory.Q.map_zero, comp_zero, DFinsupp.zero_apply]
    · have his : i ∉ z.support := by
        intro hmem
        apply hi
        apply Finset.mem_union_right s₀
        exact Finset.mem_image.mpr ⟨i, hmem, rfl⟩
      have hzi : z i = 0 := DFinsupp.notMem_support_iff.mp his
      rw [hzi, zero_comp]
      rfl
  calc
    δ ≫ DerivedCategory.Q.map (stageTransition A s₀ s₁ h c) =
        abCofanSum (homCofan X (DerivedCategory.Q.obj (stageCoproduct A s₀ c))
          (fun i : Shrink.{uA + 1} ι => DerivedCategory.Q.map
            ((coproductComplexCocone (stageComplex A s₀ c)).ι.app ⟨e.symm i⟩))) z ≫
          DerivedCategory.Q.map (stageTransition A s₀ s₁ h c) := congrArg (fun q => q ≫ DerivedCategory.Q.map
        (stageTransition A s₀ s₁ h c)) hz.symm
    _ = abCofanSum (homCofan X (DerivedCategory.Q.obj (stageCoproduct A s₁ c))
          (fun i : Shrink.{uA + 1} ι => DerivedCategory.Q.map
            ((coproductComplexCocone (stageComplex A s₁ c)).ι.app ⟨e.symm i⟩)))
          (DFinsupp.mapRange
            (fun i q => q ≫ DerivedCategory.Q.map (stageTransitionComponent A s₀ s₁ h c (e.symm i)))
            (fun i => zero_comp) z) := hnat.symm
    _ = 0 := by
      rw [hzero]
      exact map_zero _

/-- The chain projection is natural for every enlargement of the zero set. -/
lemma stageProjection_comp_stageTransition (L : CochainComplex (ModuleCat A) ℤ) (c : ℤ)
    (b : Basis ι A (L.X c)) (s₀ s₁ : Finset ι) (h : s₀ ⊆ s₁)
    (h₀ : L.d (c - 1) c ≫ stageProjectionMap A s₀ L c b = 0)
    (h₁ : L.d (c - 1) c ≫ stageProjectionMap A s₁ L c b = 0) :
    stageProjection A s₀ L c b h₀ ≫ stageTransition A s₀ s₁ h c =
      stageProjection A s₁ L c b h₁ := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = c
  · subst n
    rw [HomologicalComplex.comp_f, stageProjection_f_c, stageProjection_f_c,
      stageProjectionMap_comp_transition]
  · rw [HomologicalComplex.comp_f, stageProjection_f_of_ne A s₀ L c b h₀ n hn,
      stageProjection_f_of_ne A s₁ L c b h₁ n hn, zero_comp]

end
end RelativeFM.Stacks07LT.M4

#print axioms RelativeFM.Stacks07LT.M4.exists_stageTransition_comp_eq_zero
