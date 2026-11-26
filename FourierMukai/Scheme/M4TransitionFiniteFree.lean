import FourierMukai.Scheme.M4ProjectionFiniteFree

@[expose] public section

namespace RelativeFM.Stacks07LT.M4

open CategoryTheory CategoryTheory.Limits Module
open RelativeFM RelativeFM.DerivedCoproducts RelativeFM.NeemanM1
open scoped ZeroObject Classical

universe uA

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (A : Type uA) [CommRing A]
variable {ι : Type uA}

/-- The injection on a basis vector in the tail presentation. -/
lemma tailMap_basis {N : Type uA} [AddCommGroup N] [Module A N]
    (b : Basis ι A N) (s : Finset ι) (i : ι) :
    tailMap b s (b i) = if hi : i ∈ s then 0 else Finsupp.single ⟨i, hi⟩ 1 := by
  classical
  by_cases hi : i ∈ s
  · simp only [dite_eq_left hi]
    ext j
    have hij : i ≠ j.1 := fun h => j.property (h ▸ hi)
    simp [tailMap_apply, Finsupp.single_apply, hij]
  · simp only [dite_eq_right hi]
    ext j
    by_cases hij : i = j.1
    · have hj : j = (⟨i, hi⟩ : Tail s) := Subtype.ext hij.symm
      subst j
      simp [tailMap_apply]
    · have hj : (⟨i, hi⟩ : Tail s) ≠ j := fun h => hij (congrArg Subtype.val h)
      simp [tailMap_apply, Finsupp.single_apply, hij, hj]

/-- Compatibility of the evaluation isomorphism with coproduct injections. -/
lemma stageEvalIso_ι (s : Finset ι) (c : ℤ) (i : ι) :
    ((coproductComplexCocone (stageComplex A s c)).ι.app ⟨i⟩).f c ≫
      (stageEvalIso A s c).hom = stageTailLeg A s c i := by
  exact (complexCoproductEvalCofan_isColimit (stageComplex A s c) c).comp_coconePointUniqueUpToIso_hom
    (stageTailCofanIsColimit A s c) ⟨i⟩

/-- A nonzero summand as a copy of the regular single complex. -/
def stageSingleIso (s : Finset ι) (c : ℤ) (j : Tail s) :
    (HomologicalComplex.single (ModuleCat A) (.up ℤ) c).obj (ModuleCat.of A A) ≅
      stageComplex A s c j.1 :=
  (HomologicalComplex.single (ModuleCat A) (.up ℤ) c).mapIso (stageRegularIso A s j).symm

/-- Its canonical generator in the summand. -/
def stageSingleCore (s : Finset ι) (c : ℤ) (j : Tail s) : (stageComplex A s c j.1).X c :=
  (stageSingleIso A s c j).hom.f c
    ((HomologicalComplex.singleObjXSelf (.up ℤ) c (ModuleCat.of A A)).inv 1)

lemma stageSingleCore_eq_coord (s : Finset ι) (c : ℤ) (j : Tail s) :
    stageSingleCore A s c j = (stageCoordIso A s c j).inv 1 := by
  rfl

/-- The image of a basis vector in the intrinsic coproduct presentation. -/
def stageBasisImage (s : Finset ι) (c : ℤ) (i : ι) : (stageCoproduct A s c).X c := by
  classical
  by_cases hi : i ∈ s
  · exact 0
  · exact ((coproductComplexCocone (stageComplex A s c)).ι.app ⟨i⟩).f c
      (stageSingleCore A s c ⟨i, hi⟩)

/-- The map assigning the coproduct images of the basis vectors. -/
def stageIntrinsicMap {N : Type uA} [AddCommGroup N] [Module A N]
    (b : Basis ι A N) (s : Finset ι) (c : ℤ) : N →ₗ[A] (stageCoproduct A s c).X c :=
  b.constr A (stageBasisImage A s c)

lemma stageIntrinsicMap_basis {N : Type uA} [AddCommGroup N] [Module A N]
    (b : Basis ι A N) (s : Finset ι) (c : ℤ) (i : ι) :
    stageIntrinsicMap A b s c (b i) = stageBasisImage A s c i := by
  exact b.constr_basis A (stageBasisImage A s c) i

/-- The intrinsic map agrees with the coordinate tail projection. -/
lemma stageIntrinsicMap_comp_evalIso {N : Type uA} [AddCommGroup N] [Module A N]
    (b : Basis ι A N) (s : Finset ι) (c : ℤ) :
    ModuleCat.ofHom (stageIntrinsicMap A b s c) ≫ (stageEvalIso A s c).hom =
      ModuleCat.ofHom (tailMap b s) := by
  apply ModuleCat.hom_ext
  apply b.ext
  intro i
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_ofHom]
  rw [stageIntrinsicMap_basis, tailMap_basis]
  by_cases hi : i ∈ s
  · simp only [stageBasisImage, dite_eq_left hi]
    exact map_zero _
  · simp only [stageBasisImage, dite_eq_right hi]
    rw [stageSingleCore_eq_coord]
    rw [← ModuleCat.comp_apply, stageEvalIso_ι]
    simp [stageTailLeg, hi, Category.assoc]

/-- The two descriptions of the degree-`c` projection coincide. -/
lemma stageProjectionMap_eq_intrinsic (L : CochainComplex (ModuleCat A) ℤ) (c : ℤ)
    (b : Basis ι A (L.X c)) (s : Finset ι) :
    stageProjectionMap A s L c b = ModuleCat.ofHom (stageIntrinsicMap A b s c) := by
  rw [← cancel_mono (stageEvalIso A s c).hom]
  unfold stageProjectionMap
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    stageIntrinsicMap_comp_evalIso]

/-- The component of the coproduct transition at one basis index. -/
def stageTransitionComponent (s₀ s₁ : Finset ι) (h : s₀ ⊆ s₁) (c : ℤ) (i : ι) :
    stageComplex A s₀ c i ⟶ stageComplex A s₁ c i := by
  classical
  by_cases hi : i ∈ s₁
  · exact 0
  · have hi₀ : i ∉ s₀ := fun hi₀ => hi (h hi₀)
    exact (stageSingleIso A s₀ c ⟨i, hi₀⟩).inv ≫
      (stageSingleIso A s₁ c ⟨i, hi⟩).hom

/-- The legs of the coproduct transition. -/
def stageTransitionLeg (s₀ s₁ : Finset ι) (h : s₀ ⊆ s₁) (c : ℤ) (i : ι) :
    stageComplex A s₀ c i ⟶ stageCoproduct A s₁ c :=
  stageTransitionComponent A s₀ s₁ h c i ≫ (coproductComplexCocone (stageComplex A s₁ c)).ι.app ⟨i⟩

/-- The coproduct map replacing all generators in `s₁` by zero. -/
def stageTransition (s₀ s₁ : Finset ι) (h : s₀ ⊆ s₁) (c : ℤ) :
    stageCoproduct A s₀ c ⟶ stageCoproduct A s₁ c :=
  (coproductComplexCoconeIsColimit (stageComplex A s₀ c)).desc
    (Cofan.mk (stageCoproduct A s₁ c) (stageTransitionLeg A s₀ s₁ h c))

lemma stageTransition_ι (s₀ s₁ : Finset ι) (h : s₀ ⊆ s₁) (c : ℤ) (i : ι) :
    (coproductComplexCocone (stageComplex A s₀ c)).ι.app ⟨i⟩ ≫ stageTransition A s₀ s₁ h c =
      stageTransitionLeg A s₀ s₁ h c i := by
  exact (coproductComplexCoconeIsColimit (stageComplex A s₀ c)).fac _ ⟨i⟩

lemma stageTransitionComponent_coord (s₀ s₁ : Finset ι) (h : s₀ ⊆ s₁) (c : ℤ)
    (i : ι) (hi : i ∉ s₁) :
    (stageTransitionComponent A s₀ s₁ h c i).f c
        (stageSingleCore A s₀ c ⟨i, fun hi₀ => hi (h hi₀)⟩) =
      stageSingleCore A s₁ c ⟨i, hi⟩ := by
  have hi₀ : i ∉ s₀ := fun hi₀ => hi (h hi₀)
  simp only [stageTransitionComponent, dite_eq_right hi]
  change (stageSingleIso A s₁ c ⟨i, hi⟩).hom.f c
    ((stageSingleIso A s₀ c ⟨i, hi₀⟩).inv.f c
      ((stageSingleIso A s₀ c ⟨i, hi₀⟩).hom.f c
        ((HomologicalComplex.singleObjXSelf (.up ℤ) c (ModuleCat.of A A)).inv 1))) = _
  have hh := (stageSingleIso A s₀ c ⟨i, hi₀⟩).hom_inv_id
  have hh' : (stageSingleIso A s₀ c ⟨i, hi₀⟩).hom.f c ≫
      (stageSingleIso A s₀ c ⟨i, hi₀⟩).inv.f c = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, hh, HomologicalComplex.id_f]
  have hh'' := congrArg (fun q : ((HomologicalComplex.single (ModuleCat A) (.up ℤ) c).obj
      (ModuleCat.of A A)).X c ⟶ ((HomologicalComplex.single (ModuleCat A) (.up ℤ) c).obj
      (ModuleCat.of A A)).X c =>
    q ((HomologicalComplex.singleObjXSelf (.up ℤ) c (ModuleCat.of A A)).inv 1)) hh'
  have hn := congrArg (fun x =>
    (stageSingleIso A s₁ c ⟨i, hi⟩).hom.f c x) hh''
  simpa only [ModuleCat.comp_apply, HomologicalComplex.id_f,
    ModuleCat.id_apply, stageSingleCore] using hn

lemma stageTransitionComponent_eq_zero (s₀ s₁ : Finset ι) (h : s₀ ⊆ s₁) (c : ℤ)
    (i : ι) (hi : i ∈ s₁) : stageTransitionComponent A s₀ s₁ h c i = 0 := by
  simp [stageTransitionComponent, hi]

/-- Naturality of the intrinsic projection when the finite zero set grows. -/
lemma stageIntrinsicMap_comp_transition {N : Type uA} [AddCommGroup N] [Module A N]
    (b : Basis ι A N) (s₀ s₁ : Finset ι) (h : s₀ ⊆ s₁) (c : ℤ) :
    ModuleCat.ofHom (stageIntrinsicMap A b s₀ c) ≫
      (stageTransition A s₀ s₁ h c).f c = ModuleCat.ofHom (stageIntrinsicMap A b s₁ c) := by
  apply ModuleCat.hom_ext
  apply b.ext
  intro i
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_ofHom]
  rw [stageIntrinsicMap_basis, stageIntrinsicMap_basis]
  by_cases hi : i ∈ s₁
  · by_cases hi₀ : i ∈ s₀
    · simp only [stageBasisImage, dite_eq_left hi, dite_eq_left hi₀]
      exact map_zero _
    · simp only [stageBasisImage, dite_eq_right hi₀, dite_eq_left hi]
      change ((coproductComplexCocone (stageComplex A s₀ c)).ι.app ⟨i⟩ ≫
        stageTransition A s₀ s₁ h c).f c
          (stageSingleCore A s₀ c ⟨i, hi₀⟩) = 0
      rw [stageTransition_ι]
      simp [stageTransitionLeg, stageTransitionComponent, hi, LinearMap.zero_apply]
      rfl
  · have hi₀ : i ∉ s₀ := fun hi₀ => hi (h hi₀)
    simp only [stageBasisImage, dite_eq_right hi₀, dite_eq_right hi]
    change ((coproductComplexCocone (stageComplex A s₀ c)).ι.app ⟨i⟩ ≫
      stageTransition A s₀ s₁ h c).f c (stageSingleCore A s₀ c ⟨i, hi₀⟩) = _
    rw [stageTransition_ι]
    simp only [stageTransitionLeg, HomologicalComplex.comp_f, ModuleCat.comp_apply]
    rw [stageTransitionComponent_coord A s₀ s₁ h c i hi]

/-- Naturality of the ordinary projection map. -/
lemma stageProjectionMap_comp_transition (L : CochainComplex (ModuleCat A) ℤ) (c : ℤ)
    (b : Basis ι A (L.X c)) (s₀ s₁ : Finset ι) (h : s₀ ⊆ s₁) :
    stageProjectionMap A s₀ L c b ≫ (stageTransition A s₀ s₁ h c).f c =
      stageProjectionMap A s₁ L c b := by
  rw [stageProjectionMap_eq_intrinsic, stageProjectionMap_eq_intrinsic,
    stageIntrinsicMap_comp_transition]

end
end RelativeFM.Stacks07LT.M4

#print axioms RelativeFM.Stacks07LT.M4.tailMap_basis
#print axioms RelativeFM.Stacks07LT.M4.stageProjectionMap_eq_intrinsic
#print axioms RelativeFM.Stacks07LT.M4.stageTransition
#print axioms RelativeFM.Stacks07LT.M4.stageProjectionMap_comp_transition
