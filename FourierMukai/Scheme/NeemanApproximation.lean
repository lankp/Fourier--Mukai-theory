import FourierMukai.Scheme.AisleGenRingGeneration
import FourierMukai.Scheme.PerfectModel

/-!
# Affine Neeman approximation triangles

This module proves the approximation-triangle field of
`RelativeWeakApprox.WeakApproximationData` for `D(A-Mod)` with the standard
`t`-structure and the regular module as generator.  The bound `N = 1` suffices;
a version for every `N ≥ 1` is included for convenience.

After replacing an object of the standard aisle by a projective complex `P`
strictly bounded above by zero, the stupid-truncation short exact sequence
`σ_{≥0} P → P → σ_{≤-1} P` gives the triangle.  Its first term is a single
projective module in degree zero, hence a retract of a free module and a member
of `envelope (ringObject A) (-1) 1`; its third term is strictly bounded above by
`-1`.  Transport along the projective resolution gives the triangle ending at
the original object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox
open RelativeFM
open RelativeFM.AisleGeneration.Brutal
open RelativeFM.AisleGeneration.Ring
open ComplexShape

namespace RelativeFM.NeemanApproximation.M3

universe v u
noncomputable section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

lemma distinguished_transport_obj₂ (T : Triangle C) (hT : T ∈ distTriang C)
    {Y : C} (e : T.obj₂ ≅ Y) :
    Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ ∈ distTriang C := by
  apply isomorphic_distinguished T hT
  exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
    (by change (T.mor₁ ≫ e.hom) ≫ e.inv = 𝟙 T.obj₁ ≫ T.mor₁; simp)
    (by change (e.inv ≫ T.mor₂) ≫ 𝟙 T.obj₃ = e.inv ≫ T.mor₂; simp)
    (by change T.mor₃ ≫ (shiftFunctor C 1).map (𝟙 T.obj₁) = 𝟙 T.obj₃ ≫ T.mor₃; simp)

attribute [local instance] HasDerivedCategory.standard

lemma stupidTruncLE_neg_one_mem_standard_le (A : Type u) [CommRing A]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (AffineD.standardTStructure A).le (-1)
      (DerivedCategory.Q.obj (K.stupidTrunc (ComplexShape.embeddingUpIntLE (-1)))) := by
  let D : CochainComplex (ModuleCat.{u} A) ℤ :=
    K.stupidTrunc (ComplexShape.embeddingUpIntLE (-1))
  let _ : D.IsStrictlyLE (-1) := inferInstance
  change DerivedCategory.TStructure.t.le (-1) (DerivedCategory.Q.obj D)
  exact ⟨D, Iso.refl _, inferInstance⟩

lemma brutalGE_zero_isStrictlyLE (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsStrictlyLE 0] :
    (brutalGE P 0).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_cases h : 0 ≤ i
  · exact (P.isZero_of_isStrictlyLE 0 _ hi).of_iso
      (brutalGEXIso P 0 i h)
  · exact isZero_brutalGE_X P (by omega)


/-- The regular module in degree zero lies in the interval `[-1,1]`. -/
lemma single_regular_zero_mem (A : Type u) [CommRing A] :
    Coprod (shiftInterval (ringObject A) (-1) 1) (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A))) := by
  apply Coprod.of_mem
  refine ⟨0, by omega, by omega, ⟨?_⟩⟩
  exact (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
    0 0 0 (by omega)).app (ModuleCat.of A A)).symm

/-- A free module in degree zero lies in the coproduct/extension closure of the
regular module shifted in the interval `[-1,1]`. -/
lemma single_free_zero_mem (A : Type u) [CommRing A] (I : Type u) :
    Coprod (shiftInterval (ringObject A) (-1) 1) (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        ((ModuleCat.free A).obj I))) := by
  let R : I → ModuleCat.{u} A := fun _ => ModuleCat.of A A
  let K : I → CochainComplex (ModuleCat.{u} A) ℤ := fun j =>
    (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj (R j)
  have hKproj : ∀ j, (K j).IsKProjective := fun j => by
    dsimp [K, R]
    exact CochainComplex.isKProjective_of_projective _ 0
  have hK (j : I) : Coprod (shiftInterval (ringObject A) (-1) 1)
      (DerivedCategory.Q.obj (K j)) := by
    exact single_regular_zero_mem A
  have hcop := @RelativeFM.AisleGeneration.DerivedCoproduct.coprod_Q_coproductComplex
    (ModuleCat.{u} A) _ _ _ I _ _ (shiftInterval (ringObject A) (-1) 1) K hKproj hK
  let cc := colimit.cocone (Discrete.functor R)
  have hcc : IsColimit cc := colimit.isColimit _
  let hcSingle : IsColimit
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).mapCocone cc) :=
    isColimitOfPreserves (HomologicalComplex.single (ModuleCat.{u} A)
      (ComplexShape.up ℤ) 0) hcc
  let eD : (Discrete.functor R ⋙
      HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0) ≅
      Discrete.functor K := Discrete.natIsoFunctor
  let presSingle : ColimitPresentation (Discrete I)
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj cc.pt) :=
    { diag := Discrete.functor R ⋙
        HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0
      ι := ((HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) 0).mapCocone cc).ι
      isColimit := hcSingle }
  let presK := presSingle.changeDiag eD.symm
  let e₁ : (DerivedCoproducts.coproductComplexCocone K).pt ≅
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        cc.pt) :=
    IsColimit.coconePointUniqueUpToIso
      (DerivedCoproducts.coproductComplexCoconeIsColimit K) presK.isColimit
  let e₂ : cc.pt ≅ (ModuleCat.free A).obj I :=
    IsColimit.coconePointUniqueUpToIso hcc (ModuleCat.finsuppCoconeIsColimit A A I)
  exact (Coprod (shiftInterval (ringObject A) (-1) 1)).prop_of_iso
    (DerivedCategory.Q.mapIso (e₁ ≪≫
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).mapIso e₂)) hcop


/-- A projective module in degree zero belongs to the `[-1,1]` envelope. -/
lemma single_projective_zero_mem_envelope (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) [Projective M] :
    envelope (ringObject A) (-1) 1 (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj M)) := by
  obtain ⟨s, hs⟩ := Module.projective_def.mp (inferInstance : Module.Projective A M)
  let r : Retract M ((ModuleCat.free A).obj M) :=
    { i := ModuleCat.ofHom s
      r := ModuleCat.ofHom (Finsupp.linearCombination A _root_.id)
      retract := by
        apply ModuleCat.hom_ext
        exact LinearMap.ext hs }
  exact ObjectProperty.prop_retractClosure (single_free_zero_mem A M)
    (r.map (CochainComplex.singleFunctor (ModuleCat.{u} A) 0 ⋙ DerivedCategory.Q))


/-- The degree-zero brutal truncation of a projective complex strictly bounded
above by zero belongs to the `[-1,1]` envelope. -/
lemma brutalGE_zero_mem_envelope (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsStrictlyLE 0]
    [∀ i, Projective (P.X i)] :
    envelope (ringObject A) (-1) 1 (DerivedCategory.Q.obj (brutalGE P 0)) := by
  let E : CochainComplex (ModuleCat.{u} A) ℤ := brutalGE P 0
  let _ : E.IsStrictlyGE 0 := inferInstance
  let _ : E.IsStrictlyLE 0 := brutalGE_zero_isStrictlyLE A P
  let _ : Projective (E.X 0) :=
    Projective.of_iso (brutalGEXIso P 0 0 le_rfl).symm inferInstance
  let e : E ≅ (HomologicalComplex.single (ModuleCat.{u} A)
      (ComplexShape.up ℤ) 0).obj (P.X 0) :=
    isoSingleOfBounds E 0 ≪≫
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).mapIso
        (brutalGEXIso P 0 0 le_rfl)
  exact (envelope (ringObject A) (-1) 1).prop_of_iso
    (DerivedCategory.Q.mapIso e).symm (single_projective_zero_mem_envelope A (P.X 0))


/-- The approximation-triangle field of `WeakApproximationData` for the
unbounded derived category of modules, with bound one. -/
theorem exists_approximation_triangle (A : Type u) [CommRing A]
    (F : AffineD A) (hF : (AffineD.standardTStructure A).le 0 F) :
    ∃ (E D : AffineD A) (f : E ⟶ F) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (AffineD A) ∧
      envelope (ringObject A) (-1) 1 E ∧
      (AffineD.standardTStructure A).le (-1) D := by
  change DerivedCategory.TStructure.t.le 0 F at hF
  let _ : F.IsLE 0 := (DerivedCategory.TStructure.t.le_iff_isLE F 0).mp hF
  obtain ⟨K, hK, ⟨eFK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE F 0
  let _ : K.IsStrictlyLE 0 := hK
  obtain ⟨P, π, hπ, hP, hproj⟩ :=
    RelativeFM.KProjectiveResolution.exists_projective_resolution_of_isStrictlyLE K 0
  let _ : QuasiIso π := hπ
  let _ : P.IsStrictlyLE 0 := hP
  let _ (i : ℤ) : Projective (P.X i) := hproj i
  let _ : IsIso (DerivedCategory.Q.map π) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let e : DerivedCategory.Q.obj P ≅ F := asIso (DerivedCategory.Q.map π) ≪≫ eFK.symm
  let e₁ := ComplexShape.embeddingUpIntGE (0 : ℤ)
  let e₂ := ComplexShape.embeddingUpIntLE (-1 : ℤ)
  let ac : e₁.AreComplementary e₂ :=
    (ComplexShape.Embedding.embeddingUpInt_areComplementary (-1) 0 (by omega)).symm
  have hS := RelativeFM.AffinePerfect.stupidTruncShortComplex_shortExact P e₁ e₂ ac
  let T := DerivedCategory.triangleOfSES hS
  have hT : T ∈ distTriang (AffineD A) := DerivedCategory.triangleOfSES_distinguished hS
  refine ⟨T.obj₁, T.obj₃, T.mor₁ ≫ e.hom, e.inv ≫ T.mor₂, T.mor₃,
    distinguished_transport_obj₂ T hT e, ?_, ?_⟩
  · change envelope (ringObject A) (-1) 1
      (DerivedCategory.Q.obj (P.stupidTrunc e₁))
    simpa [e₁, brutalGE] using brutalGE_zero_mem_envelope A P
  · change (AffineD.standardTStructure A).le (-1)
      (DerivedCategory.Q.obj (P.stupidTrunc e₂))
    simpa [e₂] using stupidTruncLE_neg_one_mem_standard_le A P

/-- The approximation triangles with any bound `N ≥ 1`. -/
theorem exists_approximation_triangle_of_one_le (A : Type u) [CommRing A]
    (N : ℤ) (hN : 1 ≤ N) (F : AffineD A)
    (hF : (AffineD.standardTStructure A).le 0 F) :
    ∃ (E D : AffineD A) (f : E ⟶ F) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (AffineD A) ∧
      envelope (ringObject A) (-N) N E ∧
      (AffineD.standardTStructure A).le (-1) D := by
  obtain ⟨E, D, f, g, h, hT, hE, hD⟩ := exists_approximation_triangle A F hF
  refine ⟨E, D, f, g, h, hT, ?_, hD⟩
  exact lemma31_2_mono (ringObject A) (by omega : -N ≤ -1) (by omega : 1 ≤ N) E hE

end

end RelativeFM.NeemanApproximation.M3

#print axioms RelativeFM.NeemanApproximation.M3.exists_approximation_triangle
#print axioms RelativeFM.NeemanApproximation.M3.exists_approximation_triangle_of_one_le
