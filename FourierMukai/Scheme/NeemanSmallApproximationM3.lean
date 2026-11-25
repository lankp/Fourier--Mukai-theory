import FourierMukai.Scheme.NeemanApproximation
import FourierMukai.Scheme.NeemanGeneratorBoundsM5

/-!
# Approximation triangles in the small-Hom affine model

This is a direct small-Hom version of `NeemanApproximation.lean`.  The usual
transport theorem for weak approximation data cannot be used: the large and
small models have different Hom universes.  Spaltenstein replacement supplies
the derived-category instance, after which the same projective resolution and
stupid-truncation argument applies.

All auxiliary facts are local to the main proof: their statements mention
`DerivedCategory.Q`, so they must be elaborated only after the replacement-data
instance has been installed.  Both public theorems take the replacement data
explicitly and have no additional typeclass hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox
open RelativeFM
open RelativeFM.AisleGeneration.Brutal
open RelativeFM.AisleGeneration.Ring
open ComplexShape

namespace RelativeFM.NeemanApproximation.SmallM3

universe u
noncomputable section

/-- The approximation-triangle field of `WeakApproximationData` for the
unbounded derived category of modules, with bound one. -/
theorem exists_approximation_triangle (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A)
    (F : SmallAffineD A H) (hF : (NeemanGeneratorM5.smallStandardTStructure A H).le 0 F) :
    ∃ (E D : SmallAffineD A H) (f : E ⟶ F) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (SmallAffineD A H) ∧
      envelope (smallRingObject A H) (-1) 1 E ∧
      (NeemanGeneratorM5.smallStandardTStructure A H).le (-1) D := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  have stupidTruncLE_neg_one_mem_standard_le     (K : CochainComplex (ModuleCat.{u} A) ℤ) :
      (NeemanGeneratorM5.smallStandardTStructure A H).le (-1)
        (DerivedCategory.Q.obj (K.stupidTrunc (ComplexShape.embeddingUpIntLE (-1)))) := by
    let D : CochainComplex (ModuleCat.{u} A) ℤ :=
      K.stupidTrunc (ComplexShape.embeddingUpIntLE (-1))
    let _ : D.IsStrictlyLE (-1) := inferInstance
    change DerivedCategory.TStructure.t.le (-1) (DerivedCategory.Q.obj D)
    exact ⟨D, Iso.refl _, inferInstance⟩

  /- The regular module in degree zero lies in the interval `[-1,1]`. -/
  have single_regular_zero_mem :
      Coprod (shiftInterval (smallRingObject A H) (-1) 1) (DerivedCategory.Q.obj
        ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
          (ModuleCat.of A A))) := by
    apply Coprod.of_mem
    refine ⟨0, by omega, by omega, ⟨?_⟩⟩
    exact (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
      0 0 0 (by omega)).app (ModuleCat.of A A)).symm

  /- A free module in degree zero lies in the coproduct/extension closure of the
  regular module shifted in the interval `[-1,1]`. -/
  have single_free_zero_mem (I : Type u) :
      Coprod (shiftInterval (smallRingObject A H) (-1) 1) (DerivedCategory.Q.obj
        ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
          ((ModuleCat.free A).obj I))) := by
    let R : I → ModuleCat.{u} A := fun _ => ModuleCat.of A A
    let K : I → CochainComplex (ModuleCat.{u} A) ℤ := fun j =>
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj (R j)
    have hKproj : ∀ j, (K j).IsKProjective := fun j => by
      dsimp [K, R]
      exact CochainComplex.isKProjective_of_projective _ 0
    have hK (j : I) : Coprod (shiftInterval (smallRingObject A H) (-1) 1)
        (DerivedCategory.Q.obj (K j)) := by
      exact single_regular_zero_mem
    have hcop := @RelativeFM.AisleGeneration.DerivedCoproduct.coprod_Q_coproductComplex
      (ModuleCat.{u} A) _ _ _ I _ _ (shiftInterval (smallRingObject A H) (-1) 1) K hKproj hK
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
    exact (Coprod (shiftInterval (smallRingObject A H) (-1) 1)).prop_of_iso
      (DerivedCategory.Q.mapIso (e₁ ≪≫
        (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).mapIso e₂)) hcop


  /- A projective module in degree zero belongs to the `[-1,1]` envelope. -/
  have single_projective_zero_mem_envelope     (M : ModuleCat.{u} A) [Projective M] :
      envelope (smallRingObject A H) (-1) 1 (DerivedCategory.Q.obj
        ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj M)) := by
    obtain ⟨s, hs⟩ := Module.projective_def.mp (inferInstance : Module.Projective A M)
    let r : Retract M ((ModuleCat.free A).obj M) :=
      { i := ModuleCat.ofHom s
        r := ModuleCat.ofHom (Finsupp.linearCombination A _root_.id)
        retract := by
          apply ModuleCat.hom_ext
          exact LinearMap.ext hs }
    exact ObjectProperty.prop_retractClosure (single_free_zero_mem M)
      (r.map (CochainComplex.singleFunctor (ModuleCat.{u} A) 0 ⋙ DerivedCategory.Q))


  /- The degree-zero brutal truncation of a projective complex strictly bounded
  above by zero belongs to the `[-1,1]` envelope. -/
  have brutalGE_zero_mem_envelope     (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsStrictlyLE 0]
      [∀ i, Projective (P.X i)] :
      envelope (smallRingObject A H) (-1) 1 (DerivedCategory.Q.obj (brutalGE P 0)) := by
    let E : CochainComplex (ModuleCat.{u} A) ℤ := brutalGE P 0
    let _ : E.IsStrictlyGE 0 := inferInstance
    let _ : E.IsStrictlyLE 0 := M3.brutalGE_zero_isStrictlyLE A P
    let _ : Projective (E.X 0) :=
      Projective.of_iso (brutalGEXIso P 0 0 le_rfl).symm inferInstance
    let e : E ≅ (HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) 0).obj (P.X 0) :=
      isoSingleOfBounds E 0 ≪≫
        (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).mapIso
          (brutalGEXIso P 0 0 le_rfl)
    exact (envelope (smallRingObject A H) (-1) 1).prop_of_iso
      (DerivedCategory.Q.mapIso e).symm (single_projective_zero_mem_envelope (P.X 0))


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
  have hT : T ∈ distTriang (SmallAffineD A H) := DerivedCategory.triangleOfSES_distinguished hS
  refine ⟨T.obj₁, T.obj₃, T.mor₁ ≫ e.hom, e.inv ≫ T.mor₂, T.mor₃,
    M3.distinguished_transport_obj₂ T hT e, ?_, ?_⟩
  · change envelope (smallRingObject A H) (-1) 1
      (DerivedCategory.Q.obj (P.stupidTrunc e₁))
    simpa [e₁, brutalGE] using brutalGE_zero_mem_envelope P
  · change (NeemanGeneratorM5.smallStandardTStructure A H).le (-1)
      (DerivedCategory.Q.obj (P.stupidTrunc e₂))
    simpa [e₂] using stupidTruncLE_neg_one_mem_standard_le P

/-- The approximation triangles with any bound `N ≥ 1`. -/
theorem exists_approximation_triangle_of_one_le (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A)
    (N : ℤ) (hN : 1 ≤ N) (F : SmallAffineD A H)
    (hF : (NeemanGeneratorM5.smallStandardTStructure A H).le 0 F) :
    ∃ (E D : SmallAffineD A H) (f : E ⟶ F) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (SmallAffineD A H) ∧
      envelope (smallRingObject A H) (-N) N E ∧
      (NeemanGeneratorM5.smallStandardTStructure A H).le (-1) D := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  obtain ⟨E, D, f, g, h, hT, hE, hD⟩ := exists_approximation_triangle A H F hF
  refine ⟨E, D, f, g, h, hT, ?_, hD⟩
  exact lemma31_2_mono (smallRingObject A H) (by omega : -N ≤ -1) (by omega : 1 ≤ N) E hE

end

end RelativeFM.NeemanApproximation.SmallM3

#print axioms RelativeFM.NeemanApproximation.SmallM3.exists_approximation_triangle
#print axioms RelativeFM.NeemanApproximation.SmallM3.exists_approximation_triangle_of_one_le
