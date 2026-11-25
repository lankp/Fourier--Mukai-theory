/-
Concrete models for the local-cohomology ring object.

Import position: after `FourierMukai.Scheme.AffineGluing`.
All declarations are in the private-to-this-development namespace
`RelativeFM.TensorHom.ConcreteC`.
-/
import FourierMukai.Scheme.AffineGluing
import FourierMukai.Scheme.AffineQCoh
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Homology.SingleHomology

@[expose] public section

namespace RelativeFM.TensorHom.ConcreteC

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] HasDerivedCategory.standard

open AffineLocalCohomology

variable (A : Type u) [CommRing A] (f : A)

/-- The regular module as a cochain complex concentrated in degree zero. -/
noncomputable abbrev ringComplex : CochainComplex (ModuleCat.{u} A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)

/-- The explicit two-term representative of `RΓ_Z(A)`, namely
`cone(A[0] → A[1/f][0])[-1]`. -/
noncomputable abbrev ringLocalCohomologyComplex : CochainComplex (ModuleCat.{u} A) ℤ :=
  (complexFunctor A f).obj (ringComplex A)

/-- Local cohomology of the regular module in degree zero. -/
noncomputable abbrev ringLocalCohomologyObject : AffineD A :=
  (derivedFunctor A f).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))

/-- The explicit cochain complex is a representative of the derived ring
object. -/
noncomputable def ringLocalCohomologyObjectIso :
    ringLocalCohomologyObject A f ≅ DerivedCategory.Q.obj (ringLocalCohomologyComplex A f) :=
  (derivedFunctorFactors A f).app (ringComplex A)

/-- The explicit representative has no terms outside degrees zero and one.
In degree zero it is the copy of `A`, and in degree one the copy of `A[1/f]`,
coming from the two terms of the mapping cone. -/
lemma isZero_ringLocalCohomologyComplex_X (n : ℤ) (hn : n ≠ 0 ∧ n ≠ 1) :
    IsZero ((ringLocalCohomologyComplex A f).X n) := by
  change IsZero ((CochainComplex.mappingCone (localizationMap A f (ringComplex A))).X (n + -1))
  rw [CochainComplex.mappingCone.isZero_X_iff]
  constructor
  · apply HomologicalComplex.isZero_single_obj_X
    omega
  · exact (ModuleCat.restrictScalars (algebraMap A (Away A f))).map_isZero
      ((ModuleCat.extendScalars (algebraMap A (Away A f))).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
          (ModuleCat.of A A) (n + -1) (by omega)))

#print axioms ringLocalCohomologyObjectIso
#print axioms isZero_ringLocalCohomologyComplex_X

/-- The regular `A[1/f]`-module in degree zero, before restriction of
scalars. -/
noncomputable abbrev openRingObject : AffineD (Away A f) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} (Away A f)) 0).obj
    (ModuleCat.of (Away A f) (Away A f))

/-- Extension of scalars of the regular module is the regular module. -/
noncomputable def extendScalarsRingIso :
    (ModuleCat.extendScalars (algebraMap A (Away A f))).obj (ModuleCat.of A A) ≅
      ModuleCat.of (Away A f) (Away A f) :=
  (Functor.Monoidal.εIso (ModuleCat.extendScalars (algebraMap A (Away A f)))).symm

/-- Derived extension of scalars sends the regular module in degree zero to
the regular module of the localization. -/
noncomputable def derivedExtensionScalarsRingIso :
    (derivedExtensionScalars A f).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      openRingObject A f := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (by
    simpa [derivedExtensionScalars] using
      ((ModuleCat.extendScalars (algebraMap A (Away A f))).mapDerivedCategorySingleFunctor
        0 |>.app (ModuleCat.of A A))) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (Away A f)) 0).mapIso
      (extendScalarsRingIso A f)

/-- The third object in the localization triangle on the regular module is
`Rj_*` of the regular module over `A[1/f]`. -/
noncomputable def derivedOpenRingIso :
    (derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      (derivedRestrictionScalars A f).obj (openRingObject A f) :=
  (derivedRestrictionScalars A f).mapIso (derivedExtensionScalarsRingIso A f)

/-- The localization triangle for `C = RΓ_Z(A)` in the concrete form
`C → A[0] → Rj_*(A[1/f][0]) → C[1]`. -/
noncomputable def ringLocalCohomologyTriangle : Triangle (AffineD A) :=
  Triangle.mk
    ((derivedCounit A f).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    ((derivedExtensionRestrictionAdjunction A f).unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≫
      (derivedOpenRingIso A f).hom)
    ((derivedOpenRingIso A f).inv ≫
      (derivedConnecting A f).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))

/-- The concrete triangle is isomorphic to the canonical first gluing
triangle. -/
noncomputable def ringLocalCohomologyTriangleIso :
    derivedFirstTriangle A f
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      ringLocalCohomologyTriangle A f := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (derivedOpenRingIso A f) ?_ ?_ ?_
  all_goals simp [derivedFirstTriangle, ringLocalCohomologyTriangle]

/-- `C → A[0] → Rj_*(A[1/f][0]) → C[1]` is distinguished. -/
lemma ringLocalCohomologyTriangle_distinguished :
    ringLocalCohomologyTriangle A f ∈ distTriang (AffineD A) :=
  isomorphic_distinguished _
    (derivedFirstTriangle_distinguished A f
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) _
    (ringLocalCohomologyTriangleIso A f).symm

#print axioms extendScalarsRingIso
#print axioms derivedExtensionScalarsRingIso
#print axioms derivedOpenRingIso
#print axioms ringLocalCohomologyTriangle
#print axioms ringLocalCohomologyTriangleIso
#print axioms ringLocalCohomologyTriangle_distinguished

/-- Cohomology of a module concentrated in degree zero vanishes in every
other degree. -/
lemma isZero_homology_single_zero (M : ModuleCat.{u} A) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) := by
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  have hK : IsZero (K.homology n) :=
    HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M n hn
  have hQ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (DerivedCategory.Q.obj K)) :=
    hK.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app K)
  exact hQ.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M))

/-- Cohomology of the regular localized module, restricted back to `A`,
vanishes away from degree zero. -/
lemma isZero_homology_openRingObject (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((derivedRestrictionScalars A f).obj (openRingObject A f))) := by
  have h := isZero_homology_single_zero (Away A f)
    (ModuleCat.of (Away A f) (Away A f)) n hn
  have hR := (ModuleCat.restrictScalars (algebraMap A (Away A f))).map_isZero h
  exact hR.of_iso ((mapDerivedCategoryHomologyIso
    (ModuleCat.restrictScalars (algebraMap A (Away A f))) (openRingObject A f) n))

/-- The derived cohomology of `C = RΓ_Z(A)` is concentrated in degrees zero
and one. -/
lemma isZero_homology_ringLocalCohomology (n : ℤ) (hn : n < 0 ∨ 1 < n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (ringLocalCohomologyObject A f)) := by
  let T := ringLocalCohomologyTriangle A f
  have hT : T ∈ distTriang (AffineD A) := ringLocalCohomologyTriangle_distinguished A f
  have h := (DerivedCategory.HomologySequence.exact₁ T hT (n - 1) n (by omega)).isZero_of_both_isZero
    (isZero_homology_openRingObject A f (n - 1) (by omega))
    (isZero_homology_single_zero A (ModuleCat.of A A) n (by omega))
  simpa [T, ringLocalCohomologyTriangle] using h

/-- The degree-zero sequence `H⁰C → A → A_f` is exact. -/
lemma ringLocalCohomology_exact_zero :
    (ShortComplex.mk
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (ringLocalCohomologyTriangle A f).mor₁)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (ringLocalCohomologyTriangle A f).mor₂)
      (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _
        (ringLocalCohomologyTriangle_distinguished A f), Functor.map_zero])).Exact :=
  DerivedCategory.HomologySequence.exact₂ _ (ringLocalCohomologyTriangle_distinguished A f) 0

/-- The next sequence `A → A_f → H¹C` is exact. -/
lemma ringLocalCohomology_exact_one :
    (ShortComplex.mk
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (ringLocalCohomologyTriangle A f).mor₂)
      (DerivedCategory.HomologySequence.δ (ringLocalCohomologyTriangle A f) 0 1 (by omega))
      (DerivedCategory.HomologySequence.comp_δ _
        (ringLocalCohomologyTriangle_distinguished A f) 0 1 (by omega))).Exact :=
  DerivedCategory.HomologySequence.exact₃ _ (ringLocalCohomologyTriangle_distinguished A f)
    0 1 (by omega)

/-- `H⁰C → A` is a kernel of `A → A_f` (after the canonical degree-zero
cohomology identifications). -/
lemma ringLocalCohomology_H0_isKernel :
    Nonempty (IsLimit (KernelFork.ofι
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (ringLocalCohomologyTriangle A f).mor₁)
      (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _
        (ringLocalCohomologyTriangle_distinguished A f), Functor.map_zero]))) := by
  let T := ringLocalCohomologyTriangle A f
  have hT : T ∈ distTriang (AffineD A) := ringLocalCohomologyTriangle_distinguished A f
  let S := ShortComplex.mk
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map T.mor₁)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map T.mor₂)
    (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])
  have hS : S.Exact := DerivedCategory.HomologySequence.exact₂ T hT 0
  have hprev := DerivedCategory.HomologySequence.exact₁ T hT (-1) 0 (by omega)
  have hm : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map T.mor₁) :=
    hprev.mono_g ((isZero_homology_openRingObject A f (-1) (by omega)).eq_of_src _ _)
  exact (S.exact_and_mono_f_iff_f_is_kernel).mp ⟨hS, hm⟩

/-- `A_f → H¹C` is a cokernel of `A → A_f` (after the canonical degree-zero
cohomology identifications). -/
lemma ringLocalCohomology_H1_isCokernel :
    Nonempty (IsColimit (CokernelCofork.ofπ
      (DerivedCategory.HomologySequence.δ (ringLocalCohomologyTriangle A f) 0 1 (by omega))
      (DerivedCategory.HomologySequence.comp_δ _
        (ringLocalCohomologyTriangle_distinguished A f) 0 1 (by omega)))) := by
  let T := ringLocalCohomologyTriangle A f
  have hT : T ∈ distTriang (AffineD A) := ringLocalCohomologyTriangle_distinguished A f
  let S := ShortComplex.mk
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map T.mor₂)
    (DerivedCategory.HomologySequence.δ T 0 1 (by omega))
    (DerivedCategory.HomologySequence.comp_δ T hT 0 1 (by omega))
  have hS : S.Exact := DerivedCategory.HomologySequence.exact₃ T hT 0 1 (by omega)
  have hnext := DerivedCategory.HomologySequence.exact₁ T hT 0 1 (by omega)
  have he : Epi (DerivedCategory.HomologySequence.δ T 0 1 (by omega)) :=
    hnext.epi_f ((isZero_homology_single_zero A (ModuleCat.of A A) 1 (by omega)).eq_of_tgt _ _)
  exact (S.exact_and_epi_g_iff_g_is_cokernel).mp ⟨hS, he⟩

#print axioms isZero_homology_single_zero
#print axioms isZero_homology_openRingObject
#print axioms isZero_homology_ringLocalCohomology
#print axioms ringLocalCohomology_exact_zero
#print axioms ringLocalCohomology_exact_one
#print axioms ringLocalCohomology_H0_isKernel
#print axioms ringLocalCohomology_H1_isCokernel

/-- A binary biproduct with a zero second summand is isomorphic to its first
summand. -/
def biprodIsoLeftOfIsZero {X Y : ModuleCat.{u} A} (hY : IsZero Y) : X ⊞ Y ≅ X where
  hom := biprod.fst
  inv := biprod.inl
  hom_inv_id := by
    apply biprod.hom_ext
    · simp
    · simpa using (hY.eq_of_tgt (biprod.snd : X ⊞ Y ⟶ Y) 0).symm
  inv_hom_id := by simp

/-- A binary biproduct with a zero first summand is isomorphic to its second
summand. -/
def biprodIsoRightOfIsZero {X Y : ModuleCat.{u} A} (hX : IsZero X) : X ⊞ Y ≅ Y where
  hom := biprod.snd
  inv := biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext
    · simpa using (hX.eq_of_tgt (biprod.fst : X ⊞ Y ⟶ X) 0).symm
    · simp
  inv_hom_id := by simp

/-- The degree-zero term of the explicit local-cohomology representative is
the regular module. -/
noncomputable def ringLocalCohomologyComplexXZeroIso :
    (ringLocalCohomologyComplex A f).X 0 ≅ ModuleCat.of A A := by
  let φ := localizationMap A f (ringComplex A)
  let L := (ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
    (ComplexShape.up ℤ) ⋙
    (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)
  have hzero : IsZero ((L.obj (ringComplex A)).X (-1)) :=
    (ModuleCat.restrictScalars (algebraMap A (Away A f))).map_isZero
      ((ModuleCat.extendScalars (algebraMap A (Away A f))).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
          (ModuleCat.of A A) (-1) (by omega)))
  exact CochainComplex.shiftFunctorObjXIso (CochainComplex.mappingCone φ) (-1) 0 (-1) rfl ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod φ (-1) 0
      (ComplexShape.up_mk _ _ (by omega)) ≪≫
    biprodIsoLeftOfIsZero A hzero ≪≫ Iso.refl _

/-- The degree-one term is the localization of the regular module, regarded
as an `A`-module. -/
noncomputable def ringLocalCohomologyComplexXOneIso :
    (ringLocalCohomologyComplex A f).X 1 ≅
      (ModuleCat.restrictScalars (algebraMap A (Away A f))).obj
        ((ModuleCat.extendScalars (algebraMap A (Away A f))).obj (ModuleCat.of A A)) := by
  let φ := localizationMap A f (ringComplex A)
  have hzero : IsZero ((ringComplex A).X 1) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (ModuleCat.of A A) 1 (by omega)
  exact CochainComplex.shiftFunctorObjXIso (CochainComplex.mappingCone φ) (-1) 1 0 (by omega) ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod φ 0 1
      (ComplexShape.up_mk _ _ (by omega)) ≪≫
    biprodIsoRightOfIsZero A hzero

/-- Under the two term identifications, the differential from degree zero to
degree one is the negative of the localization unit.  The sign is the one
inherited from `mappingCone` followed by the shift by `-1`. -/
lemma ringLocalCohomologyComplex_d_zero_one :
    (ringLocalCohomologyComplexXZeroIso A f).inv ≫
      (ringLocalCohomologyComplex A f).d 0 1 ≫
      (ringLocalCohomologyComplexXOneIso A f).hom =
    -(localizationMap A f (ringComplex A)).f 0 := by
  simp [ringLocalCohomologyComplexXZeroIso, ringLocalCohomologyComplexXOneIso,
    ringLocalCohomologyComplex, complexFunctor, coneFunctor,
    biprodIsoLeftOfIsZero, biprodIsoRightOfIsZero]
  let φ := localizationMap A f (ringComplex A)
  have h10 : (ComplexShape.up ℤ).Rel (-1) 0 := ComplexShape.up_mk _ _ (by omega)
  have h01 : (ComplexShape.up ℤ).Rel 0 1 := ComplexShape.up_mk _ _ (by omega)
  have eq := HomologicalComplex.homotopyCofiber.inlX_d φ (-1) 0 1 h10 h01
  have eq2 := congrArg (fun k => k ≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod φ 0 1 h01).hom ≫ biprod.snd) eq
  dsimp [HomologicalComplex.homotopyCofiber.inlX] at eq2
  simp only [HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc,
    Category.assoc, zero_comp, neg_zero, zero_add] at eq2
  simpa [φ, CochainComplex.mappingCone, Category.assoc] using eq2

#print axioms ringLocalCohomologyComplexXZeroIso
#print axioms ringLocalCohomologyComplexXOneIso
#print axioms ringLocalCohomologyComplex_d_zero_one

end
end RelativeFM.TensorHom.ConcreteC
