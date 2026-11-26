import FourierMukai.Scheme.NeemanFiniteSupportM4
import FourierMukai.Scheme.AffineKoszulGenerator
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.ShortComplex.Exact

@[expose] public section

namespace RelativeFM.NeemanFiniteSupportM4

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open CochainComplex.HomComplex

universe w v u

noncomputable section

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A chain map out of a single projective complex is null-homotopic if its
induced map on homology is zero. -/
lemma quotient_map_from_single_eq_zero_of_homologyMap_eq_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {P : C} [Projective P] (K : CochainComplex C ℤ)
    (h : (CochainComplex.singleFunctor C 0).obj P ⟶ K)
    (hH : HomologicalComplex.homologyMap h 0 = 0) :
    (HomotopyCategory.quotient C (.up ℤ)).map h = 0 := by
  let c₀ : Cocycle ((CochainComplex.singleFunctor C 0).obj P) K 0 := Cocycle.ofHom h
  obtain ⟨k, hk, hc⟩ := Cocycle.fromSingleMk_surjective c₀ 0 (by simp) 1 rfl
  let c : Cocycle ((CochainComplex.singleFunctor C 0).obj P) K 0 := Cocycle.fromSingleMk k (by simp) 1 rfl hk
  have hc' : c = c₀ := hc
  have hh : Cocycle.homOf c = h := by
    rw [hc']
    exact Cocycle.homOf_ofHom_eq_self h
  let z : P ⟶ K.cycles 0 := K.liftCycles k 1 (by simp) hk
  let eH := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 P
  let eC := HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 P
  have hf : h.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).hom ≫ k := by
    rw [← hh]
    change (c : Cochain ((CochainComplex.singleFunctor C 0).obj P) K 0).v 0 0 (by simp) = _
    exact Cochain.fromSingleMk_v k (p := 0) (q := 0) (n := 0) (by simp)
  have hcycles : eC.hom ≫ z = HomologicalComplex.cyclesMap h 0 := by
    rw [← cancel_mono (K.iCycles 0)]
    dsimp [eC, z]
    simp only [HomologicalComplex.singleObjCyclesSelfIso_hom,
      HomologicalComplex.cyclesMap_i, Category.assoc, K.liftCycles_i, hf]
  have he : ((CochainComplex.singleFunctor C 0).obj P).homologyπ 0 ≫ eH.hom = eC.hom := by
    dsimp [eH, eC]
    exact HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom (.up ℤ) 0 P
  have hmap : eH.hom ≫ z ≫ K.homologyπ 0 = HomologicalComplex.homologyMap h 0 := by
    rw [← cancel_epi (((CochainComplex.singleFunctor C 0).obj P).homologyπ 0)]
    simp only [HomologicalComplex.homologyπ_naturality]
    calc
      ((CochainComplex.singleFunctor C 0).obj P).homologyπ 0 ≫
          (eH.hom ≫ z ≫ K.homologyπ 0) =
          (((CochainComplex.singleFunctor C 0).obj P).homologyπ 0 ≫ eH.hom) ≫
            z ≫ K.homologyπ 0 := by simp only [Category.assoc]
      _ = eC.hom ≫ z ≫ K.homologyπ 0 :=
        congrArg (fun q => q ≫ z ≫ K.homologyπ 0)
          he
      _ = HomologicalComplex.cyclesMap h 0 ≫ K.homologyπ 0 :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun q => q ≫ K.homologyπ 0) hcycles)
  have hz : z ≫ K.homologyπ 0 = 0 := by
    rw [← cancel_epi eH.hom]
    have hm := hmap
    rw [hH] at hm
    exact hm.trans (Limits.comp_zero).symm
  let SC : ShortComplex C := ShortComplex.mk (K.toCycles (-1) 0) (K.homologyπ 0)
    (K.toCycles_comp_homologyπ _ _)
  have hSC : SC.Exact := ShortComplex.exact_of_g_is_cokernel _
    (K.homologyIsCokernel (-1) 0 (by simp))
  let y : P ⟶ K.X (-1) := hSC.liftFromProjective z hz
  have hy : y ≫ K.toCycles (-1) 0 = z := hSC.liftFromProjective_comp z hz
  have hy' : y ≫ K.d (-1) 0 = k := by
    rw [← K.toCycles_i, ← Category.assoc, hy, K.liftCycles_i]
  let γ : Cochain ((CochainComplex.singleFunctor C 0).obj P) K (-1) := Cochain.fromSingleMk y (p := 0) (q := -1) (by omega)
  have hγ : Cochain.ofHom h = δ (-1) 0 γ + Cochain.ofHom 0 := by
    rw [← hh, Cocycle.cochain_ofHom_homOf_eq_coe, Cochain.ofHom_zero, add_zero]
    dsimp [c, γ]
    simp only [Cochain.δ_fromSingleMk, add_zero, hy']
  exact (HomotopyCategory.quotient_map_eq_zero_iff h).mpr
    ⟨(Cochain.equivHomotopy h 0).symm ⟨γ, hγ⟩⟩

end
end RelativeFM.NeemanFiniteSupportM4

#print axioms RelativeFM.NeemanFiniteSupportM4.quotient_map_from_single_eq_zero_of_homologyMap_eq_zero
