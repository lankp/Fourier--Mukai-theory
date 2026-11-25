import FourierMukai.Scheme.M4FiniteFreeBody
import FourierMukai.Scheme.AffineCompactness

@[expose] public section

namespace RelativeFM.Stacks07LT.M4

open CategoryTheory CategoryTheory.Limits Module
open RelativeFM RelativeFM.DerivedCoproducts RelativeFM.NeemanM1
open scoped ZeroObject

universe uA

noncomputable section

variable (A : Type uA) [CommRing A]
variable {ι : Type uA} (s : Finset ι)

/-- At the indices in `s`, the free generator is replaced by a zero module. -/
def stageModule (s : Finset ι) (i : ι) : ModuleCat.{uA} A := by
  classical
  exact if i ∈ s then ModuleCat.of A (Fin 0 → A) else ModuleCat.of A A

lemma stageModule_subsingleton_of_mem (s : Finset ι) (i : ι) (hi : i ∈ s) :
    Subsingleton (stageModule A s i) := by
  rw [stageModule, if_pos hi]
  change Subsingleton (Fin 0 → A)
  infer_instance

/-- The K-projective complex whose summands live only in degree `c`. -/
abbrev stageComplex (s : Finset ι) (c : ℤ) (i : ι) : CochainComplex (ModuleCat.{uA} A) ℤ :=
  (HomologicalComplex.single (ModuleCat.{uA} A) (.up ℤ) c).obj (stageModule A s i)

instance stageComplex_isKProjective (s : Finset ι) (c : ℤ) (i : ι) :
    (stageComplex A s c i).IsKProjective := by
  letI : Projective (stageModule A s i) := by
    by_cases hi : i ∈ s
    · letI := stageModule_subsingleton_of_mem A s i hi
      exact (ModuleCat.isZero_of_subsingleton _).projective
    · rw [stageModule, if_neg hi]
      infer_instance
  letI : (stageComplex A s c i).IsStrictlyLE c := by
    dsimp [stageComplex]
    infer_instance
  letI : ∀ n, Projective ((stageComplex A s c i).X n) := by
    intro n
    dsimp [stageComplex]
    infer_instance
  exact CochainComplex.isKProjective_of_projective _ c

/-- The explicit coproduct of the stage complexes. -/
abbrev stageCoproduct (s : Finset ι) (c : ℤ) : CochainComplex (ModuleCat.{uA} A) ℤ :=
  (coproductComplexCocone (stageComplex A s c)).pt

/-- The nonzero summand is identified with the regular module. -/
def stageRegularIso (s : Finset ι) (j : Tail s) :
    stageModule A s j.1 ≅ ModuleCat.of A A := by
  classical
  dsimp [stageModule]
  rw [if_neg j.property]

/-- The degree-`c` summand is identified with the regular module. -/
def stageCoordIso (s : Finset ι) (c : ℤ) (j : Tail s) :
    (stageComplex A s c j.1).X c ≅ ModuleCat.of A A :=
  (HomologicalComplex.eval (ModuleCat A) (.up ℤ) c).mapIso
      ((HomologicalComplex.single (ModuleCat A) (.up ℤ) c).mapIso
        (stageRegularIso A s j).symm).symm ≪≫
    HomologicalComplex.singleObjXSelf (.up ℤ) c (ModuleCat.of A A)

/-- The map from one summand to the finite-support presentation. -/
def stageTailLeg (s : Finset ι) (c : ℤ) (i : ι) :
    (stageComplex A s c i).X c ⟶ ModuleCat.of A (Tail s →₀ A) := by
  classical
  by_cases hi : i ∈ s
  · exact 0
  · exact (stageCoordIso A s c ⟨i, hi⟩).hom ≫
      ModuleCat.ofHom (Finsupp.lsingle (⟨i, hi⟩ : Tail s))

/-- The coproduct cocone at degree `c`, presented by finite-support functions
on the nonzero indices. -/
abbrev stageTailCofan (s : Finset ι) (c : ℤ) : Cofan (fun i => (stageComplex A s c i).X c) :=
  Cofan.mk (ModuleCat.of A (Tail s →₀ A)) (stageTailLeg A s c)

private def stageTailDesc (s : Finset ι) (c : ℤ) (t : Cofan (fun i => (stageComplex A s c i).X c)) :
    (Tail s →₀ A) →ₗ[A] t.pt := by
  classical
  exact Finsupp.lsum A (fun j : Tail s =>
    LinearMap.toSpanSingleton A t.pt (t.inj j ((stageCoordIso A s c j).inv 1)))

/-- The finite-support presentation is a coproduct in degree `c`. -/
def stageTailCofanIsColimit (s : Finset ι) (c : ℤ) : IsColimit (stageTailCofan A s c) := by
  classical
  refine Cofan.IsColimit.mk _ (fun t => ModuleCat.ofHom (stageTailDesc A s c t)) ?_ ?_
  · intro t i
    by_cases hi : i ∈ s
    · letI : Subsingleton (stageModule A s i) :=
        stageModule_subsingleton_of_mem A s i hi
      have hz : IsZero ((stageComplex A s c i).X c) :=
        IsZero.of_iso (ModuleCat.isZero_of_subsingleton (stageModule A s i))
          (HomologicalComplex.singleObjXSelf (.up ℤ) c (stageModule A s i))
      exact hz.eq_of_src _ _
    · rw [← cancel_epi (stageCoordIso A s c ⟨i, hi⟩).inv]
      simp only [stageTailCofan, cofan_mk_inj, stageTailLeg, hi, ↓reduceIte,
        Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [stageTailDesc, Finsupp.lsum_single, Category.assoc]
      rw [← map_smul (t.inj i).hom x ((stageCoordIso A s c ⟨i, hi⟩).inv 1),
        ← map_smul (stageCoordIso A s c ⟨i, hi⟩).inv.hom x 1]
      simp
  · intro t m hm
    apply ModuleCat.hom_ext
    apply (Finsupp.lsum A).symm.injective
    apply funext
    intro j
    apply LinearMap.ext
    intro x
    have hj := hm j.1
    rw [← cancel_epi (stageCoordIso A s c j).inv] at hj
    simp only [stageTailCofan, cofan_mk_inj, stageTailLeg, j.property,
      ↓reduceIte, Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp] at hj
    have hj' := congrArg (fun f : ModuleCat.of A A ⟶ t.pt => f x) hj
    simp only [Finsupp.lsum_symm_apply, LinearMap.comp_apply,
      ModuleCat.hom_ofHom] at hj' ⊢
    have hj'' : (m : ModuleCat.of A (Tail s →₀ A) ⟶ t.pt)
        (Finsupp.single j x) =
        (t.inj j.1) ((stageCoordIso A s c j).inv x) := by
      simpa [stageTailLeg, j.property, Category.assoc] using hj'
    simp only [Finsupp.lsingle_apply]
    rw [stageTailDesc, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
    calc
      (m : ModuleCat.of A (Tail s →₀ A) ⟶ t.pt) (Finsupp.single j x) =
          (t.inj j.1) ((stageCoordIso A s c j).inv x) := hj''
      _ = x • (t.inj j.1) ((stageCoordIso A s c j).inv 1) := by
        rw [← map_smul (t.inj j.1).hom x ((stageCoordIso A s c j).inv 1),
          ← map_smul (stageCoordIso A s c j).inv.hom x 1]
        simp

/-- Identification of the degree-`c` term of the explicit coproduct with
finite-support functions on its nonzero indices. -/
def stageEvalIso (s : Finset ι) (c : ℤ) : (stageCoproduct A s c).X c ≅ ModuleCat.of A (Tail s →₀ A) :=
  IsColimit.coconePointUniqueUpToIso (complexCoproductEvalCofan_isColimit (stageComplex A s c) c)
    (stageTailCofanIsColimit A s c)

end
end RelativeFM.Stacks07LT.M4

#print axioms RelativeFM.Stacks07LT.M4.stageTailCofanIsColimit
#print axioms RelativeFM.Stacks07LT.M4.stageEvalIso
