/-
Zero detection by a projective abelian-category separator.

This is the generator condition used by Neeman and Lank--Pauwels.  It must not
be confused with `WeakApprox.IsGenerator`, which additionally separates every
morphism; `GeneratorCounterexampleM5` shows that the latter fails for the
regular module over the integers.

The proof represents a nonzero cohomology class by a chain map from a single
complex.  Projectivity of the source makes that chain map nonzero in the
derived category, since a zero derived map would be null-homotopic and hence
would make the represented cohomology class zero.
-/
import FourierMukai.Scheme.SmallAffineAssembly
import WeakApprox.GeneratorBridge
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.AB

@[expose] public section

namespace RelativeFM.NeemanGeneratorM5.Paper

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open DerivedCategory
open CochainComplex.HomComplex

universe w v u

noncomputable section

/-- The derived homology functors jointly detect zero objects. -/
lemma isZero_of_forall_isZero_homology {C : Type u} [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (E : DerivedCategory C)
    (hE : ∀ i : ℤ, IsZero ((homologyFunctor C i).obj E)) : IsZero E := by
  rw [IsZero.iff_id_eq_zero]
  apply TStructure.t.zero' (𝟙 E)
  · rw [TStructure.t.le_iff_isLE]
    change E.IsLE 0
    rw [DerivedCategory.isLE_iff]
    exact fun i _ => hE i
  · rw [TStructure.t.ge_iff_isGE]
    change E.IsGE 1
    rw [DerivedCategory.isGE_iff]
    exact fun i _ => hE i

namespace AbelianSeparator

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A separator admits a nonzero map to every nonzero object. -/
lemma exists_nonzero_hom_of_not_isZero {P X : C} (hP : IsSeparator P)
    (hX : ¬ IsZero X) : ∃ f : P ⟶ X, f ≠ 0 := by
  by_contra h
  push_neg at h
  apply hX
  rw [IsZero.iff_id_eq_zero]
  symm
  apply hP (0 : X ⟶ X) (𝟙 X)
  intro G hG f
  obtain rfl : P = G := ObjectProperty.singleton_iff _ _ |>.mp hG
  rw [h f, Limits.zero_comp, Limits.zero_comp]

/-- Lift a nonzero homology map to a nonzero derived map from a single
projective complex. -/
lemma exists_nonzero_derived_map_from_single_of_homology
    [HasDerivedCategory.{w} C] {P : C} [Projective P] (hP : IsSeparator P)
    (L : CochainComplex C ℤ) (i : ℤ) (hi : ¬ IsZero (L.homology i)) :
    ∃ φ : (singleFunctor C i).obj P ⟶ Q.obj L, φ ≠ 0 := by
  obtain ⟨ψ, hψ⟩ := exists_nonzero_hom_of_not_isZero hP hi
  let k : P ⟶ L.cycles i := Projective.factorThru ψ (L.homologyπ i)
  let f : P ⟶ L.X i := k ≫ L.iCycles i
  have hf : f ≫ L.d i (i + 1) = 0 := by
    dsimp [f]
    rw [Category.assoc, L.iCycles_d, Limits.comp_zero]
  let α : Cocycle ((CochainComplex.singleFunctor C i).obj P) L 0 :=
    Cocycle.fromSingleMk f (p := i) (q := i) (n := 0) (by simp)
      (i + 1) rfl hf
  let φ : (CochainComplex.singleFunctor C i).obj P ⟶ L := Cocycle.homOf α
  letI : ∀ n : ℤ, Projective (((CochainComplex.singleFunctor C i).obj P).X n) := by
    intro n
    change Projective (((HomologicalComplex.single C (.up ℤ) i).obj P).X n)
    infer_instance
  letI : ((CochainComplex.singleFunctor C i).obj P).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ i
  refine ⟨Q.map φ, ?_⟩
  intro hQ
  have hquot : (HomotopyCategory.quotient C (.up ℤ)).map φ = 0 := by
    apply (DerivedCoproducts.derivedHomKProjectiveEquiv
      ((CochainComplex.singleFunctor C i).obj P) L).injective
    change DerivedCoproducts.derivedHomMap _ _
      ((HomotopyCategory.quotient C (.up ℤ)).map φ) =
        DerivedCoproducts.derivedHomMap _ _ 0
    exact calc
      DerivedCoproducts.derivedHomMap _ _
          ((HomotopyCategory.quotient C (.up ℤ)).map φ) = Q.map φ :=
        DerivedCoproducts.derivedHomMap_quotient_map φ
      _ = 0 := hQ
      _ = DerivedCoproducts.derivedHomMap _ _ 0 := by
        simp only [DerivedCoproducts.derivedHomMap, Functor.map_zero,
          Limits.zero_comp, Limits.comp_zero]
  obtain ⟨ho⟩ := (HomotopyCategory.quotient_map_eq_zero_iff φ).mp hquot
  have hα : α ∈ coboundaries ((CochainComplex.singleFunctor C i).obj P) L 0 := by
    rw [mem_coboundaries_iff _ (-1) (by simp)]
    let z := (Cochain.equivHomotopy φ 0 ho).1
    refine ⟨z, ?_⟩
    have hz := (Cochain.equivHomotopy φ 0 ho).2
    simp only [Cochain.ofHom_zero, add_zero] at hz
    rw [← hz]
    exact Cocycle.cochain_ofHom_homOf_eq_coe α
  rw [Cocycle.fromSingleMk_mem_coboundaries_iff f (p := i) (q := i) (n := 0)
    (by simp) (i + 1) rfl hf (i - 1) (by omega)] at hα
  obtain ⟨g, hg⟩ := hα
  have hk : k = g ≫ L.toCycles (i - 1) i := by
    rw [← cancel_mono (L.iCycles i), Category.assoc, L.toCycles_i]
    exact hg.symm
  apply hψ
  calc
    ψ = k ≫ L.homologyπ i := (Projective.factorThru_comp _ _).symm
    _ = (g ≫ L.toCycles (i - 1) i) ≫ L.homologyπ i := by rw [hk]
    _ = g ≫ (L.toCycles (i - 1) i ≫ L.homologyπ i) := Category.assoc _ _ _
    _ = 0 := by rw [L.toCycles_comp_homologyπ, Limits.comp_zero]

end AbelianSeparator

namespace DerivedSingle

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A projective separator in the abelian category detects zero objects in the
derived category after placing it in degree zero and using all its shifts. -/
lemma isPaperGenerator_single_of_projective_of_isSeparator {P : C}
    [Projective P] (hP : IsSeparator P) :
    IsPaperGenerator ((singleFunctor C 0).obj P) := by
  intro E hE
  apply isZero_of_forall_isZero_homology
  intro i
  by_contra hi
  let L : CochainComplex C ℤ := Q.objPreimage E
  let eL : Q.obj L ≅ E := Q.objObjPreimageIso E
  have hiL : ¬ IsZero (L.homology i) := by
    intro hzero
    apply hi
    exact hzero.of_iso ((homologyFunctor C i).mapIso eL.symm ≪≫
      (homologyFunctorFactors C i).app L)
  obtain ⟨φ, hφ⟩ := AbelianSeparator.exists_nonzero_derived_map_from_single_of_homology
    hP L i hiL
  let eP := ((singleFunctors C).shiftIso (-i) i 0 (by omega)).app P
  have hzero := hE (-i) (eP.hom ≫ φ ≫ eL.hom)
  apply hφ
  have h := congrArg (fun k => eP.inv ≫ k ≫ eL.inv) hzero
  simpa [Category.assoc] using h

end DerivedSingle

namespace Modules

variable (A : Type u) [CommRing A]

/-- The regular module is a separator in its own module category. -/
lemma regular_isSeparator : IsSeparator (ModuleCat.of A A) := by
  intro X Y f g h
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff, ModuleCat.hom_comp,
    LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply, forall_eq'] at h
  ext x
  simpa using h (ModuleCat.ofHom (LinearMap.toSpanSingleton A X x)) 1

section StandardAffine

attribute [local instance] HasDerivedCategory.standard

/-- The regular module satisfies the actual zero-detection condition used by
Neeman and Lank--Pauwels (but not the stronger morphism-separation condition). -/
theorem ringObject_isPaperGenerator : IsPaperGenerator (ringObject A) := by
  exact DerivedSingle.isPaperGenerator_single_of_projective_of_isSeparator
    (regular_isSeparator A)

end StandardAffine

end Modules

/-- Small-Hom form of regular-module zero detection. -/
theorem smallRingObject_isPaperGenerator (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) : IsPaperGenerator (smallRingObject A H) := by
  let hdc : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) := hdc
  exact @DerivedSingle.isPaperGenerator_single_of_projective_of_isSeparator
    (ModuleCat.{u} A) _ _ hdc (ModuleCat.of A A) inferInstance
    (Modules.regular_isSeparator A)

end

end RelativeFM.NeemanGeneratorM5.Paper

#print axioms RelativeFM.NeemanGeneratorM5.Paper.isZero_of_forall_isZero_homology
#print axioms RelativeFM.NeemanGeneratorM5.Paper.AbelianSeparator.exists_nonzero_hom_of_not_isZero
#print axioms RelativeFM.NeemanGeneratorM5.Paper.AbelianSeparator.exists_nonzero_derived_map_from_single_of_homology
#print axioms RelativeFM.NeemanGeneratorM5.Paper.DerivedSingle.isPaperGenerator_single_of_projective_of_isSeparator
#print axioms RelativeFM.NeemanGeneratorM5.Paper.Modules.regular_isSeparator
#print axioms RelativeFM.NeemanGeneratorM5.Paper.Modules.ringObject_isPaperGenerator
#print axioms RelativeFM.NeemanGeneratorM5.Paper.smallRingObject_isPaperGenerator
