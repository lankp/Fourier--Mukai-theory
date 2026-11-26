/-
A separator obstruction for the regular module.

`WeakApprox.IsGenerator` separates every morphism.  This is stronger than the
triangulated zero-object detection condition.  We exhibit the standard ghost:
the connecting morphism of a non-split short exact sequence, with all its
composites from shifts of a projective single complex equal to zero.

The concrete non-split extension is multiplication by two on the integers,
followed by its cokernel projection.
-/
import FourierMukai.Scheme.SmallAffineAssembly
import WeakApprox.GeneratorBridge
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Abelian.Exact

@[expose] public section

namespace RelativeFM.NeemanGeneratorM5.Counterexample

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe w v u

noncomputable section

namespace DerivedSingle

open DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Negative Ext groups between single complexes vanish by t-structure
orthogonality, without any projectivity assumption. -/
lemma hom_eq_zero_of_lt {P X : C} {a b : ℤ} (hab : a < b)
    (φ : (singleFunctor C a).obj P ⟶ (singleFunctor C b).obj X) : φ = 0 := by
  exact (DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE
    ((CochainComplex.singleFunctor C a).obj P)
    ((CochainComplex.singleFunctor C b).obj X) a b hab).elim _ _

/-- Positive Ext groups out of a projective single complex vanish. -/
lemma hom_eq_zero_of_projective_of_gt {P X : C} [Projective P] {a b : ℤ} (hba : b < a)
    (φ : (singleFunctor C a).obj P ⟶ (singleFunctor C b).obj X) : φ = 0 := by
  exact DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
    (P := P) (L := (CochainComplex.singleFunctor C b).obj X)
    (i := a) φ b hba

/-- A projective single complex has only degree-zero morphisms to another
single complex: all nonzero-degree positive and negative Ext groups vanish. -/
lemma hom_eq_zero_of_projective_of_ne {P X : C} [Projective P] {a b : ℤ} (hab : a ≠ b)
    (φ : (singleFunctor C a).obj P ⟶ (singleFunctor C b).obj X) : φ = 0 := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact hom_eq_zero_of_lt h φ
  · exact hom_eq_zero_of_projective_of_gt h φ

/-- Full faithfulness of the single embedding reflects split monomorphisms. -/
lemma isSplitMono_of_map {X Y : C} (f : X ⟶ Y) (n : ℤ)
    [IsSplitMono ((singleFunctor C n).map f)] : IsSplitMono f := by
  obtain ⟨s⟩ := IsSplitMono.exists_splitMono (f := (singleFunctor C n).map f)
  obtain ⟨r, hr⟩ := (singleFunctor C n).map_surjective s.retraction
  apply IsSplitMono.mk'
  refine { retraction := r, id := ?_ }
  apply (singleFunctor C n).map_injective
  rw [Functor.map_comp, hr, s.id]
  symm
  exact (singleFunctor C n).map_id X

/-- The connecting map of a non-split extension is nonzero. -/
lemma singleδ_ne_zero {S : ShortComplex C} (hS : S.ShortExact)
    (hf : ¬ IsSplitMono S.f) : hS.singleδ ≠ 0 := by
  intro hzero
  haveI : Mono ((singleFunctor C 0).map S.f) :=
    (hS.singleTriangle.mor₃_eq_zero_iff_mono₁ hS.singleTriangle_distinguished).mp hzero
  haveI : IsSplitMono ((singleFunctor C 0).map S.f) := isSplitMono_of_mono _
  exact hf (isSplitMono_of_map S.f 0)

/-- The connecting map is ghost for every shift of a projective single
complex. -/
lemma singleδ_isGhostFromShifts {S : ShortComplex C} (hS : S.ShortExact)
    (hf : ¬ IsSplitMono S.f) {P : C} [Projective P] :
    IsGhostFromShifts ((singleFunctor C 0).obj P) hS.singleδ := by
  refine ⟨singleδ_ne_zero hS hf, ?ghost⟩
  case ghost =>
    intro n a
    let eP := ((singleFunctors C).shiftIso n (-n) 0 (by omega)).app P
    let eX := ((singleFunctors C).shiftIso 1 (-1) 0 (by omega)).app S.X₁
    by_cases hn : 0 < n
    · have ha : eP.inv ≫ a = 0 :=
        hom_eq_zero_of_lt (P := P) (X := S.X₃) (a := -n) (b := 0) (by omega) _
      rw [← cancel_epi eP.inv]
      simp only [← Category.assoc, ha, Limits.zero_comp, Limits.comp_zero]
    · have hφ : eP.inv ≫ a ≫ hS.singleδ ≫ eX.hom = 0 :=
        hom_eq_zero_of_projective_of_ne (P := P) (X := S.X₁)
          (a := -n) (b := -1) (by omega) _
      rw [← cancel_epi eP.inv, ← cancel_mono eX.hom]
      simpa only [Category.assoc, Limits.zero_comp, Limits.comp_zero] using hφ

/-- A projective single complex is not a morphism-separating generator as
soon as the abelian category has a non-split short exact sequence. -/
lemma not_isGenerator_single_of_projective {S : ShortComplex C} (hS : S.ShortExact)
    (hf : ¬ IsSplitMono S.f) {P : C} [Projective P] :
    ¬ IsGenerator ((singleFunctor C 0).obj P) :=
  not_isGenerator_of_isGhostFromShifts (singleδ_isGhostFromShifts hS hf)

end DerivedSingle

namespace IntExample

abbrev IntModule := ModuleCat.{0} ℤ

/-- Multiplication by two on the integers. -/
def twice : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
  ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ (2 : ℤ))

lemma twice_injective : Function.Injective twice := by
  intro x y h
  change (2 : ℤ) • x = (2 : ℤ) • y at h
  apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
  simpa only [smul_eq_mul] using h

instance : Mono twice := (ModuleCat.mono_iff_injective _).mpr twice_injective

/-- The extension `ℤ --2→ ℤ → coker(2)`. -/
noncomputable def extension : ShortComplex IntModule :=
  ShortComplex.mk twice (cokernel.π twice) (cokernel.condition twice)

lemma extension_shortExact : extension.ShortExact where
  exact := ShortComplex.exact_cokernel twice
  mono_f := by
    change Mono twice
    infer_instance
  epi_g := by
    change Epi (cokernel.π twice)
    infer_instance

lemma twice_not_isSplitMono : ¬ IsSplitMono twice := by
  intro h
  obtain ⟨s⟩ := IsSplitMono.exists_splitMono (f := twice)
  have heq := congrArg (fun k : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => k.hom (1 : ℤ)) s.id
  change s.retraction.hom (twice.hom (1 : ℤ)) = (1 : ℤ) at heq
  change s.retraction.hom ((2 : ℤ) • (1 : ℤ)) = (1 : ℤ) at heq
  rw [map_smul] at heq
  simp only [smul_eq_mul] at heq
  omega

lemma extension_f_not_isSplitMono : ¬ IsSplitMono extension.f := twice_not_isSplitMono

lemma extension_singleδ_ne_zero [HasDerivedCategory.{w} IntModule] :
    extension_shortExact.singleδ ≠ 0 :=
  DerivedSingle.singleδ_ne_zero extension_shortExact extension_f_not_isSplitMono

section LargeHom

attribute [local instance] HasDerivedCategory.standard

lemma ringObject_int_not_isGenerator : ¬ IsGenerator (ringObject ℤ) := by
  exact DerivedSingle.not_isGenerator_single_of_projective
    extension_shortExact extension_f_not_isSplitMono

end LargeHom

/-- The same counterexample applies verbatim to the small-Hom localization. -/
lemma smallRingObject_int_not_isGenerator (H : AffineSpaltensteinInput ℤ) :
    ¬ IsGenerator (smallRingObject ℤ H) := by
  letI : HasDerivedCategory.{0} IntModule :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact DerivedSingle.not_isGenerator_single_of_projective
    extension_shortExact extension_f_not_isSplitMono

end IntExample

end

end RelativeFM.NeemanGeneratorM5.Counterexample

#print axioms RelativeFM.NeemanGeneratorM5.Counterexample.DerivedSingle.hom_eq_zero_of_lt
#print axioms RelativeFM.NeemanGeneratorM5.Counterexample.DerivedSingle.hom_eq_zero_of_projective_of_gt
#print axioms RelativeFM.NeemanGeneratorM5.Counterexample.DerivedSingle.hom_eq_zero_of_projective_of_ne
#print axioms RelativeFM.NeemanGeneratorM5.Counterexample.DerivedSingle.singleδ_ne_zero
#print axioms RelativeFM.NeemanGeneratorM5.Counterexample.DerivedSingle.singleδ_isGhostFromShifts
#print axioms RelativeFM.NeemanGeneratorM5.Counterexample.DerivedSingle.not_isGenerator_single_of_projective
#print axioms RelativeFM.NeemanGeneratorM5.Counterexample.IntExample.extension_singleδ_ne_zero
#print axioms RelativeFM.NeemanGeneratorM5.Counterexample.IntExample.ringObject_int_not_isGenerator
#print axioms RelativeFM.NeemanGeneratorM5.Counterexample.IntExample.smallRingObject_int_not_isGenerator
