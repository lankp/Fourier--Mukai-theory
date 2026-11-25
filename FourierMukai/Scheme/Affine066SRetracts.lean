/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0
license as described in the file LICENSE.
-/
import FourierMukai.Scheme.LeChen
import Mathlib.CategoryTheory.Idempotents.HomologicalComplex
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Retracts of bounded finite-projective models: the strict chain-level core

This module separates the elementary part of Stacks 066S from the genuinely
homotopical problem.  A strict idempotent on a complex splits in the abelian
category of complexes.  Its image is again strictly bounded with finitely
generated projective terms.  A derived retract is reduced to the same assertion
for its associated idempotent.  Thus the only missing input for this route is a
bounded finite-projective strictification theorem for derived idempotents; no
such theorem is assumed here.
-/

@[expose] public section
namespace RelativeFM.AffinePerfect.RetractsM3

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open scoped ZeroObject Classical

universe u
noncomputable section
attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- The idempotent on the large object of a retract. -/
def idempotentOfRetract {C : Type u} [Category C] {X Y : C} (r : Retract X Y) :
    Y ⟶ Y := r.r ≫ r.i

@[simp] lemma idempotentOfRetract_idem {C : Type u} [Category C] {X Y : C}
    (r : Retract X Y) :
    idempotentOfRetract r ≫ idempotentOfRetract r = idempotentOfRetract r := by
  simp [idempotentOfRetract, Category.assoc, r.retract]

/-- A model-valued splitting of the retract idempotent gives a model of the
retract itself. -/
theorem hasModel_of_splitsWithin_idempotentOfRetract
    {X Y : DerivedCategory (ModuleCat.{u} A)} (r : Retract X Y)
    (s : SplitsWithin (AffinePerfect.HasBoundedFiniteProjectiveModel A)
      (idempotentOfRetract r)) :
    AffinePerfect.HasBoundedFiniteProjectiveModel A X := by
  obtain ⟨Z, hZ, i, q, hiq, hqi⟩ := s
  obtain ⟨HZ⟩ := hZ
  change q ≫ i = r.r ≫ r.i at hqi
  let f : X ⟶ Z := r.i ≫ q
  let g : Z ⟶ X := i ≫ r.r
  have hgf : g ≫ f = 𝟙 Z := by
    dsimp [f, g]
    slice_lhs 2 3 => rw [← hqi]
    simp [Category.assoc, hiq]
  have hfg : f ≫ g = 𝟙 X := by
    dsimp [f, g]
    slice_lhs 2 3 => rw [hqi]
    simp [Category.assoc, r.retract]
  let e : X ≅ Z := ⟨f, g, hfg, hgf⟩
  exact ⟨AffinePerfect.hasBoundedFiniteProjectiveModel_of_iso A e.symm HZ⟩

/-- Finite generation passes to a categorical retract of modules. -/
lemma moduleFinite_of_retract {M N : ModuleCat.{u} A} (r : Retract M N)
    [Module.Finite A N] : Module.Finite A M := by
  apply Module.Finite.of_surjective r.r.hom
  intro x
  exact ⟨r.i.hom x, ConcreteCategory.congr_hom r.retract x⟩

/-- Projectivity passes to a categorical retract of modules. -/
lemma moduleProjective_of_retract {M N : ModuleCat.{u} A} (r : Retract M N)
    [Module.Projective A N] : Module.Projective A M := by
  apply Module.Projective.of_split r.i.hom r.r.hom
  ext x
  exact ConcreteCategory.congr_hom r.retract x

/-- A retract of a zero module is zero. -/
lemma moduleIsZero_of_retract {M N : ModuleCat.{u} A} (r : Retract M N)
    (hN : IsZero N) : IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton] at hN ⊢
  letI := hN
  constructor
  intro x y
  have hsec : ∀ z : M, r.r.hom (r.i.hom z) = z :=
    fun z ↦ ConcreteCategory.congr_hom r.retract z
  rw [← hsec x, ← hsec y]
  congr 1
  exact Subsingleton.elim _ _

/-- Terms and both strict bounds pass to a retract of a bounded
finite-projective complex. -/
noncomputable def boundedModelOfComplexRetract
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ}
    (r : Retract Q P) (a b : ℤ)
    (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfin : ∀ n, Module.Finite A (P.X n))
    (hproj : ∀ n, Module.Projective A (P.X n)) :
    BoundedFiniteProjectiveModel A (DerivedCategory.Q.obj Q) := by
  letI := hGE
  letI := hLE
  exact
    { complex := Q
      lower := a
      upper := b
      isStrictlyGE := by
        rw [CochainComplex.isStrictlyGE_iff]
        intro n hn
        exact moduleIsZero_of_retract A
          (r.map (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n))
          (P.isZero_of_isStrictlyGE a n hn)
      isStrictlyLE := by
        rw [CochainComplex.isStrictlyLE_iff]
        intro n hn
        exact moduleIsZero_of_retract A
          (r.map (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n))
          (P.isZero_of_isStrictlyLE b n hn)
      finite := fun n ↦
        letI : Module.Finite A
            ((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n).obj P) := hfin n
        moduleFinite_of_retract A
          (r.map (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n))
      projective := fun n ↦
        letI : Module.Projective A
            ((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n).obj P) := hproj n
        moduleProjective_of_retract A
          (r.map (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n))
      iso := Iso.refl _ }

/-- Strict chain-level idempotents split within bounded finite-projective
models.  This uses idempotent completeness of the abelian category of
complexes, not of its homotopy or derived category. -/
theorem splitsWithin_Q_map_of_strictIdempotent
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (a b : ℤ)
    (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfin : ∀ n, Module.Finite A (P.X n))
    (hproj : ∀ n, Module.Projective A (P.X n))
    (p : P ⟶ P) (hp : p ≫ p = p) :
    SplitsWithin (AffinePerfect.HasBoundedFiniteProjectiveModel A)
      (DerivedCategory.Q.map p) := by
  obtain ⟨Q, i, q, hiq, hqi⟩ :=
    IsIdempotentComplete.idempotents_split P p hp
  let r : Retract Q P := ⟨i, q, hiq⟩
  refine ⟨DerivedCategory.Q.obj Q,
    ⟨boundedModelOfComplexRetract A r a b hGE hLE hfin hproj⟩,
    DerivedCategory.Q.map i, DerivedCategory.Q.map q, ?_, ?_⟩
  · rw [← DerivedCategory.Q.map_comp, hiq, DerivedCategory.Q.map_id]
  · rw [← DerivedCategory.Q.map_comp, hqi]

/-- With a strict chain-level representative of the retract idempotent, the
bounded model of the retract is unconditional. -/
theorem hasModel_retract_of_strictIdempotent
    {X Y : DerivedCategory (ModuleCat.{u} A)} (r : Retract X Y)
    (H : BoundedFiniteProjectiveModel A Y)
    (p : H.complex ⟶ H.complex) (hp : p ≫ p = p)
    (hrep : DerivedCategory.Q.map p =
      H.iso.inv ≫ idempotentOfRetract r ≫ H.iso.hom) :
    AffinePerfect.HasBoundedFiniteProjectiveModel A X := by
  let s := splitsWithin_Q_map_of_strictIdempotent A H.lower H.upper
    H.isStrictlyGE H.isStrictlyLE H.finite H.projective p hp
  let e : DerivedCategory.Q.obj H.complex ≅ Y := H.iso.symm
  have hcomm : DerivedCategory.Q.map p ≫ e.hom = e.hom ≫ idempotentOfRetract r := by
    dsimp [e]
    rw [hrep]
    simp [Category.assoc]
  exact hasModel_of_splitsWithin_idempotentOfRetract A r
    (SplitsWithin.of_iso e _ _ hcomm s)

/-- Every derived idempotent on a single finitely generated projective module
splits within bounded finite-projective models. -/
theorem splitsWithin_single (M : ModuleCat.{u} A) [Module.Finite A M]
    [Module.Projective A M] (n : ℤ)
    (e : (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M)
    (he : e ≫ e = e) :
    SplitsWithin (AffinePerfect.HasBoundedFiniteProjectiveModel A) e := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) n
  obtain ⟨p, rfl⟩ := S.map_surjective e
  have hp : p ≫ p = p := by
    apply S.map_injective
    simpa only [S.map_comp] using he
  obtain ⟨N, i, q, hiq, hqi⟩ :=
    IsIdempotentComplete.idempotents_split M p hp
  let r : Retract N M := ⟨i, q, hiq⟩
  letI : Module.Finite A N := moduleFinite_of_retract A r
  letI : Module.Projective A N := moduleProjective_of_retract A r
  refine ⟨S.obj N, ⟨AffinePerfect.singleModel A N n⟩, S.map i, S.map q, ?_, ?_⟩
  · rw [← S.map_comp, hiq, S.map_id]
  · rw [← S.map_comp, hqi]

/-- One-term bounded representatives have the same splitting property. -/
theorem splitsWithin_of_singleBounds
    {Y : DerivedCategory (ModuleCat.{u} A)}
    (H : BoundedFiniteProjectiveModel A Y)
    (heq : H.lower = H.upper) (e : Y ⟶ Y) (he : e ≫ e = e) :
    SplitsWithin (AffinePerfect.HasBoundedFiniteProjectiveModel A) e := by
  let n := H.lower
  letI : H.complex.IsStrictlyGE n := H.isStrictlyGE
  letI : H.complex.IsStrictlyLE n := by
    dsimp [n]
    rw [heq]
    exact H.isStrictlyLE
  obtain ⟨M, ⟨eK⟩⟩ := H.complex.exists_iso_single n
  let eM : M ≅ H.complex.X n :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) n M).symm ≪≫
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n).mapIso eK.symm
  letI : Module.Finite A M := by
    letI : Module.Finite A (H.complex.X n) := H.finite n
    exact Module.Finite.equiv eM.symm.toLinearEquiv
  letI : Module.Projective A M := by
    letI : Module.Projective A (H.complex.X n) := H.projective n
    exact Module.Projective.of_equiv' eM.symm.toLinearEquiv
  let φ : (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M ≅ Y :=
    (DerivedCategory.Q.mapIso eK).symm ≪≫ H.iso.symm
  let e₀ := φ.hom ≫ e ≫ φ.inv
  have he₀ : e₀ ≫ e₀ = e₀ := by
    dsimp [e₀]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [← Category.assoc] using congrArg (fun k ↦ φ.hom ≫ k ≫ φ.inv) he
  have hcomm : e₀ ≫ φ.hom = φ.hom ≫ e := by
    dsimp [e₀]
    simp [Category.assoc]
  exact SplitsWithin.of_iso φ _ _ hcomm (splitsWithin_single A M n e₀ he₀)

#print axioms hasModel_of_splitsWithin_idempotentOfRetract
#print axioms boundedModelOfComplexRetract
#print axioms splitsWithin_Q_map_of_strictIdempotent
#print axioms hasModel_retract_of_strictIdempotent
#print axioms splitsWithin_single
#print axioms splitsWithin_of_singleBounds

end
end RelativeFM.AffinePerfect.RetractsM3
