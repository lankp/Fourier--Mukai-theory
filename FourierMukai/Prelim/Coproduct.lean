/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import FourierMukai.Prelim.Triangulated

/-!
# Lemma 2.3(1): closure of the iso-locus under coproducts and cofactors

This file proves both halves of Lemma 2.3(1) of

  E. Guisado Villalgordo, P. Lank, *Relative Fourier--Mukai theory for algebraic spaces*:

* if every component of a natural transformation on a family is an isomorphism, and
  the source and target functors preserve the coproduct of that family, then the
  component on the coproduct is an isomorphism;
* conversely, if the component at the coproduct is an isomorphism, then so is every
  component at a cofactor.

The paper states the lemma under the hypothesis that `C` has all `I`-indexed
coproducts and that `F, G` preserve them; the formal statements below assume only
the one coproduct involved, which is what the argument uses.  The cofactor half
needs zero morphisms in the target (the paper's categories are preadditive), used
to define the projection `∐ X ⟶ X i` by the universal property; no finiteness
assumption on the index type is needed.

The coproduct half was found by a member of the Ultramath run `smwufdjq4`
(direction D5) and the cofactor half by another (direction D6).

## Main results

* `RelativeFM.sigmaComparison_naturality`
* `RelativeFM.isIso_sigmaMap`
* `RelativeFM.isIso_app_coproduct`
* `RelativeFM.isIso_of_isIso_sigmaMap`
* `RelativeFM.NatTrans.isIso_app_of_isIso_coproduct`
-/


@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

/-- The comparison square for a natural transformation and an `I`-indexed
coproduct.  Here `sigmaComparison F A` goes from the coproduct of the images to
the image of the coproduct. -/
lemma sigmaComparison_naturality {F G : C ⥤ D} (η : F ⟶ G)
    {I : Type w} (A : I → C)
    [HasCoproduct A] [HasCoproduct fun i => F.obj (A i)]
    [HasCoproduct fun i => G.obj (A i)] :
    sigmaComparison F A ≫ η.app (∐ A) =
      Limits.Sigma.map (fun i => η.app (A i)) ≫ sigmaComparison G A := by
  ext i
  simp only [ι_comp_sigmaComparison_assoc, Sigma.ι_map_assoc,
    ι_comp_sigmaComparison, η.naturality]

/-- A coproduct of isomorphisms is an isomorphism.  Unlike Mathlib's
`Sigma.map_isIso`, this formulation assumes coproducts only of the two
families involved, not of every family indexed by the same type. -/
lemma isIso_sigmaMap {I : Type w} {A B : I → D}
    [HasCoproduct A] [HasCoproduct B] (f : ∀ i, A i ⟶ B i)
    [∀ i, IsIso (f i)] : IsIso (Limits.Sigma.map f) := by
  refine ⟨⟨Limits.Sigma.map (fun i => inv (f i)), ?_, ?_⟩⟩
  · rw [Limits.Sigma.map_comp_map]
    simp only [IsIso.hom_inv_id]
    exact Limits.Sigma.map_id
  · rw [Limits.Sigma.map_comp_map]
    simp only [IsIso.inv_hom_id]
    exact Limits.Sigma.map_id

/-- **Lemma 2.3(1), coproduct part.**  Let `η : F ⟶ G` be a natural
transformation and let `A` be an `I`-indexed family.  Assume that the relevant
coproduct of `A` exists in `C` and that `F` and `G` preserve it.  If `η` is
an isomorphism at every `A i`, then `η` is an isomorphism at `∐ A`.

No finiteness or smallness restriction is imposed on `I`. -/
theorem isIso_app_coproduct {F G : C ⥤ D} (η : F ⟶ G)
    {I : Type w} (A : I → C)
    [HasCoproduct A]
    [PreservesColimit (Discrete.functor A) F]
    [PreservesColimit (Discrete.functor A) G]
    [∀ i, IsIso (η.app (A i))] : IsIso (η.app (∐ A)) := by
  let _ : HasCoproduct (fun i => F.obj (A i)) :=
    hasColimit_of_iso (Discrete.compNatIsoDiscrete A F).symm
  let _ : HasCoproduct (fun i => G.obj (A i)) :=
    hasColimit_of_iso (Discrete.compNatIsoDiscrete A G).symm
  let _ := isIso_sigmaMap (fun i => η.app (A i))
  rw [show η.app (∐ A) =
      inv (sigmaComparison F A) ≫
        Limits.Sigma.map (fun i => η.app (A i)) ≫ sigmaComparison G A by
    rw [IsIso.eq_inv_comp, sigmaComparison_naturality]]
  infer_instance

/-! ### The cofactor half of Lemma 2.3(1) -/

/-- If a map between two `I`-indexed coproducts is induced by maps `p i` on the
cofactors, and the coproduct map is an isomorphism, then every `p i` is an
isomorphism, provided the ambient category has zero morphisms. -/
theorem isIso_of_isIso_sigmaMap [HasZeroMorphisms C]
    {I : Type w} {X Y : I → C} [HasCoproduct X] [HasCoproduct Y]
    (p : ∀ i, X i ⟶ Y i) [IsIso (Limits.Sigma.map p)] (i : I) : IsIso (p i) := by
  classical
  let πX : ∐ X ⟶ X i := Sigma.desc (Function.update (fun _ => 0) i (𝟙 (X i)))
  let πY : ∐ Y ⟶ Y i := Sigma.desc (Function.update (fun _ => 0) i (𝟙 (Y i)))
  let g : Y i ⟶ X i := Sigma.ι Y i ≫ inv (Limits.Sigma.map p) ≫ πX
  have key : πX ≫ p i = Limits.Sigma.map p ≫ πY := by
    ext j
    by_cases h : j = i
    · subst j
      simp [πX, πY]
    · simp [πX, πY, Function.update_of_ne h]
  refine ⟨⟨g, ?_, ?_⟩⟩
  · simp only [g]
    rw [← Category.assoc, ← Limits.Sigma.ι_map p i]
    rw [Category.assoc, IsIso.hom_inv_id_assoc]
    simp [πX]
  · simp only [g, Category.assoc]
    rw [key]
    simp [πY]

/-- **Lemma 2.3(1), cofactor part.**  Let `η : F ⟶ G` be a natural
transformation and suppose that `F` and `G` preserve a chosen coproduct
`∐ A`.  If the component of `η` at the coproduct is an isomorphism, then every
component at a cofactor is an isomorphism.

The target category is assumed to have zero morphisms, as in the preadditive
setting of the paper; these are used to project a coproduct onto one cofactor.
No finiteness assumption on `I` is needed. -/
theorem NatTrans.isIso_app_of_isIso_coproduct [HasZeroMorphisms D]
    {F G : C ⥤ D} (η : F ⟶ G) {I : Type w} (A : I → C)
    [HasCoproduct A] [PreservesColimit (Discrete.functor A) F]
    [PreservesColimit (Discrete.functor A) G]
    [IsIso (η.app (∐ A))] (i : I) : IsIso (η.app (A i)) := by
  let _ : HasCoproduct (fun j => F.obj (A j)) := HasColimit.mk
    ⟨Cofan.mk (F.obj (∐ A)) (fun j => F.map (Sigma.ι A j)),
      isColimitCofanMkObjOfIsColimit F A (Sigma.ι A) (coproductIsCoproduct A)⟩
  let _ : HasCoproduct (fun j => G.obj (A j)) := HasColimit.mk
    ⟨Cofan.mk (G.obj (∐ A)) (fun j => G.map (Sigma.ι A j)),
      isColimitCofanMkObjOfIsColimit G A (Sigma.ι A) (coproductIsCoproduct A)⟩
  have hcomp : sigmaComparison F A ≫ η.app (∐ A) =
      Limits.Sigma.map (fun j => η.app (A j)) ≫ sigmaComparison G A := by
    ext j
    simp
  have hmap : Limits.Sigma.map (fun j => η.app (A j)) =
      (sigmaComparison F A ≫ η.app (∐ A)) ≫ inv (sigmaComparison G A) :=
    (Iso.eq_comp_inv (asIso (sigmaComparison G A))).2 hcomp.symm
  have _ : IsIso (Limits.Sigma.map (fun j => η.app (A j))) := by
    rw [hmap]
    infer_instance
  exact isIso_of_isIso_sigmaMap (fun j => η.app (A j)) i

/-! ### The localizing part of Lemma 2.3(2) -/

namespace Trinatural

variable [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

variable {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]

/-- **Lemma 2.3(2), localizing part.**  The iso-locus of a trinatural
transformation is closed under coproducts that the two functors preserve; since it
is triangulated (`isoLocus_isTriangulated`) and thick
(`isoLocus_isStableUnderRetracts`), it is a localizing subcategory whenever `C`
has the relevant coproducts. -/
lemma isIso_app_coprod (η : Trinatural F G) {I : Type w} (A : I → C)
    [HasCoproduct A]
    [PreservesColimit (Discrete.functor A) F]
    [PreservesColimit (Discrete.functor A) G]
    (h : ∀ i, IsIso (η.toNatTrans.app (A i))) :
    IsIso (η.toNatTrans.app (∐ A)) := by
  haveI : ∀ i, IsIso (η.toNatTrans.app (A i)) := h
  exact isIso_app_coproduct η.toNatTrans A

end Trinatural

end RelativeFM
