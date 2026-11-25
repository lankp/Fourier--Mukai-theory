import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import FourierMukai.Scheme.DerivedCoproducts
import Mathlib.CategoryTheory.SmallObject.Basic

@[expose] public section

namespace RelativeFM.ProjectiveModel

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A contractible complex is acyclic. -/
lemma acyclic_of_homotopy_id_zero {K : CochainComplex C ℤ}
    (h : Homotopy (𝟙 K) 0) : K.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hK : IsZero ((HomotopyCategory.quotient C (.up ℤ)).obj K) :=
    (HomotopyCategory.isZero_quotient_obj_iff K).2 ⟨h⟩
  have hH := Functor.map_isZero (HomotopyCategory.homologyFunctor C (.up ℤ) n) hK
  exact hH.of_iso ((HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).app K).symm

/-- Acyclic complexes are closed under shifts. -/
lemma acyclic_shift {K : CochainComplex C ℤ} (hK : K.Acyclic) (n : ℤ) :
    (K⟦n⟧).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK ⊢
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app K)
    ((HomotopyCategory.subcategoryAcyclic C).le_shift n _ hK)

/-- The projection from the mapping cone of the identity on `K` to its shift. -/
noncomputable abbrev coneCover (K : CochainComplex C ℤ) :
    CochainComplex.mappingCone (𝟙 K) ⟶ K⟦(1 : ℤ)⟧ :=
  (CochainComplex.mappingCone.triangle (𝟙 K)).mor₃

lemma epi_coneCover_f (K : CochainComplex C ℤ) (n : ℤ) :
    Epi ((coneCover K).f n) := by
  have h := CochainComplex.mappingCone.inl_v_triangle_mor₃_f
    (𝟙 K) (n + 1) n (by lia)
  change (CochainComplex.mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) ≫
    (coneCover K).f n = _ at h
  let e := K.shiftFunctorObjXIso 1 n (n + 1) rfl
  letI : IsIso (-e.inv) := ⟨⟨-e.hom,
    by simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using e.inv_hom_id,
    by simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using e.hom_inv_id⟩⟩
  exact epi_of_epi_fac h

lemma quasiIso_coneCover {K : CochainComplex C ℤ} (hK : K.Acyclic) :
    QuasiIso (coneCover K) := by
  have hE : (CochainComplex.mappingCone (𝟙 K)).Acyclic :=
    acyclic_of_homotopy_id_zero (CochainComplex.mappingCone.homotopyToZeroOfId K)
  have hKs := acyclic_shift hK 1
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_exactAt _ n (hE n)]
  exact hKs n

end

end RelativeFM.ProjectiveModel

namespace RelativeFM.ProjectiveModel

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The lifting property enjoyed by cofibrant objects in Hovey's projective
model structure. We isolate this consequence instead of assuming a whole
model-category instance. -/
def LiftsDegreewiseEpiQuasiIso (P : CochainComplex C ℤ) : Prop :=
  ∀ {X Y : CochainComplex C ℤ} (p : X ⟶ Y),
    (∀ n, Epi (p.f n)) → QuasiIso p → HasLiftingProperty (initial.to P) p

/-- Hovey cofibrancy, via only its lifting property against degreewise
epimorphic quasi-isomorphisms, implies K-projectivity. -/
lemma isKProjective_of_liftsDegreewiseEpiQuasiIso {P : CochainComplex C ℤ}
    (hP : LiftsDegreewiseEpiQuasiIso P) : P.IsKProjective where
  nonempty_homotopy_zero {L} f hL := by
    let M := L⟦(-1 : ℤ)⟧
    let e : M⟦(1 : ℤ)⟧ ≅ L :=
      (shiftEquiv (CochainComplex C ℤ) (-1 : ℤ)).unitIso.symm.app L
    let p := coneCover M
    letI : HasLiftingProperty (initial.to P) p :=
      hP p (epi_coneCover_f M) (quasiIso_coneCover (acyclic_shift hL (-1)))
    let sq : CommSq (initial.to (CochainComplex.mappingCone (𝟙 M)))
        (initial.to P) p (f ≫ e.inv) := CommSq.mk (by subsingleton)
    have hl : Homotopy sq.lift 0 := by
      simpa using (CochainComplex.mappingCone.homotopyToZeroOfId M).compLeft sq.lift
    have hfac : sq.lift ≫ p ≫ e.hom = f := by
      rw [← Category.assoc, sq.fac_right, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact ⟨(Homotopy.ofEq hfac.symm).trans
      ((hl.compRight (p ≫ e.hom)).trans (Homotopy.ofEq zero_comp))⟩

/-- Degreewise epimorphisms of complexes, as a morphism property. -/
def degreewiseEpi : MorphismProperty (CochainComplex C ℤ) :=
  fun _ _ p => ∀ n, Epi (p.f n)

/-- In any model structure on unbounded complexes whose weak equivalences are
quasi-isomorphisms and whose fibrations are degreewise epimorphisms, every
cofibrant object is K-projective. -/
lemma isKProjective_of_modelCategory
    [ModelCategory (CochainComplex C ℤ)] (P : CochainComplex C ℤ)
    (hwe : weakEquivalences (CochainComplex C ℤ) = HomologicalComplex.quasiIso C (.up ℤ))
    (hfib : fibrations (CochainComplex C ℤ) = degreewiseEpi)
    [Cofibration (initial.to P)] : P.IsKProjective := by
  apply isKProjective_of_liftsDegreewiseEpiQuasiIso
  intro X Y p hep hp
  haveI : Fibration p := (fibration_iff p).2 (by rw [hfib]; exact hep)
  haveI : WeakEquivalence p := (weakEquivalence_iff p).2 (by
    rw [hwe, HomologicalComplex.mem_quasiIso_iff]
    exact hp)
  exact HomotopicalAlgebra.ModelCategory.cm4b (initial.to P) p

open RelativeFM.DerivedCoproducts

/-- Any projective model structure on unbounded complexes, with
quasi-isomorphisms as weak equivalences and degreewise epimorphisms as
fibrations, supplies the replacement data used by `DerivedCoproducts`.
The proof is precisely CM5(b) applied to the map from the initial object. -/
noncomputable def kProjectiveReplacementDataOfModelCategory [HasDerivedCategory C]
    [ModelCategory (CochainComplex C ℤ)]
    (hwe : weakEquivalences (CochainComplex C ℤ) = HomologicalComplex.quasiIso C (.up ℤ))
    (hfib : fibrations (CochainComplex C ℤ) = degreewiseEpi) :
    KProjectiveReplacementData C where
  resolution X := by
    let K := DerivedCategory.Q.objPreimage X
    let fac := MorphismProperty.factorizationData (cofibrations (CochainComplex C ℤ))
      (trivialFibrations (CochainComplex C ℤ)) (initial.to K)
    have hi : Cofibration fac.i := (cofibration_iff fac.i).2 fac.hi
    letI : Cofibration (initial.to fac.Z) := by
      rw [Subsingleton.elim (initial.to fac.Z) fac.i]
      exact hi
    have hp : QuasiIso fac.p := by
      rw [← HomologicalComplex.mem_quasiIso_iff, ← hwe]
      exact fac.hp.2
    letI : QuasiIso fac.p := hp
    exact {
      complex := fac.Z
      isKProjective := isKProjective_of_modelCategory fac.Z hwe hfib
      iso := asIso (DerivedCategory.Q.map fac.p) ≪≫
        DerivedCategory.Q.objObjPreimageIso X }

/-- The right class in the cofibrant-replacement factorization of Hovey's
projective model structure. -/
def degreewiseEpiQuasiIso : MorphismProperty (CochainComplex C ℤ) :=
  degreewiseEpi ⊓ HomologicalComplex.quasiIso C (.up ℤ)

/-- The small-object argument gives K-projective replacements as soon as a
class `I` has the correct right lifting class. No second set of generating
trivial cofibrations and no other model-category axioms are needed. -/
noncomputable def kProjectiveReplacementDataOfSmallObject.{w}
    [HasDerivedCategory C] (I : MorphismProperty (CochainComplex C ℤ))
    [I.HasSmallObjectArgument.{w}] (hI : I.rlp = degreewiseEpiQuasiIso) :
    KProjectiveReplacementData C where
  resolution X := by
    let K := DerivedCategory.Q.objPreimage X
    let fac := MorphismProperty.factorizationData I.rlp.llp I.rlp (initial.to K)
    have hlp : I.rlp.llp (initial.to fac.Z) := by
      rw [Subsingleton.elim (initial.to fac.Z) fac.i]
      exact fac.hi
    have hZK : degreewiseEpiQuasiIso fac.p := by
      rw [← hI]
      exact fac.hp
    have hp : QuasiIso fac.p :=
      (HomologicalComplex.mem_quasiIso_iff fac.p).1 hZK.2
    have hP : LiftsDegreewiseEpiQuasiIso fac.Z := by
      intro X Y p hep hq
      apply hlp p
      rw [hI]
      exact ⟨hep, (HomologicalComplex.mem_quasiIso_iff p).2 hq⟩
    letI : QuasiIso fac.p := hp
    exact {
      complex := fac.Z
      isKProjective := isKProjective_of_liftsDegreewiseEpiQuasiIso hP
      iso := asIso (DerivedCategory.Q.map fac.p) ≪≫
        DerivedCategory.Q.objObjPreimageIso X }

#print axioms RelativeFM.ProjectiveModel.isKProjective_of_liftsDegreewiseEpiQuasiIso
#print axioms RelativeFM.ProjectiveModel.isKProjective_of_modelCategory
#print axioms RelativeFM.ProjectiveModel.kProjectiveReplacementDataOfModelCategory
#print axioms RelativeFM.ProjectiveModel.kProjectiveReplacementDataOfSmallObject

end

end RelativeFM.ProjectiveModel
