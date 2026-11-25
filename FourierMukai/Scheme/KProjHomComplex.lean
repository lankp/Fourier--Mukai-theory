import FourierMukai.Scheme.DerivedCoproducts
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Hom complexes out of a K-projective complex

This module packages postcomposition on Mathlib's `HomComplex`, and proves that
it preserves quasi-isomorphisms when the source is K-projective.  The proof is
at the level of cohomology classes: after passing to the derived category, it
is postcomposition by an isomorphism.  No K-injective resolution is used.
-/

@[expose] public section

namespace RelativeFM.KProjectiveTensorHom

open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

/-- Postcomposition as a morphism of homomorphism complexes. -/
def homComplexPostcomp (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ}
    (f : L ⟶ M) : HomComplex K L ⟶ HomComplex K M where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z => z.comp (Cochain.ofHom f) (add_zero n)
      map_zero' := by ext p q hpq; simp
      map_add' := by intro x y; ext p q hpq; simp }
  comm' _ m _ := by
    ext z
    exact δ_comp_ofHom z f m

@[simp]
lemma homComplexPostcomp_f_apply (K : CochainComplex C ℤ)
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ) (z : Cochain K L n) :
    ((homComplexPostcomp K f).f n).hom z =
      z.comp (Cochain.ofHom f) (add_zero n) := rfl

lemma homComplexPostcomp_δ (K : CochainComplex C ℤ)
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (n m : ℤ) (z : Cochain K L n) :
    δ n m (((homComplexPostcomp K f).f n).hom z) =
      ((homComplexPostcomp K f).f m).hom (δ n m z) :=
  ConcreteCategory.congr_hom ((homComplexPostcomp K f).comm n m) z

/-- The map on cocycles induced by `homComplexPostcomp`. -/
def homCocyclesPostcomp (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ}
    (f : L ⟶ M) (n : ℤ) : Cocycle K L n →+ Cocycle K M n where
  toFun z := ⟨((homComplexPostcomp K f).f n).hom (z : Cochain K L n), by
    change δ n (n + 1) (((homComplexPostcomp K f).f n).hom (z : Cochain K L n)) = 0
    rw [homComplexPostcomp_δ, z.δ_eq_zero]
    exact ((homComplexPostcomp K f).f (n + 1)).hom.map_zero⟩
  map_zero' := Subtype.ext (((homComplexPostcomp K f).f n).hom.map_zero)
  map_add' x y := Subtype.ext (((homComplexPostcomp K f).f n).hom.map_add
    (x : Cochain K L n) (y : Cochain K L n))

@[simp]
lemma homCocyclesPostcomp_apply (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ}
    (f : L ⟶ M) (n : ℤ) (z : Cocycle K L n) :
    homCocyclesPostcomp K f n z = z.postcomp f := rfl

/-- The map on cohomology classes induced by `homComplexPostcomp`. -/
def homClassesPostcomp (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ}
    (f : L ⟶ M) (n : ℤ) :
    CohomologyClass K L n →+ CohomologyClass K M n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K M n).comp (homCocyclesPostcomp K f n)) (by
      rintro z ⟨r, hr, b, hb⟩
      change CohomologyClass.mk (homCocyclesPostcomp K f n z) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ r hr]
      refine ⟨((homComplexPostcomp K f).f r).hom b, ?_⟩
      change δ r n (((homComplexPostcomp K f).f r).hom b) =
        ((homComplexPostcomp K f).f n).hom (z : Cochain K L n)
      rw [homComplexPostcomp_δ, hb])

@[simp]
lemma homClassesPostcomp_mk (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ}
    (f : L ⟶ M) (n : ℤ) (z : Cocycle K L n) :
    homClassesPostcomp K f n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.postcomp f) := rfl

/-- The explicit homology comparison for `homComplexPostcomp`. -/
def homPostcompLeftHomologyMapData (K : CochainComplex C ℤ)
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
        (homComplexPostcomp K f))
      (leftHomologyData K L n) (leftHomologyData K M n) := by
  let F := homComplexPostcomp K f
  refine { φK := AddCommGrpCat.ofHom (homCocyclesPostcomp K f n)
           φH := AddCommGrpCat.ofHom (homClassesPostcomp K f n)
           commi := ?_, commf' := ?_, commπ := ?_ }
  · ext z
    rfl
  · have hi : AddCommGrpCat.ofHom (homCocyclesPostcomp K f n) ≫
        (leftHomologyData K M n).i = (leftHomologyData K L n).i ≫ F.f n := by
      ext z
      rfl
    rw [← cancel_mono (leftHomologyData K M n).i, Category.assoc, hi, ← Category.assoc,
      ShortComplex.LeftHomologyData.f'_i, Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor _ _ n).map F).comm₁₂.symm
  · ext z
    rfl

/-- A postcomposition morphism of Hom complexes is a quasi-isomorphism exactly
when its maps on cohomology classes are bijective in every degree. -/
lemma homComplexPostcomp_quasiIso_iff (K : CochainComplex C ℤ)
    {L M : CochainComplex C ℤ} (f : L ⟶ M) :
    QuasiIso (homComplexPostcomp K f) ↔
      ∀ n, Function.Bijective (homClassesPostcomp K f n) := by
  rw [quasiIso_iff]
  apply forall_congr'
  intro n
  rw [quasiIsoAt_iff, (homPostcompLeftHomologyMapData K f n).quasiIso_iff,
    ConcreteCategory.isIso_iff_bijective]
  rfl

/-- Covariance of the Hom complex in its target, packaged as a functor. -/
def homComplexFunctor (K : CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex AddCommGrpCat ℤ where
  obj L := HomComplex K L
  map f := homComplexPostcomp K f
  map_id L := by
    ext n z
    change (z : Cochain K L n).comp (Cochain.ofHom (𝟙 L)) (add_zero n) = z
    rw [Cochain.comp_id]
  map_comp f g := by
    ext n z
    change (z : Cochain K _ n).comp (Cochain.ofHom (f ≫ g)) (add_zero n) =
      ((z : Cochain K _ n).comp (Cochain.ofHom f) (add_zero n)).comp
        (Cochain.ofHom g) (add_zero n)
    rw [Cochain.ofHom_comp]
    exact (Cochain.comp_assoc z (Cochain.ofHom f) (Cochain.ofHom g)
      (add_zero n) (zero_add 0) (by omega)).symm

lemma homComplexFunctor_map (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ}
    (f : L ⟶ M) : (homComplexFunctor K).map f = homComplexPostcomp K f := rfl

/-- Postcomposition is additive in the target morphism. -/
noncomputable instance homComplexFunctor_additive (K : CochainComplex C ℤ) :
    (homComplexFunctor K).Additive where
  map_add {X Y} f g := by
    ext n z
    change (z : Cochain K X n).comp (Cochain.ofHom (f + g)) (add_zero n) =
      (z : Cochain K X n).comp (Cochain.ofHom f) (add_zero n) +
        (z : Cochain K X n).comp (Cochain.ofHom g) (add_zero n)
    rw [Cochain.ofHom_add, Cochain.comp_add]

/-- Postcomposition on cohomology classes is ordinary postcomposition in the
homotopy category. -/
lemma homClassesPostcomp_toHom (K : CochainComplex C ℤ)
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ)
    (z : CohomologyClass K L n) :
    CohomologyClass.toHom (homClassesPostcomp K f n z) =
      CohomologyClass.toHom z ≫
        (HomotopyCategory.quotient C (.up ℤ)).map (f⟦n⟧') := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [homClassesPostcomp_mk, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]
  rfl

/-- Postcomposition with an isomorphism is bijective on morphisms. -/
lemma postcomp_bijective {D : Type*} [Category* D] {A B : D}
    (f : A ⟶ B) [IsIso f] (T : D) :
    Function.Bijective (fun g : T ⟶ A => g ≫ f) := by
  refine ⟨fun g h eq => (cancel_mono f).1 eq, fun g => ⟨g ≫ inv f, ?_⟩⟩
  simp

end Preadditive

section Derived

variable [Abelian C]

/-- Derived morphisms from a K-projective source, computed by cohomology
classes of the ordinary Hom complex. -/
noncomputable def derivedCohomologyClassEquiv (K L : CochainComplex C ℤ)
    [K.IsKProjective] (n : ℤ) :
    CohomologyClass K L n ≃
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (L⟦n⟧)) :=
  (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).toEquiv.trans
    (DerivedCoproducts.derivedHomKProjectiveEquiv K (L⟦n⟧))

lemma derivedCohomologyClassEquiv_postcomp (K : CochainComplex C ℤ)
    [K.IsKProjective] {L M : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ)
    (z : CohomologyClass K L n) :
    derivedCohomologyClassEquiv K M n (homClassesPostcomp K f n z) =
      derivedCohomologyClassEquiv K L n z ≫ DerivedCategory.Q.map (f⟦n⟧') := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  simp only [derivedCohomologyClassEquiv, Equiv.trans_apply]
  change DerivedCoproducts.derivedHomKProjectiveEquiv K (M⟦n⟧)
      (CohomologyClass.toHom (homClassesPostcomp K f n (CohomologyClass.mk z))) = _
  rw [homClassesPostcomp_toHom, DerivedCoproducts.derivedHomKProjectiveEquiv_apply,
    DerivedCoproducts.derivedHomMap_comp]
  rfl

/-- **K-projective sources compute derived Hom.** Postcomposition with a
quasi-isomorphism induces a quasi-isomorphism of ordinary Hom complexes. -/
theorem postcomp_quasiIso_of_isKProjective (K : CochainComplex C ℤ)
    [K.IsKProjective] {L M : CochainComplex C ℤ} (f : L ⟶ M) [QuasiIso f] :
    QuasiIso (homComplexPostcomp K f) := by
  rw [homComplexPostcomp_quasiIso_iff]
  intro n
  haveI : QuasiIso (f⟦n⟧') := inferInstance
  haveI : IsIso (DerivedCategory.Q.map (f⟦n⟧')) := inferInstance
  apply (Function.Bijective.of_comp_iff'
    (derivedCohomologyClassEquiv K M n).bijective _).1
  simpa only [Function.comp_def, derivedCohomologyClassEquiv_postcomp] using
    (postcomp_bijective (DerivedCategory.Q.map (f⟦n⟧')) _).comp
      (derivedCohomologyClassEquiv K L n).bijective

/-- The functor `Hom^•(K,-)` descends to derived categories when `K` is
K-projective. -/
noncomputable def derivedHomComplexFunctor (K : CochainComplex C ℤ)
    [K.IsKProjective] : DerivedCategory C ⥤ DerivedCategory AddCommGrpCat := by
  exact Localization.lift (homComplexFunctor K ⋙ DerivedCategory.Q)
    (fun _ _ f hf => by
      letI : QuasiIso f := (HomologicalComplex.mem_quasiIso_iff f).1 hf
      change IsIso (DerivedCategory.Q.map (homComplexPostcomp K f))
      letI : QuasiIso (homComplexPostcomp K f) :=
        postcomp_quasiIso_of_isKProjective K f
      infer_instance) DerivedCategory.Q

/-- The comparison of the descended Hom-complex functor with its explicit
complex-level representative. -/
noncomputable def derivedHomComplexFunctorFactors (K : CochainComplex C ℤ)
    [K.IsKProjective] :
    DerivedCategory.Q ⋙ derivedHomComplexFunctor K ≅
      homComplexFunctor K ⋙ DerivedCategory.Q :=
  Localization.fac (homComplexFunctor K ⋙ DerivedCategory.Q) _ DerivedCategory.Q

end Derived

end
end RelativeFM.KProjectiveTensorHom

#print axioms RelativeFM.KProjectiveTensorHom.postcomp_quasiIso_of_isKProjective
#print axioms RelativeFM.KProjectiveTensorHom.derivedHomComplexFunctor
#print axioms RelativeFM.KProjectiveTensorHom.derivedHomComplexFunctorFactors
#print axioms RelativeFM.KProjectiveTensorHom.homComplexFunctor_additive
