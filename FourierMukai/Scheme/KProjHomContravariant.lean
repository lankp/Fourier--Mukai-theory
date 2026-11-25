import FourierMukai.Scheme.KProjHomComplex
import FourierMukai.Scheme.KProjIndependence

/-!
# Contravariant Hom-complex maps between K-projective sources

A quasi-isomorphism between K-projective complexes induces a quasi-isomorphism
between their ordinary Hom complexes.  Consequently the derived Hom model does
not depend on the chosen K-projective representative.
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

/-- Precomposition as a morphism of homomorphism complexes. -/
def homComplexPrecomp {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) : HomComplex K L ⟶ HomComplex K' L where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z => (Cochain.ofHom f).comp z (zero_add n)
      map_zero' := by ext p q hpq; simp
      map_add' := by intro x y; ext p q hpq; simp }
  comm' _ m _ := by
    ext z
    exact δ_ofHom_comp f z m

@[simp]
lemma homComplexPrecomp_f_apply {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) (z : Cochain K L n) :
    ((homComplexPrecomp f L).f n).hom z =
      (Cochain.ofHom f).comp z (zero_add n) := rfl

lemma homComplexPrecomp_δ {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n m : ℤ) (z : Cochain K L n) :
    δ n m (((homComplexPrecomp f L).f n).hom z) =
      ((homComplexPrecomp f L).f m).hom (δ n m z) :=
  ConcreteCategory.congr_hom ((homComplexPrecomp f L).comm n m) z

/-- The map on cocycles induced by `homComplexPrecomp`. -/
def homCocyclesPrecomp {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) : Cocycle K L n →+ Cocycle K' L n where
  toFun z := ⟨((homComplexPrecomp f L).f n).hom (z : Cochain K L n), by
    change δ n (n + 1) (((homComplexPrecomp f L).f n).hom (z : Cochain K L n)) = 0
    rw [homComplexPrecomp_δ, z.δ_eq_zero]
    exact ((homComplexPrecomp f L).f (n + 1)).hom.map_zero⟩
  map_zero' := Subtype.ext (((homComplexPrecomp f L).f n).hom.map_zero)
  map_add' x y := Subtype.ext (((homComplexPrecomp f L).f n).hom.map_add
    (x : Cochain K L n) (y : Cochain K L n))

@[simp]
lemma homCocyclesPrecomp_apply {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) (z : Cocycle K L n) :
    homCocyclesPrecomp f L n z = z.precomp f := rfl

/-- The map on cohomology classes induced by `homComplexPrecomp`. -/
def homClassesPrecomp {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass K L n →+ CohomologyClass K' L n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K' L n).comp (homCocyclesPrecomp f L n)) (by
      rintro z ⟨r, hr, b, hb⟩
      change CohomologyClass.mk (homCocyclesPrecomp f L n z) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ r hr]
      refine ⟨((homComplexPrecomp f L).f r).hom b, ?_⟩
      change δ r n (((homComplexPrecomp f L).f r).hom b) =
        ((homComplexPrecomp f L).f n).hom (z : Cochain K L n)
      rw [homComplexPrecomp_δ, hb])

@[simp]
lemma homClassesPrecomp_mk {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) (z : Cocycle K L n) :
    homClassesPrecomp f L n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.precomp f) := rfl

/-- The explicit homology comparison for `homComplexPrecomp`. -/
def homPrecompLeftHomologyMapData {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
        (homComplexPrecomp f L))
      (leftHomologyData K L n) (leftHomologyData K' L n) := by
  let F := homComplexPrecomp f L
  refine { φK := AddCommGrpCat.ofHom (homCocyclesPrecomp f L n)
           φH := AddCommGrpCat.ofHom (homClassesPrecomp f L n)
           commi := ?_, commf' := ?_, commπ := ?_ }
  · ext z
    rfl
  · have hi : AddCommGrpCat.ofHom (homCocyclesPrecomp f L n) ≫
        (leftHomologyData K' L n).i = (leftHomologyData K L n).i ≫ F.f n := by
      ext z
      rfl
    rw [← cancel_mono (leftHomologyData K' L n).i, Category.assoc, hi, ← Category.assoc,
      ShortComplex.LeftHomologyData.f'_i, Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor _ _ n).map F).comm₁₂.symm
  · ext z
    rfl

/-- A precomposition morphism of Hom complexes is a quasi-isomorphism exactly
when its maps on cohomology classes are bijective in every degree. -/
lemma homComplexPrecomp_quasiIso_iff {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) :
    QuasiIso (homComplexPrecomp f L) ↔
      ∀ n, Function.Bijective (homClassesPrecomp f L n) := by
  rw [quasiIso_iff]
  apply forall_congr'
  intro n
  rw [quasiIsoAt_iff, (homPrecompLeftHomologyMapData f L n).quasiIso_iff,
    ConcreteCategory.isIso_iff_bijective]
  rfl

/-- Contravariance of the Hom complex in its source, packaged as a functor. -/
def homComplexContravariantFunctor (L : CochainComplex C ℤ) :
    (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex AddCommGrpCat ℤ where
  obj K := HomComplex K.unop L
  map f := homComplexPrecomp f.unop L
  map_id K := by
    ext n z
    change (Cochain.ofHom (𝟙 K.unop)).comp (z : Cochain K.unop L n) (zero_add n) = z
    rw [Cochain.id_comp]
  map_comp f g := by
    ext n z
    change (Cochain.ofHom (g.unop ≫ f.unop)).comp (z : Cochain _ L n) (zero_add n) =
      (Cochain.ofHom g.unop).comp
        ((Cochain.ofHom f.unop).comp (z : Cochain _ L n) (zero_add n)) (zero_add n)
    rw [Cochain.ofHom_comp]
    exact Cochain.comp_assoc (Cochain.ofHom g.unop) (Cochain.ofHom f.unop) z
      (zero_add 0) (zero_add n) (by omega)

/-- Precomposition on cohomology classes is ordinary precomposition in the
homotopy category. -/
lemma homClassesPrecomp_toHom {K K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) (z : CohomologyClass K L n) :
    CohomologyClass.toHom (homClassesPrecomp f L n z) =
      (HomotopyCategory.quotient C (.up ℤ)).map f ≫ CohomologyClass.toHom z := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [homClassesPrecomp_mk, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, Functor.map_comp]
  rfl

/-- Precomposition with an isomorphism is bijective on morphisms. -/
lemma precomp_bijective {D : Type*} [Category* D] {A B : D}
    (f : A ⟶ B) [IsIso f] (T : D) :
    Function.Bijective (fun g : B ⟶ T => f ≫ g) := by
  refine ⟨fun g h eq => (cancel_epi f).1 eq, fun g => ⟨inv f ≫ g, ?_⟩⟩
  simp

end Preadditive

section Derived

variable [Abelian C]

/-- The derived comparison induced by precomposition. -/
lemma derivedCohomologyClassEquiv_precomp {K K' : CochainComplex C ℤ}
    [K.IsKProjective] [K'.IsKProjective] (f : K' ⟶ K)
    (L : CochainComplex C ℤ) (n : ℤ) (z : CohomologyClass K L n) :
    derivedCohomologyClassEquiv K' L n (homClassesPrecomp f L n z) =
      DerivedCategory.Q.map f ≫ derivedCohomologyClassEquiv K L n z := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  simp only [derivedCohomologyClassEquiv, Equiv.trans_apply]
  change DerivedCoproducts.derivedHomKProjectiveEquiv K' (L⟦n⟧)
      (CohomologyClass.toHom (homClassesPrecomp f L n (CohomologyClass.mk z))) = _
  rw [homClassesPrecomp_toHom, DerivedCoproducts.derivedHomKProjectiveEquiv_apply,
    DerivedCoproducts.derivedHomMap_comp]
  rfl

/-- **Independence of K-projective representatives for derived Hom.** -/
theorem precomp_quasiIso_of_isKProjective {K K' : CochainComplex C ℤ}
    [K.IsKProjective] [K'.IsKProjective] (f : K' ⟶ K)
    (L : CochainComplex C ℤ) [QuasiIso f] :
    QuasiIso (homComplexPrecomp f L) := by
  rw [homComplexPrecomp_quasiIso_iff]
  intro n
  haveI : IsIso (DerivedCategory.Q.map f) := inferInstance
  apply (Function.Bijective.of_comp_iff'
    (derivedCohomologyClassEquiv K' L n).bijective _).1
  simpa only [Function.comp_def, derivedCohomologyClassEquiv_precomp] using
    (precomp_bijective (DerivedCategory.Q.map f) _).comp
      (derivedCohomologyClassEquiv K L n).bijective

/-- The induced derived comparison between Hom models of two K-projective
representatives is an isomorphism. -/
noncomputable def qObjHomComplexIsoOfDerivedIso {K K' : CochainComplex C ℤ}
    [K.IsKProjective] [K'.IsKProjective]
    (e : DerivedCategory.Q.obj K' ≅ DerivedCategory.Q.obj K)
    (L : CochainComplex C ℤ) :
    DerivedCategory.Q.obj (HomComplex K L) ≅ DerivedCategory.Q.obj (HomComplex K' L) := by
  let f := (homotopyEquivOfDerivedIso e).hom
  haveI : QuasiIso f := homotopyEquivalences_le_quasiIso _ _ _
    (homotopyEquivOfDerivedIso e).homotopyEquivalences_hom
  haveI : QuasiIso (homComplexPrecomp f L) := precomp_quasiIso_of_isKProjective f L
  exact asIso (DerivedCategory.Q.map (homComplexPrecomp f L))

end Derived
end
end RelativeFM.KProjectiveTensorHom

#print axioms RelativeFM.KProjectiveTensorHom.precomp_quasiIso_of_isKProjective
#print axioms RelativeFM.KProjectiveTensorHom.qObjHomComplexIsoOfDerivedIso
