import FourierMukai.Scheme.DerivedCoproducts
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# K-projective resolutions

This file proves the bounded-above part of Spaltenstein's resolution theorem.  If
`C` is abelian with enough projectives and `K` is strictly bounded above by `d`,
then `boundedAbove K d` is a K-projective resolution of `K`, represented by a
strictly `≤ d` complex of projectives.  It also proves mapping-cone closure,
projective resolutions of single objects, and the corresponding derived-coproduct
statement for families of bounded-above complexes.

The proof resolves the opposite complex by Mathlib's bounded-below injective
resolution (`CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective`),
and transports it back along `CochainComplex.opEquivalence`.

The full unbounded theorem is not asserted here.  What remains is Spaltenstein's
special-direct-system approximation (Lemma 3.3) and the closure of K-projectives
under special direct limits (Corollary 2.8), followed by Theorem 3.4.
-/

@[expose] public section

namespace RelativeFM.KProjectiveResolution

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

attribute [local instance] HasDerivedCategory.standard

/-- The K-projective objects, viewed as a full subcategory of the homotopy category. -/
def kProjective : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal

instance : (kProjective (C := C)).IsClosedUnderIsomorphisms := by
  dsimp [kProjective]
  infer_instance

instance : (kProjective (C := C)).IsTriangulated := by
  dsimp [kProjective]
  infer_instance

lemma mem_kProjective_iff (K : CochainComplex C ℤ) :
    kProjective ((HomotopyCategory.quotient C (.up ℤ)).obj K) ↔ K.IsKProjective :=
  (CochainComplex.isKProjective_iff_leftOrthogonal K).symm

/-- K-projective complexes are closed under mapping cones. -/
lemma isKProjective_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L)
    [K.IsKProjective] [L.IsKProjective] :
    (CochainComplex.mappingCone f).IsKProjective := by
  rw [← mem_kProjective_iff]
  apply kProjective.ext_of_isTriangulatedClosed₃
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
  · exact (mem_kProjective_iff K).2 inferInstance
  · exact (mem_kProjective_iff L).2 inferInstance

/-- A usual projective resolution gives a K-projective resolution of an object placed
in cohomological degree zero. -/
noncomputable def singleZero (X : C) [HasProjectiveResolution X] :
    DerivedCoproducts.KProjectiveResolution
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X)) :=
  let P := CategoryTheory.projectiveResolution X
  { complex := P.cochainComplex
    isKProjective := CochainComplex.isKProjective_of_projective P.cochainComplex 0
    iso := asIso (DerivedCategory.Q.map P.π') }

#print axioms RelativeFM.KProjectiveResolution.isKProjective_mappingCone
#print axioms RelativeFM.KProjectiveResolution.singleZero

end

end RelativeFM.KProjectiveResolution

namespace ComplexShape.Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- A surjective embedding of complex shapes commutes with `prev`. -/
lemma prev_f_of_surjective (e : c.Embedding c') [e.IsRelIff]
    (he : Function.Surjective e.f) {i j : ι} (hij : c.prev j = i) :
    c'.prev (e.f j) = e.f i := by
  by_cases h : c'.Rel (c'.prev (e.f j)) (e.f j)
  · obtain ⟨p, hp⟩ := he (c'.prev (e.f j))
    have hprel : c.Rel p j := (e.rel_iff p j).1 (by rwa [hp])
    have hp' : c.prev j = p := c.prev_eq' hprel
    calc
      c'.prev (e.f j) = e.f p := hp.symm
      _ = e.f i := by rw [← hp', hij]
  · have hf : c'.prev (e.f j) = e.f j := c'.prev_eq_self _ h
    have hc : ∀ k, ¬ c.Rel k j := by
      intro k hk
      have hk' := e.rel hk
      exact h (by simpa only [c'.prev_eq' hk'] using hk')
    have hs : c.prev j = j := c.prev_eq_self j (hc _)
    rw [← hij, hs]
    exact hf

/-- A surjective embedding of complex shapes commutes with `next`. -/
lemma next_f_of_surjective (e : c.Embedding c') [e.IsRelIff]
    (he : Function.Surjective e.f) {j k : ι} (hjk : c.next j = k) :
    c'.next (e.f j) = e.f k := by
  by_cases h : c'.Rel (e.f j) (c'.next (e.f j))
  · obtain ⟨p, hp⟩ := he (c'.next (e.f j))
    have hprel : c.Rel j p := (e.rel_iff j p).1 (by rwa [hp])
    have hp' : c.next j = p := c.next_eq' hprel
    calc
      c'.next (e.f j) = e.f p := hp.symm
      _ = e.f k := by rw [← hp', hjk]
  · have hf : c'.next (e.f j) = e.f j := c'.next_eq_self _ h
    have hc : ∀ k, ¬ c.Rel j k := by
      intro k hk
      have hk' := e.rel hk
      exact h (by simpa only [c'.next_eq' hk'] using hk')
    have hs : c.next j = j := c.next_eq_self j (hc _)
    rw [← hjk, hs]
    exact hf

end ComplexShape.Embedding

section RestrictionQuasiIso

universe u v

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable {K L : HomologicalComplex C c'} (φ : K ⟶ L) (e : c.Embedding c')

lemma HomologicalComplex.restrictionXIso_hom_comp_restrictionMap [e.IsRelIff]
    {i : ι} {i' : ι'} (hi : e.f i = i') :
    (K.restrictionXIso e hi).hom ≫ φ.f i' =
      (HomologicalComplex.restrictionMap φ e).f i ≫ (L.restrictionXIso e hi).hom := by
  rw [HomologicalComplex.restrictionMap_f' φ e hi]
  simp

/-- Restriction along a surjective embedding preserves and reflects quasi-isomorphisms
in each degree. -/
lemma HomologicalComplex.quasiIsoAt_restrictionMap_iff_of_surjective [e.IsRelIff]
    (he : Function.Surjective e.f) (j : ι)
    [K.HasHomology (e.f j)] [L.HasHomology (e.f j)]
    [(K.restriction e).HasHomology j] [(L.restriction e).HasHomology j] :
    QuasiIsoAt (HomologicalComplex.restrictionMap φ e) j ↔ QuasiIsoAt φ (e.f j) := by
  rw [quasiIsoAt_iff' _ _ _ _ rfl rfl,
    quasiIsoAt_iff' φ _ _ _ (e.prev_f_of_surjective he rfl)
      (e.next_f_of_surjective he rfl)]
  apply ShortComplex.quasiIso_iff_of_arrow_mk_iso
  exact Iso.refl _

/-- Restriction along a surjective embedding of complex shapes preserves and reflects
quasi-isomorphisms. -/
lemma HomologicalComplex.quasiIso_restrictionMap_iff_of_surjective [e.IsRelIff]
    (he : Function.Surjective e.f)
    [∀ j, K.HasHomology j] [∀ j, L.HasHomology j]
    [∀ j, (K.restriction e).HasHomology j] [∀ j, (L.restriction e).HasHomology j] :
    QuasiIso (HomologicalComplex.restrictionMap φ e) ↔ QuasiIso φ := by
  rw [quasiIso_iff, quasiIso_iff]
  constructor
  · intro h j'
    obtain ⟨j, rfl⟩ := he j'
    exact (HomologicalComplex.quasiIsoAt_restrictionMap_iff_of_surjective φ e he j).1 (h j)
  · intro h j
    exact (HomologicalComplex.quasiIsoAt_restrictionMap_iff_of_surjective φ e he j).2 (h (e.f j))

end RestrictionQuasiIso

namespace RelativeFM.KProjectiveResolution

#print axioms ComplexShape.Embedding.prev_f_of_surjective
#print axioms ComplexShape.Embedding.next_f_of_surjective
#print axioms HomologicalComplex.quasiIso_restrictionMap_iff_of_surjective

end RelativeFM.KProjectiveResolution
section OppositeQuasiIso

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Transport of quasi-isomorphisms through the inverse of the opposite-complex
equivalence (with the cohomological reindexing `n ↦ -n`). -/
lemma CochainComplex.quasiIso_unop_opEquivalence_inverse_map_iff
    {K L : CochainComplex Cᵒᵖ ℤ} (f : K ⟶ L) :
    QuasiIso ((CochainComplex.opEquivalence C).inverse.map f).unop ↔ QuasiIso f := by
  change QuasiIso ((HomologicalComplex.unopFunctor C (.down ℤ)).map
    (HomologicalComplex.restrictionMap f
      ComplexShape.embeddingDownIntUpInt).op) ↔ QuasiIso f
  rw [HomologicalComplex.quasiIso_unopFunctor_map_iff,
    HomologicalComplex.quasiIso_restrictionMap_iff_of_surjective _ _
      (fun n ↦ ⟨-n, by simp⟩)]

end OppositeQuasiIso

namespace RelativeFM.KProjectiveResolution

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Spaltenstein's bounded-above step, obtained from Mathlib's bounded-below
injective resolution in the opposite category. -/
lemma exists_projective_resolution_of_isStrictlyLE [EnoughProjectives C]
    (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    ∃ (P : CochainComplex C ℤ) (π : P ⟶ K), QuasiIso π ∧
      P.IsStrictlyLE d ∧ ∀ n, Projective (P.X n) := by
  let E := CochainComplex.opEquivalence C
  let Kop : CochainComplex Cᵒᵖ ℤ := E.functor.obj (op K)
  have hKop : Kop.IsStrictlyGE (-d) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE d _ (by dsimp; lia)).op
  letI : Kop.IsStrictlyGE (-d) := hKop
  obtain ⟨L, i, hi, hL, hLge⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective Kop (-d)
  let P : CochainComplex C ℤ :=
    (L.restriction ComplexShape.embeddingDownIntUpInt).unopSymm
  let K₀ : CochainComplex C ℤ := (E.inverse.obj (E.functor.obj (op K))).unop
  let π₀ : P ⟶ K₀ := (E.inverse.map i).unop
  let eK : K₀ ≅ K :=
    (E.unitIso.app (op K)).unop
  have hπ₀ : QuasiIso π₀ :=
    (CochainComplex.quasiIso_unop_opEquivalence_inverse_map_iff i).2 hi
  letI : QuasiIso π₀ := hπ₀
  let π : P ⟶ K := π₀ ≫ eK.hom
  have hP : P.IsStrictlyLE d := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    change IsZero (unop (L.X (-n)))
    exact (L.isZero_of_isStrictlyGE (-d) (-n) (by lia)).unop
  have hproj (n : ℤ) : Projective (P.X n) := by
    change Projective (unop (L.X (-n)))
    infer_instance
  refine ⟨P, π, inferInstance, hP, hproj⟩

end RelativeFM.KProjectiveResolution

namespace RelativeFM.KProjectiveResolution

universe u v

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A bounded-above complex has a K-projective resolution, computed by a bounded-above
complex of projective objects. -/
noncomputable def boundedAbove [EnoughProjectives C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    DerivedCoproducts.KProjectiveResolution (DerivedCategory.Q.obj K) :=
  let H := exists_projective_resolution_of_isStrictlyLE K d
  let P := H.choose
  let π : P ⟶ K := H.choose_spec.choose
  let hπ : QuasiIso π := H.choose_spec.choose_spec.1
  let hP : P.IsStrictlyLE d := H.choose_spec.choose_spec.2.1
  let hproj : ∀ n, Projective (P.X n) := H.choose_spec.choose_spec.2.2
  letI : QuasiIso π := hπ
  letI : P.IsStrictlyLE d := hP
  letI (n : ℤ) : Projective (P.X n) := hproj n
  { complex := P
    isKProjective := CochainComplex.isKProjective_of_projective P d
    iso := asIso (DerivedCategory.Q.map π) }

#print axioms RelativeFM.KProjectiveResolution.exists_projective_resolution_of_isStrictlyLE
#print axioms RelativeFM.KProjectiveResolution.boundedAbove
#print axioms CochainComplex.quasiIso_unop_opEquivalence_inverse_map_iff

end RelativeFM.KProjectiveResolution

namespace RelativeFM.KProjectiveResolution

open CategoryTheory CategoryTheory.Limits

universe w u v

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} (K : ι → CochainComplex C ℤ) (d : ι → ℤ)

/-- Coproducts of bounded-above complexes exist in the derived category. The bounds
may vary with the summand; no unbounded Spaltenstein replacement is needed. -/
theorem hasCoproductQObjOfIsStrictlyLE [EnoughProjectives C] [HasDerivedCategory C]
    [HasCoproductsOfShape ι C] [∀ i, (K i).IsStrictlyLE (d i)] :
    HasCoproduct (fun i ↦ DerivedCategory.Q.obj (K i)) :=
  DerivedCoproducts.hasCoproductOfKProjectiveResolutions _
    (fun i ↦ boundedAbove (K i) (d i))

#print axioms RelativeFM.KProjectiveResolution.hasCoproductQObjOfIsStrictlyLE

end RelativeFM.KProjectiveResolution
