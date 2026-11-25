/-
Compactness of the regular module, and the affine K-projective compactness argument.
This file is in the m1 namespace; it is intended to be split into the repository's
affine compactness layer after integration.
-/
import FourierMukai.Scheme.AffineUniverse
import WeakApprox.CompactAb
import WeakApprox.CompactThick
import FourierMukai.Scheme.SmallAffineAssembly
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Module.Equiv.Basic

@[expose] public section

namespace RelativeFM.NeemanM1

open CategoryTheory CategoryTheory.Limits
open RelativeWeakApprox

universe u v

noncomputable section

/-- Module maps from the regular module are the points of the target, additively. -/
noncomputable def regularHomEvalAddEquiv (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) : (ModuleCat.of A A ⟶ M) ≃+ M where
  toFun f := f 1
  invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton A M x)
  left_inv f := by
    apply ModuleCat.hom_ext
    change LinearMap.toSpanSingleton A M (f 1) = f.hom
    exact (LinearMap.ringLmapEquivSelf A ℕ M).symm_apply_apply f.hom
  right_inv x := by simp
  map_add' f g := rfl

@[simp]
lemma regularHomEvalAddEquiv_apply (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) (f : ModuleCat.of A A ⟶ M) :
    regularHomEvalAddEquiv A M f = f 1 := rfl

/-- The explicit direct-sum cofan, after applying `Hom(A, -)`. -/
noncomputable abbrev regularHomCofan (A : Type u) [CommRing A]
    {J : Type u} [DecidableEq J] (M : J → ModuleCat.{u} A) :
    Cofan (fun j => (abCoyoneda (ModuleCat.of A A)).obj (M j)) :=
  Cofan.mk ((abCoyoneda (ModuleCat.of A A)).obj (ModuleCat.coproductCocone M).pt)
    (fun j => (abCoyoneda (ModuleCat.of A A)).map ((ModuleCat.coproductCocone M).inj j))

/-- On generators of the finite-support direct sum, the comparison map is just
inclusion followed by evaluation at `1`. -/
@[simp]
lemma regularHomCofan_abCofanSum_single (A : Type u) [CommRing A]
    {J : Type u} [DecidableEq J] (M : J → ModuleCat.{u} A)
    (j : J) (f : ModuleCat.of A A ⟶ M j) (x : A) :
    ((abCofanSum (regularHomCofan A M) (DFinsupp.single j f) :
      ModuleCat.of A A ⟶ (ModuleCat.coproductCocone M).pt).hom) x =
      DirectSum.lof A J (fun j => M j) j (f x) := by
  rw [abCofanSum_single]
  rfl

/-- A single summand is detected by the direct-sum projections. -/
lemma regularHomCofan_abCofanSum_single_component (A : Type u) [CommRing A]
    {J : Type u} [DecidableEq J] (M : J → ModuleCat.{u} A)
    (i j : J) (f : ModuleCat.of A A ⟶ M i) :
    DirectSum.component A J (fun j => M j) j
      (((abCofanSum (regularHomCofan A M) (DFinsupp.single i f) :
        ModuleCat.of A A ⟶ (ModuleCat.coproductCocone M).pt).hom) 1) =
      ((DFinsupp.single i f : DFinsupp (fun j => ModuleCat.of A A ⟶ M j)) j) 1 := by
  rw [regularHomCofan_abCofanSum_single]
  by_cases h : i = j
  · subst j
    simp
  · have h' : j ≠ i := Ne.symm h
    simp only [DFinsupp.single_eq_of_ne h']
    rw [DirectSum.component.of]
    simp [h]

/-- The coordinate form of the finite-support comparison map. -/
lemma regularHomCofan_abCofanSum_apply_one_apply (A : Type u) [CommRing A]
    {J : Type u} [DecidableEq J] (M : J → ModuleCat.{u} A)
    (z : DFinsupp (fun j => ModuleCat.of A A ⟶ M j)) (j : J) :
    DirectSum.component A J (fun j => M j) j
      (((abCofanSum (regularHomCofan A M) z :
        ModuleCat.of A A ⟶ (ModuleCat.coproductCocone M).pt).hom) 1) = (z j) 1 := by
  let lhs : DFinsupp (fun j => ModuleCat.of A A ⟶ M j) →+ M j :=
    (DirectSum.component A J (fun j => M j) j).toAddMonoidHom.comp
      ((regularHomEvalAddEquiv A (ModuleCat.coproductCocone M).pt).toAddMonoidHom.comp
        (abCofanSum (regularHomCofan A M)).hom)
  let rhs : DFinsupp (fun j => ModuleCat.of A A ⟶ M j) →+ M j :=
    (regularHomEvalAddEquiv A (M j)).toAddMonoidHom.comp (DFinsupp.evalAddMonoidHom j)
  have h : lhs = rhs := by
    apply DFinsupp.addHom_ext
    intro i f
    exact regularHomCofan_abCofanSum_single_component A M i j f
  exact DFunLike.congr_fun h z

/-- `Hom(A, -)` takes the concrete direct sum of modules to the direct sum of
abelian groups. -/
lemma regularHomCofan_abCofanSum_bijective (A : Type u) [CommRing A]
    {J : Type u} [DecidableEq J] (M : J → ModuleCat.{u} A) :
    Function.Bijective (abCofanSum (regularHomCofan A M)) := by
  constructor
  · intro z w h
    apply DFinsupp.ext
    intro j
    apply (regularHomEvalAddEquiv A (M j)).injective
    change (z j) 1 = (w j) 1
    rw [← regularHomCofan_abCofanSum_apply_one_apply A M z j,
      ← regularHomCofan_abCofanSum_apply_one_apply A M w j, h]
  · intro q
    change ModuleCat.of A A ⟶ (ModuleCat.coproductCocone M).pt at q
    let x : DirectSum J (fun j => M j) := q 1
    let z : DFinsupp (fun j => ModuleCat.of A A ⟶ M j) :=
      DFinsupp.mapRange.addMonoidHom
        (fun j => (regularHomEvalAddEquiv A (M j)).symm.toAddMonoidHom) x
    refine ⟨z, ?_⟩
    apply (regularHomEvalAddEquiv A (ModuleCat.coproductCocone M).pt).injective
    apply DirectSum.ext_component A
    intro j
    change DirectSum.component A J (fun j => M j) j
      (((abCofanSum (regularHomCofan A M) z :
        ModuleCat.of A A ⟶ (ModuleCat.coproductCocone M).pt).hom) 1) =
      DirectSum.component A J (fun j => M j) j (q 1)
    rw [regularHomCofan_abCofanSum_apply_one_apply]
    simp only [z, DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_apply,
      regularHomEvalAddEquiv_apply, AddEquiv.apply_symm_apply]
    change regularHomEvalAddEquiv A (M j) ((regularHomEvalAddEquiv A (M j)).symm (x j)) = x j
    exact (regularHomEvalAddEquiv A (M j)).apply_symm_apply (x j)

/-- The concrete direct-sum cofan stays a coproduct after applying `Hom(A, -)`. -/
noncomputable def regularHomCofanIsColimit (A : Type u) [CommRing A]
    {J : Type u} [DecidableEq J] (M : J → ModuleCat.{u} A) :
    IsColimit (regularHomCofan A M) :=
  isColimitCofan_of_bijective_abCofanSum _ (regularHomCofan_abCofanSum_bijective A M)

/-- The regular module is coproduct-compact as an object of its module category. -/
theorem regularModule_isCompactAb (A : Type u) [CommRing A] :
    IsCompactAb (ModuleCat.of A A) where
  preserves J := by
    classical
    letI : ∀ (M : J → ModuleCat.{u} A),
        PreservesColimit (Discrete.functor M) (abCoyoneda (ModuleCat.of A A)) :=
      fun M => preservesColimit_of_preserves_colimit_cocone
        (ModuleCat.coproductCoconeIsColimit M)
        ((Cofan.isColimitMapCoconeEquiv (abCoyoneda (ModuleCat.of A A)) M
          (ModuleCat.coproductCocone M)).symm (regularHomCofanIsColimit A M))
    haveI : PreservesColimitsOfShape (Discrete J) (abCoyoneda (ModuleCat.of A A)) :=
      preservesColimitsOfShape_of_discrete _
    exact preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive (ModuleCat.of A A))

section PreadditiveCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {J : Type v} [DecidableEq J]

/-- The Hom-cofan attached to explicit coproduct legs in a preadditive category. -/
noncomputable abbrev homCofan (H S : C) {X : J → C} (g : ∀ j, X j ⟶ S) :
    Cofan (fun j => (abCoyoneda H).obj (X j)) :=
  Cofan.mk ((abCoyoneda H).obj S) (fun j => (abCoyoneda H).map (g j))

@[simp]
lemma abCofanSum_homCofan_comp_coproductProjection (H S : C) {X : J → C}
    (g : ∀ j, X j ⟶ S) (hc : IsColimit (Cofan.mk S g))
    (z : DFinsupp (fun j => H ⟶ X j)) (j : J) :
    abCofanSum (homCofan H S g) z ≫ coproductProjection g hc j = z j := by
  let post : (H ⟶ S) →+ (H ⟶ X j) :=
    ((abCoyoneda H).map (coproductProjection g hc j)).hom
  have hz := post.map_dfinsuppSumAddHom z (fun k => ((homCofan H S g).inj k).hom)
  calc
    abCofanSum (homCofan H S g) z ≫ coproductProjection g hc j =
        post ((DFinsupp.sumAddHom fun k => ((homCofan H S g).inj k).hom) z) := rfl
    _ = (DFinsupp.sumAddHom fun k => post.comp ((homCofan H S g).inj k).hom) z := hz
    _ = z j := by
      have hfun : (fun k => post.comp ((homCofan H S g).inj k).hom) =
          Pi.single j (AddMonoidHom.id (H ⟶ X j)) := by
        funext k
        by_cases h : k = j
        · subst k
          ext q
          dsimp [post]
          rw [Category.assoc, coproductProjection_comp]
          simp
        · ext q
          dsimp [post]
          rw [Category.assoc, coproductProjection_comp]
          simp [h]
      rw [hfun, DFinsupp.sumAddHom_piSingle]
      rfl

/-- Postcomposition is natural for finite-support decompositions. -/
lemma abCofanSum_homCofan_mapRange_comp (H S T : C) {X Y : J → C}
    (gX : ∀ j, X j ⟶ S) (gY : ∀ j, Y j ⟶ T)
    (d : ∀ j, X j ⟶ Y j) (dS : S ⟶ T)
    (hcomm : ∀ j, gX j ≫ dS = d j ≫ gY j)
    (z : DFinsupp (fun j => H ⟶ X j)) :
    abCofanSum (homCofan H T gY)
      (DFinsupp.mapRange (fun j q => q ≫ d j) (fun j => by simp) z) =
        abCofanSum (homCofan H S gX) z ≫ dS := by
  classical
  let post : (H ⟶ S) →+ (H ⟶ T) := ((abCoyoneda H).map dS).hom
  have hz := post.map_dfinsuppSumAddHom z (fun k => ((homCofan H S gX).inj k).hom)
  change (DFinsupp.sumAddHom fun k => ((homCofan H T gY).inj k).hom)
      (DFinsupp.mapRange (fun j q => q ≫ d j) (fun j => by simp) z) =
    post ((DFinsupp.sumAddHom fun k => ((homCofan H S gX).inj k).hom) z)
  rw [hz]
  simp only [DFinsupp.sumAddHom_apply]
  rw [DFinsupp.sum_mapRange_index (h0 := fun j => by
    change (0 : H ⟶ Y j) ≫ gY j = 0
    exact Limits.zero_comp)]
  apply congrArg (fun F : ∀ j, (H ⟶ X j) → (H ⟶ T) => z.sum F)
  funext j q
  dsimp [post, homCofan, abCoyoneda]
  simpa only [Category.assoc] using congrArg (fun e => q ≫ e) (hcomm j).symm

/-- Additive functors commute with finite-support sums of Hom classes. -/
lemma abCofanSum_homCofan_mapRange_map {D : Type*} [Category.{v} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (H S : C) {X : J → C} (g : ∀ j, X j ⟶ S)
    (z : DFinsupp (fun j => H ⟶ X j)) :
    abCofanSum (homCofan (F.obj H) (F.obj S) (fun j => F.map (g j)))
      (DFinsupp.mapRange (fun j q => F.map q) (fun j => by simp) z) =
        F.map (abCofanSum (homCofan H S g) z) := by
  classical
  let post : (H ⟶ S) →+ (F.obj H ⟶ F.obj S) := F.mapAddHom
  have hz := post.map_dfinsuppSumAddHom z (fun k => ((homCofan H S g).inj k).hom)
  change (DFinsupp.sumAddHom fun k =>
      ((homCofan (F.obj H) (F.obj S) (fun j => F.map (g j))).inj k).hom)
      (DFinsupp.mapRange (fun j q => F.map q) (fun j => by simp) z) =
    post ((DFinsupp.sumAddHom fun k => ((homCofan H S g).inj k).hom) z)
  rw [hz]
  simp only [DFinsupp.sumAddHom_apply]
  rw [DFinsupp.sum_mapRange_index (h0 := fun j => by
    dsimp [homCofan, abCoyoneda]
    exact Limits.zero_comp)]
  apply congrArg (fun G : ∀ j, (H ⟶ X j) → (F.obj H ⟶ F.obj S) => z.sum G)
  funext j q
  dsimp [post, homCofan, abCoyoneda]
  rw [← F.map_comp]
  rfl

/-- Compactness supplies finite-support decompositions over every coproduct cocone. -/
lemma exists_abCofanSum_homCofan (H S : C) [IsCompactAb H] {X : J → C}
    (g : ∀ j, X j ⟶ S) (hc : IsColimit (Cofan.mk S g)) (f : H ⟶ S) :
    ∃ z : DFinsupp (fun j => H ⟶ X j), abCofanSum (homCofan H S g) z = f := by
  letI : PreservesColimitsOfShape (Discrete J) (abCoyoneda H) :=
    preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive H).symm
  have hc' : IsColimit (homCofan H S g) :=
    (Cofan.isColimitMapCoconeEquiv (abCoyoneda H) X (Cofan.mk S g))
      (isColimitOfPreserves (abCoyoneda H) hc)
  exact (bijective_abCofanSum_of_isColimit hc').2 f

end PreadditiveCoproducts

section SingleComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The cochain complex supported at a single object in degree zero. -/
noncomputable abbrev singleZeroComplex (P : C) : CochainComplex C ℤ :=
  (HomologicalComplex.single C (.up ℤ) 0).obj P

/-- The chain map out of a single complex attached to a degree-zero chain map,
or zero if the input is not a cycle. -/
noncomputable def singleMapOrZero (P : C) (K : CochainComplex C ℤ) (g : P ⟶ K.X 0) :
    singleZeroComplex P ⟶ K := by
  classical
  exact if hg : g ≫ K.d 0 1 = 0 then
    HomologicalComplex.mkHomFromSingle g (fun k hk => by
      obtain rfl : (1 : ℤ) = k := by simpa using hk
      exact hg)
  else 0

lemma singleMapOrZero_zero (P : C) (K : CochainComplex C ℤ) :
    singleMapOrZero P K (0 : P ⟶ K.X 0) = 0 := by
  classical
  unfold singleMapOrZero
  split
  · apply HomologicalComplex.from_single_hom_ext
    simp
  · rename_i h
    exact (h (by simp)).elim

lemma singleMapOrZero_f_zero (P : C) (K : CochainComplex C ℤ) (g : P ⟶ K.X 0)
    (hg : g ≫ K.d 0 1 = 0) :
    (singleMapOrZero P K g).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).hom ≫ g := by
  classical
  unfold singleMapOrZero
  split
  · exact HomologicalComplex.mkHomFromSingle_f _ _
  · rename_i h
    exact (h hg).elim

end SingleComplex

section DerivedCoproductHom

open RelativeFM.DerivedCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{v} C]
variable {J : Type v} [DecidableEq J] [HasCoproductsOfShape J C]
variable (K₀ : CochainComplex C ℤ) (K : J → CochainComplex C ℤ)
variable [∀ j, (K j).IsKProjective]

/-- Evaluation of the explicit degreewise coproduct of complexes. -/
noncomputable abbrev complexCoproductEvalCofan (n : ℤ) : Cofan (fun j => (K j).X n) :=
  Cofan.mk ((coproductComplexCocone K).pt.X n)
    (fun j => ((coproductComplexCocone K).ι.app ⟨j⟩).f n)

noncomputable def complexCoproductEvalCofan_isColimit (n : ℤ) :
    IsColimit (complexCoproductEvalCofan K n) := by
  have h := isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) n)
    (coproductComplexCoconeIsColimit K)
  exact (Cofan.isColimitMapCoconeEquiv (HomologicalComplex.eval C (.up ℤ) n)
    (fun j => K j) (coproductComplexCocone K)) h

/-- The cofan of derived Homs out of a fixed complex on the explicit
K-projective derived coproduct. -/
noncomputable abbrev derivedHomCofan : Cofan (fun j =>
    (abCoyoneda (DerivedCategory.Q.obj K₀)).obj (DerivedCategory.Q.obj (K j))) :=
  homCofan (DerivedCategory.Q.obj K₀) (derivedCoproductCofan K).pt
    (derivedCoproductCofan K).inj

/-- Reconstruct a chain map out of a single complex from a finite-support
decomposition of its degree-zero component. -/
lemma abCofanSum_singleMapOrZero_of_cycles (P : C) (K : J → CochainComplex C ℤ)
    (f : singleZeroComplex P ⟶ (coproductComplexCocone K).pt)
    (z : DFinsupp (fun j => P ⟶ (K j).X 0))
    (hz : abCofanSum (homCofan P ((coproductComplexCocone K).pt.X 0)
      (complexCoproductEvalCofan K 0).inj) z =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0)
    (hzc : ∀ j, z j ≫ (K j).d 0 1 = 0) :
    abCofanSum (homCofan (singleZeroComplex P) (coproductComplexCocone K).pt
      (fun j => (coproductComplexCocone K).ι.app ⟨j⟩))
      (DFinsupp.mapRange (fun j => singleMapOrZero P (K j))
        (fun j => singleMapOrZero_zero P (K j)) z) = f := by
  classical
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 P
  let pre : (singleZeroComplex P ⟶ (coproductComplexCocone K).pt) →+
      (P ⟶ (coproductComplexCocone K).pt.X 0) := AddMonoidHom.mk'
    (fun q : singleZeroComplex P ⟶ (coproductComplexCocone K).pt =>
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ q.f 0)
    (by intros q₁ q₂; simp [Preadditive.comp_add])
  have hnatural := pre.map_dfinsuppSumAddHom
    (DFinsupp.mapRange (fun j => singleMapOrZero P (K j))
      (fun j => singleMapOrZero_zero P (K j)) z)
    (fun k => ((homCofan (singleZeroComplex P) (coproductComplexCocone K).pt
      (fun j => (coproductComplexCocone K).ι.app ⟨j⟩)).inj k).hom)
  have hsumzero : e.inv ≫
      (abCofanSum (homCofan (singleZeroComplex P) (coproductComplexCocone K).pt
        (fun j => (coproductComplexCocone K).ι.app ⟨j⟩))
        (DFinsupp.mapRange (fun j => singleMapOrZero P (K j))
          (fun j => singleMapOrZero_zero P (K j)) z)).f 0 =
      abCofanSum (homCofan P ((coproductComplexCocone K).pt.X 0)
        (complexCoproductEvalCofan K 0).inj) z := by
    change pre ((DFinsupp.sumAddHom (fun k =>
      ((homCofan (singleZeroComplex P) (coproductComplexCocone K).pt
        (fun j => (coproductComplexCocone K).ι.app ⟨j⟩)).inj k).hom))
      (DFinsupp.mapRange (fun j => singleMapOrZero P (K j))
        (fun j => singleMapOrZero_zero P (K j)) z)) =
      (DFinsupp.sumAddHom (fun k =>
        ((homCofan P ((coproductComplexCocone K).pt.X 0)
          (complexCoproductEvalCofan K 0).inj).inj k).hom)) z
    rw [hnatural]
    simp only [DFinsupp.sumAddHom_apply]
    rw [DFinsupp.sum_mapRange_index (h0 := fun j => by
      dsimp [pre, homCofan, abCoyoneda]
      simp)]
    unfold DFinsupp.sum
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [pre, homCofan, abCoyoneda]
    change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫
      (singleMapOrZero P (K j) (z j) ≫ (coproductComplexCocone K).ι.app ⟨j⟩).f 0 =
        (z j) ≫ ((coproductComplexCocone K).ι.app ⟨j⟩).f 0
    rw [HomologicalComplex.comp_f, ← Category.assoc,
      singleMapOrZero_f_zero P (K j) (z j) (hzc j)]
    simp
  apply HomologicalComplex.from_single_hom_ext
  apply (cancel_epi e.inv).1
  exact hsumzero.trans hz

/-- A compact projective single complex is coproduct-compact on the explicit
K-projective derived coproduct. -/
lemma derivedHomCofan_abCofanSum_surjective_singleProjective (P : C)
    [Projective P] [IsCompactAb P] :
    Function.Surjective
      (abCofanSum (derivedHomCofan (singleZeroComplex P) K)) := by
  classical
  letI : (singleZeroComplex P).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ 0
  intro q
  change DerivedCategory.Q.obj (singleZeroComplex P) ⟶
    (derivedCoproductCofan K).pt at q
  let hrep := (derivedHomKProjectiveEquiv (singleZeroComplex P)
    (coproductComplexCocone K).pt).symm q
  let f : singleZeroComplex P ⟶ (coproductComplexCocone K).pt := hrep.out
  have hq : DerivedCategory.Q.map f = q := by
    change DerivedCategory.Q.map hrep.out = q
    rw [← derivedHomMap_quotient_map, HomotopyCategory.quotient_map_out]
    exact (derivedHomKProjectiveEquiv (singleZeroComplex P)
      (coproductComplexCocone K).pt).apply_symm_apply q
  let φ : P ⟶ (coproductComplexCocone K).pt.X 0 :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0
  have hφ : φ ≫ (coproductComplexCocone K).pt.d 0 1 = 0 := by
    dsimp [φ]
    rw [Category.assoc, f.comm]
    simp [HomologicalComplex.single_obj_d]
  obtain ⟨z, hz⟩ := exists_abCofanSum_homCofan P ((coproductComplexCocone K).pt.X 0)
    (complexCoproductEvalCofan K 0).inj (complexCoproductEvalCofan_isColimit K 0) φ
  have hnat := abCofanSum_homCofan_mapRange_comp P
    ((coproductComplexCocone K).pt.X 0) ((coproductComplexCocone K).pt.X 1)
    (complexCoproductEvalCofan K 0).inj (complexCoproductEvalCofan K 1).inj
    (fun j => (K j).d 0 1) ((coproductComplexCocone K).pt.d 0 1)
    (fun j => ((coproductComplexCocone K).ι.app ⟨j⟩).comm 0 1) z
  let z₁ : DFinsupp (fun j => P ⟶ (K j).X 1) :=
    DFinsupp.mapRange (fun j q => q ≫ (K j).d 0 1) (fun j => by simp) z
  have hzc (j : J) : z j ≫ (K j).d 0 1 = 0 := by
    let p := coproductProjection (complexCoproductEvalCofan K 1).inj
      (complexCoproductEvalCofan_isColimit K 1) j
    have hp := abCofanSum_homCofan_comp_coproductProjection P
      ((coproductComplexCocone K).pt.X 1) (complexCoproductEvalCofan K 1).inj
      (complexCoproductEvalCofan_isColimit K 1) z₁ j
    calc
      z j ≫ (K j).d 0 1 = abCofanSum (homCofan P ((coproductComplexCocone K).pt.X 1)
          (complexCoproductEvalCofan K 1).inj) z₁ ≫ p := by
        simpa [z₁, p] using hp.symm
      _ = (abCofanSum (homCofan P ((coproductComplexCocone K).pt.X 0)
          (complexCoproductEvalCofan K 0).inj) z ≫
          (coproductComplexCocone K).pt.d 0 1) ≫ p := by rw [hnat]
      _ = (φ ≫ (coproductComplexCocone K).pt.d 0 1) ≫ p := by rw [hz]
      _ = 0 := by rw [hφ]; simp
  let zC : DFinsupp (fun j => singleZeroComplex P ⟶ K j) :=
    DFinsupp.mapRange (fun j => singleMapOrZero P (K j))
      (fun j => singleMapOrZero_zero P (K j)) z
  let zD : DFinsupp (fun j => DerivedCategory.Q.obj (singleZeroComplex P) ⟶
      DerivedCategory.Q.obj (K j)) :=
    DFinsupp.mapRange (fun j q => DerivedCategory.Q.map q)
      (fun j => by rw [DerivedCategory.Q.map_zero]) zC
  refine ⟨zD, ?_⟩
  have hQ := abCofanSum_homCofan_mapRange_map DerivedCategory.Q
    (singleZeroComplex P) (coproductComplexCocone K).pt
    (fun j => (coproductComplexCocone K).ι.app ⟨j⟩) zC
  have hchain := abCofanSum_singleMapOrZero_of_cycles P K f z hz hzc
  change abCofanSum (homCofan (DerivedCategory.Q.obj (singleZeroComplex P))
    (DerivedCategory.Q.obj (coproductComplexCocone K).pt)
    (fun j => DerivedCategory.Q.map ((coproductComplexCocone K).ι.app ⟨j⟩))) zD = q
  exact hQ.trans ((congrArg DerivedCategory.Q.map hchain).trans hq)

/-- Finite-support sums of derived Hom classes are detected by the component
projections, hence the comparison map is injective. -/
lemma derivedHomCofan_abCofanSum_injective :
    Function.Injective (abCofanSum (derivedHomCofan K₀ K)) := by
  intro z w h
  apply DFinsupp.ext
  intro j
  let hc := derivedCoproductCofanIsColimit K
  let p := coproductProjection (derivedCoproductCofan K).inj hc j
  have hz := abCofanSum_homCofan_comp_coproductProjection
    (DerivedCategory.Q.obj K₀) (derivedCoproductCofan K).pt
    (derivedCoproductCofan K).inj hc z j
  have hw := abCofanSum_homCofan_comp_coproductProjection
    (DerivedCategory.Q.obj K₀) (derivedCoproductCofan K).pt
    (derivedCoproductCofan K).inj hc w j
  calc
    z j = abCofanSum (derivedHomCofan K₀ K) z ≫ p := hz.symm
    _ = abCofanSum (derivedHomCofan K₀ K) w ≫ p := congrArg (fun q => q ≫ p) h
    _ = w j := hw

/-- The finite-support comparison for a compact projective single complex is a
coproduct cocone in abelian groups. -/
noncomputable def derivedHomCofanIsColimit_singleProjective (P : C)
    [Projective P] [IsCompactAb P] :
    IsColimit (derivedHomCofan (singleZeroComplex P) K) :=
  isColimitCofan_of_bijective_abCofanSum _
    ⟨derivedHomCofan_abCofanSum_injective (singleZeroComplex P) K,
      derivedHomCofan_abCofanSum_surjective_singleProjective K P⟩

/-- Hom out of a compact projective single complex preserves the coproduct of a
K-projective family in the derived category. -/
lemma preservesColimit_ofKProjective_singleProjective (P : C)
    [Projective P] [IsCompactAb P] :
    PreservesColimit (Discrete.functor (fun j => DerivedCategory.Q.obj (K j)))
      (preadditiveCoyoneda.obj (.op (DerivedCategory.Q.obj (singleZeroComplex P)))) := by
  letI : PreservesColimit (Discrete.functor (fun j => DerivedCategory.Q.obj (K j)))
      (abCoyoneda (DerivedCategory.Q.obj (singleZeroComplex P))) :=
    preservesColimit_of_preserves_colimit_cocone (derivedCoproductCofanIsColimit K)
      ((Cofan.isColimitMapCoconeEquiv
        (abCoyoneda (DerivedCategory.Q.obj (singleZeroComplex P)))
        (fun j => DerivedCategory.Q.obj (K j)) (derivedCoproductCofan K)).symm
        (derivedHomCofanIsColimit_singleProjective K P))
  exact preservesColimit_of_natIso _
    (abCoyonedaIsoPreadditive (DerivedCategory.Q.obj (singleZeroComplex P)))

/-- Compact projective single objects are compact in the derived category,
given arbitrary K-projective replacements for the objects indexing coproducts. -/
theorem isCompactAb_singleProjective_of_replacementData (P : C)
    [Projective P] [IsCompactAb P] (H : KProjectiveReplacementData C)
    [HasCoproducts.{v} C] :
    IsCompactAb (DerivedCategory.Q.obj (singleZeroComplex P)) where
  preserves J := by
    classical
    letI : ∀ (X : J → DerivedCategory C),
        PreservesColimit (Discrete.functor X)
          (preadditiveCoyoneda.obj (.op (DerivedCategory.Q.obj (singleZeroComplex P)))) := by
      intro X
      letI : ∀ j, ((H.resolution (X j)).complex).IsKProjective :=
        fun j => (H.resolution (X j)).isKProjective
      letI : PreservesColimit (Discrete.functor (fun j =>
          DerivedCategory.Q.obj ((H.resolution (X j)).complex)))
          (preadditiveCoyoneda.obj (.op (DerivedCategory.Q.obj (singleZeroComplex P)))) :=
        preservesColimit_ofKProjective_singleProjective
          (fun j => (H.resolution (X j)).complex) P
      let e : Discrete.functor (fun j =>
          DerivedCategory.Q.obj ((H.resolution (X j)).complex)) ≅
          Discrete.functor X :=
        Discrete.natIso (fun ⟨j⟩ => (H.resolution (X j)).iso)
      exact preservesColimit_of_iso_diagram _ e
    exact preservesColimitsOfShape_of_discrete _

section SmallAffineCompactness

open RelativeFM

/-- The regular module is compact in the universe-correct small-Hom affine
derived model. -/
theorem smallRingObject_isCompactAb (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    IsCompactAb (smallRingObject A H) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  let R := UniverseDecision.kProjectiveReplacementDataOfHasDerivedCategory H
  letI : IsCompactAb (ModuleCat.of A A) := regularModule_isCompactAb A
  exact isCompactAb_singleProjective_of_replacementData
    (C := ModuleCat.{u} A) (P := ModuleCat.of A A) (H := R)

/-- Every object of the small affine thick envelope of the regular module is
compact. -/
theorem smallPerf_le_isCompactAb (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    SmallPerf A H ≤ compactObjectProperty (SmallAffineD A H) :=
  triangEnvelope_singleton_le_compact (smallRingObject_isCompactAb A H)

/-- Objectwise perfect-to-compact implication in the small-Hom affine model. -/
theorem isCompactAb_of_smallPerf (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X : SmallAffineD A H} (hX : SmallPerf A H X) :
    IsCompactAb X :=
  smallPerf_le_isCompactAb A H X hX

/-- Compact objects are exactly `SmallPerf` once only the remaining
compact-to-perfect direction is supplied. -/
theorem isCompactAb_iff_smallPerf_of_neeman (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (I : SmallNeemanCompactToPerfectInput A H)
    (X : SmallAffineD A H) : IsCompactAb X ↔ SmallPerf A H X :=
  ⟨I.perfect_of_compact X, isCompactAb_of_smallPerf A H⟩

end SmallAffineCompactness

end DerivedCoproductHom

end

end RelativeFM.NeemanM1

#print axioms RelativeFM.NeemanM1.regularHomEvalAddEquiv
#print axioms RelativeFM.NeemanM1.regularHomCofan_abCofanSum_single
#print axioms RelativeFM.NeemanM1.regularHomCofan_abCofanSum_single_component
#print axioms RelativeFM.NeemanM1.regularHomCofan_abCofanSum_apply_one_apply
#print axioms RelativeFM.NeemanM1.regularHomCofan_abCofanSum_bijective
#print axioms RelativeFM.NeemanM1.regularHomCofanIsColimit
#print axioms RelativeFM.NeemanM1.regularModule_isCompactAb
#print axioms RelativeFM.NeemanM1.abCofanSum_homCofan_comp_coproductProjection
#print axioms RelativeFM.NeemanM1.exists_abCofanSum_homCofan
#print axioms RelativeFM.NeemanM1.complexCoproductEvalCofan_isColimit
#print axioms RelativeFM.NeemanM1.derivedHomCofan_abCofanSum_injective
#print axioms RelativeFM.NeemanM1.abCofanSum_homCofan_mapRange_comp
#print axioms RelativeFM.NeemanM1.abCofanSum_homCofan_mapRange_map
#print axioms RelativeFM.NeemanM1.singleMapOrZero_zero
#print axioms RelativeFM.NeemanM1.singleMapOrZero_f_zero
#print axioms RelativeFM.NeemanM1.abCofanSum_singleMapOrZero_of_cycles
#print axioms RelativeFM.NeemanM1.derivedHomCofan_abCofanSum_surjective_singleProjective
#print axioms RelativeFM.NeemanM1.derivedHomCofanIsColimit_singleProjective
#print axioms RelativeFM.NeemanM1.preservesColimit_ofKProjective_singleProjective
#print axioms RelativeFM.NeemanM1.isCompactAb_singleProjective_of_replacementData
#print axioms RelativeFM.NeemanM1.smallRingObject_isCompactAb
#print axioms RelativeFM.NeemanM1.smallPerf_le_isCompactAb
#print axioms RelativeFM.NeemanM1.isCompactAb_of_smallPerf
#print axioms RelativeFM.NeemanM1.isCompactAb_iff_smallPerf_of_neeman
