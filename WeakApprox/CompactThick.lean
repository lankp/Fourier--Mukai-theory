import WeakApprox.CompactAb
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Triangulated.Generators


/-!
# Coproduct-compact objects are thick

This file proves that `IsCompactAb` is closed under retracts and distinguished
triangles, and hence under taking the thick triangulated envelope of a compact
object.  The triangle argument uses the contravariant Hom long exact sequence,
finite-support direct sums in `AddCommGrpCat`, and the additive five lemma.
No coproduct-exactness assumption on the pretriangulated category is needed.
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

universe v u

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Precomposition as a homomorphism of additive Hom-groups. -/
def precompAddHom {X Y : C} (f : X ⟶ Y) (A : C) :
    (Y ⟶ A) →+ (X ⟶ A) where
  toFun g := f ≫ g
  map_zero' := comp_zero
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _

@[simp] lemma precompAddHom_apply {X Y : C} (f : X ⟶ Y) (A : C) (g : Y ⟶ A) :
    precompAddHom f A g = f ≫ g := rfl

/-- The image of a coproduct cofan under additive covariant Hom, as a literal cofan. -/
def abMapCofan {J : Type v} (X : C) {f : J → C} (c : Cofan f) :
    Cofan (fun j => (abCoyoneda X).obj (f j)) :=
  Cofan.mk (AddCommGrpCat.of (X ⟶ c.pt)) (fun j => (abCoyoneda X).map (c.inj j))

/-- Postcomposition as an additive homomorphism. -/
def postcompAddHom {A B : C} (X : C) (g : A ⟶ B) :
    (X ⟶ A) →+ (X ⟶ B) where
  toFun q := q ≫ g
  map_zero' := zero_comp
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

/-- The finite-support sum of maps into a coproduct cocone. -/
def abSumHom {J : Type v} [DecidableEq J] (X : C) {f : J → C} (c : Cofan f) :
    (Π₀ j, (X ⟶ f j)) →+ (X ⟶ c.pt) :=
  DFinsupp.sumAddHom (fun j => postcompAddHom X (c.inj j))

lemma abSumHom_eq {J : Type v} [DecidableEq J] (X : C)
    {f : J → C} (c : Cofan f) :
    abSumHom X c = (abCofanSum (abMapCofan X c)).hom := by
  ext z
  rfl

/-- The comparison squares for finite-support direct sums commute. -/
lemma abCofanSum_precomp {J : Type v} [DecidableEq J] {X Y : C} (t : X ⟶ Y)
    {f : J → C} (c : Cofan f) :
    (precompAddHom t c.pt).comp (abSumHom Y c) =
      (abSumHom X c).comp
        (DFinsupp.mapRange.addMonoidHom (fun j => precompAddHom t (f j))) := by
  apply DFinsupp.addHom_ext
  intro j x
  simp [abSumHom, postcompAddHom, precompAddHom, Category.assoc]

/-- Exactness is preserved by finite-support direct sums. -/
lemma dfinsupp_exact {J : Type v} [DecidableEq J]
    {A B D : J → Type v} [∀ j, AddCommGroup (A j)] [∀ j, AddCommGroup (B j)]
    [∀ j, AddCommGroup (D j)]
    (f₁ : ∀ j, A j →+ B j) (f₂ : ∀ j, B j →+ D j)
    (h : ∀ j, Function.Exact (f₁ j) (f₂ j)) :
    Function.Exact (DFinsupp.mapRange.addMonoidHom f₁)
      (DFinsupp.mapRange.addMonoidHom f₂) := by
  classical
  intro y
  constructor
  · intro hy
    have hj (j : J) : f₂ j (y j) = 0 := by
      exact congrArg (fun z => z j) hy
    choose x hx using fun j => ((h j) (y j)).1 (hj j)
    let z : Π₀ j, A j := DFinsupp.mk y.support (fun j => x j.1)
    refine ⟨z, ?_⟩
    ext j
    by_cases hj' : j ∈ y.support
    · simpa [z, hj'] using hx j
    · have hyj : y j = 0 := by simpa using hj'
      simp [z, hj', hyj]
  · rintro ⟨z, rfl⟩
    ext j
    exact (h j).apply_apply_eq_zero (z j)


section TriangleCompactness

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

lemma exact_precomp_rotate_mor₃_mor₃ (T : Triangle C) (hT : T ∈ distTriang C)
    (A : C) : Function.Exact (precompAddHom (-T.mor₁⟦(1 : ℤ)⟧') A)
      (precompAddHom T.mor₃ A) := by
  intro x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := T.rotate.yoneda_exact₃ (rot_of_distTriang _ hT) x hx
    exact ⟨g, hg.symm⟩
  · rintro ⟨y, rfl⟩
    dsimp [precompAddHom]
    have hzero : T.mor₃ ≫ (-T.mor₁⟦(1 : ℤ)⟧') = 0 :=
      comp_distTriang_mor_zero₂₃ T.rotate (rot_of_distTriang _ hT)
    rw [← Category.assoc, hzero, zero_comp]

lemma exact_precomp_mor₃_mor₂ (T : Triangle C) (hT : T ∈ distTriang C)
    (A : C) : Function.Exact (precompAddHom T.mor₃ A)
      (precompAddHom T.mor₂ A) := by
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := T.yoneda_exact₃ hT z hz
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    dsimp [precompAddHom]
    rw [← Category.assoc, comp_distTriang_mor_zero₂₃ _ hT, zero_comp]

lemma exact_precomp_mor₂_mor₁ (T : Triangle C) (hT : T ∈ distTriang C)
    (A : C) : Function.Exact (precompAddHom T.mor₂ A)
      (precompAddHom T.mor₁ A) := by
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := T.yoneda_exact₂ hT y hy
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, rfl⟩
    dsimp [precompAddHom]
    rw [← Category.assoc, comp_distTriang_mor_zero₁₂ _ hT, zero_comp]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma bijective_abSumHom_of_compact {J : Type v} [DecidableEq J]
    (W : C) (hW : IsCompactAb W) {f : J → C} (c : Cofan f) (hc : IsColimit c) :
    Function.Bijective (abSumHom W c) := by
  let _ : PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (.op W)) :=
    hW.preserves J
  let _ : PreservesColimitsOfShape (Discrete J) (abCoyoneda W) :=
    preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive W).symm
  rw [abSumHom_eq]
  exact bijective_abCofanSum_of_isColimit
    ((Cofan.isColimitMapCoconeEquiv (abCoyoneda W) f c)
      (isColimitOfPreserves (abCoyoneda W) hc))

/-- Compactness passes to the cone of a morphism between compact objects. -/
lemma isCompactAb_obj₃ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsCompactAb T.obj₁) (h₂ : IsCompactAb T.obj₂) : IsCompactAb T.obj₃ := by
  classical
  have h₁' : IsCompactAb (T.obj₁⟦(1 : ℤ)⟧) := isCompactAb_shift _ _ h₁
  have h₂' : IsCompactAb (T.obj₂⟦(1 : ℤ)⟧) := isCompactAb_shift _ _ h₂
  constructor
  intro J
  let _ : PreservesColimitsOfShape (Discrete J) (abCoyoneda T.obj₃) := by
    have _ : ∀ (f : J → C), PreservesColimit (Discrete.functor f) (abCoyoneda T.obj₃) :=
      fun f => { preserves := fun {c} hc => ⟨by
        let c₀ : Cofan f := Cofan.mk c.pt (fun j => c.ι.app (Discrete.mk j))
        let e : c₀ ≅ c := Cocone.ext (Iso.refl _) (by
          intro j
          cases j
          simp [c₀])
        have hc₀ : IsColimit c₀ := hc.ofIsoColimit e.symm
        refine (Cofan.isColimitMapCoconeEquiv (abCoyoneda T.obj₃) f c).symm ?_
        apply isColimitCofan_of_bijective_abCofanSum
        change Function.Bijective (abCofanSum (abMapCofan T.obj₃ c₀))
        have hb : Function.Bijective (abSumHom T.obj₃ c₀) :=
          AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
          (DFinsupp.mapRange.addMonoidHom (fun j => precompAddHom (-T.mor₁⟦(1 : ℤ)⟧') (f j)))
          (DFinsupp.mapRange.addMonoidHom (fun j => precompAddHom T.mor₃ (f j)))
          (DFinsupp.mapRange.addMonoidHom (fun j => precompAddHom T.mor₂ (f j)))
          (DFinsupp.mapRange.addMonoidHom (fun j => precompAddHom T.mor₁ (f j)))
          (precompAddHom (-T.mor₁⟦(1 : ℤ)⟧') c₀.pt)
          (precompAddHom T.mor₃ c₀.pt)
          (precompAddHom T.mor₂ c₀.pt)
          (precompAddHom T.mor₁ c₀.pt)
          (abSumHom (T.obj₂⟦(1 : ℤ)⟧) c₀)
          (abSumHom (T.obj₁⟦(1 : ℤ)⟧) c₀)
          (abSumHom T.obj₃ c₀)
          (abSumHom T.obj₂ c₀)
          (abSumHom T.obj₁ c₀)
          (abCofanSum_precomp (-T.mor₁⟦(1 : ℤ)⟧') c₀)
          (abCofanSum_precomp T.mor₃ c₀)
          (abCofanSum_precomp T.mor₂ c₀)
          (abCofanSum_precomp T.mor₁ c₀)
          (dfinsupp_exact _ _ (fun j => exact_precomp_rotate_mor₃_mor₃ T hT (f j)))
          (dfinsupp_exact _ _ (fun j => exact_precomp_mor₃_mor₂ T hT (f j)))
          (dfinsupp_exact _ _ (fun j => exact_precomp_mor₂_mor₁ T hT (f j)))
          (exact_precomp_rotate_mor₃_mor₃ T hT c₀.pt)
          (exact_precomp_mor₃_mor₂ T hT c₀.pt)
          (exact_precomp_mor₂_mor₁ T hT c₀.pt)
          (bijective_abSumHom_of_compact _ h₂' c₀ hc₀).surjective
          (bijective_abSumHom_of_compact _ h₁' c₀ hc₀)
          (bijective_abSumHom_of_compact _ h₂ c₀ hc₀)
          (bijective_abSumHom_of_compact _ h₁ c₀ hc₀).injective
        rw [abSumHom_eq] at hb
        exact hb⟩ }
    exact preservesColimitsOfShape_of_discrete _
  exact preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive T.obj₃)


lemma isCompactAb_obj₂ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsCompactAb T.obj₁) (h₃ : IsCompactAb T.obj₃) : IsCompactAb T.obj₂ := by
  exact isCompactAb_obj₃ T.invRotate (inv_rot_of_distTriang _ hT)
    (isCompactAb_shift _ _ h₃) h₁

end TriangleCompactness

section CompactObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma isCompactAb_of_isZero {X : C} (hX : IsZero X) : IsCompactAb X := by
  constructor
  intro J
  apply (preadditiveCoyoneda.obj (.op X)).preservesColimitsOfShape_of_isZero
  rw [Functor.isZero_iff]
  intro Y
  let _ : Subsingleton ((preadditiveCoyoneda.obj (.op X)).obj Y) :=
    ⟨fun f g => hX.eq_of_src f g⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma precompAddHom_retract {X Y : C} (r : Retract X Y) (A : C) :
    (precompAddHom r.i A).comp (precompAddHom r.r A) = AddMonoidHom.id _ := by
  ext f
  dsimp [precompAddHom]
  rw [← Category.assoc, r.retract, Category.id_comp]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma dfinsupp_precomp_retract {J : Type v} [DecidableEq J] {X Y : C}
    (r : Retract X Y) (f : J → C) :
    (DFinsupp.mapRange.addMonoidHom (fun j => precompAddHom r.i (f j))).comp
      (DFinsupp.mapRange.addMonoidHom (fun j => precompAddHom r.r (f j))) =
        AddMonoidHom.id _ := by
  ext z j
  dsimp [DFinsupp.mapRange.addMonoidHom, precompAddHom]
  rw [← Category.assoc, r.retract, Category.id_comp]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma bijective_abSumHom_retract {J : Type v} [DecidableEq J] {X Y : C}
    (r : Retract X Y) {f : J → C} (c : Cofan f)
    (hY : Function.Bijective (abSumHom Y c)) :
    Function.Bijective (abSumHom X c) := by
  let sM := DFinsupp.mapRange.addMonoidHom (fun j => precompAddHom r.i (f j))
  let tM := DFinsupp.mapRange.addMonoidHom (fun j => precompAddHom r.r (f j))
  have hs : (precompAddHom r.i c.pt).comp (abSumHom Y c) =
      (abSumHom X c).comp sM := abCofanSum_precomp r.i c
  have ht : (precompAddHom r.r c.pt).comp (abSumHom X c) =
      (abSumHom Y c).comp tM := abCofanSum_precomp r.r c
  have hstM : sM.comp tM = AddMonoidHom.id _ := dfinsupp_precomp_retract r f
  have hstN : (precompAddHom r.i c.pt).comp (precompAddHom r.r c.pt) =
      AddMonoidHom.id _ := precompAddHom_retract r c.pt
  constructor
  · intro z₁ z₂ hz
    have htz : tM z₁ = tM z₂ := by
      apply hY.injective
      calc
        (abSumHom Y c) (tM z₁) = precompAddHom r.r c.pt ((abSumHom X c) z₁) :=
          (DFunLike.congr_fun ht z₁).symm
        _ = precompAddHom r.r c.pt ((abSumHom X c) z₂) := congrArg _ hz
        _ = (abSumHom Y c) (tM z₂) := DFunLike.congr_fun ht z₂
    have hz' : (sM.comp tM) z₁ = (sM.comp tM) z₂ := by
      simp only [AddMonoidHom.comp_apply, htz]
    rw [hstM] at hz'
    exact hz'
  · intro x
    obtain ⟨z, hz⟩ := hY.surjective (precompAddHom r.r c.pt x)
    refine ⟨sM z, ?_⟩
    calc
      (abSumHom X c) (sM z) = precompAddHom r.i c.pt ((abSumHom Y c) z) :=
        (DFunLike.congr_fun hs z).symm
      _ = precompAddHom r.i c.pt (precompAddHom r.r c.pt x) := congrArg _ hz
      _ = x := DFunLike.congr_fun hstN x

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma isCompactAb_of_retract {X Y : C} (r : Retract X Y)
    (hY : IsCompactAb Y) : IsCompactAb X := by
  classical
  constructor
  intro J
  let _ : PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (.op Y)) :=
    hY.preserves J
  let _ : PreservesColimitsOfShape (Discrete J) (abCoyoneda Y) :=
    preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive Y).symm
  let _ : PreservesColimitsOfShape (Discrete J) (abCoyoneda X) := by
    have _ : ∀ (f : J → C), PreservesColimit (Discrete.functor f) (abCoyoneda X) :=
      fun f => { preserves := fun {c} hc => ⟨by
        let c₀ : Cofan f := Cofan.mk c.pt (fun j => c.ι.app (Discrete.mk j))
        let e : c₀ ≅ c := Cocone.ext (Iso.refl _) (by
          intro j
          cases j
          simp [c₀])
        have hc₀ : IsColimit c₀ := hc.ofIsoColimit e.symm
        refine (Cofan.isColimitMapCoconeEquiv (abCoyoneda X) f c).symm ?_
        apply isColimitCofan_of_bijective_abCofanSum
        change Function.Bijective (abCofanSum (abMapCofan X c₀))
        have hb : Function.Bijective (abSumHom X c₀) :=
          bijective_abSumHom_retract r c₀ (bijective_abSumHom_of_compact _ hY c₀ hc₀)
        rw [abSumHom_eq] at hb
        exact hb⟩ }
    exact preservesColimitsOfShape_of_discrete _
  exact preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive X)

/-- The object property of `Ab`-valued coproduct-compact objects. -/
def compactObjectProperty (C : Type u) [Category.{v} C] [HasZeroObject C]
    [Preadditive C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] : ObjectProperty C := IsCompactAb

instance : (compactObjectProperty C).IsClosedUnderIsomorphisms where
  of_iso e hX := isCompactAb_of_iso e hX

instance : (compactObjectProperty C).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, isCompactAb_of_isZero (isZero_zero _)⟩

instance : (compactObjectProperty C).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ObjectProperty.IsStableUnderShiftBy.mk
    (fun X hX => isCompactAb_shift X a hX)

instance : (compactObjectProperty C).IsStableUnderRetracts where
  of_retract r hY := isCompactAb_of_retract r hY

instance : (compactObjectProperty C).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ => isCompactAb_obj₂ T hT h₁ h₃)

instance : (compactObjectProperty C).IsTriangulated where

lemma isCompactAb_of_mem_triangEnvelope {G X : C} (hG : IsCompactAb G)
    (hX : (ObjectProperty.singleton G).triangEnvelope X) : IsCompactAb X := by
  have hle : (ObjectProperty.singleton G).triangEnvelope ≤ compactObjectProperty C :=
    (ObjectProperty.triangEnvelope_le_iff _).2 (by
      rw [ObjectProperty.singleton_le_iff]
      exact hG)
  exact hle X hX

lemma triangEnvelope_singleton_le_compact {G : C} (hG : IsCompactAb G) :
    (ObjectProperty.singleton G).triangEnvelope ≤ compactObjectProperty C :=
  fun _ hX => isCompactAb_of_mem_triangEnvelope hG hX

end CompactObjectProperty

end

#print axioms isCompactAb_obj₃
#print axioms isCompactAb_obj₂
#print axioms isCompactAb_of_retract
#print axioms isCompactAb_of_mem_triangEnvelope
#print axioms triangEnvelope_singleton_le_compact

end RelativeWeakApprox
