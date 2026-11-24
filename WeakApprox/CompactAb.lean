/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# `Ab`-valued compactness

The paper's compactness of an object `H` of a preadditive category is that the
covariant Hom functor `Hom(H, -)`, taken with values in abelian groups
(`CategoryTheory.preadditiveCoyoneda`), preserves small coproducts.  This file
develops that notion, `IsCompactAb`.

## Why the `Ab` rendering

`WeakApprox.Basic` also has `IsCoproductCompact`, which asks the *`Type`-valued*
`coyoneda` to preserve the same coproducts.  That condition is strictly
stronger: a `Type`-valued coproduct is a disjoint union, so it forces every
morphism `H ⟶ ∐ X_j` to factor through a single summand, whereas the `Ab`-valued
coproduct is the finite-support subobject.  Crucially, `IsCoproductCompact` is
**not** closed under binary biproducts (a map `X ⊞ Y ⟶ Z₁ ⊞ Z₂` mixes
summands), while `IsCompactAb` is: finite biproducts commute with small
coproducts in `AddCommGrpCat`.  This is what allows
`G = G'⟦m⟧ ⊞ j_!G_U` to be compact without an extra hypothesis, i.e. it is the
rendering used in Lemma 4.3(2).

## Main results

* `IsCompactAb` and its invariance under isomorphisms and shifts;
* `isCompactAb_of_isCoproductCompact`, the migration direction from the
  `Type`-valued notion (the converse cannot hold);
* `isCompactAb_biprod`: compactness of a binary biproduct from its summands;
* `preservesColimitsOfShape_prod` and `preservesColimitsOfShape_abPair`: binary
  products of coproduct-preserving `AddCommGrpCat`-valued functors preserve
  coproducts;
* `isCompactAb_leftAdjoint_obj'`: Neeman's adjoint criterion in the `Ab`
  rendering.

Found by a member of the Ultramath run `smwuoh1xz` (direction D1).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u u'

/-- The canonical additive map from the finite-support direct sum to the point of a
cocone in `AddCommGrpCat`. -/
noncomputable def abCofanSum {J : Type v} [DecidableEq J] {f : J → AddCommGrpCat.{v}} (c : Cofan f) :
    AddCommGrpCat.of (DFinsupp (fun j => f j)) ⟶ c.pt :=
  AddCommGrpCat.ofHom (DFinsupp.sumAddHom fun j => (c.inj j).hom)

@[simp]
lemma abCofanSum_single {J : Type v} [DecidableEq J] {f : J → AddCommGrpCat.{v}} (c : Cofan f)
    (j : J) (x : f j) : abCofanSum c (DFinsupp.single j x) = c.inj j x := by
  classical
  exact DFinsupp.sumAddHom_single _ _ _

/-- A discrete cocone of abelian groups is a colimit as soon as its canonical
map from the finite-support direct sum is bijective. -/
noncomputable def isColimitCofan_of_bijective_abCofanSum {J : Type v} [DecidableEq J]
    {f : J → AddCommGrpCat.{v}} (c : Cofan f)
    (h : Function.Bijective (abCofanSum c)) : IsColimit c := by
  classical
  let e : DFinsupp (fun j => f j) ≃+ c.pt := AddEquiv.ofBijective _ h
  refine Cofan.IsColimit.mk c
    (fun s => AddCommGrpCat.ofHom
      ((DFinsupp.sumAddHom fun j => (s.inj j).hom).comp e.symm.toAddMonoidHom)) ?_ ?_
  · intro s j
    ext x
    simp only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_ofHom,
      AddMonoidHom.comp_apply]
    rw [← abCofanSum_single c j x]
    change (DFinsupp.sumAddHom fun k => (s.inj k).hom)
      (e.symm (abCofanSum c (DFinsupp.single j x))) = s.inj j x
    rw [show abCofanSum c (DFinsupp.single j x) = e (DFinsupp.single j x) from rfl,
      e.symm_apply_apply]
    exact DFinsupp.sumAddHom_single _ _ _
  · intro s m hm
    ext y
    obtain ⟨x, rfl⟩ := h.2 y
    have hm' : m.hom.comp (DFinsupp.sumAddHom fun j => (c.inj j).hom) =
        DFinsupp.sumAddHom fun j => (s.inj j).hom := by
      apply DFinsupp.addHom_ext
      intro j x
      simp only [AddMonoidHom.comp_apply, DFinsupp.sumAddHom_single]
      change m (c.inj j x) = s.inj j x
      simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom (hm j) x
    change m (abCofanSum c x) = (DFinsupp.sumAddHom fun j => (s.inj j).hom)
      (e.symm (abCofanSum c x))
    rw [show abCofanSum c x = e x from rfl, e.symm_apply_apply]
    change m (DFinsupp.sumAddHom (fun j => (c.inj j).hom) x) = _
    simpa only [AddMonoidHom.comp_apply] using DFunLike.congr_fun hm' x

section CompactAb

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v} D] [Preadditive D]

/-- `Ab`-valued compactness is invariant under isomorphism. -/
lemma isCompactAb_of_iso {X Y : C} (e : X ≅ Y) (hX : IsCompactAb X) :
    IsCompactAb Y := by
  constructor
  intro J
  letI : PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (.op X)) :=
    hX.preserves J
  exact preservesColimitsOfShape_of_natIso (preadditiveCoyoneda.mapIso e.symm.op)

/-- The additive enhancement of `Adjunction.compCoyonedaIso`, evaluated at `X`. -/
def preadditiveCompCoyonedaIso {F : C ⥤ D} {G : D ⥤ C} [F.Additive] (adj : F ⊣ G) (X : C) :
    preadditiveCoyoneda.obj (.op (F.obj X)) ≅ G ⋙ preadditiveCoyoneda.obj (.op X) :=
  NatIso.ofComponents
    (fun Y => (adj.homAddEquiv X Y).toAddCommGrpIso)
    (fun g => by
      ext f
      exact adj.homEquiv_naturality_right f g)

/-- Neeman's adjoint criterion, with compactness rendered in `AddCommGrpCat`. -/
lemma isCompactAb_leftAdjoint_obj' {F : C ⥤ D} {G : D ⥤ C} [F.Additive]
    (adj : F ⊣ G) {X : C} (hX : IsCompactAb X)
    (hG : ∀ (J : Type v), PreservesColimitsOfShape (Discrete J) G) :
    IsCompactAb (F.obj X) := by
  constructor
  intro J
  letI : PreservesColimitsOfShape (Discrete J) G := hG J
  letI : PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (.op X)) :=
    hX.preserves J
  exact preservesColimitsOfShape_of_natIso (preadditiveCompCoyonedaIso adj X).symm

/-- Shifts preserve `Ab`-valued compactness. -/
lemma isCompactAb_shift [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] (X : C) (n : ℤ)
    (hX : IsCompactAb X) : IsCompactAb (X⟦n⟧) := by
  letI : (shiftEquiv C n).functor.Additive := by
    change (shiftFunctor C n).Additive
    infer_instance
  exact isCompactAb_leftAdjoint_obj' (shiftEquiv C n).toAdjunction hX
    (fun _ => inferInstance)


/-- A direct, elementary presentation of the additive covariant Hom functor. -/
abbrev abCoyoneda {C : Type u} [Category.{v} C] [Preadditive C] (H : C) :
    C ⥤ AddCommGrpCat.{v} where
  obj X := AddCommGrpCat.of (H ⟶ X)
  map f := AddCommGrpCat.ofHom
    { toFun := fun q => q ≫ f
      map_zero' := zero_comp
      map_add' := fun _ _ => Preadditive.add_comp _ _ _ _ _ _ }

/-- The elementary additive Hom functor is definitionally identified with
Mathlib's `preadditiveCoyoneda` at every object. -/
def abCoyonedaIsoPreadditive {C : Type u} [Category.{v} C] [Preadditive C] (H : C) :
    abCoyoneda H ≅ preadditiveCoyoneda.obj (.op H) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by ext q; rfl)

/-- The projection onto one component of a colimit cofan in a preadditive
category.  The other components are sent to zero. -/
noncomputable def coproductProjection {J : Type v} [DecidableEq J] {C : Type u}
    [Category.{v} C] [Preadditive C] {f : J → C} {P : C} (g : ∀ j, f j ⟶ P)
    (hc : IsColimit (Cofan.mk P g)) (j : J) : P ⟶ f j :=
  Cofan.IsColimit.desc hc fun k => if h : k = j then eqToHom (congrArg f h) else 0

@[simp]
lemma coproductProjection_comp {J : Type v} [DecidableEq J] {C : Type u}
    [Category.{v} C] [Preadditive C] {f : J → C} {P : C} (g : ∀ j, f j ⟶ P)
    (hc : IsColimit (Cofan.mk P g)) (j k : J) :
    g k ≫ coproductProjection g hc j =
      if h : k = j then eqToHom (congrArg f h) else 0 := by
  exact Cofan.IsColimit.fac hc _ k

/-- `Ab`-valued `Hom` maps a coproduct cocone to a colimit whenever ordinary
`Type`-valued `Hom` does so.  Unlike the incorrect argument using preservation
by `forget AddCommGrpCat`, this proof uses projections to detect each component
of the finite-support direct sum. -/
noncomputable def isColimitCofan_preadditiveCoyoneda {J : Type v} [DecidableEq J] {C : Type u}
    [Category.{v} C] [Preadditive C] (H : C) {f : J → C} {P : C}
    (g : ∀ j, f j ⟶ P) (hc : IsColimit (Cofan.mk P g))
    (hType : IsColimit (Cofan.mk (H ⟶ P) (fun j => ↾(fun q : H ⟶ f j => q ≫ g j)) :
      Cofan fun j => H ⟶ f j)) :
    IsColimit (Cofan.mk ((abCoyoneda H).obj P)
      (fun j => (abCoyoneda H).map (g j)) :
      Cofan fun j => (abCoyoneda H).obj (f j)) := by
  classical
  let c : Cofan (fun j => (abCoyoneda H).obj (f j)) :=
    Cofan.mk _ (fun j => (abCoyoneda H).map (g j))
  apply isColimitCofan_of_bijective_abCofanSum c
  constructor
  · intro x y hxy
    ext j
    let p : P ⟶ f j := coproductProjection g hc j
    let post : (H ⟶ P) →+ (H ⟶ f j) :=
      ((abCoyoneda H).map p).hom
    have eval (z : DFinsupp (fun k => H ⟶ f k)) :
        (abCofanSum c z) ≫ p = z j := by
      have hz := post.map_dfinsuppSumAddHom z (fun k => (c.inj k).hom)
      calc
        (abCofanSum c z) ≫ p =
            post ((DFinsupp.sumAddHom fun k => (c.inj k).hom) z) := rfl
        _ = (DFinsupp.sumAddHom fun k => post.comp (c.inj k).hom) z := hz
        _ = z j := by
          have hfun : (fun k => post.comp (c.inj k).hom) =
              Pi.single j (AddMonoidHom.id (H ⟶ f j)) := by
            funext k
            by_cases h : k = j
            · subst k
              ext q
              simp [post, p, c]
            · ext q
              simp [post, p, c, h]
          rw [hfun, DFinsupp.sumAddHom_piSingle]
          rfl
    have hz := congrArg (fun q : H ⟶ P => q ≫ p) hxy
    rwa [eval x, eval y] at hz
  · intro q
    obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hType q
    refine ⟨DFinsupp.single j.as x, ?_⟩
    change H ⟶ f j.as at x
    change H ⟶ P at q
    change x ≫ g j.as = q at hx
    change (DFinsupp.sumAddHom fun k => (c.inj k).hom) (DFinsupp.single j.as x) = q
    exact (DFinsupp.sumAddHom_single (fun k => (c.inj k).hom) j.as x).trans hx


/-- Ordinary coproduct compactness implies the standard `Ab`-valued
compactness.  The proof does **not** compose with `forget AddCommGrpCat`
(which does not preserve coproducts): it detects the finite-support direct sum
using coproduct projections. -/
lemma isCompactAb_of_isCoproductCompact {C : Type u} [Category.{v} C]
    [Preadditive C] {H : C} (hH : IsCoproductCompact H) : IsCompactAb H := by
  constructor
  intro J
  classical
  letI : PreservesColimitsOfShape (Discrete J) (coyoneda.obj (.op H)) := hH.preserves J
  haveI : PreservesColimitsOfShape (Discrete J) (abCoyoneda H) := by
    letI : ∀ (f : J → C), PreservesColimit (Discrete.functor f) (abCoyoneda H) :=
      fun f =>
        { preserves := fun {c} hc => ⟨by
            let c0 : Cofan f := Cofan.mk c.pt (fun j => c.ι.app (Discrete.mk j))
            let e : c0 ≅ c := Cocone.ext (Iso.refl _) (by
              intro j
              cases j
              simp [c0])
            have hc0 : IsColimit c0 := hc.ofIsoColimit e.symm
            have hType := (Cofan.isColimitMapCoconeEquiv (coyoneda.obj (.op H)) f c)
              (isColimitOfPreserves (coyoneda.obj (.op H)) hc)
            have hAb := isColimitCofan_preadditiveCoyoneda H (fun j => c.ι.app (Discrete.mk j)) hc0 hType
            exact (Cofan.isColimitMapCoconeEquiv (abCoyoneda H) f c).symm hAb⟩ }
    exact preservesColimitsOfShape_of_discrete _
  exact preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive H)


/-- The finite-support direct sum, viewed as a cofan of abelian groups. -/
noncomputable def dfinsuppCofan {J : Type v} [DecidableEq J]
    (f : J → AddCommGrpCat.{v}) : Cofan f :=
  Cofan.mk (AddCommGrpCat.of (DFinsupp (fun j => f j)))
    (fun j => AddCommGrpCat.ofHom (DFinsupp.singleAddHom (fun j => f j) j))

/-- The direct-sum comparison map of a colimit cocone is bijective. -/
lemma bijective_abCofanSum_of_isColimit {J : Type v} [DecidableEq J]
    {f : J → AddCommGrpCat.{v}} {c : Cofan f} (hc : IsColimit c) :
    Function.Bijective (abCofanSum c) := by
  let d := dfinsuppCofan f
  have hd : IsColimit d := by
    apply isColimitCofan_of_bijective_abCofanSum d
    change Function.Bijective (DFinsupp.sumAddHom
      (fun j => DFinsupp.singleAddHom (fun j => f j) j))
    rw [DFinsupp.sumAddHom_singleAddHom]
    exact Function.bijective_id
  let e : d.pt ≅ c.pt := IsColimit.coconePointUniqueUpToIso hd hc
  have he : e.hom = abCofanSum c := by
    apply Cofan.IsColimit.hom_ext hd
    intro j
    ext x
    simp [e, d, abCofanSum, dfinsuppCofan]
    simpa [d, dfinsuppCofan, Cofan.inj] using DFunLike.congr_fun
      (congrArg AddCommGrpCat.Hom.hom
        (IsColimit.comp_coconePointUniqueUpToIso_hom hd hc (Discrete.mk j))) x
  haveI : IsIso (abCofanSum c) := by
    rw [← he]
    change IsIso e.hom
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- Finite-support functions into a product are the product of the two
families of finite-support functions. -/
noncomputable def dfinsuppProdAddEquiv {J : Type v} [DecidableEq J]
    (A B : J → Type v) [∀ j, AddCommGroup (A j)] [∀ j, AddCommGroup (B j)] :
    (DFinsupp (fun j => A j × B j)) ≃+
      (DFinsupp A) × (DFinsupp B) where
  toFun z :=
    (DFinsupp.mapRange (fun _ p => p.1) (by simp) z,
      DFinsupp.mapRange (fun _ p => p.2) (by simp) z)
  invFun z := DFinsupp.zipWith (fun _ a b => (a, b)) (by simp) z.1 z.2
  left_inv z := by
    ext j <;> rfl
  right_inv z := by
    rcases z with ⟨x, y⟩
    ext <;> rfl
  map_add' x y := by
    ext <;> rfl

/-- The explicit pointwise product of two `AddCommGrpCat`-valued functors. -/
abbrev abPair {C : Type u} [Category.{v} C] (F G : C ⥤ AddCommGrpCat.{v}) :
    C ⥤ AddCommGrpCat.{v} where
  obj X := AddCommGrpCat.of (F.obj X × G.obj X)
  map f := AddCommGrpCat.ofHom ((F.map f).hom.prodMap (G.map f).hom)

/-- First projection from the explicit pointwise product. -/
def abPairFst {C : Type u} [Category.{v} C] (F G : C ⥤ AddCommGrpCat.{v}) :
    abPair F G ⟶ F where
  app X := AddCommGrpCat.ofHom (AddMonoidHom.fst (F.obj X) (G.obj X))
  naturality _ _ _ := rfl

/-- Second projection from the explicit pointwise product. -/
def abPairSnd {C : Type u} [Category.{v} C] (F G : C ⥤ AddCommGrpCat.{v}) :
    abPair F G ⟶ G where
  app X := AddCommGrpCat.ofHom (AddMonoidHom.snd (F.obj X) (G.obj X))
  naturality _ _ _ := rfl

/-- The explicit product as a binary fan in the functor category. -/
def abPairBinaryFan {C : Type u} [Category.{v} C] (F G : C ⥤ AddCommGrpCat.{v}) :
    BinaryFan F G := BinaryFan.mk (abPairFst F G) (abPairSnd F G)

/-- The explicit pointwise product is a categorical binary product. -/
def abPairIsLimit {C : Type u} [Category.{v} C] (F G : C ⥤ AddCommGrpCat.{v}) :
    IsLimit (abPairBinaryFan F G) := by
  apply evaluationJointlyReflectsLimits
  intro X
  exact (BinaryFan.isLimitMapConeEquiv (F := (evaluation C AddCommGrpCat).obj X)).symm
    (AddCommGrpCat.binaryProductLimitCone (F.obj X) (G.obj X)).isLimit

/-- The explicit pointwise product, identified with the categorical binary
product in the functor category. -/
noncomputable def abPairIsoProd {C : Type u} [Category.{v} C] (F G : C ⥤ AddCommGrpCat.{v}) :
    abPair F G ≅ Limits.prod F G :=
  IsLimit.conePointUniqueUpToIso (abPairIsLimit F G) (limit.isLimit (pair F G))


/-- A binary product of colimit cofans in `AddCommGrpCat`, over the same
discrete shape, is again a colimit cofan. -/
noncomputable def isColimitCofan_abPair {J : Type v} [DecidableEq J] {C : Type u}
    [Category.{v} C] {F G : C ⥤ AddCommGrpCat.{v}} {f : J → C} {P : C}
    (g : ∀ j, f j ⟶ P)
    (hF : IsColimit (Cofan.mk (F.obj P) (fun j => F.map (g j)) :
      Cofan fun j => F.obj (f j)))
    (hG : IsColimit (Cofan.mk (G.obj P) (fun j => G.map (g j)) :
      Cofan fun j => G.obj (f j))) :
    IsColimit (Cofan.mk ((abPair F G).obj P) (fun j => (abPair F G).map (g j)) :
      Cofan fun j => (abPair F G).obj (f j)) := by
  classical
  let cP : Cofan (fun j => (abPair F G).obj (f j)) :=
    Cofan.mk _ (fun j => (abPair F G).map (g j))
  let eD := dfinsuppProdAddEquiv (fun j => F.obj (f j)) (fun j => G.obj (f j))
  let eFG : (DFinsupp (fun j => F.obj (f j))) × (DFinsupp (fun j => G.obj (f j))) ≃+
      F.obj P × G.obj P :=
    AddEquiv.prodCongr
      (AddEquiv.ofBijective _ (bijective_abCofanSum_of_isColimit hF))
      (AddEquiv.ofBijective _ (bijective_abCofanSum_of_isColimit hG))
  let e := eD.trans eFG
  apply isColimitCofan_of_bijective_abCofanSum cP
  have he : (abCofanSum cP).hom = e.toAddMonoidHom := by
    apply DFinsupp.addHom_ext
    intro j p
    rcases p with ⟨x, y⟩
    change abCofanSum cP (DFinsupp.single j (x, y)) = e (DFinsupp.single j (x, y))
    rw [abCofanSum_single]
    simp [e, eD, eFG, cP, dfinsuppProdAddEquiv, AddEquiv.ofBijective, Equiv.ofBijective, AddEquiv.prodCongr]
    exact ⟨(abCofanSum_single (Cofan.mk (F.obj P) (fun j => F.map (g j)) :
        Cofan fun j => F.obj (f j)) j x).symm,
      (abCofanSum_single (Cofan.mk (G.obj P) (fun j => G.map (g j)) :
        Cofan fun j => G.obj (f j)) j y).symm⟩
  change Function.Bijective (abCofanSum cP).hom
  rw [he]
  exact e.bijective

/-- Binary products of coproduct-preserving `AddCommGrpCat`-valued functors
preserve coproducts.  This is proved directly, rather than hoped for as an
instance: finite-support direct sums commute with binary products. -/
lemma preservesColimitsOfShape_abPair {C : Type u} [Category.{v} C]
    (F G : C ⥤ AddCommGrpCat.{v}) (J : Type v)
    [PreservesColimitsOfShape (Discrete J) F]
    [PreservesColimitsOfShape (Discrete J) G] :
    PreservesColimitsOfShape (Discrete J) (abPair F G) := by
  classical
  letI : ∀ (f : J → C), PreservesColimit (Discrete.functor f) (abPair F G) :=
    fun f =>
      { preserves := fun {c} hc => ⟨by
          have hF := (Cofan.isColimitMapCoconeEquiv F f c) (isColimitOfPreserves F hc)
          have hG := (Cofan.isColimitMapCoconeEquiv G f c) (isColimitOfPreserves G hc)
          have hP := isColimitCofan_abPair (F := F) (G := G)
            (fun j => c.ι.app (Discrete.mk j)) hF hG
          exact (Cofan.isColimitMapCoconeEquiv (abPair F G) f c).symm hP⟩ }
  exact preservesColimitsOfShape_of_discrete _


/-- Maps out of a binary biproduct are, additively, pairs of maps out of its
summands. -/
noncomputable def biprodHomAddEquiv {C : Type u} [Category.{v} C] [Preadditive C]
    (X Y Z : C) [HasBinaryBiproduct X Y] :
    (X ⊞ Y ⟶ Z) ≃+ (X ⟶ Z) × (Y ⟶ Z) where
  toFun f := (biprod.inl ≫ f, biprod.inr ≫ f)
  invFun p := biprod.desc p.1 p.2
  left_inv f := by
    apply biprod.hom_ext' <;> simp
  right_inv p := by
    rcases p with ⟨a, b⟩
    simp
  map_add' f g := by
    ext <;> simp

/-- Covariant additive Hom turns a binary biproduct into the explicit binary
product of abelian-group-valued functors. -/
noncomputable def abCoyonedaBiprodIso {C : Type u} [Category.{v} C] [Preadditive C]
    (X Y : C) [HasBinaryBiproduct X Y] :
    abCoyoneda (X ⊞ Y) ≅ abPair (abCoyoneda X) (abCoyoneda Y) :=
  NatIso.ofComponents
    (fun Z => (biprodHomAddEquiv X Y Z).toAddCommGrpIso)
    (fun f => by
      ext q <;> simp [biprodHomAddEquiv, Category.assoc])

/-- Naturality of `abPair` in both factors. -/
def abPairCongr {C : Type u} [Category.{v} C]
    {F F' G G' : C ⥤ AddCommGrpCat.{v}} (eF : F ≅ F') (eG : G ≅ G') :
    abPair F G ≅ abPair F' G' :=
  NatIso.ofComponents
    (fun X => (AddEquiv.prodCongr (eF.app X).addCommGroupIsoToAddEquiv
      (eG.app X).addCommGroupIsoToAddEquiv).toAddCommGrpIso)
    (fun f => by
      ext q
      · exact ConcreteCategory.congr_hom (eF.hom.naturality f) q.1
      · exact ConcreteCategory.congr_hom (eG.hom.naturality f) q.2)

/-- The stated natural iso for `preadditiveCoyoneda`, to the explicit pointwise
binary product. -/
noncomputable def preadditiveCoyonedaBiprodIso {C : Type u} [Category.{v} C] [Preadditive C]
    (X Y : C) [HasBinaryBiproduct X Y] :
    preadditiveCoyoneda.obj (.op (X ⊞ Y)) ≅
      abPair (preadditiveCoyoneda.obj (.op X)) (preadditiveCoyoneda.obj (.op Y)) :=
  (abCoyonedaIsoPreadditive (X ⊞ Y)).symm ≪≫ abCoyonedaBiprodIso X Y ≪≫
    abPairCongr (abCoyonedaIsoPreadditive X) (abCoyonedaIsoPreadditive Y)

/-- Covariant additive Hom sends a binary biproduct to the categorical binary
product of `AddCommGrpCat`-valued functors. -/
noncomputable def preadditiveCoyonedaBiprodIsoProd {C : Type u} [Category.{v} C]
    [Preadditive C] (X Y : C) [HasBinaryBiproduct X Y] :
    preadditiveCoyoneda.obj (.op (X ⊞ Y)) ≅
      Limits.prod (preadditiveCoyoneda.obj (.op X)) (preadditiveCoyoneda.obj (.op Y)) :=
  preadditiveCoyonedaBiprodIso X Y ≪≫ abPairIsoProd _ _

/-- **Biproduct closure of compactness.**  This is the `Ab`-valued compactness
statement needed in Lemma 4.3(2); no such closure is available for the old
`Type`-valued `IsCoproductCompact`. -/
lemma isCompactAb_biprod {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} [HasBinaryBiproduct X Y]
    (hX : IsCompactAb X) (hY : IsCompactAb Y) : IsCompactAb (X ⊞ Y) := by
  constructor
  intro J
  letI : PreservesColimitsOfShape (Discrete J) (abCoyoneda X) :=
    preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive X).symm
  letI : PreservesColimitsOfShape (Discrete J) (abCoyoneda Y) :=
    preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive Y).symm
  letI : PreservesColimitsOfShape (Discrete J)
      (abPair (abCoyoneda X) (abCoyoneda Y)) := preservesColimitsOfShape_abPair _ _ J
  letI : PreservesColimitsOfShape (Discrete J) (abCoyoneda (X ⊞ Y)) :=
    preservesColimitsOfShape_of_natIso (abCoyonedaBiprodIso X Y).symm
  exact preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive (X ⊞ Y))


/-- The categorical binary product of coproduct-preserving
`AddCommGrpCat`-valued functors preserves coproducts. -/
lemma preservesColimitsOfShape_prod {C : Type u} [Category.{v} C]
    (F G : C ⥤ AddCommGrpCat.{v}) (J : Type v)
    [PreservesColimitsOfShape (Discrete J) F]
    [PreservesColimitsOfShape (Discrete J) G] :
    PreservesColimitsOfShape (Discrete J) (Limits.prod F G) := by
  letI : PreservesColimitsOfShape (Discrete J) (abPair F G) :=
    preservesColimitsOfShape_abPair F G J
  exact preservesColimitsOfShape_of_natIso (abPairIsoProd F G)

end CompactAb

end RelativeWeakApprox
