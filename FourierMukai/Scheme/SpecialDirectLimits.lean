import FourierMukai.Scheme.KProjectiveResolution
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Split telescopes

An explicit degreewise splitting of the telescope of a sequential direct system
whose successor maps have chosen retractions.  The construction is purely
additive-categorical and uses no exactness of filtered colimits.
-/

@[expose] public section

namespace RelativeFM.SpecialDirectLimits

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasCoproductsOfShape ℕ C]

/-- The successor transition in a sequential direct system. -/
abbrev step (A : ℕ ⥤ C) (n : ℕ) : A.obj n ⟶ A.obj (n + 1) :=
  A.map (homOfLE (Nat.le_add_right n 1))

/-- The coproduct injection at stage `n`. -/
abbrev inj (A : ℕ ⥤ C) (n : ℕ) : A.obj n ⟶ ∐ A.obj :=
  Sigma.ι A.obj n

/-- The shift endomorphism of the direct sum of all stages. -/
def telescopeShift (A : ℕ ⥤ C) : (∐ A.obj) ⟶ (∐ A.obj) :=
  Sigma.desc (fun n ↦ step A n ≫ inj A (n + 1))

@[simp, reassoc]
lemma inj_telescopeShift (A : ℕ ⥤ C) (n : ℕ) :
    inj A n ≫ telescopeShift A = step A n ≫ inj A (n + 1) :=
  Sigma.ι_comp_desc _ n

/-- The telescope differential `1 - shift`. -/
def telescopeDifference (A : ℕ ⥤ C) : (∐ A.obj) ⟶ (∐ A.obj) :=
  𝟙 _ - telescopeShift A

@[simp, reassoc]
lemma inj_telescopeDifference (A : ℕ ⥤ C) (n : ℕ) :
    inj A n ≫ telescopeDifference A = inj A n - step A n ≫ inj A (n + 1) := by
  simp [telescopeDifference]

/-- The canonical map from the direct sum of stages to a cocone. -/
def telescopeToCocone (A : ℕ ⥤ C) (c : Cocone A) : (∐ A.obj) ⟶ c.pt :=
  Sigma.desc (fun n ↦ c.ι.app n)

@[simp, reassoc]
lemma inj_telescopeToCocone (A : ℕ ⥤ C) (c : Cocone A) (n : ℕ) :
    inj A n ≫ telescopeToCocone A c = c.ι.app n :=
  Sigma.ι_comp_desc _ n

@[simp, reassoc]
lemma telescopeDifference_toCocone (A : ℕ ⥤ C) (c : Cocone A) :
    telescopeDifference A ≫ telescopeToCocone A c = 0 := by
  apply Sigma.hom_ext
  intro n
  rw [inj_telescopeDifference_assoc]
  simp only [Preadditive.sub_comp, Category.assoc, inj_telescopeToCocone, zero_comp]
  dsimp only [step]
  rw [c.w]
  simp

/-- The telescope short complex attached to a cocone on a sequential system. -/
def telescopeShortComplex (A : ℕ ⥤ C) (c : Cocone A) :
    ShortComplex C :=
  ShortComplex.mk (telescopeDifference A) (telescopeToCocone A c)
    (telescopeDifference_toCocone A c)

/-- Recursive corrections used to split the telescope. -/
def correction (A : ℕ ⥤ C) (q : ∀ n, A.obj (n + 1) ⟶ A.obj n) :
    ∀ n, A.obj n ⟶ (∐ A.obj)
  | 0 => 0
  | n + 1 => q n ≫ (correction A q n + inj A n)

@[reassoc]
lemma step_correction (A : ℕ ⥤ C) (q : ∀ n, A.obj (n + 1) ⟶ A.obj n)
    (hq : ∀ n, step A n ≫ q n = 𝟙 _) (n : ℕ) :
    step A n ≫ correction A q (n + 1) = correction A q n + inj A n := by
  rw [correction, ← Category.assoc, hq, Category.id_comp]

/-- Components of the section of the telescope projection. -/
def sectionComponent (A : ℕ ⥤ C) (q : ∀ n, A.obj (n + 1) ⟶ A.obj n) (n : ℕ) :
    A.obj n ⟶ (∐ A.obj) :=
  inj A n + correction A q n ≫ telescopeDifference A

lemma step_sectionComponent (A : ℕ ⥤ C) (q : ∀ n, A.obj (n + 1) ⟶ A.obj n)
    (hq : ∀ n, step A n ≫ q n = 𝟙 _) (n : ℕ) :
    step A n ≫ sectionComponent A q (n + 1) = sectionComponent A q n := by
  rw [sectionComponent, sectionComponent, Preadditive.comp_add,
    step_correction_assoc A q hq]
  simp only [Preadditive.add_comp, Category.assoc, inj_telescopeDifference]
  abel

/-- The compatible family of corrected coproduct injections, as a cocone. -/
def sectionCocone (A : ℕ ⥤ C) (q : ∀ n, A.obj (n + 1) ⟶ A.obj n)
    (hq : ∀ n, step A n ≫ q n = 𝟙 _) : Cocone A :=
  Cocone.mk (∐ A.obj) (NatTrans.ofSequence (sectionComponent A q) (fun n ↦ by
    simpa using step_sectionComponent A q hq n))

/-- The section of the canonical map from the telescope to the colimit. -/
def telescopeSection (A : ℕ ⥤ C) (c : Cocone A) (hc : IsColimit c)
    (q : ∀ n, A.obj (n + 1) ⟶ A.obj n) (hq : ∀ n, step A n ≫ q n = 𝟙 _) :
    c.pt ⟶ (∐ A.obj) :=
  hc.desc (sectionCocone A q hq)

@[simp, reassoc]
lemma coconeι_telescopeSection (A : ℕ ⥤ C) (c : Cocone A) (hc : IsColimit c)
    (q : ∀ n, A.obj (n + 1) ⟶ A.obj n) (hq : ∀ n, step A n ≫ q n = 𝟙 _) (n : ℕ) :
    c.ι.app n ≫ telescopeSection A c hc q hq = sectionComponent A q n :=
  hc.fac (sectionCocone A q hq) n

@[simp, reassoc]
lemma telescopeSection_toCocone (A : ℕ ⥤ C) (c : Cocone A) (hc : IsColimit c)
    (q : ∀ n, A.obj (n + 1) ⟶ A.obj n) (hq : ∀ n, step A n ≫ q n = 𝟙 _) :
    telescopeSection A c hc q hq ≫ telescopeToCocone A c = 𝟙 _ := by
  apply hc.hom_ext
  intro n
  rw [coconeι_telescopeSection_assoc, Category.comp_id,
    sectionComponent, Preadditive.add_comp]
  simp only [Category.assoc, telescopeDifference_toCocone, comp_zero,
    add_zero, inj_telescopeToCocone]

end

end RelativeFM.SpecialDirectLimits

namespace RelativeFM.SpecialDirectLimits

open CategoryTheory CategoryTheory.Limits

universe v' u'

noncomputable section

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
variable [HasCoproductsOfShape ℕ D]

/-- The retraction of the telescope differential, with coproduct components
given by the negatives of the recursive corrections. -/
def telescopeRetraction (A : ℕ ⥤ D) (q : ∀ n, A.obj (n + 1) ⟶ A.obj n) :
    (∐ A.obj) ⟶ (∐ A.obj) :=
  Sigma.desc (fun n ↦ -correction A q n)

@[simp, reassoc]
lemma inj_telescopeRetraction (A : ℕ ⥤ D) (q : ∀ n, A.obj (n + 1) ⟶ A.obj n)
    (n : ℕ) :
    inj A n ≫ telescopeRetraction A q = -correction A q n :=
  Sigma.ι_comp_desc _ n

@[simp, reassoc]
lemma telescopeDifference_retraction (A : ℕ ⥤ D)
    (q : ∀ n, A.obj (n + 1) ⟶ A.obj n) (hq : ∀ n, step A n ≫ q n = 𝟙 _) :
    telescopeDifference A ≫ telescopeRetraction A q = 𝟙 _ := by
  apply Sigma.hom_ext
  intro n
  rw [inj_telescopeDifference_assoc]
  simp only [Preadditive.sub_comp, Category.assoc, inj_telescopeRetraction,
    Preadditive.comp_neg, neg_neg, step_correction A q hq, Category.comp_id]
  abel

lemma telescope_retraction_add_section (A : ℕ ⥤ D) (c : Cocone A)
    (hc : IsColimit c) (q : ∀ n, A.obj (n + 1) ⟶ A.obj n)
    (hq : ∀ n, step A n ≫ q n = 𝟙 _) :
    telescopeRetraction A q ≫ telescopeDifference A +
        telescopeToCocone A c ≫ telescopeSection A c hc q hq = 𝟙 _ := by
  apply Sigma.hom_ext
  intro n
  simp only [Preadditive.comp_add, inj_telescopeRetraction_assoc,
    inj_telescopeToCocone_assoc, coconeι_telescopeSection, Category.comp_id,
    Preadditive.neg_comp, sectionComponent]
  abel

/-- A sequential system with chosen retractions of its successor maps has a
canonically split telescope. In particular the telescope is a short exact
sequence, without assuming AB5 or any `lim¹` statement. -/
def telescopeSplitting (A : ℕ ⥤ D) (c : Cocone A) (hc : IsColimit c)
    (q : ∀ n, A.obj (n + 1) ⟶ A.obj n) (hq : ∀ n, step A n ≫ q n = 𝟙 _) :
    (telescopeShortComplex A c).Splitting where
  r := telescopeRetraction A q
  s := telescopeSection A c hc q hq
  f_r := telescopeDifference_retraction A q hq
  s_g := telescopeSection_toCocone A c hc q hq
  id := telescope_retraction_add_section A c hc q hq

/-- The short complex underlying `telescopeSplitting` is short exact. -/
lemma telescopeShortComplex_shortExact (A : ℕ ⥤ D) (c : Cocone A)
    (hc : IsColimit c) (q : ∀ n, A.obj (n + 1) ⟶ A.obj n)
    (hq : ∀ n, step A n ≫ q n = 𝟙 _) :
    (telescopeShortComplex A c).ShortExact :=
  (telescopeSplitting A c hc q hq).shortExact

#print axioms RelativeFM.SpecialDirectLimits.telescopeDifference_retraction
#print axioms RelativeFM.SpecialDirectLimits.telescopeSection_toCocone
#print axioms RelativeFM.SpecialDirectLimits.telescope_retraction_add_section
#print axioms RelativeFM.SpecialDirectLimits.telescopeSplitting
#print axioms RelativeFM.SpecialDirectLimits.telescopeShortComplex_shortExact

end

end RelativeFM.SpecialDirectLimits

namespace RelativeFM.SpecialDirectLimits

open CategoryTheory CategoryTheory.Limits

universe vC uC

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

variable {E : Type uC} [Category.{vC} E] [Abelian E]
variable [HasCoproductsOfShape ℕ E]

/-- The sequential system of terms in a fixed cochain degree. -/
abbrev stages (P : ℕ ⥤ CochainComplex E ℤ) (i : ℤ) : ℕ ⥤ E where
  obj n := (P.obj n).X i
  map f := (P.map f).f i
  map_id _ := by simp
  map_comp _ _ := by simp

/-- The explicit countable coproduct of a sequence of cochain complexes,
with terms literally given by `Sigma` coproducts. -/
abbrev complexCoproduct (P : ℕ ⥤ CochainComplex E ℤ) : CochainComplex E ℤ where
  X i := ∐ (stages P i).obj
  d i j := Sigma.desc (fun n ↦ (P.obj n).d i j ≫
    inj (stages P j) n)
  shape i j h := by
    apply Sigma.hom_ext
    intro n
    rw [Sigma.ι_comp_desc, (P.obj n).shape _ _ h]
    simp
  d_comp_d' i j k _ _ := by
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc, Sigma.ι_comp_desc,
      ← Category.assoc, (P.obj n).d_comp_d, zero_comp, comp_zero]

@[simp, reassoc]
lemma complexCoproduct_ι_d (P : ℕ ⥤ CochainComplex E ℤ)
    (k : ℕ) (i j : ℤ) :
    inj (stages P i) k ≫ (complexCoproduct P).d i j =
      (P.obj k).d i j ≫ inj (stages P j) k := by
  exact Sigma.ι_comp_desc _ k

/-- The chain-map injection of one stage into `complexCoproduct`. -/
def complexCoproductInj (P : ℕ ⥤ CochainComplex E ℤ) (k : ℕ) :
    P.obj k ⟶ complexCoproduct P where
  f i := inj (stages P i) k
  comm' _ _ _ := complexCoproduct_ι_d P k _ _

/-- The explicit coproduct cocone of a sequence of complexes. -/
def complexCoproductCofan (P : ℕ ⥤ CochainComplex E ℤ) :
    Cofan (fun n ↦ P.obj n) :=
  Cofan.mk (complexCoproduct P) (complexCoproductInj P)

/-- The explicit coproduct cocone is colimiting. -/
def complexCoproductCofanIsColimit (P : ℕ ⥤ CochainComplex E ℤ) :
    IsColimit (complexCoproductCofan P) := by
  let desc : ∀ t : Cofan (fun n ↦ P.obj n), complexCoproduct P ⟶ t.pt := fun t ↦
    { f := fun i ↦ Sigma.desc (fun n ↦ (t.inj n).f i)
      comm' := fun i j _ ↦ by
        apply Sigma.hom_ext
        intro n
        rw [← Category.assoc, Sigma.ι_comp_desc, complexCoproduct_ι_d_assoc, Sigma.ι_comp_desc]
        exact (t.inj n).comm i j }
  refine Cofan.IsColimit.mk _ desc ?_ ?_
  · intro t n
    ext i
    exact Sigma.ι_comp_desc _ n
  · intro t m hm
    ext i
    apply Sigma.hom_ext
    intro n
    have h := congrArg (fun f ↦ f.f i) (hm n)
    exact h.trans (Sigma.ι_comp_desc (fun n ↦ (t.inj n).f i) n).symm

/-- The shift endomorphism of the coproduct complex, defined degreewise by
`telescopeShift`. -/
def complexTelescopeShift (P : ℕ ⥤ CochainComplex E ℤ) :
    complexCoproduct P ⟶ complexCoproduct P where
  f i := telescopeShift (stages P i)
  comm' i j _ := by
    apply Sigma.hom_ext
    intro k
    rw [inj_telescopeShift_assoc]
    change (step P k).f i ≫
        inj (stages P i) (k + 1) ≫
          (complexCoproduct P).d i j = _
    rw [complexCoproduct_ι_d, complexCoproduct_ι_d_assoc, inj_telescopeShift]
    simp only [← Category.assoc, (step P k).comm]

end

end RelativeFM.SpecialDirectLimits

namespace RelativeFM.SpecialDirectLimits

open CategoryTheory CategoryTheory.Limits

universe vD uD

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

variable {E : Type uD} [Category.{vD} E] [Abelian E]
variable [HasCoproductsOfShape ℕ E]

/-- The isomorphism between Mathlib's chosen coproduct complex and the native
`Sigma` coproduct complex used here. -/
def complexCoproductIso (P : ℕ ⥤ CochainComplex E ℤ) :
    (DerivedCoproducts.coproductComplexCocone (fun n ↦ P.obj n)).pt ≅
      complexCoproduct P :=
  IsColimit.coconePointUniqueUpToIso
    (DerivedCoproducts.coproductComplexCoconeIsColimit (fun n ↦ P.obj n))
    (complexCoproductCofanIsColimit P)

/-- The native `Sigma` coproduct of K-projective complexes is K-projective. -/
lemma isKProjectiveComplexCoproduct (P : ℕ ⥤ CochainComplex E ℤ)
    [∀ n, (P.obj n).IsKProjective] :
    (complexCoproduct P).IsKProjective :=
  CochainComplex.isKProjective_of_iso (complexCoproductIso P)

/-- The telescope difference on the coproduct complex. -/
abbrev complexTelescopeDifference (P : ℕ ⥤ CochainComplex E ℤ) :
    complexCoproduct P ⟶ complexCoproduct P :=
  𝟙 _ - complexTelescopeShift P

/-- The cocone on the terms in one fixed cochain degree. -/
abbrev stageCocone (P : ℕ ⥤ CochainComplex E ℤ) (c : Cocone P) (i : ℤ) :
    Cocone (stages P i) :=
  Cocone.mk (c.pt.X i)
    { app := fun n ↦ (c.ι.app n).f i
      naturality := fun m n f ↦ by
        have h := congrArg (fun g : P.obj m ⟶ c.pt ↦ g.f i) (c.ι.naturality f)
        simpa only [HomologicalComplex.comp_f, Functor.const_obj_map,
          HomologicalComplex.id_f, Category.comp_id] using h }

/-- The chain-map projection from the coproduct complex to a cocone. -/
abbrev complexTelescopeToCocone (P : ℕ ⥤ CochainComplex E ℤ) (c : Cocone P) :
    complexCoproduct P ⟶ c.pt where
  f i := telescopeToCocone (stages P i) (stageCocone P c i)
  comm' i j _ := by
    apply Sigma.hom_ext
    intro n
    rw [inj_telescopeToCocone_assoc, complexCoproduct_ι_d_assoc,
      inj_telescopeToCocone]
    exact (c.ι.app n).comm i j

@[simp]
lemma complexTelescopeDifference_toCocone (P : ℕ ⥤ CochainComplex E ℤ)
    (c : Cocone P) :
    complexTelescopeDifference P ≫ complexTelescopeToCocone P c = 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  exact telescopeDifference_toCocone (stages P i) (stageCocone P c i)

/-- The telescope short complex of a sequential system of complexes. -/
def complexTelescopeShortComplex (P : ℕ ⥤ CochainComplex E ℤ) (c : Cocone P) :
    ShortComplex (CochainComplex E ℤ) :=
  ShortComplex.mk (complexTelescopeDifference P) (complexTelescopeToCocone P c)
    (complexTelescopeDifference_toCocone P c)

/-- The degreewise splittings of the complex telescope. -/
def complexTelescopeSplitting [HasColimitsOfShape ℕ E]
    (P : ℕ ⥤ CochainComplex E ℤ) (c : Cocone P) (hc : IsColimit c)
    (q : ∀ n i, (P.obj (n + 1)).X i ⟶ (P.obj n).X i)
    (hq : ∀ n i, (step P n).f i ≫ q n i = 𝟙 _) (i : ℤ) :
    ((complexTelescopeShortComplex P c).map
      (HomologicalComplex.eval E (.up ℤ) i)).Splitting := by
  let hc' : IsColimit (stageCocone P c i) :=
    isColimitOfPreserves (HomologicalComplex.eval E (.up ℤ) i) hc
  exact telescopeSplitting (stages P i) (stageCocone P c i) hc' (q · i) (hq · i)

/-- The two-out-of-three closure step for degreewise-split short complexes. -/
lemma isKProjective_obj₃_of_degreewiseSplit
    (S : ShortComplex (CochainComplex E ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval E (.up ℤ) n)).Splitting)
    [S.X₁.IsKProjective] [S.X₂.IsKProjective] :
    S.X₃.IsKProjective := by
  rw [← KProjectiveResolution.mem_kProjective_iff]
  apply KProjectiveResolution.kProjective.ext_of_isTriangulatedClosed₃
    (CochainComplex.trianglehOfDegreewiseSplit S σ)
  · rw [HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit]
    exact ⟨S, σ, ⟨Iso.refl _⟩⟩
  · exact (KProjectiveResolution.mem_kProjective_iff S.X₁).2 inferInstance
  · exact (KProjectiveResolution.mem_kProjective_iff S.X₂).2 inferInstance

/-- Countable special direct limits of K-projective complexes are K-projective.
The hypotheses are exactly a sequential colimit, countable coproducts, and
chosen degreewise retractions of the successor maps. No AB4, AB5,
Mittag--Leffler, or `lim¹` hypothesis is needed. -/
theorem isKProjective_colimit_of_degreewiseSplit [HasColimitsOfShape ℕ E]
    (P : ℕ ⥤ CochainComplex E ℤ) (c : Cocone P) (hc : IsColimit c)
    [∀ n, (P.obj n).IsKProjective]
    (q : ∀ n i, (P.obj (n + 1)).X i ⟶ (P.obj n).X i)
    (hq : ∀ n i, (step P n).f i ≫ q n i = 𝟙 _) :
    c.pt.IsKProjective := by
  letI : (complexCoproduct P).IsKProjective := isKProjectiveComplexCoproduct P
  letI : (complexTelescopeShortComplex P c).X₁.IsKProjective := by
    change (complexCoproduct P).IsKProjective
    infer_instance
  letI : (complexTelescopeShortComplex P c).X₂.IsKProjective := by
    change (complexCoproduct P).IsKProjective
    infer_instance
  exact isKProjective_obj₃_of_degreewiseSplit (complexTelescopeShortComplex P c)
    (complexTelescopeSplitting P c hc q hq)

#print axioms RelativeFM.SpecialDirectLimits.complexCoproductCofanIsColimit
#print axioms RelativeFM.SpecialDirectLimits.complexTelescopeShift
#print axioms RelativeFM.SpecialDirectLimits.isKProjectiveComplexCoproduct
#print axioms RelativeFM.SpecialDirectLimits.complexTelescopeToCocone
#print axioms RelativeFM.SpecialDirectLimits.complexTelescopeSplitting
#print axioms RelativeFM.SpecialDirectLimits.isKProjective_obj₃_of_degreewiseSplit
#print axioms RelativeFM.SpecialDirectLimits.isKProjective_colimit_of_degreewiseSplit

end

end RelativeFM.SpecialDirectLimits

namespace RelativeFM.SpecialDirectLimits

open CategoryTheory CategoryTheory.Limits

universe vE uE

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

variable {E : Type uE} [Category.{vE} E] [Abelian E]

/-- The middle term of a degreewise-split short complex is K-projective when
its outer terms are K-projective. This is the successor-extension step. -/
lemma isKProjective_obj₂_of_degreewiseSplit
    (S : ShortComplex (CochainComplex E ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval E (.up ℤ) n)).Splitting)
    [S.X₁.IsKProjective] [S.X₃.IsKProjective] :
    S.X₂.IsKProjective := by
  rw [← KProjectiveResolution.mem_kProjective_iff]
  apply KProjectiveResolution.kProjective.ext_of_isTriangulatedClosed₂
    (CochainComplex.trianglehOfDegreewiseSplit S σ)
  · rw [HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit]
    exact ⟨S, σ, ⟨Iso.refl _⟩⟩
  · exact (KProjectiveResolution.mem_kProjective_iff S.X₁).2 inferInstance
  · exact (KProjectiveResolution.mem_kProjective_iff S.X₃).2 inferInstance

/-- The first term of a degreewise-split short complex is K-projective when
its last two terms are K-projective. -/
lemma isKProjective_obj₁_of_degreewiseSplit
    (S : ShortComplex (CochainComplex E ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval E (.up ℤ) n)).Splitting)
    [S.X₂.IsKProjective] [S.X₃.IsKProjective] :
    S.X₁.IsKProjective := by
  rw [← KProjectiveResolution.mem_kProjective_iff]
  apply KProjectiveResolution.kProjective.ext_of_isTriangulatedClosed₁
    (CochainComplex.trianglehOfDegreewiseSplit S σ)
  · rw [HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit]
    exact ⟨S, σ, ⟨Iso.refl _⟩⟩
  · exact (KProjectiveResolution.mem_kProjective_iff S.X₂).2 inferInstance
  · exact (KProjectiveResolution.mem_kProjective_iff S.X₃).2 inferInstance

/-- `SplitMono`-data form of `isKProjective_colimit_of_degreewiseSplit`. -/
theorem isKProjective_colimit_ofSplitMono [HasColimitsOfShape ℕ E]
    [HasCoproductsOfShape ℕ E]
    (P : ℕ ⥤ CochainComplex E ℤ) (c : Cocone P) (hc : IsColimit c)
    [∀ n, (P.obj n).IsKProjective]
    (s : ∀ n i, SplitMono ((step P n).f i)) :
    c.pt.IsKProjective :=
  isKProjective_colimit_of_degreewiseSplit P c hc
    (fun n i ↦ (s n i).retraction) (fun n i ↦ (s n i).id)

#print axioms RelativeFM.SpecialDirectLimits.isKProjective_obj₂_of_degreewiseSplit
#print axioms RelativeFM.SpecialDirectLimits.isKProjective_obj₁_of_degreewiseSplit
#print axioms RelativeFM.SpecialDirectLimits.isKProjective_colimit_ofSplitMono

end

end RelativeFM.SpecialDirectLimits

namespace RelativeFM.SpecialDirectLimits

open CategoryTheory CategoryTheory.Limits

universe vF uF

noncomputable section

variable {E : Type uF} [Category.{vF} E] [Abelian E]

/-- Direct colimit form of countable special-direct-limit closure. -/
theorem isKProjective_colimit [HasColimitsOfShape ℕ E] [HasCoproductsOfShape ℕ E]
    (P : ℕ ⥤ CochainComplex E ℤ) [∀ n, (P.obj n).IsKProjective]
    (s : ∀ n i, SplitMono ((step P n).f i)) :
    (colimit P).IsKProjective :=
  isKProjective_colimit_ofSplitMono P (colimit.cocone P) (colimit.isColimit P) s

#print axioms RelativeFM.SpecialDirectLimits.isKProjective_colimit

end

end RelativeFM.SpecialDirectLimits

namespace RelativeFM.SpecialDirectLimits

open CategoryTheory CategoryTheory.Limits

universe vG uG

noncomputable section

variable {E : Type uG} [Category.{vG} E] [Abelian E] [HasDerivedCategory E]

/-- Spaltenstein's sequential approximation, together with the induced
quasi-isomorphism, gives a K-projective resolution in the interface already
used by `DerivedCoproducts`. -/
def resolutionOfSequentialSpecialDirectLimit [HasColimitsOfShape ℕ E]
    [HasCoproductsOfShape ℕ E]
    (K : CochainComplex E ℤ) (P : ℕ ⥤ CochainComplex E ℤ)
    [∀ n, (P.obj n).IsKProjective]
    (s : ∀ n i, SplitMono ((step P n).f i))
    (π : colimit P ⟶ K) [QuasiIso π] :
    DerivedCoproducts.KProjectiveResolution (DerivedCategory.Q.obj K) where
  complex := colimit P
  isKProjective := isKProjective_colimit P s
  iso := asIso (DerivedCategory.Q.map π)

#print axioms RelativeFM.SpecialDirectLimits.resolutionOfSequentialSpecialDirectLimit

end

end RelativeFM.SpecialDirectLimits
