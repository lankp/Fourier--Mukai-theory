/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.SpecialDirectLimits
import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-! # Brutal lower truncations, with degreewise split exact sequences -/

@[expose] public section

namespace RelativeFM.AisleGeneration.Brutal

open CategoryTheory CategoryTheory.Limits
open ComplexShape

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The brutal truncation which retains the terms in degrees at least `a`. -/
noncomputable abbrev brutalGE (K : CochainComplex C ℤ) (a : ℤ) : CochainComplex C ℤ :=
  K.stupidTrunc (embeddingUpIntGE a)

lemma ge_index_eq (a i : ℤ) (hi : a ≤ i) :
    (embeddingUpIntGE a).f (i - a).natAbs = i := by
  change a + ((i - a).natAbs : ℤ) = i
  rw [Int.natAbs_of_nonneg (by omega)]
  omega

/-- The retained terms of a brutal truncation identify with the original ones. -/
noncomputable def brutalGEXIso (K : CochainComplex C ℤ) (a i : ℤ) (hi : a ≤ i) :
    (brutalGE K a).X i ≅ K.X i :=
  K.stupidTruncXIso (embeddingUpIntGE a) (ge_index_eq a i hi)

lemma isZero_brutalGE_X (K : CochainComplex C ℤ) {a i : ℤ} (hi : i < a) :
    IsZero ((brutalGE K a).X i) :=
  K.isZero_stupidTrunc_X (embeddingUpIntGE a) i
    ((notMem_range_embeddingUpIntGE_iff a i).2 hi)

@[reassoc]
lemma stupidTrunc_d_eq (K : CochainComplex C ℤ)
    {ι : Type*} {c : ComplexShape ι} (e : c.Embedding (ComplexShape.up ℤ))
    [e.IsRelIff] {i j : ℤ} {k l : ι} (hi : e.f k = i) (hj : e.f l = j) :
    (K.stupidTrunc e).d i j =
      (K.stupidTruncXIso e hi).hom ≫ K.d i j ≫ (K.stupidTruncXIso e hj).inv := by
  subst i
  subst j
  change ((K.restriction e).extend e).d (e.f k) (e.f l) = _
  rw [HomologicalComplex.extend_d_eq _ _ rfl rfl,
    HomologicalComplex.restriction_d_eq _ _ rfl rfl]
  simp only [HomologicalComplex.stupidTruncXIso]
  simp only [Iso.trans_hom, Iso.trans_inv]
  simp [HomologicalComplex.restrictionXIso, Category.assoc]

lemma brutalGE_d (K : CochainComplex C ℤ) {a i j : ℤ} (hi : a ≤ i) (hj : a ≤ j) :
    (brutalGE K a).d i j =
      (brutalGEXIso K a i hi).hom ≫ K.d i j ≫ (brutalGEXIso K a j hj).inv :=
  stupidTrunc_d_eq K (embeddingUpIntGE a) (ge_index_eq a i hi) (ge_index_eq a j hj)

/-- Components of the inclusion of a brutal lower truncation. -/
noncomputable def brutalGEιHom (K : CochainComplex C ℤ) (a i : ℤ) :
    (brutalGE K a).X i ⟶ K.X i :=
  if hi : a ≤ i then (brutalGEXIso K a i hi).hom else 0

/-- The inclusion of the brutal truncation in degrees at least `a`. -/
noncomputable def brutalGEι (K : CochainComplex C ℤ) (a : ℤ) : brutalGE K a ⟶ K where
  f := brutalGEιHom K a
  comm' i j hij := by
    by_cases hi : a ≤ i
    · have hj : a ≤ j := by
        have h : i + 1 = j := hij
        omega
      dsimp [brutalGEιHom]
      rw [dite_eq_left hi, dite_eq_left hj, brutalGE_d K hi hj]
      simp [Category.assoc]
    · exact (isZero_brutalGE_X K (by omega)).eq_of_src _ _

/-- Components of a degreewise retraction of `brutalGEι`. -/
noncomputable def brutalGERetractionHom (K : CochainComplex C ℤ) (a i : ℤ) :
    K.X i ⟶ (brutalGE K a).X i :=
  if hi : a ≤ i then (brutalGEXIso K a i hi).inv else 0

lemma brutalGEι_retraction_f (K : CochainComplex C ℤ) (a i : ℤ) :
    brutalGEιHom K a i ≫ brutalGERetractionHom K a i = 𝟙 _ := by
  by_cases hi : a ≤ i
  · simp [brutalGEιHom, brutalGERetractionHom, hi]
  · exact (isZero_brutalGE_X K (by omega)).eq_of_src _ _

lemma isIso_brutalGEι_f (K : CochainComplex C ℤ) (a i : ℤ) (hi : a ≤ i) :
    IsIso ((brutalGEι K a).f i) := by
  change IsIso (brutalGEιHom K a i)
  rw [show brutalGEιHom K a i = (brutalGEXIso K a i hi).hom by simp [brutalGEιHom, hi]]
  infer_instance

/-- Components of the inclusion `brutalGE K a → brutalGE K b` when `b ≤ a`. -/
noncomputable def brutalGEιOfLEHom (K : CochainComplex C ℤ) {a b : ℤ} (hab : b ≤ a)
    (i : ℤ) : (brutalGE K a).X i ⟶ (brutalGE K b).X i :=
  if hi : a ≤ i then
    (brutalGEXIso K a i hi).hom ≫ (brutalGEXIso K b i (hab.trans hi)).inv
  else 0

/-- The nested inclusion of brutal truncations. -/
noncomputable def brutalGEιOfLE (K : CochainComplex C ℤ) {a b : ℤ} (hab : b ≤ a) :
    brutalGE K a ⟶ brutalGE K b where
  f := brutalGEιOfLEHom K hab
  comm' i j hij := by
    by_cases hi : a ≤ i
    · have hj : a ≤ j := by
        have h : i + 1 = j := hij
        omega
      dsimp [brutalGEιOfLEHom]
      rw [dite_eq_left hi, dite_eq_left hj, brutalGE_d K hi hj,
        brutalGE_d K (hab.trans hi) (hab.trans hj)]
      simp [Category.assoc]
    · exact (isZero_brutalGE_X K (by omega)).eq_of_src _ _

/-- Components of a degreewise retraction of `brutalGEιOfLE`. -/
noncomputable def brutalGEιOfLERetractionHom (K : CochainComplex C ℤ) {a b : ℤ}
    (hab : b ≤ a) (i : ℤ) : (brutalGE K b).X i ⟶ (brutalGE K a).X i :=
  if hi : a ≤ i then
    (brutalGEXIso K b i (hab.trans hi)).hom ≫ (brutalGEXIso K a i hi).inv
  else 0

lemma brutalGEιOfLE_retraction_f (K : CochainComplex C ℤ) {a b : ℤ} (hab : b ≤ a)
    (i : ℤ) : brutalGEιOfLEHom K hab i ≫ brutalGEιOfLERetractionHom K hab i = 𝟙 _ := by
  by_cases hi : a ≤ i
  · simp [brutalGEιOfLEHom, brutalGEιOfLERetractionHom, hi, Category.assoc]
  · exact (isZero_brutalGE_X K (by omega)).eq_of_src _ _

@[reassoc]
lemma brutalGEιOfLE_comp_brutalGEι (K : CochainComplex C ℤ) {a b : ℤ} (hab : b ≤ a) :
    brutalGEιOfLE K hab ≫ brutalGEι K b = brutalGEι K a := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : a ≤ i
  · change brutalGEιOfLEHom K hab i ≫ brutalGEιHom K b i = brutalGEιHom K a i
    simp [brutalGEιOfLEHom, brutalGEιHom, hi, hab.trans hi, Category.assoc]
  · exact (isZero_brutalGE_X K (by omega)).eq_of_src _ _

/-- Projection to the object in degree `a`, as a single complex. -/
noncomputable def brutalGEToSingle (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a] :
    K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (K.X a) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi =>
    (K.isZero_of_isStrictlyGE a i (by
      have h : a - 1 = i := by simpa using (ComplexShape.up ℤ).prev_eq' hi
      omega)).eq_of_src _ _)

/-- Components of a degreewise section of `brutalGEToSingle`. -/
noncomputable def singleSectionHom (K : CochainComplex C ℤ) (a i : ℤ) :
    ((HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (K.X a)).X i ⟶ K.X i :=
  if hi : i = a then
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) a (K.X a) i hi).hom ≫
      (K.XIsoOfEq hi).inv
  else 0

@[simp]
lemma brutalGEToSingle_f_self (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a] :
    (brutalGEToSingle K a).f a = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a _).inv := by
  simp [brutalGEToSingle, HomologicalComplex.mkHomToSingle_f]

lemma brutalGEToSingle_f_of_ne (K : CochainComplex C ℤ) (a i : ℤ) [K.IsStrictlyGE a]
    (hi : i ≠ a) : (brutalGEToSingle K a).f i = 0 := by
  dsimp [brutalGEToSingle, HomologicalComplex.mkHomToSingle]
  rw [dite_eq_right hi]

/-- The degree-split short complex which removes the bottom term of `K`. -/
noncomputable def brutalGEShortComplex (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a] :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (brutalGEι K (a + 1)) (brutalGEToSingle K a) (by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : a + 1 ≤ i
    · have hia : i ≠ a := by omega
      change (brutalGEι K (a + 1)).f i ≫ (brutalGEToSingle K a).f i = 0
      rw [brutalGEToSingle_f_of_ne K a i hia, comp_zero]
    · exact (isZero_brutalGE_X K (by omega)).eq_of_src _ _)

/-- Every degree of `brutalGEShortComplex` splits canonically. -/
noncomputable def brutalGESplitting (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (i : ℤ) : ((brutalGEShortComplex K a).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting where
  r := brutalGERetractionHom K (a + 1) i
  s := singleSectionHom K a i
  f_r := by
    exact brutalGEι_retraction_f K (a + 1) i
  s_g := by
    by_cases hi : i = a
    · subst i
      change singleSectionHom K a a ≫ (brutalGEToSingle K a).f a = 𝟙 _
      rw [brutalGEToSingle_f_self]
      simp [singleSectionHom, HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq]
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a _ i hi).eq_of_src _ _
  id := by
    by_cases hi : a + 1 ≤ i
    · have hia : i ≠ a := by omega
      change brutalGERetractionHom K (a + 1) i ≫ (brutalGEι K (a + 1)).f i +
        (brutalGEToSingle K a).f i ≫ singleSectionHom K a i = 𝟙 _
      rw [brutalGEToSingle_f_of_ne K a i hia, zero_comp, add_zero]
      change brutalGERetractionHom K (a + 1) i ≫ brutalGEιHom K (a + 1) i = 𝟙 _
      simp [brutalGERetractionHom, brutalGEιHom, hi, Category.assoc]
    · by_cases hia : i = a
      · subst i
        simp [brutalGEShortComplex, brutalGERetractionHom, brutalGEιHom,
          singleSectionHom, HomologicalComplex.singleObjXSelf,
          HomologicalComplex.singleObjXIsoOfEq]
      · have hzero : IsZero (K.X i) := K.isZero_of_isStrictlyGE a i (by omega)
        exact hzero.eq_of_src _ _

lemma brutalGEShortComplex_shortExact (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a] :
    (brutalGEShortComplex K a).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i => (brutalGESplitting K a i).shortExact)

/-- A complex strictly supported only in degree `a` is its degree-`a` single complex. -/
noncomputable def isoSingleOfBounds (K : CochainComplex C ℤ) (a : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE a] :
    K ≅ (HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (K.X a) := by
  let z (i : ℤ) (hi : i ≠ a) : IsZero (K.X i) := by
    by_cases h : i < a
    · exact K.isZero_of_isStrictlyGE a i h
    · exact K.isZero_of_isStrictlyLE a i (by omega)
  let e (i : ℤ) : K.X i ≅
      ((HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (K.X a)).X i :=
    if hi : i = a then
      (K.XIsoOfEq hi) ≪≫
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) a (K.X a) i hi).symm
    else IsZero.iso (z i hi) (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a _ i hi)
  exact HomologicalComplex.Hom.isoOfComponents e (by
    intro i j hij
    by_cases hi : i = a
    · subst i
      have hzero : IsZero (K.X j) := K.isZero_of_isStrictlyLE a j (by
        have h : a + 1 = j := hij
        omega)
      have hd : K.d a j = 0 := hzero.eq_of_tgt _ _
      rw [HomologicalComplex.single_obj_d, comp_zero, hd, zero_comp]
    · exact (z i hi).eq_of_src _ _)

end

end RelativeFM.AisleGeneration.Brutal

#print axioms RelativeFM.AisleGeneration.Brutal.brutalGEι
#print axioms RelativeFM.AisleGeneration.Brutal.brutalGEToSingle
#print axioms RelativeFM.AisleGeneration.Brutal.brutalGEShortComplex
#print axioms RelativeFM.AisleGeneration.Brutal.brutalGESplitting
#print axioms RelativeFM.AisleGeneration.Brutal.brutalGEShortComplex_shortExact
#print axioms RelativeFM.AisleGeneration.Brutal.isoSingleOfBounds
