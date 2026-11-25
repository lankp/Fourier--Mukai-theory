/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0
license as described in the file LICENSE.
-/
import FourierMukai.Scheme.AisleGenBrutal

/-!
# A concrete obstruction to stupid-truncation induction for 066S

Over the integers we construct a contractible three-term complex and a
null-homotopic endomorphism `p`.  Every null-homotopic map is homotopy
idempotent.  Nevertheless its brutal truncation is not homotopy idempotent:
comparison with `ℤ[0]` detects multiplication by two versus multiplication
by four.  `stupidTrunc` cannot be used to restrict the derived idempotent in
the proposed Le--Chen amplitude induction.
-/

@[expose] public section
namespace RelativeFM.AffinePerfect.RetractsM3.Counterexample

open CategoryTheory CategoryTheory.Limits
open RelativeFM.AisleGeneration.Brutal
open scoped ZeroObject Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The module in degree `i` of the test complex. -/
def terms (i : ℤ) : ModuleCat.{0} ℤ :=
  if i = -1 then ModuleCat.of ℤ ℤ
  else if i = 0 then ModuleCat.of ℤ (ℤ × ℤ)
  else if i = 1 then ModuleCat.of ℤ ℤ
  else 0

/-- Its two differentials, `x ↦ (x, 0)` and `(x, y) ↦ y`. -/
def diffe (n : ℤ) : terms n ⟶ terms (n + 1) :=
  if hn : n = -1 then
    eqToHom (by rw [hn]; rfl) ≫ ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ) ≫
      eqToHom (by rw [hn]; rfl)
  else if hn : n = 0 then
    eqToHom (by rw [hn]; rfl) ≫ ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ) ≫
      eqToHom (by rw [hn]; rfl)
  else 0

lemma diffe_comp_diffe (n : ℤ) : diffe n ≫ diffe (n + 1) = 0 := by
  by_cases h₁ : n = -1
  · subst n
    change ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ) ≫
      ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ) = 0
    ext x
    rfl
  · by_cases h₀ : n = 0
    · subst n
      change ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ) ≫ (0 : terms 1 ⟶ terms 2) = 0
      exact comp_zero
    · have hn : diffe n = 0 := by simp [diffe, h₁, h₀]
      rw [hn, zero_comp]

/-- The contractible complex `ℤ → ℤ² → ℤ`. -/
def P : CochainComplex (ModuleCat.{0} ℤ) ℤ := CochainComplex.of terms diffe diffe_comp_diffe

@[simp] lemma P_X (n : ℤ) : P.X n = terms n := rfl

@[simp] lemma P_d (n : ℤ) : P.d n (n + 1) = diffe n := by
  exact CochainComplex.of_d terms diffe n

/-- The only nonzero homotopy component, `(x, y) ↦ 2x`. -/
def homData (i j : ℤ) : terms i ⟶ terms j :=
  if h : i = 0 ∧ j = -1 then
    eqToHom (by rw [h.1]; rfl : terms i = ModuleCat.of ℤ (ℤ × ℤ)) ≫
      ((2 : ℤ) • ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ)) ≫
      eqToHom (by rw [h.2]; rfl : ModuleCat.of ℤ ℤ = terms j)
  else 0

/-- The homotopy data, typed with the terms of `P` itself. -/
def pData (i j : ℤ) : P.X i ⟶ P.X j := by
  change terms i ⟶ terms j
  exact homData i j

/-- A null-homotopic endomorphism whose lower component is multiplication by
two. -/
def p : P ⟶ P := Homotopy.nullHomotopicMap'
  (fun i j _ ↦ pData i j)

/-- The original map is homotopy idempotent, since it is null-homotopic. -/
def homotopy_p_sq_p : Homotopy (p ≫ p) p := by
  let h := Homotopy.nullHomotopy' (fun i j _ ↦ pData i j)
  exact (h.comp h).trans ((Homotopy.ofEq (zero_comp)).trans h.symm)

lemma p_f_neg_one :
    eqToHom ((P_X (-1)).symm) ≫ p.f (-1) ≫
      eqToHom (P_X (-1)) =
    ModuleCat.ofHom ((2 : ℤ) • LinearMap.id) := by
  rw [p, Homotopy.nullHomotopicMap'_f (k₂ := -2) (k₁ := -1)
    (k₀ := 0) (by decide) (by decide)]
  dsimp [terms, P, pData, homData, diffe] at *
  simp only [CochainComplex.of_d, Category.id_comp, Category.comp_id,
    zero_comp, add_zero, comp_zero]
  change ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ) ≫
    ModuleCat.ofHom ((2 : ℤ) • LinearMap.fst ℤ ℤ ℤ) =
      ModuleCat.ofHom ((2 : ℤ) • LinearMap.id)
  ext x
  rfl

lemma p_f_zero :
    eqToHom ((P_X 0).symm) ≫ p.f 0 ≫
      eqToHom (P_X 0) =
    ModuleCat.ofHom ((LinearMap.inl ℤ ℤ ℤ).comp
      ((2 : ℤ) • LinearMap.fst ℤ ℤ ℤ)) := by
  rw [p, Homotopy.nullHomotopicMap'_f (k₂ := -1) (k₁ := 0)
    (k₀ := 1) (by decide) (by decide)]
  dsimp [terms, P, pData, homData, diffe] at *
  simp only [CochainComplex.of_d, Category.id_comp, Category.comp_id,
    zero_comp, add_zero, comp_zero]
  rw [zero_add]
  change ModuleCat.ofHom ((2 : ℤ) • LinearMap.fst ℤ ℤ ℤ) ≫
    ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ) =
      ModuleCat.ofHom ((LinearMap.inl ℤ ℤ ℤ).comp
        ((2 : ℤ) • LinearMap.fst ℤ ℤ ℤ))
  ext x <;> simp [LinearMap.comp_apply, smul_eq_mul]

abbrev Q : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  RelativeFM.AisleGeneration.Brutal.brutalGE P 0

/-- The brutal truncation of the null-homotopic endomorphism. -/
def pQ : Q ⟶ Q := HomologicalComplex.stupidTruncMap p (ComplexShape.embeddingUpIntGE 0)

instance : Q.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact RelativeFM.AisleGeneration.Brutal.isZero_brutalGE_X P hn

open RelativeFM.AisleGeneration.Brutal in
private def qIso : Q.X 0 ≅ P.X 0 := brutalGEXIso P 0 0 (by omega)

private def qProj : Q.X 0 ⟶ ModuleCat.of ℤ ℤ :=
  qIso.hom ≫ ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ)

/-- Projection from the truncation to `ℤ[0]`. -/
def q : Q ⟶ (CochainComplex.singleFunctor (ModuleCat.{0} ℤ) 0).obj
    (ModuleCat.of ℤ ℤ) :=
  HomologicalComplex.mkHomToSingle qProj (by
    intro i hi
    change i + 1 = 0 at hi
    have hi' : i = -1 := by omega
    subst i
    exact (isZero_brutalGE_X P (by omega : (-1 : ℤ) < 0)).eq_of_src _ _)

private def sIncl : ModuleCat.of ℤ ℤ ⟶ Q.X 0 :=
  ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ) ≫ qIso.inv

/-- Inclusion of the kernel of the degree-zero differential into the truncation. -/
def s : (CochainComplex.singleFunctor (ModuleCat.{0} ℤ) 0).obj
    (ModuleCat.of ℤ ℤ) ⟶ Q :=
  HomologicalComplex.mkHomFromSingle sIncl (by
    intro k hk
    change 0 + 1 = k at hk
    have hk' : k = 1 := by omega
    subst k
    change sIncl ≫ Q.d 0 1 = 0
    rw [show Q.d 0 1 = qIso.hom ≫ P.d 0 1 ≫
      (brutalGEXIso P 0 1 (by omega)).inv from
      brutalGE_d P (a := 0) (i := 0) (j := 1) (by omega) (by omega)]
    change sIncl ≫ (qIso.hom ≫ P.d 0 (0 + 1) ≫
      (brutalGEXIso P 0 1 (by omega)).inv) = 0
    rw [P_d 0]
    dsimp [sIncl, qProj]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    slice_lhs 1 2 => rw [show ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ) ≫
      diffe 0 = 0 from by
        change ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ) ≫
          ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ) = 0
        ext x
        rfl]
    exact zero_comp)

lemma pQ_f_zero_naturality : pQ.f 0 ≫ qIso.hom = qIso.hom ≫ p.f 0 := by
  exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom p
    (ComplexShape.embeddingUpIntGE 0) (ge_index_eq 0 0 (by omega))

lemma pQ_sq_f_zero_naturality : (pQ ≫ pQ).f 0 ≫ qIso.hom =
    qIso.hom ≫ (p ≫ p).f 0 := by
  simp only [HomologicalComplex.comp_f]
  rw [Category.assoc, pQ_f_zero_naturality, ← Category.assoc,
    pQ_f_zero_naturality, Category.assoc]

lemma composite_pQ : sIncl ≫ pQ.f 0 ≫ qProj =
    ModuleCat.ofHom ((2 : ℤ) • LinearMap.id) := by
  dsimp [sIncl, qProj]
  slice_lhs 3 4 => rw [pQ_f_zero_naturality]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ) ≫
    eqToHom ((P_X 0).symm) ≫ p.f 0 ≫ eqToHom (P_X 0) ≫
      ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ) =
    ModuleCat.ofHom ((2 : ℤ) • LinearMap.id)
  have h := congrArg (fun k : P.X 0 ⟶ P.X 0 ↦
    ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ) ≫ k ≫
      ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ)) p_f_zero
  refine h.trans ?_
  ext x <;> rfl

lemma composite_pQ_sq : sIncl ≫ pQ.f 0 ≫ pQ.f 0 ≫ qProj =
    ModuleCat.ofHom ((4 : ℤ) • LinearMap.id) := by
  dsimp [sIncl, qProj]
  slice_lhs 4 5 => rw [pQ_f_zero_naturality]
  slice_lhs 3 4 => rw [pQ_f_zero_naturality]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ) ≫
    eqToHom ((P_X 0).symm) ≫ p.f 0 ≫ eqToHom (P_X 0) ≫
      eqToHom ((P_X 0).symm) ≫ p.f 0 ≫ eqToHom (P_X 0) ≫
      ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ) =
    ModuleCat.ofHom ((4 : ℤ) • LinearMap.id)
  have h := congrArg (fun k : P.X 0 ⟶ P.X 0 ↦
    ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ) ≫ k ≫ k ≫
      ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ)) p_f_zero
  refine h.trans ?_
  ext x <;> rfl

lemma spQ_f_zero : (s ≫ pQ ≫ q).f 0 =
    ModuleCat.ofHom ((2 : ℤ) • LinearMap.id) := by
  simp only [s, q, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.mkHomToSingle_f, HomologicalComplex.comp_f,
    Category.assoc]
  slice_lhs 2 4 => rw [composite_pQ]
  rfl

lemma spQ_sq_f_zero : (s ≫ pQ ≫ pQ ≫ q).f 0 =
    ModuleCat.ofHom ((4 : ℤ) • LinearMap.id) := by
  simp only [s, q, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.mkHomToSingle_f, HomologicalComplex.comp_f,
    Category.assoc]
  slice_lhs 2 5 => rw [composite_pQ_sq]
  rfl

/-- Homotopies between endomorphisms of a single complex are equalities. -/
lemma eq_of_homotopy_single_self
    {M : ModuleCat.{0} ℤ}
    {f g : (CochainComplex.singleFunctor (ModuleCat.{0} ℤ) 0).obj M ⟶
      (CochainComplex.singleFunctor (ModuleCat.{0} ℤ) 0).obj M}
    (h : Homotopy f g) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    have hn : dNext 0 h.hom = 0 := by
      dsimp [dNext]
      exact zero_comp
    have hp : prevD 0 h.hom = 0 := by
      dsimp [prevD]
      exact comp_zero
    have hc := h.comm 0
    rw [hn, hp] at hc
    simpa only [zero_add] using hc
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi).eq_of_src _ _

/-- The brutal truncation does not preserve homotopy idempotence in this
concrete example. -/
theorem not_homotopy_pQ_sq_p : ¬ Nonempty (Homotopy (pQ ≫ pQ) pQ) := by
  rintro ⟨h⟩
  have hc := eq_of_homotopy_single_self ((h.compLeft s).compRight q)
  have h0 := congrArg (fun f ↦ f.f 0) hc
  change (s ≫ pQ ≫ pQ ≫ q).f 0 = (s ≫ pQ ≫ q).f 0 at h0
  rw [spQ_sq_f_zero, spQ_f_zero] at h0
  have hval := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ ↦
    f.hom (1 : ℤ)) h0
  norm_num at hval

#print axioms homotopy_p_sq_p
#print axioms composite_pQ
#print axioms composite_pQ_sq
#print axioms eq_of_homotopy_single_self
#print axioms not_homotopy_pQ_sq_p

end
end RelativeFM.AffinePerfect.RetractsM3.Counterexample
