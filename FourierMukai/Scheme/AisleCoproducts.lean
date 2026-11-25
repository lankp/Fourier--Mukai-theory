/-
Coproduct hypotheses localized to fixed aisles.

Candidate module: WeakApprox/AisleCoproducts.lean,
after WeakApprox.Proposition48 and WeakApprox.CompactVanishing.
-/
import WeakApprox.Proposition48
import WeakApprox.Setup44
import WeakApprox.CompactVanishing
import WeakApprox.Lemma46
import WeakApprox.TwoStage
import WeakApprox.MainMinimal
import Mathlib.CategoryTheory.Monad.Limits
import FourierMukai.Scheme.AffineBoundedAboveCoproducts
import FourierMukai.Scheme.AffineUniverse

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Existence of coproducts only for families uniformly bounded above by one
fixed degree of `t`. Unlike `HasCoproducts`, this is available on standard
derived categories using bounded-above K-projective resolutions. -/
class HasAisleCoproducts (t : TStructure C) : Prop where
  hasCoproduct {ι : Type v} (X : ι → C) (d : ℤ) :
    (∀ i, t.le d (X i)) → HasCoproduct X

instance (priority := 100) HasAisleCoproducts.ofHasCoproducts (t : TStructure C)
    [HasCoproducts.{v} C] : HasAisleCoproducts t where
  hasCoproduct _ _ _ := inferInstance

lemma shiftInterval_le (t : TStructure C) {H : C} {n : ℤ} (hH : t.le n H)
    (a b : ℤ) : shiftInterval H a b ≤ t.le (n + b) := by
  rintro X ⟨k, hak, hkb, ⟨e⟩⟩
  apply (t.le (n + b)).prop_of_iso e.symm
  apply t.le_monotone (show n + k ≤ n + b by omega)
  exact t.le_shift n (-k) (n + k) (by ring) H hH

lemma coprod_shiftInterval_le (t : TStructure C) {H : C} {n : ℤ}
    (hH : t.le n H) (a b : ℤ) : Coprod (shiftInterval H a b) ≤ t.le (n + b) := by
  letI (J : Type v) : (t.le (n + b)).IsClosedUnderColimitsOfShape (Discrete J) :=
    TStructure.le_isClosedUnderColimitsOfShape t (n + b) (Discrete J)
  letI : (t.le (n + b)).IsTriangulatedClosed₂ :=
    TStructure.le_isTriangulatedClosed₂ t (n + b)
  exact Coprod.le (shiftInterval_le t hH a b)

lemma envelope_le (t : TStructure C) {H : C} {n : ℤ}
    (hH : t.le n H) (a b : ℤ) : envelope H a b ≤ t.le (n + b) := by
  rw [envelope, ObjectProperty.retractClosure_le_iff]
  exact coprod_shiftInterval_le t hH a b

/-- A bounded-above envelope is closed under every existing small coproduct.
Only coproducts of the chosen `Coprod` representatives (and of their given
retracts) are constructed; both families have the same uniform aisle bound. -/
theorem envelope_closedUnderColimits (t : TStructure C) [HasAisleCoproducts t]
    {H : C} {n : ℤ} (hH : t.le n H) (a b : ℤ) (J : Type v) :
    (envelope H a b).IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    let f : J → C := p.diag.obj ∘ Discrete.mk
    choose Y hY hr using fun j => p.prop_diag_obj ⟨j⟩
    let r : ∀ j, Retract (f j) (Y j) := fun j => (hr j).some
    have hbY : ∀ j, t.le (n + b) (Y j) := fun j =>
      coprod_shiftInterval_le t hH a b (Y j) (hY j)
    letI : HasCoproduct Y :=
      HasAisleCoproducts.hasCoproduct Y (n + b) hbY
    have hbf : ∀ j, t.le (n + b) (f j) := fun j =>
      (t.le (n + b)).prop_of_retract (r j) (hbY j)
    letI : HasCoproduct f :=
      HasAisleCoproducts.hasCoproduct f (n + b) hbf
    have hSigma : envelope H a b (∐ f) := by
      refine ⟨∐ Y, Coprod.of_sigma Y hY, ⟨{
        i := Limits.Sigma.map (fun j => (r j).i)
        r := Limits.Sigma.map (fun j => (r j).r)
        retract := ?_ }⟩⟩
      rw [Limits.Sigma.map_comp_map]
      simpa only [Retract.retract] using (Limits.Sigma.map_id (f := f))
    letI : HasColimit p.diag := p.hasColimit
    have hcolim : envelope H a b (colimit p.diag) :=
      (envelope H a b).prop_of_iso
        (HasColimit.isoOfNatIso Discrete.natIsoFunctor).symm hSigma
    exact (envelope H a b).prop_of_iso
      ((colimit.isColimit p.diag).coconePointUniqueUpToIso p.isColimit) hcolim

/-- Lemma 3.1(5) using only coproducts of uniformly bounded-above families.
The sole coproduct constructed in the proof is the countable Eilenberg-swindle
family; each member is isomorphic to the bounded-above object `Y`. -/
theorem lemma_3_1_5_of_aisleCoproducts (t : TStructure C)
    [HasAisleCoproducts t] (H : C) (a b n : ℤ) (hH : t.le n H) :
    envelope H a b ≤ Coprod (shiftInterval H a (b + 1)) := by
  rintro X ⟨Y, hY, ⟨r⟩⟩
  have hbY : t.le (n + b) Y := coprod_shiftInterval_le t hH a b Y hY
  obtain ⟨X', ⟨e⟩⟩ := retract_exists_biprod_complement r
  have hY' : Coprod (shiftInterval H a b) (X ⊞ X') := .of_isoClosure e hY
  letI : HasCoproduct (fun _ : ULift.{v} ℕ => X ⊞ X') :=
    HasAisleCoproducts.hasCoproduct _ (n + b) (fun _ =>
      (t.le (n + b)).prop_of_iso e hbY)
  let Z : C := ∐ fun _ : ULift.{v} ℕ => X ⊞ X'
  have hZ : Coprod (shiftInterval H a b) Z :=
    Coprod.of_sigma (fun _ : ULift.{v} ℕ => X ⊞ X') (fun _ => hY')
  have hZ_target : Coprod (shiftInterval H a (b + 1)) Z :=
    Coprod_mono (shiftInterval_mono H le_rfl (by omega)) Z hZ
  have hZ_shifted₀ : Coprod (shiftInterval H (a + 1) (b + 1)) (Z⟦(-1 : ℤ)⟧) := by
    have h := map_shift_Coprod (shiftInterval H a b) (-1 : ℤ) hZ
    rw [shiftImage_shiftInterval] at h
    simpa only [sub_neg_eq_add, zero_add] using h
  have hZ_shifted : Coprod (shiftInterval H a (b + 1)) (Z⟦(-1 : ℤ)⟧) :=
    Coprod_mono (shiftInterval_mono H (by omega) (by omega)) _ hZ_shifted₀
  let eZ : X ⊞ Z ≅ Z := swindleIso X X'
  let eT : binaryBiproductTriangle X Z ≅
      Triangle.mk (biprod.inl ≫ eZ.hom) (eZ.inv ≫ biprod.snd) 0 :=
    Triangle.isoMk _ _ (Iso.refl X) eZ (Iso.refl Z)
      (by
        show biprod.inl ≫ eZ.hom = 𝟙 X ≫ (biprod.inl ≫ eZ.hom)
        simp)
      (by
        show (biprod.snd : X ⊞ Z ⟶ Z) ≫ 𝟙 Z = eZ.hom ≫ (eZ.inv ≫ biprod.snd)
        simp)
      (by
        show (0 : Z ⟶ X⟦(1 : ℤ)⟧) ≫ (shiftFunctor C 1).map (𝟙 X) =
          𝟙 Z ≫ (0 : Z ⟶ X⟦(1 : ℤ)⟧)
        simp)
  let T := Triangle.mk (biprod.inl ≫ eZ.hom) (eZ.inv ≫ biprod.snd) 0
  have hT : T ∈ distTriang C := isomorphic_distinguished (binaryBiproductTriangle X Z)
    (binaryBiproductTriangle_distinguished X Z) T eT.symm
  exact Coprod.of_extension T.invRotate (inv_rot_of_distTriang T hT) hZ_shifted hZ_target

end

end RelativeWeakApprox

#print axioms RelativeWeakApprox.shiftInterval_le
#print axioms RelativeWeakApprox.coprod_shiftInterval_le
#print axioms RelativeWeakApprox.envelope_le
#print axioms RelativeWeakApprox.lemma_3_1_5_of_aisleCoproducts

#print axioms RelativeWeakApprox.envelope_closedUnderColimits

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe uZ uD v u

noncomputable section

section BoundedProposition48

variable {DZ : Type uZ} {D : Type uD} [Category.{v} DZ] [Category.{v} D]
  [HasZeroObject DZ] [HasZeroObject D] [HasShift DZ ℤ] [HasShift D ℤ]
  [Preadditive DZ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [IsTriangulated DZ] [IsTriangulated D]

/-- The map of coproducts induced by a family of isomorphisms, assuming only
the two displayed coproducts rather than coproducts of every family. -/
def sigmaMapIsoOfHasCoproduct {C : Type u} [Category.{v} C]
    {ι : Type v} {f g : ι → C} [HasCoproduct f] [HasCoproduct g]
    (e : ∀ j, f j ≅ g j) : (∐ f) ≅ (∐ g) where
  hom := Sigma.desc (fun j => (e j).hom ≫ Sigma.ι g j)
  inv := Sigma.desc (fun j => (e j).inv ≫ Sigma.ι f j)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro j
    simp [Category.assoc]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro j
    simp [Category.assoc]

@[simp] lemma sigmaMapIsoOfHasCoproduct_ι_hom {C : Type u} [Category.{v} C]
    {ι : Type v} {f g : ι → C} [HasCoproduct f] [HasCoproduct g]
    (e : ∀ j, f j ≅ g j) (j : ι) :
    Sigma.ι f j ≫ (sigmaMapIsoOfHasCoproduct e).hom = (e j).hom ≫ Sigma.ι g j := by
  simp [sigmaMapIsoOfHasCoproduct]

/-- Coproduct of lifts, with existence only for a bounded target family and
for the corresponding uniformly bounded family of lift sources. -/
theorem liftableClass_of_sigma_of_aisleCoproducts
    (iStar : D ⥤ DZ) (P K : ObjectProperty D)
    [∀ (J : Type v), PreservesColimitsOfShape (Discrete J) iStar]
    [∀ (J : Type v), P.IsClosedUnderColimitsOfShape (Discrete J)]
    (tD : TStructure D) (tZ : TStructure DZ) (k d : ℤ)
    [HasAisleCoproducts tD] [HasAisleCoproducts tZ] (hPk : P ≤ tD.le k)
    {ι : Type v} (E' : ι → DZ) (hE'le : ∀ j, tZ.le d (E' j)) [HasCoproduct E']
    (hE : ∀ j, liftableClass iStar P K (E' j)) :
    liftableClass iStar P K (∐ E') := by
  intro Y hY f'
  let L (j : ι) : PLift iStar P (Sigma.ι E' j ≫ f') := (hE j hY _).some
  let E : ι → D := fun j => (L j).source
  letI : HasCoproduct E := HasAisleCoproducts.hasCoproduct E k (fun j =>
    hPk (L j).source (L j).source_mem)
  letI : HasCoproduct (fun j => iStar.obj (E j)) :=
    ⟨⟨⟨Cofan.mk _ (fun j => iStar.map (Sigma.ι E j)),
      isColimitOfHasCoproductOfPreservesColimit iStar E⟩⟩⟩
  let q : (∐ E) ⟶ Y := Sigma.desc fun j => (L j).q
  let θ : iStar.obj (∐ E) ≅ ∐ E' :=
    PreservesCoproduct.iso iStar E ≪≫ sigmaMapIsoOfHasCoproduct (fun j => (L j).θ)
  have hP : P (∐ E) := P.prop_colimit (Discrete.functor E) (fun j =>
    (L j.as).source_mem)
  refine ⟨{ source := ∐ E, source_mem := hP, q := q, θ := θ, comm := ?_ }⟩
  let hc := isColimitOfHasCoproductOfPreservesColimit iStar E
  apply hc.hom_ext
  rintro ⟨j⟩
  change iStar.map (Sigma.ι E j) ≫ iStar.map q =
    iStar.map (Sigma.ι E j) ≫ θ.hom ≫ f'
  rw [← iStar.map_comp]
  have hq : Sigma.ι E j ≫ q = (L j).q := by simp [q]
  rw [hq, (L j).comm]
  change (L j).θ.hom ≫ Sigma.ι E' j ≫ f' = _
  simp only [θ, Iso.trans_hom, Category.assoc]
  have hpreserved : iStar.map (Sigma.ι E j) ≫ (PreservesCoproduct.iso iStar E).hom =
      Sigma.ι (fun j => iStar.obj (E j)) j := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit iStar E) (colimit.isColimit _) ⟨j⟩
  simp only [← Category.assoc, hpreserved, sigmaMapIsoOfHasCoproduct_ι_hom]

/-- Bounded coproduct closure of the liftable class intersected with the
containing aisle. -/
theorem liftableClass_inf_aisle_coproducts
    (iStar : D ⥤ DZ) (P K : ObjectProperty D)
    [∀ (J : Type v), PreservesColimitsOfShape (Discrete J) iStar]
    [∀ (J : Type v), P.IsClosedUnderColimitsOfShape (Discrete J)]
    (tD : TStructure D) (tZ : TStructure DZ) (k d : ℤ)
    [HasAisleCoproducts tD] [HasAisleCoproducts tZ] (hPk : P ≤ tD.le k)
    (J : Type v) :
    (liftableClass iStar P K ⊓ tZ.le d).IsClosedUnderColimitsOfShape (Discrete J) := by
  letI := liftableClass_strictFull iStar P K
  letI : (tZ.le d).IsClosedUnderColimitsOfShape (Discrete J) :=
    TStructure.le_isClosedUnderColimitsOfShape tZ d (Discrete J)
  constructor
  rintro X ⟨hX⟩
  let f : J → DZ := hX.diag.obj ∘ Discrete.mk
  have hf : ∀ j, tZ.le d (f j) := fun j => (hX.prop_diag_obj ⟨j⟩).2
  letI : HasCoproduct f := HasAisleCoproducts.hasCoproduct f d hf
  have h : liftableClass iStar P K (∐ f) :=
    liftableClass_of_sigma_of_aisleCoproducts iStar P K tD tZ k d hPk f hf
      (fun j => (hX.prop_diag_obj ⟨j⟩).1)
  letI : HasColimit hX.diag := hX.hasColimit
  letI : HasColimit (Discrete.functor f) := by infer_instance
  let e₁ : (∐ f) ≅ colimit hX.diag :=
    (HasColimit.isoOfNatIso Discrete.natIsoFunctor).symm
  let e₂ : colimit hX.diag ≅ X :=
    (hX.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)).symm
  constructor
  · intro Y hY f'
    obtain ⟨L⟩ := h hY ((e₁.trans e₂).hom ≫ f')
    refine ⟨{ source := L.source
              source_mem := L.source_mem
              q := L.q
              θ := L.θ.trans (e₁.trans e₂)
              comm := ?_ }⟩
    rw [L.comm]
    simp only [Iso.trans_hom, Category.assoc]
  · exact (tZ.le d).prop_of_isColimit hX.isColimit (fun j =>
      (hX.prop_diag_obj j).2)

/-- Proposition 4.8's response inclusion using only coproducts uniformly bounded
by the given aisles. -/
theorem coprod_shiftInterval_le_liftableClass_of_aisleCoproducts
    (iStar : D ⥤ DZ) [iStar.CommShift ℤ] [iStar.IsTriangulated]
    (P K : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    [K.IsClosedUnderIsomorphisms] [P.IsTriangulatedClosed₂]
    [K.IsTriangulatedClosed₂]
    [∀ (J : Type v), PreservesColimitsOfShape (Discrete J) iStar]
    [∀ (J : Type v), P.IsClosedUnderColimitsOfShape (Discrete J)]
    (tD : TStructure D) (tZ : TStructure DZ) (k d : ℤ)
    [HasAisleCoproducts tD] [HasAisleCoproducts tZ]
    (hPk : P ≤ tD.le k) (hPK : P ≤ K)
    (hKshift : ∀ {X : D}, K X → K (X⟦(1 : ℤ)⟧))
    (G : D) (A : ℤ) (hbase : shiftInterval (iStar.obj G) (-A) (A + 1) ≤ tZ.le d)
    (hlemma46 : ∀ n : ℤ, -A - 1 ≤ n → n ≤ A →
      liftableClass iStar P K ((iStar.obj G)⟦n⟧)) :
    Coprod (shiftInterval (iStar.obj G) (-A) (A + 1)) ≤ liftableClass iStar P K := by
  letI : (liftableClass iStar P K).IsClosedUnderIsomorphisms :=
    liftableClass_strictFull iStar P K
  letI : (liftableClass iStar P K).IsTriangulatedClosed₂ :=
    liftableClass_extensions iStar P K hPK hKshift
  letI : (tZ.le d).IsTriangulatedClosed₂ :=
    TStructure.le_isTriangulatedClosed₂ tZ d
  letI : (liftableClass iStar P K ⊓ tZ.le d).IsClosedUnderIsomorphisms := {
    of_iso := fun e hX => ⟨(liftableClass iStar P K).prop_of_iso e hX.1,
      (tZ.le d).prop_of_iso e hX.2⟩ }
  letI : (liftableClass iStar P K ⊓ tZ.le d).IsTriangulatedClosed₂ := by
    apply ObjectProperty.IsTriangulatedClosed₂.mk'
    intro T hT h₁ h₃
    exact ⟨(liftableClass iStar P K).ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1,
      (tZ.le d).ext_of_isTriangulatedClosed₂ T hT h₁.2 h₃.2⟩
  letI (J : Type v) :
      (liftableClass iStar P K ⊓ tZ.le d).IsClosedUnderColimitsOfShape (Discrete J) :=
    liftableClass_inf_aisle_coproducts iStar P K tD tZ k d hPk J
  have hmem : Coprod (shiftInterval (iStar.obj G) (-A) (A + 1)) ≤
      (liftableClass iStar P K ⊓ tZ.le d) := by
    apply Coprod.le
    intro X hX
    obtain ⟨kk, hk_lower, hk_upper, ⟨e⟩⟩ := hX
    constructor
    · have h : liftableClass iStar P K ((iStar.obj G)⟦-kk⟧) :=
        hlemma46 (-kk) (by omega) (by omega)
      intro Y hY f'
      obtain ⟨L⟩ := h hY (e.inv ≫ f')
      refine ⟨{ source := L.source
                source_mem := L.source_mem
                q := L.q
                θ := L.θ.trans e.symm
                comm := ?_ }⟩
      rw [L.comm]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    · exact hbase X ⟨kk, hk_lower, hk_upper, ⟨e⟩⟩
  exact fun X hX => (hmem X hX).1

end BoundedProposition48

end

end RelativeWeakApprox

#print axioms RelativeWeakApprox.liftableClass_of_sigma_of_aisleCoproducts
#print axioms RelativeWeakApprox.liftableClass_inf_aisle_coproducts
#print axioms RelativeWeakApprox.coprod_shiftInterval_le_liftableClass_of_aisleCoproducts

#print axioms RelativeWeakApprox.sigmaMapIsoOfHasCoproduct

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u v uD

noncomputable section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type uD} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

lemma map_coprod_of_closed (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ (ι : Type v), PreservesColimitsOfShape (Discrete ι) F]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    [∀ (ι : Type v), (Coprod Q).retractClosure.IsClosedUnderColimitsOfShape (Discrete ι)]
    (h : ∀ Y, P Y → (Coprod Q).retractClosure (F.obj Y)) {X : C}
    (hX : Coprod P X) : (Coprod Q).retractClosure (F.obj X) := by
  induction hX with
  | of_mem X hX => exact h X hX
  | of_isoClosure e _ ih => exact (Coprod Q).retractClosure.prop_of_iso (F.mapIso e) ih
  | @of_colimitPresentation X J pres hmem ih =>
      exact (Coprod Q).retractClosure.prop_of_isColimit
        (isColimitOfPreserves F pres.isColimit) ih
  | of_extension T hT _ _ ih₁ ih₃ =>
      exact extension_retractClosure _ _ _ (F.map_distinguished T hT) ih₁ ih₃

lemma map_retractClosure_of_closed (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ (ι : Type v), PreservesColimitsOfShape (Discrete ι) F]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    [∀ (ι : Type v), (Coprod Q).retractClosure.IsClosedUnderColimitsOfShape (Discrete ι)]
    (h : ∀ Y, P Y → (Coprod Q).retractClosure (F.obj Y)) {X : C}
    (hX : (Coprod P).retractClosure X) : (Coprod Q).retractClosure (F.obj X) := by
  obtain ⟨Y, hY, ⟨r⟩⟩ := hX
  exact (Coprod Q).retractClosure.prop_of_retract (r.map F)
    (map_coprod_of_closed F h hY)

theorem lemma_3_1_3_of_closed (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ (ι : Type v), PreservesColimitsOfShape (Discrete ι) F]
    (H : C) (H' : D) (a b c d : ℤ) (hF : envelope H' c d (F.obj H))
    [∀ (ι : Type v), (envelope H' (a + c) (b + d)).IsClosedUnderColimitsOfShape
      (Discrete ι)]
    {X : C} (hX : envelope H a b X) : envelope H' (a + c) (b + d) (F.obj X) := by
  letI (ι : Type v) :
      (Coprod (shiftInterval H' (a + c) (b + d))).retractClosure.IsClosedUnderColimitsOfShape (Discrete ι) := by
    change (envelope H' (a + c) (b + d)).IsClosedUnderColimitsOfShape (Discrete ι)
    infer_instance
  refine map_retractClosure_of_closed F ?_ hX
  intro Y hY
  obtain ⟨k, hak, hkb, ⟨e⟩⟩ := hY
  have hshift : (Coprod (shiftInterval H' (a + c) (b + d))).retractClosure
      ((F.obj H)⟦-k⟧) := by
    refine retractClosure_shift (-k) ?_ hF
    intro Z hZ
    exact shiftInterval_mono H' (show a + c ≤ c - -k by omega)
      (show d - -k ≤ b + d by omega) _ (shiftInterval_shift' (-k) hZ)
  exact (Coprod (shiftInterval H' (a + c) (b + d))).retractClosure.prop_of_iso
    (F.mapIso e ≪≫ (F.commShiftIso (-k)).app H).symm hshift

end

end RelativeWeakApprox

#print axioms RelativeWeakApprox.map_coprod_of_closed
#print axioms RelativeWeakApprox.map_retractClosure_of_closed
#print axioms RelativeWeakApprox.lemma_3_1_3_of_closed

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe uU uZ uD v

noncomputable section

section AisleLemma46

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [IsTriangulated DZ] [IsTriangulated D] [IsTriangulated DU]

/-- Lemma 4.6's envelope transport, using only bounded-above coproducts on the
middle category. The open category needs no coproduct-existence assumption:
`j_!` preserves the presentations which occur in the given source envelope. -/
theorem lemma_4_6_envelope_jShriek_of_aisleCoproducts
    (R : Recollement DZ D DU) (WU : WeakApproximationData DU) (tD : TStructure D)
    [HasAisleCoproducts tD] (G : D) (hG_le : tD.le 0 G)
    (hGU : envelope G 0 0 (R.jShriek.obj WU.G)) {W : DU}
    (hW : envelope WU.G (1 - 3 * WU.A) (2 * WU.A + 1) W) :
    envelope G (-3 * WU.A) (3 * WU.A) (R.jShriek.obj W) := by
  letI (ι : Type v) : PreservesColimitsOfShape (Discrete ι) R.jShriek := by
    letI := Adjunction.leftAdjoint_preservesColimits.{v, v} R.jShriekAdj
    infer_instance
  letI (ι : Type v) :
      (envelope G ((1 - 3 * WU.A) + 0) ((2 * WU.A + 1) + 0)).IsClosedUnderColimitsOfShape (Discrete ι) :=
    envelope_closedUnderColimits tD hG_le _ _ _
  have hmap := lemma_3_1_3_of_closed R.jShriek WU.G G
    (1 - 3 * WU.A) (2 * WU.A + 1) 0 0 hGU hW
  simp only [add_zero] at hmap
  exact lemma31_2_mono G (by have := WU.A_pos; omega)
    (by have := WU.A_pos; omega) _ hmap

end AisleLemma46

end

end RelativeWeakApprox

#print axioms RelativeWeakApprox.lemma_4_6_envelope_jShriek_of_aisleCoproducts

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe uZ uD uU v

noncomputable section

section AisleLemma46Full

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [IsTriangulated DZ] [IsTriangulated D] [IsTriangulated DU]

/-- Lemma 4.6 with coproduct existence localized to the fixed aisles of the
middle category. The approximation and triangle arguments are unchanged. -/
theorem lemma_4_6_of_aisleCoproducts
    (R : Recollement DZ D DU) (WU : WeakApproximationData DU)
    (tD : TStructure D) [HasAisleCoproducts tD] (tZ : TStructure DZ)
    (hglue : tD.le 0 = gluedLe R.iStar R.jStar tZ WU.t 0)
    (G : D) (hG_le : tD.le 0 G)
    (hGU : envelope G 0 0 (R.jShriek.obj WU.G))
    (hvan : ∀ {Z : D}, tD.le (-WU.A) Z → ∀ f : G ⟶ Z, f = 0)
    {Y : D} (hY : tD.le (WU.A + 1) Y) {n : ℤ}
    (hn₁ : -WU.A - 1 ≤ n) (hn₂ : n ≤ WU.A)
    (f' : (R.iStar.obj G)⟦n⟧ ⟶ R.iStar.obj Y) :
    Nonempty (PLift R.iStar (lemma46P G tD WU.A) f') := by
  obtain ⟨W, V, w, c, d, hT, hW, hWa, hV⟩ :=
    lemma_4_6_approximation R WU tD tZ hglue hY
  let J : Triangle D := R.jShriek.mapTriangle.obj (Triangle.mk w c d)
  have hJ : J ∈ distTriang D := R.jShriek.map_distinguished _ hT
  let S : Triangle D := (Triangle.shiftFunctor D (1 : ℤ)).obj J
  have hS : S ∈ distTriang D := Triangle.shift_distinguished J hJ (1 : ℤ)
  let f₀ : R.iStar.obj (G⟦n⟧) ⟶ R.iStar.obj Y :=
    (R.iStar.commShiftIso n).hom.app G ≫ f'
  let g : G⟦n⟧ ⟶ R.iLower.obj (R.iStar.obj Y) := R.iStarAdj.homEquiv _ _ f₀
  have hf₀ : f₀ = R.iStar.map g ≫ R.iStarAdj.counit.app (R.iStar.obj Y) := by
    calc
      f₀ = (R.iStarAdj.homEquiv _ _).symm (R.iStarAdj.homEquiv _ _ f₀) :=
        ((R.iStarAdj.homEquiv _ _).symm_apply_apply f₀).symm
      _ = _ := R.iStarAdj.homEquiv_counit _ _ g
  let ξ : G⟦n⟧ ⟶ R.jShriek.obj (R.jStar.obj Y)⟦(1 : ℤ)⟧ :=
    g ≫ R.firstConnecting.app Y
  obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₂ S hS ξ
    (lemma_4_6_vanishing R tD tZ WU.t hglue G hvan hV hn₂ _)
  change G⟦n⟧ ⟶ R.jShriek.obj W⟦(1 : ℤ)⟧ at z
  obtain ⟨Q, α, β, hTop⟩ := distinguished_cocone_triangle₂ (-z)
  change ξ = z ≫ ((1 : ℤ).negOnePow • (R.jShriek.map w)⟦(1 : ℤ)⟧') at hz
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul] at hz
  have hcomm : (-z) ≫ (R.jShriek.map w)⟦(1 : ℤ)⟧' =
      g ≫ R.firstConnecting.app Y := by
    simpa only [ξ, Preadditive.neg_comp, Preadditive.comp_neg] using hz.symm
  obtain ⟨q, _hq₁, hq₂⟩ := complete_distinguished_triangle_morphism₂
    (Triangle.mk α β (-z)) (R.firstTriangle Y) hTop (R.first_distinguished Y)
    (R.jShriek.map w) g hcomm
  change Q ⟶ Y at q
  change β ≫ g = q ≫ R.iStarAdj.unit.app Y at hq₂
  have hβ : IsIso (R.iStar.map β) := by
    let T' : Triangle DZ := R.iStar.mapTriangle.obj (Triangle.mk α β (-z))
    have hT' : T' ∈ distTriang DZ := R.iStar.map_distinguished _ hTop
    have hzero : IsZero T'.obj₁ := R.iStar_jShriek_isZero W
    have h := (T'.isZero₁_iff_isIso₂ hT').1 hzero
    exact h
  let θ : R.iStar.obj Q ≅ (R.iStar.obj G)⟦n⟧ :=
    asIso (R.iStar.map β) ≪≫ (R.iStar.commShiftIso n).app G
  have hmapq : R.iStar.map β ≫ R.iStar.map g =
      R.iStar.map q ≫ R.iStar.map (R.iStarAdj.unit.app Y) := by
    calc
      R.iStar.map β ≫ R.iStar.map g = R.iStar.map (β ≫ g) :=
        (R.iStar.map_comp β g).symm
      _ = R.iStar.map (q ≫ R.iStarAdj.unit.app Y) := congrArg (fun k => R.iStar.map k) hq₂
      _ = R.iStar.map q ≫ R.iStar.map (R.iStarAdj.unit.app Y) :=
        R.iStar.map_comp q (R.iStarAdj.unit.app Y)
  have hq : R.iStar.map q = θ.hom ≫ f' := by
    calc
      R.iStar.map q = R.iStar.map q ≫
          (R.iStar.map (R.iStarAdj.unit.app Y) ≫ R.iStarAdj.counit.app (R.iStar.obj Y)) := by
        rw [R.iStarAdj.left_triangle_components, Category.comp_id]
      _ = (R.iStar.map q ≫ R.iStar.map (R.iStarAdj.unit.app Y)) ≫
          R.iStarAdj.counit.app (R.iStar.obj Y) := by rw [Category.assoc]
      _ = (R.iStar.map β ≫ R.iStar.map g) ≫ R.iStarAdj.counit.app (R.iStar.obj Y) := by
        rw [← hmapq]
      _ = R.iStar.map β ≫
          (R.iStar.map g ≫ R.iStarAdj.counit.app (R.iStar.obj Y)) := by
        rw [Category.assoc]
      _ = R.iStar.map β ≫ f₀ := by rw [← hf₀]
      _ = θ.hom ≫ f' := by simp [θ, f₀, Category.assoc]
  have hJWenv : envelope G (-3 * WU.A) (3 * WU.A) (R.jShriek.obj W) :=
    lemma_4_6_envelope_jShriek_of_aisleCoproducts R WU tD G hG_le hGU hW
  have hJWa : tD.le (WU.A + 1) (R.jShriek.obj W) :=
    lemma_4_2_jShriek R.iStar R.jShriek R.jStar tD tZ WU.t hglue
      R.jShriekAdj R.iStar_jShriek (WU.A + 1) hWa
  have hGnenv : envelope G (-3 * WU.A) (3 * WU.A) (G⟦n⟧) := by
    apply lemma31_2_mono G (a := -WU.A) (b := WU.A + 1)
      (by have := WU.A_pos; omega) (by have := WU.A_pos; omega)
    apply lemma_3_1_1_contains
    refine ⟨-n, by omega, by omega, ⟨?_⟩⟩
    rw [neg_neg]
  have hGna : tD.le (WU.A + 1) (G⟦n⟧) := by
    have h := tD.le_shift 0 n (-n) (by omega) G hG_le
    exact tD.le_monotone (by omega) _ h
  have hQenv : envelope G (-3 * WU.A) (3 * WU.A) Q := by
    let _ := lemma_3_1_1_extensions G (-3 * WU.A) (3 * WU.A)
    exact (envelope G (-3 * WU.A) (3 * WU.A)).ext_of_isTriangulatedClosed₂
      (Triangle.mk α β (-z)) hTop hJWenv hGnenv
  have hQa : tD.le (WU.A + 1) Q :=
    (tD.isLE₂ (Triangle.mk α β (-z)) hTop (WU.A + 1) ⟨hJWa⟩ ⟨hGna⟩).le
  exact ⟨⟨Q, q, θ, ⟨hQenv, hQa⟩, hq⟩⟩

end AisleLemma46Full

end

end RelativeWeakApprox

#print axioms RelativeWeakApprox.lemma_4_6_of_aisleCoproducts

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe uZ uD uU v

noncomputable section

namespace Setup44

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

variable (S : Setup44 DZ D DU)

/-- The closed generator lies in degree at most zero. -/
theorem iStar_G_mem_le_zero : S.tZ.le 0 (S.R.iStar.obj S.G) := by
  rw [S.tZ_le_zero_eq_coprod]
  exact Coprod.of_mem _ ⟨0, le_rfl, ⟨(shiftFunctorZero DZ ℤ).symm.app (S.R.iStar.obj S.G)⟩⟩

/-- `P` is closed under existing coproducts, using only bounded coproduct
existence on the middle `t`-structure. -/
theorem P_coproducts_of_aisleCoproducts [HasAisleCoproducts S.tD] (J : Type v) :
    S.P.IsClosedUnderColimitsOfShape (Discrete J) := by
  letI : (envelope S.G (-S.B) S.B).IsClosedUnderColimitsOfShape (Discrete J) :=
    envelope_closedUnderColimits S.tD S.G_mem_le_zero (-S.B) S.B J
  letI : (S.tD.le S.K).IsClosedUnderColimitsOfShape (Discrete J) :=
    TStructure.le_isClosedUnderColimitsOfShape S.tD S.K (Discrete J)
  refine ⟨?_⟩
  rintro X ⟨p⟩
  exact ⟨(envelope S.G (-S.B) S.B).prop_of_isColimit p.isColimit
      (fun j => (p.prop_diag_obj j).1),
    (S.tD.le S.K).prop_of_isColimit p.isColimit
      (fun j => (p.prop_diag_obj j).2)⟩

/-- Lemma 4.6 specialized to Setup 4.4 with bounded middle coproducts. -/
theorem exists_PLift_of_aisleCoproducts [HasAisleCoproducts S.tD]
    {Y : D} (hY : S.tD.le S.K Y) {n : ℤ}
    (hn₁ : -S.A - 1 ≤ n) (hn₂ : n ≤ S.A)
    (f' : (S.R.iStar.obj S.G)⟦n⟧ ⟶ S.R.iStar.obj Y) :
    Nonempty (PLift S.R.iStar S.P f') := by
  have hY' : S.tD.le (S.approxU.A + 1) Y := by
    simpa only [K, S.approxU_A] using hY
  have hn₁' : -S.approxU.A - 1 ≤ n := by simpa only [S.approxU_A] using hn₁
  have hn₂' : n ≤ S.approxU.A := by simpa only [S.approxU_A] using hn₂
  have hP : S.P = lemma46P S.G S.tD S.approxU.A := by
    ext Z
    simp only [P, B, K, lemma46P, S.approxU_A, ObjectProperty.prop_inf_iff, neg_mul]
  rw [hP]
  exact lemma_4_6_of_aisleCoproducts S.R S.approxU S.tD S.tZ S.tD_glued_approxU
    S.G S.G_mem_le_zero S.jShriek_approxU_G_mem_envelope_zero
    (fun hY f => S.hom_vanishing_approxU hY f) hY' hn₁' hn₂' f'

/-- Proposition 4.8's swindle inclusion with bounded closed coproducts. -/
theorem envelope_le_coprod_of_aisleCoproducts [HasAisleCoproducts S.tZ] :
    envelope (S.R.iStar.obj S.G) (-S.A) S.A ≤
      Coprod (shiftInterval (S.R.iStar.obj S.G) (-S.A) (S.A + 1)) :=
  lemma_3_1_5_of_aisleCoproducts S.tZ (S.R.iStar.obj S.G) (-S.A) S.A 0
    S.iStar_G_mem_le_zero

/-- Proposition 4.8's lift inclusion with bounded middle and closed coproducts. -/
theorem coprod_shiftInterval_le_liftableClass_of_aisleCoproducts
    [HasAisleCoproducts S.tD] [HasAisleCoproducts S.tZ] :
    Coprod (shiftInterval (S.R.iStar.obj S.G) (-S.A) (S.A + 1)) ≤
      liftableClass S.R.iStar S.P (S.tD.le S.K) := by
  letI : S.P.IsClosedUnderIsomorphisms := S.P_isClosedUnderIsomorphisms
  letI : S.P.IsTriangulatedClosed₂ := S.P_extensions
  letI : (S.tD.le S.K).IsTriangulatedClosed₂ :=
    TStructure.le_isTriangulatedClosed₂ S.tD S.K
  letI (J : Type v) : PreservesColimitsOfShape (Discrete J) S.R.iStar := by
    letI := Adjunction.leftAdjoint_preservesColimits.{v, v} S.R.iStarAdj
    infer_instance
  letI (J : Type v) : S.P.IsClosedUnderColimitsOfShape (Discrete J) :=
    S.P_coproducts_of_aisleCoproducts J
  have hPK : S.P ≤ S.tD.le S.K := fun _ hX => hX.2
  have hKshift : ∀ {X : D}, S.tD.le S.K X → S.tD.le S.K (X⟦(1 : ℤ)⟧) := by
    intro X hX
    apply S.tD.le_monotone (show S.K - 1 ≤ S.K by omega)
    exact S.tD.le_shift S.K 1 (S.K - 1) (by ring) X hX
  have hbase : shiftInterval (S.R.iStar.obj S.G) (-S.A) (S.A + 1) ≤
      S.tZ.le (S.A + 1) := by
    simpa only [zero_add] using
      shiftInterval_le S.tZ S.iStar_G_mem_le_zero (-S.A) (S.A + 1)
  have hlemma : ∀ n : ℤ, -S.A - 1 ≤ n → n ≤ S.A →
      liftableClass S.R.iStar S.P (S.tD.le S.K) ((S.R.iStar.obj S.G)⟦n⟧) := by
    intro n hn₁ hn₂ Y hY f'
    exact S.exists_PLift_of_aisleCoproducts hY hn₁ hn₂ f'
  exact RelativeWeakApprox.coprod_shiftInterval_le_liftableClass_of_aisleCoproducts
    S.R.iStar S.P (S.tD.le S.K) S.tD S.tZ S.K (S.A + 1)
    (fun _ hX => hX.2) hPK hKshift S.G S.A hbase hlemma

end Setup44

end

end RelativeWeakApprox

#print axioms RelativeWeakApprox.Setup44.iStar_G_mem_le_zero
#print axioms RelativeWeakApprox.Setup44.P_coproducts_of_aisleCoproducts
#print axioms RelativeWeakApprox.Setup44.exists_PLift_of_aisleCoproducts
#print axioms RelativeWeakApprox.Setup44.envelope_le_coprod_of_aisleCoproducts
#print axioms RelativeWeakApprox.Setup44.coprod_shiftInterval_le_liftableClass_of_aisleCoproducts

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe uZ uD uU v

noncomputable section

namespace Setup44

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- The first stage of Theorem 1.1 with bounded aisle coproducts. -/
theorem exists_firstApproximation_of_aisleCoproducts (S : Setup44 DZ D DU)
    [HasAisleCoproducts S.tD] [HasAisleCoproducts S.tZ]
    {F : D} (hF : S.tD.le 0 F) :
    ∃ (E N : D) (q : E ⟶ F) (r : F ⟶ N) (s : N ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk q r s ∈ distTriang D ∧
      envelope S.G (-S.B) S.B E ∧ S.tD.le S.K E ∧
      S.tZ.le (-1) (S.R.iStar.obj N) := by
  have hiF : S.approxZ.t.le 0 (S.R.iStar.obj F) := by
    rw [S.approxZ_t]
    exact lemma_4_2_iStar S.R.iStar S.R.jStar S.tD S.tZ S.tU S.tD_glued 0 hF
  obtain ⟨E', Z, f', g', h', hT', hE', hZ⟩ := S.approxZ.exists_triangle _ hiF
  have hE'' : envelope (S.R.iStar.obj S.G) (-S.A) S.A E' := by
    simpa only [S.approxZ_G, S.approxZ_A, G] using hE'
  have hZ' : S.tZ.le (-1) Z := by
    rw [← S.approxZ_t]
    exact hZ
  have hFK : S.tD.le S.K F := by
    apply S.tD.le_monotone (show 0 ≤ S.K by dsimp [K]; have := S.A_pos; omega) F hF
  have hEC : Coprod (shiftInterval (S.R.iStar.obj S.G) (-S.A) (S.A + 1)) E' :=
    S.envelope_le_coprod_of_aisleCoproducts E' hE''
  obtain ⟨L⟩ := S.coprod_shiftInterval_le_liftableClass_of_aisleCoproducts
    E' hEC hFK f'
  obtain ⟨N, r, s, hN⟩ := distinguished_cocone_triangle L.q
  let Ti := S.R.iStar.mapTriangle.obj (Triangle.mk L.q r s)
  have hTi : Ti ∈ distTriang DZ := S.R.iStar.map_distinguished _ hN
  let φ := completeDistinguishedTriangleMorphism Ti (Triangle.mk f' g' h') hTi hT'
    L.θ.hom (𝟙 (S.R.iStar.obj F)) (by
      change S.R.iStar.map L.q ≫ 𝟙 (S.R.iStar.obj F) = L.θ.hom ≫ f'
      rw [Category.comp_id, L.comm])
  haveI : IsIso φ.hom₁ := by change IsIso L.θ.hom; infer_instance
  haveI : IsIso φ.hom₂ := by change IsIso (𝟙 (S.R.iStar.obj F)); infer_instance
  haveI : IsIso φ.hom₃ := by
    apply isIso₃_of_isIso₁₂ φ hTi hT'
    · infer_instance
    · infer_instance
  let eN' := asIso φ.hom₃
  let eN : Ti.obj₃ ≅ Z := eN'
  have hiN : S.tZ.le (-1) (S.R.iStar.obj N) :=
    (S.tZ.le (-1)).prop_of_iso eN.symm hZ'
  exact ⟨L.source, N, L.q, r, s, hN, L.source_mem.1, L.source_mem.2, hiN⟩

end Setup44

end

end RelativeWeakApprox

#print axioms RelativeWeakApprox.Setup44.exists_firstApproximation_of_aisleCoproducts

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe uZ uD uU v

noncomputable section

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- The reverse implication in LP Theorem 1.1 with only bounded-above
coproduct existence on the middle and closed `t`-structures. -/
theorem theorem_1_1_of_aisleCoproducts (S : Setup44 DZ D DU)
    [HasAisleCoproducts S.tD] [HasAisleCoproducts S.tZ] :
    ∃ (W : WeakApproximationData D), W.t = S.tD ∧ W.G = S.G ∧ W.A = S.B := by
  have hBpos : 0 < S.B := by dsimp [Setup44.B]; have := S.A_pos; omega
  have hGmem : S.tD.le S.B S.G := by
    apply S.tD.le_monotone (show 0 ≤ S.B by omega) S.G S.G_mem_le_zero
  have hvan : ∀ {Y : D}, S.tD.le (-S.B) Y → ∀ f : S.G ⟶ Y, f = 0 := by
    intro Y hY f
    apply S.G_hom_vanishing _ f
    exact S.tD.le_monotone (by dsimp [Setup44.B]; have := S.A_pos; omega) Y hY
  refine ⟨{
    G := S.G
    t := S.tD
    A := S.B
    A_pos := hBpos
    G_compact := S.G_compact
    G_generates := S.G_generates
    G_mem_le := hGmem
    hom_vanishing := hvan
    exists_triangle := ?_ }, rfl, rfl, rfl⟩
  intro F hF
  obtain ⟨E, N, q, r, s, hN, hE, hEK, hiN⟩ := S.exists_firstApproximation_of_aisleCoproducts hF
  have hFK : S.tD.le S.K F := by
    apply S.tD.le_monotone (show 0 ≤ S.K by dsimp [Setup44.K]; have := S.A_pos; omega) F hF
  have hEKshift : S.tD.le S.K (E⟦(1 : ℤ)⟧) := by
    apply S.tD.le_monotone (show S.K - 1 ≤ S.K by omega)
    exact S.tD.le_shift S.K 1 (S.K - 1) (by ring) E hEK
  have hNK : S.tD.le S.K N := by
    exact (S.tD.isLE₂ (Triangle.mk q r s).rotate (rot_of_distTriang _ hN) S.K
      ⟨hFK⟩ ⟨hEKshift⟩).le
  have hNK' : S.tD.le (S.approxU.A + 1) N := by
    simpa only [Setup44.K, S.approxU_A] using hNK
  obtain ⟨X, V, w, c, d, hXV, hX, hXK, hV⟩ :=
    lemma_4_6_approximation S.R S.approxU S.tD S.tZ S.tD_glued_approxU hNK'
  let p : S.R.jShriek.obj X ⟶ N := (S.R.jShriekAdj.homEquiv X N).symm w
  obtain ⟨C, k, l, hC⟩ := distinguished_cocone_triangle p
  let Ti := S.R.iStar.mapTriangle.obj (Triangle.mk p k l)
  have hTi : Ti ∈ distTriang DZ := S.R.iStar.map_distinguished _ hC
  have hzero : IsZero Ti.obj₁ := S.R.iStar_jShriek_isZero X
  haveI : IsIso (S.R.iStar.map k) := (Ti.isZero₁_iff_isIso₂ hTi).1 hzero
  let ei : S.R.iStar.obj N ≅ S.R.iStar.obj C := asIso (S.R.iStar.map k)
  have hiC : S.tZ.le (-1) (S.R.iStar.obj C) :=
    (S.tZ.le (-1)).prop_of_iso ei hiN
  let Tj := S.R.jStar.mapTriangle.obj (Triangle.mk p k l)
  have hTj : Tj ∈ distTriang DU := S.R.jStar.map_distinguished _ hC
  let eX : Tj.obj₁ ≅ X := (asIso (S.R.jShriekAdj.unit.app X)).symm
  have hw : w = S.R.jShriekAdj.unit.app X ≫ S.R.jStar.map p := by
    change w = S.R.jShriekAdj.unit.app X ≫
      S.R.jStar.map ((S.R.jShriekAdj.homEquiv X N).symm w)
    simpa only [Equiv.apply_symm_apply] using
      (S.R.jShriekAdj.homEquiv_unit (f := (S.R.jShriekAdj.homEquiv X N).symm w))
  have hcomm : Tj.mor₁ = eX.hom ≫ w := by
    change S.R.jStar.map p = inv (S.R.jShriekAdj.unit.app X) ≫ w
    rw [hw]
    simp
  obtain ⟨l', hX'⟩ := exists_distinguished_triangle_same_mor₂ Tj hTj eX w hcomm
  let φV := completeDistinguishedTriangleMorphism (Triangle.mk w c d)
    (Triangle.mk w Tj.mor₂ l') hXV hX' (𝟙 X) (𝟙 (S.R.jStar.obj N)) (by
      change w ≫ 𝟙 (S.R.jStar.obj N) = 𝟙 X ≫ w
      simp)
  haveI : IsIso φV.hom₁ := by change IsIso (𝟙 X); infer_instance
  haveI : IsIso φV.hom₂ := by change IsIso (𝟙 (S.R.jStar.obj N)); infer_instance
  haveI : IsIso φV.hom₃ := by
    apply isIso₃_of_isIso₁₂ φV hXV hX'
    · infer_instance
    · infer_instance
  let eV' := asIso φV.hom₃
  let eV : V ≅ Tj.obj₃ := eV'
  have hV' : S.approxU.t.le (-1) V := by
    apply S.approxU.t.le_monotone (show -2 * S.approxU.A ≤ -1 by have := S.approxU.A_pos; omega)
    exact hV
  have hjC : S.tU.le (-1) (S.R.jStar.obj C) := by
    rw [← S.approxU_t]
    exact (S.approxU.t.le (-1)).prop_of_iso eV hV'
  obtain ⟨E', f, h, hE'⟩ := distinguished_cocone_triangle₁ (r ≫ k)
  obtain ⟨u, v, huv⟩ := remark_3_2_2 r k q s p l f h hN hC hE'
  have hJX : envelope S.G (-S.B) S.B (S.R.jShriek.obj X) := by
    simpa only [Setup44.B, S.approxU_A, neg_mul] using
      lemma_4_6_envelope_jShriek_of_aisleCoproducts S.R S.approxU S.tD S.G
        S.G_mem_le_zero S.jShriek_approxU_G_mem_envelope_zero hX
  have hE'env : envelope S.G (-S.B) S.B E' := by
    letI : (envelope S.G (-S.B) S.B).IsTriangulatedClosed₂ :=
      lemma_3_1_1_extensions S.G (-S.B) S.B
    exact (envelope S.G (-S.B) S.B).ext_of_isTriangulatedClosed₂
      (Triangle.mk u v (p ≫ s)) huv hE hJX
  have hCle : S.tD.le (-1) C := by
    rw [lemma_4_2 S.R.iStar S.R.jStar S.tD S.tZ S.tU S.tD_glued (-1)]
    exact ⟨hiC, hjC⟩
  exact ⟨E', C, f, r ≫ k, h, hE', hE'env, hCle⟩

/-- Categorical weak approximability with only bounded aisle coproducts. -/
theorem satisfiesWA_of_aisleCoproducts (S : Setup44 DZ D DU)
    [HasAisleCoproducts S.tD] [HasAisleCoproducts S.tZ] : SatisfiesWA D := by
  obtain ⟨W, _⟩ := theorem_1_1_of_aisleCoproducts S
  exact ⟨W⟩

end

end RelativeWeakApprox

#print axioms RelativeWeakApprox.theorem_1_1_of_aisleCoproducts
#print axioms RelativeWeakApprox.satisfiesWA_of_aisleCoproducts

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe uZ uD uU v

noncomputable section

namespace SetupMainMinimal

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- LP Theorem 1.1 at the minimal setup level, with unrestricted coproduct
existence replaced by fixed-aisle coproducts on the middle and closed ends. -/
theorem theorem_1_1_of_aisleCoproducts (S : SetupMainMinimal DZ D DU)
    [HasAisleCoproducts S.tD] [HasAisleCoproducts S.tZ]
    (h09SR : ∀ (G : D), IsGenerator G → IsCompactAb G →
      IsClassicalGeneratorOnCompacts G) :
    SatisfiesWA D ↔ ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∀ f : S.G' ⟶ S.G'⟦n⟧, f = 0 := by
  constructor
  · intro h
    obtain ⟨W⟩ := h
    have hgen : IsClassicalGeneratorOnCompacts W.G :=
      h09SR W.G W.G_generates W.G_compact
    have hmem : (ObjectProperty.singleton W.G).triangEnvelope S.G' :=
      hgen S.G' S.G'_compact
    exact eventuallyHomZero_self_of_mem_triangEnvelope W hmem
  · intro h
    let S44 := (S.withEventual h).toSetup44
      (h09SR S.G' S.G'_generates S.G'_compact)
    letI : HasAisleCoproducts S44.tD := by
      change HasAisleCoproducts S.tD
      infer_instance
    letI : HasAisleCoproducts S44.tZ := by
      change HasAisleCoproducts S.tZ
      infer_instance
    exact satisfiesWA_of_aisleCoproducts S44

end SetupMainMinimal

end

end RelativeWeakApprox

#print axioms RelativeWeakApprox.SetupMainMinimal.theorem_1_1_of_aisleCoproducts

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

noncomputable section

/-- Reflect one coproduct, rather than assuming every coproduct of the same
shape in the ambient category. This is the construction inside Mathlib's
`hasColimitsOfShape_of_reflective`, specialized to the displayed family. -/
theorem hasCoproduct_of_reflective.{uC, uD, v} {C : Type uC} {D : Type uD}
    [Category.{v} C] [Category.{v} D] (R : D ⥤ C) [Reflective R]
    {ι : Type v} (X : ι → D) [HasCoproduct (fun i => R.obj (X i))] :
    HasCoproduct X := by
  let e : Discrete.functor X ⋙ R ≅ Discrete.functor (fun i => R.obj (X i)) :=
    Discrete.natIso (fun ⟨i⟩ => Iso.refl (R.obj (X i)))
  letI : HasColimit (Discrete.functor X ⋙ R) := hasColimit_of_iso e
  let c := (monadicLeftAdjoint R).mapCocone (colimit.cocone (Discrete.functor X ⋙ R))
  let : PreservesColimitsOfShape (Discrete ι) _ :=
    (monadicAdjunction R).leftAdjoint_preservesColimits.1
  let t : IsColimit c := isColimitOfPreserves (monadicLeftAdjoint R) (colimit.isColimit _)
  apply HasColimit.mk ⟨_, (IsColimit.precomposeInvEquiv _ _).symm t⟩
  apply (Functor.isoWhiskerLeft (Discrete.functor X) (asIso (monadicAdjunction R).counit) :) ≪≫
    (Discrete.functor X).rightUnitor

universe uZ uD uU v

section ClosedAisle

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- Bounded coproducts on the closed end follow from bounded coproducts in the
middle category. The image under `i_*` of a bounded family is bounded by
Lemma 4.2, and its coproduct is reflected by `i^*`. -/
theorem hasAisleCoproductsClosedOfMiddle
    (R : Recollement DZ D DU) (tD : TStructure D) (tZ : TStructure DZ)
    (tU : TStructure DU) [HasAisleCoproducts tD]
    (hglue : tD.le 0 = gluedLe R.iStar R.jStar tZ tU 0) :
    HasAisleCoproducts tZ where
  hasCoproduct X d hX := by
    letI : HasCoproduct (fun i => R.iLower.obj (X i)) :=
      HasAisleCoproducts.hasCoproduct _ d (fun i =>
        lemma_4_2_iLower R.iStar R.iLower R.jStar tD tZ tU hglue R.iStarAdj
          R.jStar_iLower d (hX i))
    letI : Reflective R.iLower := ⟨_, R.iStarAdj⟩
    exact hasCoproduct_of_reflective R.iLower X

end ClosedAisle

namespace SetupMainMinimal

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- LP Theorem 1.1 with only bounded-above coproduct existence for the middle
`t`-structure. -/
theorem theorem_1_1_of_middleAisleCoproducts (S : SetupMainMinimal DZ D DU)
    [HasAisleCoproducts S.tD]
    (h09SR : ∀ (G : D), IsGenerator G → IsCompactAb G →
      IsClassicalGeneratorOnCompacts G) :
    SatisfiesWA D ↔ ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∀ f : S.G' ⟶ S.G'⟦n⟧, f = 0 := by
  have hglue : S.tD.le 0 = gluedLe S.R.iStar S.R.jStar S.tZ S.tU 0 :=
    lemma_4_3_3 S.R S.tD S.tZ S.tU S.G' S.GU S.m S.jStar_G'_mem
      S.tD_compactlyGenerated S.tZ_compactlyGenerated S.tU_compactlyGenerated
  letI : HasAisleCoproducts S.tZ :=
    hasAisleCoproductsClosedOfMiddle S.R S.tD S.tZ S.tU hglue
  exact S.theorem_1_1_of_aisleCoproducts h09SR

end SetupMainMinimal

end

end RelativeWeakApprox

#print axioms RelativeWeakApprox.hasCoproduct_of_reflective
#print axioms RelativeWeakApprox.hasAisleCoproductsClosedOfMiddle
#print axioms RelativeWeakApprox.SetupMainMinimal.theorem_1_1_of_middleAisleCoproducts

namespace RelativeFM.KProjectiveResolution

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Triangulated
open RelativeWeakApprox

universe vC uCC

noncomputable section

variable {C : Type uCC} [Category.{vC} C] [Abelian C]

/-- The standard derived `t`-structure has all coproducts indexed by the
ambient abelian category's coproduct universe within each fixed aisle. Only
bounded-above K-projective resolutions are used. -/
theorem hasAisleCoproducts_standard [EnoughProjectives C]
    [HasDerivedCategory.{vC} C] [HasCoproducts.{vC} C] :
    HasAisleCoproducts (DerivedCategory.TStructure.t (C := C)) where
  hasCoproduct X d hX := by
    letI : ∀ i, (X i).IsLE d := fun i => ⟨hX i⟩
    choose K hK e using fun i => DerivedCategory.exists_iso_Q_obj_of_isLE (X i) d
    let _ : ∀ i, (K i).IsStrictlyLE d := hK
    let _ : HasCoproduct (fun i => DerivedCategory.Q.obj (K i)) :=
      hasCoproductQObjOfIsStrictlyLE K d
    exact hasCoproduct_of_equiv_of_iso (fun i => DerivedCategory.Q.obj (K i)) X
      (Equiv.refl _) (fun i => (e i).some)

end

end RelativeFM.KProjectiveResolution

#print axioms RelativeFM.KProjectiveResolution.hasAisleCoproducts_standard

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits
open RelativeWeakApprox
open UniverseDecision

noncomputable section

universe uA uZZ uUU

variable (A : Type uA) [CommRing A] (H : AffineSpaltensteinInput A)
  (DZ : Type uZZ) (DU : Type uUU)
  [Category.{uA} DZ] [Category.{uA} DU]
  [Preadditive DZ] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive] [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DU]

/-- LP Theorem 1.1 in the small-localization affine model, with no coproduct
input package at all. The middle `t`-structure is the standard one; its
bounded-aisle coproducts come from bounded-above projective resolutions, and
the closed ones are reflected from the middle category. -/
theorem affine_theorem_1_1_small_noCoproducts
    (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hT : S.tD = @DerivedCategory.TStructure.t (ModuleCat.{uA} A) _ _
      (hasDerivedCategoryOfKProjectiveReplacementData H))
    (h09SR : Stacks09SR (SmallAffineD A H)) :
    SatisfiesWA (SmallAffineD A H) ↔
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∀ f : S.G' ⟶ S.G'⟦n⟧, f = 0 := by
  letI : HasDerivedCategory.{uA} (ModuleCat.{uA} A) :=
    hasDerivedCategoryOfKProjectiveReplacementData H
  letI : HasAisleCoproducts S.tD := by
    rw [hT]
    exact KProjectiveResolution.hasAisleCoproducts_standard (C := ModuleCat.{uA} A)
  exact S.theorem_1_1_of_middleAisleCoproducts h09SR

end

end RelativeFM

#print axioms RelativeFM.affine_theorem_1_1_small_noCoproducts
