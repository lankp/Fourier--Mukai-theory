/-
Coproduct hypotheses localized to fixed aisles.

Candidate module: WeakApprox/AisleCoproducts.lean,
after WeakApprox.Proposition48 and WeakApprox.CompactVanishing.
-/
import WeakApprox.Proposition48
import WeakApprox.Setup44
import WeakApprox.CompactVanishing
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

end

end RelativeWeakApprox

#print axioms RelativeWeakApprox.hasCoproduct_of_reflective
#print axioms RelativeWeakApprox.hasAisleCoproductsClosedOfMiddle

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

