import WeakApprox.Basic
import WeakApprox.PLift
import WeakApprox.Closure
import WeakApprox.Shift
import WeakApprox.Octahedron
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Proposition 4.8: closure of the class of `P`-liftable objects

It uses the `PLift` of `WeakApprox/PLift.lean`: a `P`-lift of
`f' : E' ⟶ iStar.obj Y` consists of `q : E ⟶ Y` with `E ∈ P` and
`θ : iStar.obj E ≅ E'` such that `iStar.map q = θ.hom ≫ f'`.

Found by a member of the Ultramath run `smwunmkmj` (direction D4).

The theorem `proposition_4_8` takes Lemma 4.6 as the explicit hypothesis
`hlemma46`.  The small coproducts are indexed by the hom universe of `DZ`;
`iStar` is assumed to preserve them and `P` to be closed under them.  The
extension theorem is stated for an arbitrary target class `K`, with the
closure and positive-shift properties of an aisle as explicit hypotheses.
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe w vZ uZ vD uD

noncomputable section

/-- Sources every map from which, to `i^*` of an object of `K`, has a `P`-lift. -/
def liftableClass {DZ : Type uZ} {D : Type uD} [Category.{vZ} DZ] [Category.{vD} D]
    (iStar : D ⥤ DZ) (P : ObjectProperty D) (K : ObjectProperty D) : ObjectProperty DZ :=
  fun E' => ∀ {Y : D}, K Y → ∀ f' : E' ⟶ iStar.obj Y, Nonempty (PLift iStar P f')

section BasicClosure

variable {DZ : Type uZ} {D : Type uD} [Category.{vZ} DZ] [Category.{vD} D]
  (iStar : D ⥤ DZ) (P : ObjectProperty D) (K : ObjectProperty D)

/-- Proposition 4.8: the liftable class is strictly full. -/
theorem liftableClass_strictFull :
    (liftableClass iStar P K).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    intro Y hY f'
    obtain ⟨L⟩ := hE hY (e.hom ≫ f')
    refine ⟨{ source := L.source
              source_mem := L.source_mem
              q := L.q
              θ := L.θ.trans e
              comm := ?_ }⟩
    rw [L.comm]
    simp only [Iso.trans_hom, Category.assoc]

/-- Coproducts of lifts assemble into a lift of the coproduct map. -/
theorem liftableClass_of_sigma [HasZeroObject DZ] [HasZeroObject D]
    [HasShift DZ ℤ] [HasShift D ℤ] [Preadditive DZ] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor DZ n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [Pretriangulated DZ] [Pretriangulated D]
    [HasCoproducts.{w} DZ] [HasCoproducts.{w} D]
    [∀ (J : Type w), PreservesColimitsOfShape (Discrete J) iStar]
    [∀ (J : Type w), P.IsClosedUnderColimitsOfShape (Discrete J)]
    {ι : Type w} (E' : ι → DZ)
    (hE : ∀ j, liftableClass iStar P K (E' j)) :
    liftableClass iStar P K (∐ E') := by
  intro Y hY f'
  let L (j : ι) : PLift iStar P (Sigma.ι E' j ≫ f') := (hE j hY _).some
  let E : ι → D := fun j => (L j).source
  let q : (∐ E) ⟶ Y := Sigma.desc fun j => (L j).q
  let θ : iStar.obj (∐ E) ≅ ∐ E' :=
    PreservesCoproduct.iso iStar E ≪≫ Sigma.mapIso (fun j => (L j).θ)
  have hP : P (∐ E) := P.prop_colimit (Discrete.functor E) (fun j => (L j.as).source_mem)
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
  simp only [← Category.assoc, hpreserved, Sigma.ι_mapIso_hom]

/-- The liftable class has the coproduct closure required by `Coprod.le`. -/
theorem liftableClass_coproducts [HasZeroObject DZ] [HasZeroObject D]
    [HasShift DZ ℤ] [HasShift D ℤ] [Preadditive DZ] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor DZ n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [Pretriangulated DZ] [Pretriangulated D]
    [HasCoproducts.{w} DZ] [HasCoproducts.{w} D]
    [∀ (J : Type w), PreservesColimitsOfShape (Discrete J) iStar]
    [∀ (J : Type w), P.IsClosedUnderColimitsOfShape (Discrete J)]
    (J : Type w) :
    (liftableClass iStar P K).IsClosedUnderColimitsOfShape (Discrete J) := by
  letI := liftableClass_strictFull iStar P K
  constructor
  rintro X ⟨hX⟩
  letI := hX.hasColimit
  have h : liftableClass iStar P K (∐ fun j : J => hX.diag.obj ⟨j⟩) :=
    liftableClass_of_sigma iStar P K (fun j : J => hX.diag.obj ⟨j⟩)
      (fun j => hX.prop_diag_obj ⟨j⟩)
  let e₁ : (∐ fun j : J => hX.diag.obj ⟨j⟩) ≅ colimit hX.diag :=
    (HasColimit.isoOfNatIso (F := hX.diag) Discrete.natIsoFunctor).symm
  let e₂ : colimit hX.diag ≅ X :=
    (hX.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)).symm
  intro Y hY f'
  obtain ⟨L⟩ := h hY ((e₁.trans e₂).hom ≫ f')
  refine ⟨{ source := L.source
            source_mem := L.source_mem
            q := L.q
            θ := L.θ.trans (e₁.trans e₂)
            comm := ?_ }⟩
  rw [L.comm]
  simp only [Iso.trans_hom, Category.assoc]

end BasicClosure

section TriangleHelpers

variable {C : Type uD} [Category.{vD} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Transport a distinguished triangle across isomorphisms of its first two
objects, keeping its third object and its second morphism fixed. -/
theorem exists_distinguished_triangle_same_mor₂ (T : Triangle C) (hT : T ∈ distTriang C)
    {X : C} (e : T.obj₁ ≅ X) (f : X ⟶ T.obj₂) (comm : T.mor₁ = e.hom ≫ f) :
    ∃ w : T.obj₃ ⟶ X⟦(1 : ℤ)⟧, Triangle.mk f T.mor₂ w ∈ distTriang C := by
  obtain ⟨Z, g, h, hT₀⟩ := distinguished_cocone_triangle f
  let φ := completeDistinguishedTriangleMorphism T (Triangle.mk f g h) hT hT₀
    e.hom (𝟙 T.obj₂) (by
      change T.mor₁ ≫ 𝟙 T.obj₂ = e.hom ≫ f
      rw [Category.comp_id, comm])
  haveI : IsIso φ.hom₁ := by change IsIso e.hom; infer_instance
  haveI : IsIso φ.hom₂ := by change IsIso (𝟙 T.obj₂); infer_instance
  haveI : IsIso φ.hom₃ := by
    apply isIso₃_of_isIso₁₂ φ hT hT₀
    · change IsIso e.hom; infer_instance
    · change IsIso (𝟙 T.obj₂); infer_instance
  let e₃' := asIso φ.hom₃
  let e₃ : T.obj₃ ≅ Z := e₃'
  have heq : T.mor₂ ≫ e₃.hom = g := by
    change T.mor₂ ≫ φ.hom₃ = g
    rw [φ.comm₂]
    change (𝟙 T.obj₂) ≫ g = g
    simp
  have hcomm₂ : g ≫ e₃.inv = T.mor₂ := by
    rw [← heq, Category.assoc, e₃.hom_inv_id, Category.comp_id]
  have hcomm₃ : h ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 X) =
      e₃.inv ≫ (e₃.hom ≫ h) := by
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← Category.assoc, e₃.inv_hom_id, Category.id_comp]
  refine ⟨e₃.hom ≫ h, ?_⟩
  exact isomorphic_distinguished (Triangle.mk f g h) hT₀ _
    (Triangle.isoMk (Triangle.mk f g h) (Triangle.mk f T.mor₂ (e₃.hom ≫ h))
      (Iso.refl _) (Iso.refl _) e₃.symm
      (by change f ≫ 𝟙 T.obj₂ = 𝟙 X ≫ f; simp)
      (by change g ≫ e₃.inv = 𝟙 T.obj₂ ≫ T.mor₂; rw [Category.id_comp]; exact hcomm₂)
      (by exact hcomm₃)).symm

end TriangleHelpers

section ExtensionClosure

variable {DZ : Type uZ} {D : Type uD} [Category.{vZ} DZ] [Category.{vD} D]
  [HasZeroObject DZ] [HasZeroObject D] [HasShift DZ ℤ] [HasShift D ℤ]
  [Preadditive DZ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [IsTriangulated DZ] [IsTriangulated D]
  (iStar : D ⥤ DZ) [iStar.CommShift ℤ] [iStar.IsTriangulated]
  (P K : ObjectProperty D)

/-- Proposition 4.8, extension closure.  The hypotheses `hPK` and `hKshift`
are the relevant properties of the aisle `tD.le K`; `P` is the extension-closed
class from Setup 4.4. -/
theorem liftableClass_extensions [P.IsClosedUnderIsomorphisms]
    [K.IsClosedUnderIsomorphisms] [P.IsTriangulatedClosed₂]
    [K.IsTriangulatedClosed₂] (hPK : P ≤ K)
    (hKshift : ∀ {X : D}, K X → K (X⟦(1 : ℤ)⟧)) :
    (liftableClass iStar P K).IsTriangulatedClosed₂ := by
  letI := liftableClass_strictFull iStar P K
  apply ObjectProperty.IsTriangulatedClosed₂.mk'
  intro T hT hE₁ hE₂
  change Triangle.mk T.mor₁ T.mor₂ T.mor₃ ∈ distTriang DZ at hT
  intro Y hY f'
  obtain ⟨L₁⟩ := hE₁ hY (T.mor₁ ≫ f')
  obtain ⟨Y₁, r₁, s₁, hT₁⟩ := distinguished_cocone_triangle L₁.q
  let T₁ : Triangle D := Triangle.mk L₁.q r₁ s₁
  change T₁ ∈ distTriang D at hT₁
  have hY₁ : K Y₁ := K.ext_of_isTriangulatedClosed₂ T₁.rotate
    (rot_of_distTriang _ hT₁) hY (hKshift (hPK _ L₁.source_mem))
  obtain ⟨w₁, hB₁⟩ := exists_distinguished_triangle_same_mor₂
    (iStar.mapTriangle.obj T₁) (iStar.map_distinguished _ hT₁)
    L₁.θ (T.mor₁ ≫ f') L₁.comm
  change iStar.obj Y₁ ⟶ T.obj₁⟦(1 : ℤ)⟧ at w₁
  change Triangle.mk (T.mor₁ ≫ f') (iStar.map r₁) w₁ ∈ distTriang DZ at hB₁
  obtain ⟨R, p', z', hTR⟩ := distinguished_cocone_triangle f'
  let o := Triangulated.someOctahedron (rfl : T.mor₁ ≫ f' = T.mor₁ ≫ f')
    hT hTR hB₁
  obtain ⟨L₂⟩ := hE₂ hY₁ o.m₁
  obtain ⟨Y₂, r₂, s₂, hT₂⟩ := distinguished_cocone_triangle L₂.q
  let T₂ : Triangle D := Triangle.mk L₂.q r₂ s₂
  change T₂ ∈ distTriang D at hT₂
  let χφ := completeDistinguishedTriangleMorphism (iStar.mapTriangle.obj T₂) o.triangle
    (iStar.map_distinguished _ hT₂) o.mem L₂.θ.hom (𝟙 _) (by
      change iStar.map L₂.q ≫ 𝟙 _ = L₂.θ.hom ≫ o.m₁
      rw [Category.comp_id, L₂.comm])
  haveI : IsIso χφ.hom₁ := by change IsIso L₂.θ.hom; infer_instance
  haveI : IsIso χφ.hom₂ := by change IsIso (𝟙 (iStar.obj Y₁)); infer_instance
  haveI : IsIso χφ.hom₃ := by
    apply isIso₃_of_isIso₁₂ χφ (iStar.map_distinguished _ hT₂) o.mem
    · change IsIso L₂.θ.hom; infer_instance
    · change IsIso (𝟙 (iStar.obj Y₁)); infer_instance
  let χ := χφ.hom₃
  change iStar.obj Y₂ ⟶ R at χ
  haveI : IsIso χ := by change IsIso χφ.hom₃; infer_instance
  have hχ : iStar.map r₂ ≫ χ = o.m₃ := by
    have eq := χφ.comm₂
    change iStar.map r₂ ≫ χ = (𝟙 (iStar.obj Y₁)) ≫ o.m₃ at eq
    exact eq.trans (Category.id_comp _)
  have ho : iStar.map r₁ ≫ o.m₃ = p' := by
    exact o.comm₃
  have hχr : iStar.map (r₁ ≫ r₂) ≫ χ = p' := by
    have h₁ : iStar.map (r₁ ≫ r₂) ≫ χ = (iStar.map r₁ ≫ iStar.map r₂) ≫ χ := by
      rw [iStar.map_comp]
    have h₂ : (iStar.map r₁ ≫ iStar.map r₂) ≫ χ = iStar.map r₁ ≫ o.m₃ := by
      rw [Category.assoc, hχ]
    exact h₁.trans (h₂.trans ho)
  obtain ⟨E, q, t, hTq⟩ := distinguished_cocone_triangle₁ (r₁ ≫ r₂)
  let Tq : Triangle D := Triangle.mk q (r₁ ≫ r₂) t
  change Tq ∈ distTriang D at hTq
  obtain ⟨u, v, huv⟩ := remark_3_2_2 r₁ r₂ L₁.q s₁ L₂.q s₂ q t hT₁ hT₂ hTq
  have hPE : P E := P.ext_of_isTriangulatedClosed₂ (Triangle.mk u v (L₂.q ≫ s₁))
    huv L₁.source_mem L₂.source_mem
  have hmid : (iStar.mapTriangle.obj Tq).mor₂ ≫ χ = (𝟙 (iStar.obj Y)) ≫ p' := by
    change iStar.map (r₁ ≫ r₂) ≫ χ = (𝟙 (iStar.obj Y)) ≫ p'
    exact hχr.trans (Category.id_comp _).symm
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁
    (iStar.mapTriangle.obj Tq) (Triangle.mk f' p' z')
    (iStar.map_distinguished _ hTq) hTR (𝟙 (iStar.obj Y)) χ hmid
  let φ : iStar.mapTriangle.obj Tq ⟶ Triangle.mk f' p' z' :=
    Triangle.homMk _ _ a (𝟙 (iStar.obj Y)) χ ha₁ hmid ha₃
  haveI : IsIso φ.hom₁ := by
    apply isIso₁_of_isIso₂₃ φ (iStar.map_distinguished _ hTq) hTR
    · change IsIso (𝟙 (iStar.obj Y)); infer_instance
    · change IsIso χ; infer_instance
  haveI : IsIso a := by change IsIso φ.hom₁; infer_instance
  let θ' := asIso a
  let θ : iStar.obj E ≅ T.obj₂ := θ'
  refine ⟨{ source := E
            source_mem := hPE
            q := q
            θ := θ
            comm := ?_ }⟩
  change iStar.map q = a ≫ f'
  have ha₁' : iStar.map q ≫ (𝟙 (iStar.obj Y)) = a ≫ f' := ha₁
  simpa using ha₁'

end ExtensionClosure

section Lemma315

variable {C : Type uD} [Category.{vD} C]

section Swindle

variable [HasZeroObject C] [Preadditive C] [HasBinaryBiproducts C]

/-- Forward map in the `ULift ℕ`-indexed Eilenberg swindle. -/
noncomputable def swindleHom (X X' : C)
    [HasCoproduct (fun _ : ULift.{vD} ℕ => X ⊞ X')] :
    X ⊞ (∐ fun _ : ULift.{vD} ℕ => X ⊞ X') ⟶ (∐ fun _ : ULift.{vD} ℕ => X ⊞ X') :=
  biprod.desc
    (biprod.inl ≫ Sigma.ι (fun _ : ULift.{vD} ℕ => X ⊞ X') (ULift.up 0))
    (Sigma.desc fun n => biprod.desc
      (biprod.inl ≫ Sigma.ι (fun _ : ULift.{vD} ℕ => X ⊞ X') (ULift.up (n.down + 1)))
      (biprod.inr ≫ Sigma.ι (fun _ : ULift.{vD} ℕ => X ⊞ X') n))

/-- Inverse map in the `ULift ℕ`-indexed Eilenberg swindle. -/
noncomputable def swindleInv (X X' : C)
    [HasCoproduct (fun _ : ULift.{vD} ℕ => X ⊞ X')] :
    (∐ fun _ : ULift.{vD} ℕ => X ⊞ X') ⟶ X ⊞ (∐ fun _ : ULift.{vD} ℕ => X ⊞ X') :=
  Sigma.desc fun n => biprod.desc
    (Nat.casesOn n.down biprod.inl (fun k =>
      biprod.inl ≫ Sigma.ι (fun _ : ULift.{vD} ℕ => X ⊞ X') (ULift.up k) ≫ biprod.inr))
    (biprod.inr ≫ Sigma.ι (fun _ : ULift.{vD} ℕ => X ⊞ X') n ≫ biprod.inr)

lemma swindleHom_swindleInv (X X' : C)
    [HasCoproduct (fun _ : ULift.{vD} ℕ => X ⊞ X')] :
    swindleHom X X' ≫ swindleInv X X' = 𝟙 _ := by
  apply biprod.hom_ext'
  · simp [swindleHom, swindleInv]
  · apply Sigma.hom_ext
    rintro ⟨n⟩
    apply biprod.hom_ext'
    · cases n with
      | zero => simp [swindleHom, swindleInv]
      | succ n => simp [swindleHom, swindleInv]
    · simp [swindleHom, swindleInv]

lemma swindleInv_swindleHom (X X' : C)
    [HasCoproduct (fun _ : ULift.{vD} ℕ => X ⊞ X')] :
    swindleInv X X' ≫ swindleHom X X' = 𝟙 _ := by
  apply Sigma.hom_ext
  rintro ⟨n⟩
  apply biprod.hom_ext'
  · cases n with
    | zero => simp [swindleHom, swindleInv]
    | succ n => simp [swindleHom, swindleInv]
  · simp [swindleHom, swindleInv]

/-- The countable-coproduct form of the Eilenberg swindle for a binary
biproduct `X ⊞ X'`, indexed in the category's hom universe. -/
noncomputable def swindleIso (X X' : C)
    [HasCoproduct (fun _ : ULift.{vD} ℕ => X ⊞ X')] :
    X ⊞ (∐ fun _ : ULift.{vD} ℕ => X ⊞ X') ≅ (∐ fun _ : ULift.{vD} ℕ => X ⊞ X') where
  hom := swindleHom X X'
  inv := swindleInv X X'
  hom_inv_id := swindleHom_swindleInv X X'
  inv_hom_id := swindleInv_swindleHom X X'

end Swindle

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A retract has a biproduct complement in a pretriangulated category. -/
lemma retract_exists_biprod_complement {X Y : C} (r : Retract X Y) :
    ∃ (X' : C), Nonempty (Y ≅ X ⊞ X') := by
  obtain ⟨X', f, g, hT⟩ := distinguished_cocone_triangle r.i
  let T := Triangle.mk r.i f g
  change T ∈ distTriang C at hT
  letI : IsSplitMono r.i := IsSplitMono.mk' { retraction := r.r, id := r.retract }
  haveI : Mono r.i := inferInstance
  have hzero : T.mor₃ = 0 := T.mor₃_eq_zero_of_mono₁ hT
    (show Mono r.i from inferInstance)
  obtain ⟨e, _⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hzero
  exact ⟨X', ⟨e⟩⟩

/-- **Lemma 3.1(5)** for the official `Coprod`: every direct summand of an
object of `Coprod(H[a,b])` belongs to `Coprod(H[a,b+1])`.  The swindle is
indexed by `ULift ℕ : Type v`, so it uses exactly the small coproducts in the
definition of `Coprod`. -/
theorem lemma_3_1_5 [HasCoproducts.{vD} C] (H : C) (a b : ℤ) :
    envelope H a b ≤ Coprod (shiftInterval H a (b + 1)) := by
  rintro X ⟨Y, hY, ⟨r⟩⟩
  obtain ⟨X', ⟨e⟩⟩ := retract_exists_biprod_complement r
  have hY' : Coprod (shiftInterval H a b) (X ⊞ X') := .of_isoClosure e hY
  let Z : C := ∐ fun _ : ULift.{vD} ℕ => X ⊞ X'
  have hZ : Coprod (shiftInterval H a b) Z :=
    Coprod.of_sigma (fun _ : ULift.{vD} ℕ => X ⊞ X') (fun _ => hY')
  have hZ_target : Coprod (shiftInterval H a (b + 1)) Z :=
    Coprod_mono (shiftInterval_mono H le_rfl (by omega)) Z hZ
  have hZ_shifted₀ : Coprod (shiftInterval H (a + 1) (b + 1)) (Z⟦(-1 : ℤ)⟧) := by
    have h := map_shift_Coprod (shiftInterval H a b) (-1 : ℤ) hZ
    rw [shiftImage_shiftInterval] at h
    simpa only [sub_neg_eq_add, zero_add] using h
  have hZ_shifted : Coprod (shiftInterval H a (b + 1)) (Z⟦(-1 : ℤ)⟧) :=
    Coprod_mono (shiftInterval_mono H (by omega) (by omega)) _ hZ_shifted₀
  let eZ : X ⊞ Z ≅ Z := swindleIso X X'
  have eT : binaryBiproductTriangle X Z ≅
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

end Lemma315

section Proposition48

variable {DZ : Type uZ} {D : Type uD} [Category.{vZ} DZ] [Category.{vD} D]
  [HasZeroObject DZ] [HasZeroObject D] [HasShift DZ ℤ] [HasShift D ℤ]
  [Preadditive DZ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [IsTriangulated DZ] [IsTriangulated D]
  (iStar : D ⥤ DZ) [iStar.CommShift ℤ] [iStar.IsTriangulated]
  (P K : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
  [K.IsClosedUnderIsomorphisms] [P.IsTriangulatedClosed₂]
  [K.IsTriangulatedClosed₂]
  [HasCoproducts.{vZ} DZ] [HasCoproducts.{vZ} D]
  [∀ (J : Type vZ), PreservesColimitsOfShape (Discrete J) iStar]
  [∀ (J : Type vZ), P.IsClosedUnderColimitsOfShape (Discrete J)]

/-- The `Coprod` inclusion in Proposition 4.8.  The argument `hlemma46` is
exactly the conclusion of Lemma 4.6 for the shifts in `[-A-1,A]`. -/
theorem coprod_shiftInterval_le_liftableClass (G : D) (A : ℤ)
    (hPK : P ≤ K) (hKshift : ∀ {X : D}, K X → K (X⟦(1 : ℤ)⟧))
    (hlemma46 : ∀ n : ℤ, -A - 1 ≤ n → n ≤ A →
      liftableClass iStar P K ((iStar.obj G)⟦n⟧)) :
    Coprod (shiftInterval (iStar.obj G) (-A) (A + 1)) ≤ liftableClass iStar P K := by
  letI : (liftableClass iStar P K).IsClosedUnderIsomorphisms :=
    liftableClass_strictFull iStar P K
  letI : (liftableClass iStar P K).IsTriangulatedClosed₂ :=
    liftableClass_extensions iStar P K hPK hKshift
  letI (J : Type vZ) : (liftableClass iStar P K).IsClosedUnderColimitsOfShape (Discrete J) :=
    liftableClass_coproducts iStar P K J
  apply Coprod.le
  intro X hX
  obtain ⟨k, hk_lower, hk_upper, ⟨e⟩⟩ := hX
  have h : liftableClass iStar P K ((iStar.obj G)⟦-k⟧) :=
    hlemma46 (-k) (by omega) (by omega)
  intro Y hY f'
  obtain ⟨L⟩ := h hY (e.inv ≫ f')
  refine ⟨{ source := L.source
            source_mem := L.source_mem
            q := L.q
            θ := L.θ.trans e.symm
            comm := ?_ }⟩
  rw [L.comm]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]

/-- **Proposition 4.8**.  The class of objects admitting `P`-lifts is strictly
full, closed under small coproducts and extensions, contains the shifts handled
by Lemma 4.6, and satisfies the two displayed inclusions.  The target aisle is
represented by `K` together with `hPK` and `hKshift`; small coproducts are
indexed by `Type vZ`, the hom universe of `DZ`. -/
theorem proposition_4_8 (G : D) (A : ℤ)
    (hPK : P ≤ K) (hKshift : ∀ {X : D}, K X → K (X⟦(1 : ℤ)⟧))
    (hlemma46 : ∀ n : ℤ, -A - 1 ≤ n → n ≤ A →
      liftableClass iStar P K ((iStar.obj G)⟦n⟧)) :
    (liftableClass iStar P K).IsClosedUnderIsomorphisms ∧
    (∀ J : Type vZ, (liftableClass iStar P K).IsClosedUnderColimitsOfShape (Discrete J)) ∧
    (liftableClass iStar P K).IsTriangulatedClosed₂ ∧
    (∀ n : ℤ, -A - 1 ≤ n → n ≤ A → liftableClass iStar P K ((iStar.obj G)⟦n⟧)) ∧
    envelope (iStar.obj G) (-A) A ≤ Coprod (shiftInterval (iStar.obj G) (-A) (A + 1)) ∧
    Coprod (shiftInterval (iStar.obj G) (-A) (A + 1)) ≤ liftableClass iStar P K := by
  exact ⟨liftableClass_strictFull iStar P K,
    liftableClass_coproducts iStar P K,
    liftableClass_extensions iStar P K hPK hKshift,
    hlemma46,
    lemma_3_1_5 (iStar.obj G) (-A) A,
    coprod_shiftInterval_le_liftableClass iStar P K G A hPK hKshift hlemma46⟩

end Proposition48

end
end RelativeWeakApprox
