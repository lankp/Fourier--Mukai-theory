/-
Copyright (c) 2026 Formalization of Lank--Pauwels--Peng.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Closure
import Mathlib.Tactic

/-!
# Lemma 3.1(3): functoriality of `⟨H⟩^[a,b]`

Lemma 3.1(3) of

  P. Lank, B. Pauwels, F. Peng, *Gluing weak approximability along recollements*:
if `F : T ⥤ T'` is exact, preserves small coproducts and `F(H) ∈ ⟨H'⟩^[c,d]`, then
`F(⟨H⟩^[a,b]) ⊆ ⟨H'⟩^[a+c,b+d]`.

The proof is the paper's: for `Y = H⟦-k⟧` with `a ≤ k ≤ b`, commutation of `F`
with the shift gives `F(H⟦-k⟧) ≅ F(H)⟦-k⟧ ∈ ⟨H'⟩^[c+k,d+k] ⊆ ⟨H'⟩^[a+c,b+d]`;
this is pushed through coproducts, extensions and retracts.

Found by a member of the Ultramath run `smwufzlp4` (direction D3), ported to the
`Coprod`/`envelope` of `WeakApprox/Basic.lean`.
-/

@[expose] public section

namespace RelativeWeakApprox

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Pretriangulated _root_.CategoryTheory.Triangulated

universe v v2 u u2

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u2} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

/-! ### Shifting through the closure -/

/-- Elementwise form of `H[a,b]⟦s⟧ = H[a-s,b-s]`. -/
lemma shiftInterval_shift' {H : C} {a b : ℤ} (s : ℤ) {X : C}
    (hX : shiftInterval H a b X) : shiftInterval H (a - s) (b - s) (X⟦s⟧) := by
  obtain ⟨k, hak, hkb, ⟨e⟩⟩ := hX
  refine ⟨k - s, by omega, by omega, ⟨(shiftFunctor C s).mapIso e ≪≫
    (shiftFunctorAdd' C (-k) s (-(k - s)) (by ring)).symm.app H⟩⟩

/-- If `P` is carried into `Q` after a shift by `s`, then so is `Coprod P`. -/
lemma coprod_shift {P Q : ObjectProperty C} (s : ℤ) (h : ∀ Y, P Y → Q (Y⟦s⟧))
    {X : C} (hX : Coprod P X) : Coprod Q (X⟦s⟧) := by
  induction hX with
  | of_mem X hX => exact .of_mem _ (h X hX)
  | of_isoClosure e _ ih => exact .of_isoClosure ((shiftFunctor C s).mapIso e) ih
  | of_colimitPresentation pres _ ih =>
      exact .of_colimitPresentation (pres.map (shiftFunctor C s)) ih
  | of_extension T hT _ _ ih₁ ih₃ =>
      exact .of_extension _ (T.shift_distinguished hT s) ih₁ ih₃

/-- Same, for the retract closure. -/
lemma retractClosure_shift {P Q : ObjectProperty C} (s : ℤ)
    (h : ∀ Y, P Y → Q (Y⟦s⟧)) {X : C} (hX : (Coprod P).retractClosure X) :
    (Coprod Q).retractClosure (X⟦s⟧) := by
  obtain ⟨Y, hY, ⟨r⟩⟩ := hX
  exact ⟨Y⟦s⟧, coprod_shift s h hY, ⟨r.map (shiftFunctor C s)⟩⟩

/-! ### Coproducts of retracts -/

/-- A coproduct of retracts of members of `Coprod P` lies in the retract closure
of `Coprod P`. -/
lemma coprod_retractClosure {P : ObjectProperty C} {ι : Type v} (f : ι → C)
    [HasCoproducts.{v} C] (hf : ∀ i, (Coprod P).retractClosure (f i)) :
    (Coprod P).retractClosure (∐ f) := by
  choose Y hY hr using hf
  let r : ∀ i, Retract (f i) (Y i) := fun i => Classical.choice (hr i)
  refine ⟨∐ Y, Coprod.of_sigma Y (fun i => hY i), ⟨{
    i := Limits.Sigma.map (fun i => (r i).i)
    r := Limits.Sigma.map (fun i => (r i).r)
    retract := ?_ }⟩⟩
  rw [Limits.Sigma.map_comp_map]
  simpa only [Retract.retract] using (Limits.Sigma.map_id (f := f))

/-- The `Discrete J`-colimit of members of the retract closure lies in it. -/
lemma colimit_retractClosure {P : ObjectProperty C} (J : Type v) [HasCoproducts.{v} C]
    (F : Discrete J ⥤ C) (hF : ∀ j, (Coprod P).retractClosure (F.obj j)) :
    (Coprod P).retractClosure (colimit F) := by
  let f : J → C := fun j => F.obj ⟨j⟩
  have hf : ∀ j, (Coprod P).retractClosure (f j) := fun j => hF ⟨j⟩
  exact (Coprod P).retractClosure.prop_of_iso
    (HasColimit.isoOfNatIso Discrete.natIsoFunctor).symm (coprod_retractClosure f hf)

/-! ### Extensions of retracts -/

/-- An extension of members of the retract closure of `Coprod P` lies in it. -/
lemma extension_retractClosure {P : ObjectProperty C} {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g k ∈ distTriang C)
    (hX : (Coprod P).retractClosure X) (hZ : (Coprod P).retractClosure Z) :
    (Coprod P).retractClosure Y := by
  have h' := ObjectProperty.extensionProduct_retractClosure_retractClosure_le
    (Coprod P) (Coprod P) Y ⟨X, Z, f, g, k, hT, hX, hZ⟩
  obtain ⟨Y', ⟨A, B, f', g', k', hT', hA, hB⟩, r⟩ := h'
  exact ⟨Y', .of_extension _ hT' hA hB, r⟩

/-! ### Exact functors preserve the envelope -/

/-- An exact functor preserving small coproducts carries `Coprod P` into the
retract closure of `Coprod Q` whenever it carries `P` there. -/
lemma map_coprod [HasCoproducts.{v} C] [HasCoproducts.{v} D] (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated]
    [∀ (ι : Type v), PreservesColimitsOfShape (Discrete ι) G]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    (h : ∀ Y, P Y → (Coprod Q).retractClosure (G.obj Y)) {X : C}
    (hX : Coprod P X) : (Coprod Q).retractClosure (G.obj X) := by
  induction hX with
  | of_mem X hX => exact h X hX
  | of_isoClosure e _ ih => exact (Coprod Q).retractClosure.prop_of_iso (G.mapIso e) ih
  | @of_colimitPresentation X J pres hmem ih =>
      have hcol : (Coprod Q).retractClosure (colimit (pres.diag ⋙ G)) :=
        colimit_retractClosure J _ (fun j => ih j)
      refine (Coprod Q).retractClosure.prop_of_iso
        ((colimit.isColimit _).coconePointUniqueUpToIso (isColimitOfPreserves G pres.isColimit)) ?_
      simpa using hcol
  | of_extension T hT _ _ ih₁ ih₃ =>
      exact extension_retractClosure _ _ _ (G.map_distinguished T hT) ih₁ ih₃

/-- Same, for the retract closure. -/
lemma map_retractClosure [HasCoproducts.{v} C] [HasCoproducts.{v} D] (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated]
    [∀ (ι : Type v), PreservesColimitsOfShape (Discrete ι) G]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    (h : ∀ Y, P Y → (Coprod Q).retractClosure (G.obj Y)) {X : C}
    (hX : (Coprod P).retractClosure X) : (Coprod Q).retractClosure (G.obj X) := by
  obtain ⟨Y, hY, ⟨r⟩⟩ := hX
  exact (Coprod Q).retractClosure.prop_of_retract (r.map G) (map_coprod G h hY)

/-- **Lemma 3.1(3).** -/
theorem lemma_3_1_3 [HasCoproducts.{v} C] [HasCoproducts.{v} D] (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated]
    [∀ (ι : Type v), PreservesColimitsOfShape (Discrete ι) G]
    (H : C) (H' : D) (a b c d : ℤ) (hF : envelope H' c d (G.obj H)) {X : C}
    (hX : envelope H a b X) : envelope H' (a + c) (b + d) (G.obj X) := by
  refine map_retractClosure G ?_ hX
  intro Y hY
  obtain ⟨k, hak, hkb, ⟨e⟩⟩ := hY
  have hshift : (Coprod (shiftInterval H' (a + c) (b + d))).retractClosure
      ((G.obj H)⟦-k⟧) := by
    refine retractClosure_shift (-k) ?_ hF
    intro Z hZ
    exact shiftInterval_mono H' (show a + c ≤ c - -k by omega)
      (show d - -k ≤ b + d by omega) _ (shiftInterval_shift' (-k) hZ)
  exact (Coprod (shiftInterval H' (a + c) (b + d))).retractClosure.prop_of_iso
    (G.mapIso e ≪≫ (G.commShiftIso (-k)).app H).symm hshift

end RelativeWeakApprox
