/-
Copyright (c) 2026 Formalization of Lank--Pauwels--Peng.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Lemma 3.1(1): `⟨H⟩^[a,b]` and its closure properties

Lemma 3.1(1) of

  P. Lank, B. Pauwels, F. Peng, *Gluing weak approximability along recollements*:
`⟨H⟩^[a,b] = smd(Coprod(H[a,b]))` is the smallest strictly full subcategory of `T`
containing `H[a,b]` and closed under small coproducts, extensions and direct
summands.

Two pieces of Mathlib infrastructure are proved here on the way, and are reusable
independently of the paper:

* the retract closure of a class closed under `Discrete J`-colimits is closed under
  them (`ObjectProperty.retractClosure.IsClosedUnderColimitsOfShape`);
* the retract closure of a class closed under extensions is closed under
  extensions (`ObjectProperty.retractClosure_isTriangulatedClosed₂`).

Found by a member of the Ultramath run `smwufzlp4` (direction D1); the generic
lemmas are kept verbatim and the six items of the lemma are restated for the
official `envelope` of `WeakApprox/Basic.lean`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- The coproduct of a family of retracts of objects satisfying `P` is a
retract of the coproduct of those objects. -/
lemma prop_coproduct_retractClosure (P : ObjectProperty C) {J : Type w}
    (F : J → C) [HasCoproduct F] [HasCoproducts.{w} C]
    [P.IsClosedUnderColimitsOfShape (Discrete J)]
    (hF : ∀ j, P.retractClosure (F j)) : P.retractClosure (∐ F) := by
  choose G hG hr using hF
  let r (j : J) : Retract (F j) (G j) := (hr j).some
  let i : (∐ F) ⟶ (∐ G) := Sigma.desc fun j => (r j).i ≫ Sigma.ι G j
  let s : (∐ G) ⟶ (∐ F) := Sigma.desc fun j => (r j).r ≫ Sigma.ι F j
  refine ⟨∐ G, P.prop_colimit (Discrete.functor G) (fun j => hG j.as), ⟨i, s, ?_⟩⟩
  apply Sigma.hom_ext
  intro j
  simp [i, s, Category.assoc]

/-- Retract closure preserves closure under coproducts indexed by `Discrete J`. -/
lemma prop_colimit_retractClosure (P : ObjectProperty C) {J : Type w}
    [HasCoproducts.{w} C] (F : Discrete J ⥤ C) [HasColimit F]
    [P.IsClosedUnderColimitsOfShape (Discrete J)]
    (hF : ∀ j, P.retractClosure (F.obj j)) : P.retractClosure (colimit F) := by
  let f : J → C := fun j => F.obj ⟨j⟩
  have hf : ∀ j, P.retractClosure (f j) := fun j => hF ⟨j⟩
  exact P.retractClosure.prop_of_iso (HasColimit.isoOfNatIso Discrete.natIsoFunctor).symm
    (prop_coproduct_retractClosure P f hf)

instance (P : ObjectProperty C) (J : Type w) [HasCoproducts.{w} C]
    [P.IsClosedUnderColimitsOfShape (Discrete J)] :
    P.retractClosure.IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := by
    rintro X ⟨hX⟩
    letI := hX.hasColimit
    exact P.retractClosure.prop_of_iso
      ((colimit.isColimit hX.diag).coconePointUniqueUpToIso hX.isColimit)
      (prop_colimit_retractClosure P hX.diag hX.prop_diag_obj)

end CategoryTheory.ObjectProperty

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

variable {C : Type u} [Category.{v} C]


section RetractClosure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Retract closure preserves closure under extensions in a pretriangulated category. -/
instance retractClosure_isTriangulatedClosed₂ (P : ObjectProperty C)
    [P.IsTriangulatedClosed₂] [P.IsClosedUnderIsomorphisms] :
    P.retractClosure.IsTriangulatedClosed₂ := by
  apply ObjectProperty.IsTriangulatedClosed₂.mk'
  intro T hT h₁ h₃
  have hE : ObjectProperty.extensionProduct P.retractClosure P.retractClosure T.obj₂ :=
    ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃, hT, h₁, h₃⟩
  have hR : (ObjectProperty.extensionProduct P P).retractClosure T.obj₂ :=
    ObjectProperty.extensionProduct_retractClosure_retractClosure_le P P T.obj₂ hE
  have hPP : ObjectProperty.extensionProduct P P ≤ P :=
    ObjectProperty.extensionProduct_le_of_isTriangulatedClosed₂ (le_refl P) (le_refl P)
  exact ObjectProperty.monotone_retractClosure hPP T.obj₂ hR

end RetractClosure

section Envelope

variable [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

variable (H : C) (a b : ℤ)

/-- **Lemma 3.1(1)**, coproduct part. -/
theorem lemma_3_1_1_coproducts [HasCoproducts.{v} C] (J : Type v) :
    (envelope H a b).IsClosedUnderColimitsOfShape (Discrete J) := by
  unfold envelope
  infer_instance

/-- **Lemma 3.1(1)**, extension part. -/
theorem lemma_3_1_1_extensions : (envelope H a b).IsTriangulatedClosed₂ := by
  unfold envelope
  infer_instance

/-- **Lemma 3.1(1)**, direct-summand part. -/
theorem lemma_3_1_1_summands : (envelope H a b).IsStableUnderRetracts := by
  unfold envelope
  infer_instance

/-- **Lemma 3.1(1)**: the envelope is strictly full. -/
theorem lemma_3_1_1_strictlyFull : (envelope H a b).IsClosedUnderIsomorphisms := by
  unfold envelope
  infer_instance

/-- **Lemma 3.1(1)**: the envelope contains `H[a,b]`. -/
theorem lemma_3_1_1_contains : shiftInterval H a b ≤ envelope H a b := fun X hX =>
  ObjectProperty.le_retractClosure _ X (Coprod.of_mem X hX)

/-- **Lemma 3.1(1)**, minimality. -/
theorem lemma_3_1_1_minimal {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    [∀ (J : Type v), Q.IsClosedUnderColimitsOfShape (Discrete J)]
    [Q.IsTriangulatedClosed₂] [Q.IsStableUnderRetracts]
    (hQ : shiftInterval H a b ≤ Q) : envelope H a b ≤ Q := by
  rw [envelope, ObjectProperty.retractClosure_le_iff]
  exact Coprod.le hQ

end Envelope

end RelativeWeakApprox
