/-
Copyright (c) 2026 Formalization of Lank--Pauwels--Peng.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Generator.Basic

/-!
# Basic definitions for *Gluing weak approximability along recollements*

This file holds the definitions of §2.1.2 and §2.1.5 of

  P. Lank, B. Pauwels, F. Peng, *Gluing weak approximability along recollements*.

The development lives in its own tree (`WeakApprox/`) so that it can be moved,
unchanged, into a repository of its own.  See `results/WEAK_APPROX.md` for the
module plan, what Mathlib provides, and what is missing.

## Main definitions

* `RelativeWeakApprox.shiftInterval`: the class `H[a,b]` of §2.1.2.
* `RelativeWeakApprox.Coprod`: closure under small coproducts and extensions,
  with universal property `Coprod.le`.
* `RelativeWeakApprox.envelope`: `⟨H⟩^[a,b] = smd(Coprod(H[a,b]))`.
* `RelativeWeakApprox.IsCoproductCompact`, `IsGenerator`: the two halves of
  "compact generator".
* `RelativeWeakApprox.WeakApproximationData`: Definition 2.1.

## Renderings (documented, not weakenings)

* `Coprod P` is the inductive closure: it contains `P`, is closed under
  isomorphisms, under colimits over `Discrete J` for `J : Type v` (i.e. small
  coproducts) and under extensions along distinguished triangles.  `Coprod.le`
  proves that it is contained in any class with these closure properties.
* `IsCoproductCompact H` says that `Hom(H, -)` preserves `Type v`-small
  coproducts, i.e. that `H` is compact.
* `IsGenerator G` says that the shifts of `G` separate morphisms.  See
  `results/WEAK_APPROX.md` for the (still missing) bridge to the paper's
  formulation "`Hom(G[n], E) = 0` for all `n` implies `E ≅ 0`".
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The class `H[a,b]` of the paper, §2.1.2: objects isomorphic to `H⟦-k⟧` for
some integer `k` with `a ≤ k ≤ b`. -/
def shiftInterval (H : C) (a b : ℤ) : ObjectProperty C := fun X =>
  ∃ k : ℤ, a ≤ k ∧ k ≤ b ∧ Nonempty (X ≅ H⟦-k⟧)

lemma mem_shiftInterval {H X : C} {a b : ℤ} :
    shiftInterval H a b X ↔ ∃ k : ℤ, a ≤ k ∧ k ≤ b ∧ Nonempty (X ≅ H⟦-k⟧) :=
  Iff.rfl

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] in
/-- `H` itself lies in `H[a,b]` as soon as `0 ∈ [a,b]`. -/
lemma shiftInterval_self (H : C) {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    shiftInterval H a b H := by
  refine ⟨0, ha, hb, ?_⟩
  rw [neg_zero]
  exact ⟨(shiftFunctorZero C ℤ).symm.app H⟩

/-- Monotonicity of `H[a,b]` in the interval. -/
lemma shiftInterval_mono (H : C) {a a' b b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') :
    shiftInterval H a b ≤ shiftInterval H a' b' := by
  rintro X ⟨k, h₁, h₂, h₃⟩
  exact ⟨k, ha.trans h₁, h₂.trans hb, h₃⟩

/-- The smallest strictly full object property containing `P` and closed under
small coproducts and extensions.  Coproducts are represented by colimit
presentations over `Discrete J` for `J : Type v`. -/
inductive Coprod (P : ObjectProperty C) : ObjectProperty C where
  | of_mem (X : C) (hX : P X) : Coprod P X
  | of_isoClosure {X Y : C} (e : X ≅ Y) (hX : Coprod P X) : Coprod P Y
  | of_colimitPresentation {X : C} {J : Type v} (pres : ColimitPresentation (Discrete J) X)
      (h : ∀ j, Coprod P (pres.diag.obj j)) : Coprod P X
  | of_extension (T : Triangle C) (hT : T ∈ distTriang C)
      (h₁ : Coprod P T.obj₁) (h₃ : Coprod P T.obj₃) : Coprod P T.obj₂

namespace Coprod

variable {P : ObjectProperty C}

instance : (Coprod P).IsClosedUnderIsomorphisms where
  of_iso e hX := .of_isoClosure e hX

instance (J : Type v) : (Coprod P).IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := by
    rintro X ⟨hX⟩
    exact .of_colimitPresentation (J := J) hX.toColimitPresentation hX.prop_diag_obj

instance : (Coprod P).IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := (Coprod P).le_isoClosure _ (.of_extension T hT h₁ h₃)

lemma le_coprod : P ≤ Coprod P := fun X hX => .of_mem X hX

/-- Monotonicity of the coproduct/extension closure. -/
lemma monotone {P Q : ObjectProperty C} (h : P ≤ Q) : Coprod P ≤ Coprod Q := by
  intro X hX
  induction hX with
  | of_mem X hX => exact .of_mem X (h X hX)
  | of_isoClosure e _ ih => exact .of_isoClosure e ih
  | of_colimitPresentation pres _ ih => exact .of_colimitPresentation pres ih
  | of_extension T hT _ _ ih₁ ih₃ => exact .of_extension T hT ih₁ ih₃

/-- Universal property of the coproduct/extension closure. -/
lemma le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    [∀ (J : Type v), Q.IsClosedUnderColimitsOfShape (Discrete J)]
    [Q.IsTriangulatedClosed₂] (h : P ≤ Q) : Coprod P ≤ Q := by
  intro X hX
  induction hX with
  | of_mem X hX => exact h X hX
  | of_isoClosure e hX ih => exact Q.prop_of_iso e ih
  | of_colimitPresentation pres hmem ih => exact Q.prop_of_isColimit pres.isColimit ih
  | of_extension T hT h₁ h₃ ih₁ ih₃ => exact Q.ext_of_isTriangulatedClosed₂ T hT ih₁ ih₃

/-- A chosen `Type v`-indexed coproduct of members of `Coprod P` is again in it. -/
lemma of_sigma {ι : Type v} (f : ι → C) [HasCoproduct f]
    (hf : ∀ i, Coprod P (f i)) : Coprod P (∐ f) := by
  let pres : ColimitPresentation (Discrete ι) (∐ f) := .colimit (Discrete.functor f)
  exact .of_colimitPresentation pres (fun j => hf j.as)

end Coprod

/-- `⟨H⟩^[a,b] = smd(Coprod(H[a,b]))`. -/
def envelope (H : C) (a b : ℤ) : ObjectProperty C :=
  ObjectProperty.retractClosure (Coprod (shiftInterval H a b))

/-- Compactness of `H`: the functor `Hom(H, -)` preserves `Type v`-small
coproducts. -/
class IsCoproductCompact (H : C) : Prop where
  preserves (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (coyoneda.obj (.op H))

attribute [instance] IsCoproductCompact.preserves

/-- Generation: the shifts of `G` separate morphisms. -/
def IsGenerator (G : C) : Prop :=
  ((ObjectProperty.singleton G).shiftClosure ℤ).IsSeparating

/-- **Definition 2.1** (weak approximation data): a compact generator `G`, a
`t`-structure, an integer `A > 0`, with `G ∈ T^{≤A}`, `Hom(G, T^{≤-A}) = 0`, and
every `F ∈ T^{≤0}` fitting into a distinguished triangle `E ⟶ F ⟶ D ⟶ E⟦1⟧`
with `E ∈ ⟨G⟩^[-A,A]` and `D ∈ T^{≤-1}`. -/
structure WeakApproximationData (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [Pretriangulated C] where
  /-- the compact generator -/
  G : C
  /-- the `t`-structure -/
  t : TStructure C
  /-- the bound -/
  A : ℤ
  /-- positivity of the bound -/
  A_pos : 0 < A
  /-- `G` is compact -/
  G_compact : IsCoproductCompact G
  /-- `G` generates -/
  G_generates : IsGenerator G
  /-- `G ∈ T^{≤A}` -/
  G_mem_le : t.le A G
  /-- `Hom(G, T^{≤-A}) = 0` -/
  hom_vanishing : ∀ {Y : C}, t.le (-A) Y → ∀ f : G ⟶ Y, f = 0
  /-- the approximation triangles -/
  exists_triangle : ∀ F : C, t.le 0 F →
    ∃ (E D : C) (f : E ⟶ F) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ envelope G (-A) A E ∧ t.le (-1) D

end RelativeWeakApprox
