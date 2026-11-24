/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The mate bijection

This file formalizes the mate bijection used in Section 7 of
E. Guisado Villalgordo and P. Lank, *Relative Fourier--Mukai theory for
algebraic spaces*.

For adjunctions `adj : F ⊣ G` and `adj' : F' ⊣ G'`, a natural transformation
`α : H ⋙ F' ⟶ F ⋙ K` has right mate `mate adj adj' α : G ⋙ H ⟶ K ⋙ G'`.
This is the paper's `α : F' H ⟶ K F` and `β : H G ⟶ G' K`, translated into
Mathlib's diagrammatic composition notation.  In particular, this spelling is
the well-typed version of the formulas in the task (which reverses the order
of the functor composites).

The definitions below use precisely the unit/counit whiskering formula from
the paper.  The inverse identities are obtained from Mathlib's general
`CategoryTheory.mateEquiv`; thus no special assumptions on the four
categories or functors are needed.

Mathlib already contains the mate bijection for 2-cells of the shape of a square
(`CategoryTheory.mateEquiv` in `Mathlib.CategoryTheory.Adjunction.Mates`).  What
this file adds is the paper's formula spelled out as a natural transformation
between `NatTrans` types, the proof that it is *definitionally* Mathlib's
`mateEquiv` (so the paper's formula and Mathlib's agree), the componentwise
formulas `mate_app` and `mateInv_app`, and the packaged bijection `matesEquiv`.

Still to add (paper Lemma 7.1(1)): the commutativity of the Hom-set square, i.e.
compatibility of the correspondence with pre- and post-composition
(`CategoryTheory.mateEquiv_vcomp` and `mateEquiv_hcomp` are the tools).

The file was produced by a member of the Ultramath run `smwufdjq4` (direction D1).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {B : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} B]
  {F : C ⥤ D} {G : D ⥤ C} {F' : E ⥤ B} {G' : B ⥤ E}
  {H : C ⥤ E} {K : D ⥤ B}

/-- The **right mate** of `α` with respect to `adj : F ⊣ G` and
`adj' : F' ⊣ G'` (paper Lemma 7.2; the bijection requested in the task).

Explicitly, after inserting the identity and associativity isomorphisms, it is
`(G ⋙ H) ◁ adj'.unit`, followed by `G ◁ (α ▷ G')`, followed by
`adj.counit ▷ (K ⋙ G')`.  At components this is the familiar formula
`η' ≫ G'.map α ≫ G'.map (K.map ε)`; see `mate_app`.
-/
def mate (adj : F ⊣ G) (adj' : F' ⊣ G') (α : H ⋙ F' ⟶ F ⋙ K) :
    G ⋙ H ⟶ K ⋙ G' :=
  (rightUnitor _).inv ≫
  whiskerLeft (G ⋙ H) adj'.unit ≫
  (associator _ _ _).hom ≫ whiskerLeft _ (associator _ _ _).inv ≫
  whiskerLeft G (whiskerRight α G') ≫
  whiskerLeft _ (associator _ _ _).hom ≫ (associator _ _ _).inv ≫
  whiskerRight adj.counit (K ⋙ G') ≫
  (leftUnitor _).hom

/-- The **left mate**, given by the dual unit/counit formula.  It is the
inverse of `mate` by `mateInv_mate` and `mate_mateInv`.
-/
def mateInv (adj : F ⊣ G) (adj' : F' ⊣ G') (β : G ⋙ H ⟶ K ⋙ G') :
    H ⋙ F' ⟶ F ⋙ K :=
  (leftUnitor _).inv ≫
  whiskerRight adj.unit (H ⋙ F') ≫
  (associator _ _ _).inv ≫ whiskerRight (associator _ _ _).hom _ ≫
  whiskerRight (whiskerLeft F β) F' ≫
  whiskerRight (associator _ _ _).inv _ ≫ (associator _ _ _).hom ≫
  whiskerLeft (F ⋙ K) adj'.counit ≫
  (rightUnitor _).hom

/-- `mate` is the natural-transformation form of Mathlib's two-square mate
correspondence.  This is definitional: the preceding formula is exactly the
unit/counit formula used there.
-/
theorem mate_eq_categoryTheory_mateEquiv (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) :
    mate adj adj' α = CategoryTheory.mateEquiv adj adj' α := rfl

/-- The inverse formula agrees with the inverse of Mathlib's mate
correspondence, again by definition.
-/
theorem mateInv_eq_categoryTheory_mateEquiv_symm (adj : F ⊣ G) (adj' : F' ⊣ G')
    (β : G ⋙ H ⟶ K ⋙ G') :
    mateInv adj adj' β = (CategoryTheory.mateEquiv adj adj').symm β := rfl

/-- Componentwise formula for the right mate: precompose with the unit of
`adj'`, apply `G'` to `α`, and then to the counit of `adj` under `K`.
-/
@[simp]
theorem mate_app (adj : F ⊣ G) (adj' : F' ⊣ G') (α : H ⋙ F' ⟶ F ⋙ K) (d : D) :
    (mate adj adj' α).app d =
      adj'.unit.app (H.obj (G.obj d)) ≫
        G'.map (α.app (G.obj d)) ≫ G'.map (K.map (adj.counit.app d)) := by
  simp [mate]

/-- Componentwise formula for the inverse, or left-mate, construction. -/
@[simp]
theorem mateInv_app (adj : F ⊣ G) (adj' : F' ⊣ G') (β : G ⋙ H ⟶ K ⋙ G') (c : C) :
    (mateInv adj adj' β).app c =
      F'.map (H.map (adj.unit.app c)) ≫ F'.map (β.app (F.obj c)) ≫
        adj'.counit.app (K.obj (F.obj c)) := by
  simp [mateInv]

/-- Taking the left mate of the right mate recovers the original 2-cell. -/
@[simp]
theorem mateInv_mate (adj : F ⊣ G) (adj' : F' ⊣ G') (α : H ⋙ F' ⟶ F ⋙ K) :
    mateInv adj adj' (mate adj adj' α) = α :=
  (CategoryTheory.mateEquiv adj adj').left_inv α

/-- Taking the right mate of the left mate recovers the original 2-cell. -/
@[simp]
theorem mate_mateInv (adj : F ⊣ G) (adj' : F' ⊣ G') (β : G ⋙ H ⟶ K ⋙ G') :
    mate adj adj' (mateInv adj adj' β) = β :=
  (CategoryTheory.mateEquiv adj adj').right_inv β

/-- **The mate bijection.**  Natural transformations `H ⋙ F' ⟶ F ⋙ K` and
`G ⋙ H ⟶ K ⋙ G'` are in canonical bijection, with the two displayed
unit/counit formulas as mutually inverse maps.
-/
def matesEquiv (adj : F ⊣ G) (adj' : F' ⊣ G') :
    (H ⋙ F' ⟶ F ⋙ K) ≃ (G ⋙ H ⟶ K ⋙ G') where
  toFun := mate adj adj'
  invFun := mateInv adj adj'
  left_inv := mateInv_mate adj adj'
  right_inv := mate_mateInv adj adj'

/-- Function form of the mate bijection (Lemma 7.2(2) of the paper, called
Lemma 7.1 in the task).
-/
theorem mate_bijective (adj : F ⊣ G) (adj' : F' ⊣ G') :
    Function.Bijective (mate (H := H) (K := K) adj adj') :=
  (matesEquiv adj adj').bijective

/-- Two 2-cells are mates precisely when applying the right-mate map to the
first gives the second.
-/
theorem mate_eq_iff (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) (β : G ⋙ H ⟶ K ⋙ G') :
    mate adj adj' α = β ↔ mateInv adj adj' β = α := by
  constructor
  · rintro rfl
    exact mateInv_mate adj adj' α
  · intro h
    rw [← h, mate_mateInv]

/-! ### Lemma 7.8: mates of isomorphisms -/

/-- **Lemma 7.8(2)**, forward direction: if the unit of `adj'` and the counit of
`adj` are isomorphisms, then the mate of an isomorphism is an isomorphism.  (Only
these two of the four unit/counit 2-cells occur in the formula for `mate`.) -/
theorem isIso_mate (adj : F ⊣ G) (adj' : F' ⊣ G') (α : H ⋙ F' ⟶ F ⋙ K) [IsIso α]
    [IsIso adj'.unit] [IsIso adj.counit] : IsIso (mate adj adj' α) := by
  unfold mate
  infer_instance

/-- **Lemma 7.8(2)**, converse direction: if the unit of `adj` and the counit of
`adj'` are isomorphisms, then `α` is an isomorphism as soon as its mate is.  (Only
these two occur in the formula for `mateInv`.) -/
theorem isIso_of_isIso_mate (adj : F ⊣ G) (adj' : F' ⊣ G') (α : H ⋙ F' ⟶ F ⋙ K)
    [IsIso adj.unit] [IsIso adj'.counit] [IsIso (mate adj adj' α)] : IsIso α := by
  have h := mateInv_mate adj adj' α
  rw [← h]
  have hcomp : ∀ c, IsIso ((mateInv adj adj' (mate adj adj' α)).app c) := by
    intro c
    rw [mateInv_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **Lemma 7.8(2)**: if both adjunctions are adjoint equivalences, the mate
correspondence preserves and reflects isomorphisms. -/
theorem isIso_mate_iff (adj : F ⊣ G) (adj' : F' ⊣ G') (α : H ⋙ F' ⟶ F ⋙ K)
    [IsIso adj.unit] [IsIso adj.counit] [IsIso adj'.unit] [IsIso adj'.counit] :
    IsIso (mate adj adj' α) ↔ IsIso α :=
  ⟨fun _ => isIso_of_isIso_mate adj adj' α, fun _ => isIso_mate adj adj' α⟩

end RelativeFM
