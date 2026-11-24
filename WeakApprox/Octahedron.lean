/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Basic
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Remark 3.2(2): the cocone triangle of a composition

This file formalizes Remark 3.2(2) of Lank--Pauwels, *Gluing weak
approximability along recollements*.

Found by a member of the Ultramath run `smwun9hk2` (direction D3).  Given chosen cocone triangles for
composable morphisms `f`, `g`, and `f ≫ g`, the octahedron axiom supplies a
distinguished triangle on their cocones.

There is no weakening of the statement.  We use Mathlib's rotated octahedron
`Octahedron'`, whose three input triangles have precisely the cocone
orientation used in the paper.  The chosen constructions are noncomputable
because they use the axiom of choice to select an octahedron from
`IsTriangulated.octahedron_axiom`; the final existence theorem itself is in
`Prop`.
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

section Composition

variable {X Y Z F_f F_g F_gf : C}
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable (a : F_f ⟶ X) (b : Y ⟶ F_f⟦(1 : ℤ)⟧)
variable (c : F_g ⟶ Y) (d : Z ⟶ F_g⟦(1 : ℤ)⟧)
variable (e : F_gf ⟶ X) (k : Z ⟶ F_gf⟦(1 : ℤ)⟧)
variable (hf : Triangle.mk a f b ∈ distTriang C)
variable (hg : Triangle.mk c g d ∈ distTriang C)
variable (hgf : Triangle.mk e (f ≫ g) k ∈ distTriang C)

/-- The chosen rotated octahedron attached to three cocone triangles for
`f`, `g`, and `f ≫ g`.  Its `m₁` and `m₃` are the first two maps in the
cocone triangle of Remark 3.2(2). -/
noncomputable def compositionCoconeOctahedron :
    Octahedron' (rfl : f ≫ g = f ≫ g) hf hg hgf :=
  Triangulated.someOctahedron' rfl hf hg hgf

/-- **Remark 3.2(2), chosen triangle.**  The triangle
`F_f ⟶ F_gf ⟶ F_g ⟶ F_f⟦1⟧` obtained from the chosen octahedron.  The last
map is the composite `F_g ⟶ Y ⟶ F_f⟦1⟧` coming from the given cocone
triangles. -/
noncomputable def compositionCoconeTriangle : Triangle C :=
  (compositionCoconeOctahedron f g a b c d e k hf hg hgf).triangle

@[simp] theorem compositionCoconeTriangle_obj₁ :
    (compositionCoconeTriangle f g a b c d e k hf hg hgf).obj₁ = F_f := rfl

@[simp] theorem compositionCoconeTriangle_obj₂ :
    (compositionCoconeTriangle f g a b c d e k hf hg hgf).obj₂ = F_gf := rfl

@[simp] theorem compositionCoconeTriangle_obj₃ :
    (compositionCoconeTriangle f g a b c d e k hf hg hgf).obj₃ = F_g := rfl

/-- The constructed cocone triangle is distinguished. -/
theorem compositionCoconeTriangle_distinguished :
    compositionCoconeTriangle f g a b c d e k hf hg hgf ∈ distTriang C :=
  (compositionCoconeOctahedron f g a b c d e k hf hg hgf).mem

include f g a b c d e k hf hg hgf in
/-- **Remark 3.2(2), existential form.**  For composable `f : X ⟶ Y` and
`g : Y ⟶ Z` and chosen cocone triangles for `f`, `g`, and `f ≫ g`, there is a
distinguished triangle `F_f ⟶ F_gf ⟶ F_g ⟶ F_f⟦1⟧`. -/
theorem remark_3_2_2 :
    ∃ (p : F_f ⟶ F_gf) (q : F_gf ⟶ F_g),
      Triangle.mk p q (c ≫ b) ∈ distTriang C := by
  let o := compositionCoconeOctahedron f g a b c d e k hf hg hgf
  exact ⟨o.m₁, o.m₃, o.mem⟩

end Composition

end RelativeWeakApprox
