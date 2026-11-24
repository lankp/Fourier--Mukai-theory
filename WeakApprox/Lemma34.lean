/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Aisle
import WeakApprox.Closure
import WeakApprox.Shift
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Tactic

/-!
# Lemma 3.4: iterated weak approximation

For weak approximation data `(H, T^{≤0}, A)`, this file constructs, for every
`F ∈ T^{≤0}` and integer `m ≥ 1`, a distinguished triangle
`E_m ⟶ F ⟶ D_m ⟶ E_m⟦1⟧` with
`E_m ∈ ⟨H⟩^[1-m-A,A] ∩ T^{≤0}` and `D_m ∈ T^{≤-m}`.

The induction is the proof in the paper.  Mathlib's rotated octahedron
`Octahedron'` directly supplies the cocone triangle needed in the induction
step; no separate octahedral hypothesis is introduced.

**Ambient hypothesis.** `WeakApproximationData` is defined in `WeakApprox`
using only `Pretriangulated`.  The theorem additionally assumes
`IsTriangulated C`, as does the paper's standing notion of a triangulated
category.  This supplies precisely the octahedron axiom used in the proof.
The intersection in the conclusion is written as the conjunction of envelope
membership and aisle membership.

Found by a member of the Ultramath run `smwun9hk2` (direction D5).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Lemma 3.4 (iterated weak approximation).**  For weak approximation data
`W`, every `F` in its degree-zero aisle and every integer `m ≥ 1` admit a
distinguished triangle with the stated envelope and aisle bounds.

The additional `[IsTriangulated C]` assumption (compared with the bare
`WeakApproximationData` structure) is the paper's octahedron axiom. -/
theorem lemma_3_4 (W : WeakApproximationData C) [IsTriangulated C]
    {F : C} (hF : W.t.le 0 F) {m : ℤ} (hm : 1 ≤ m) :
    ∃ (E D : C) (a : E ⟶ F) (f : F ⟶ D) (b : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk a f b ∈ distTriang C ∧
      envelope W.G (1 - m - W.A) W.A E ∧ W.t.le 0 E ∧ W.t.le (-m) D := by
  induction m, hm using Int.leInduction with
  | base =>
      obtain ⟨E, D, a, f, b, hT, hE, hD⟩ := W.exists_triangle F hF
      refine ⟨E, D, a, f, b, hT, ?_, ?_, ?_⟩
      · have heq : 1 - (1 : ℤ) - W.A = -W.A := by ring
        rw [heq]
        exact hE
      · exact mem_le_zero_of_distinguished_triangle W.t a f b hT
          (by norm_num) hF hD
      · exact hD
  | succ m hm ih =>
      obtain ⟨E, D, a, f, b, hT, hE, _hEa, hD⟩ := ih
      have hDzero : W.t.le 0 (D⟦-m⟧) :=
        W.t.le_shift (-m) (-m) 0 (by ring) D hD
      obtain ⟨E', D', a', f', b', hT', hE', hD'⟩ :=
        W.exists_triangle (D⟦-m⟧) hDzero
      let p : E'⟦m⟧ ⟶ (D⟦-m⟧)⟦m⟧ := m.negOnePow • a'⟦m⟧'
      let q : (D⟦-m⟧)⟦m⟧ ⟶ D'⟦m⟧ := m.negOnePow • f'⟦m⟧'
      let r : D'⟦m⟧ ⟶ (E'⟦m⟧)⟦(1 : ℤ)⟧ :=
        m.negOnePow • b'⟦m⟧' ≫ (shiftFunctorComm C 1 m).hom.app E'
      let S : Triangle C := Triangle.mk p q r
      have hS : S ∈ distTriang C :=
        (Triangle.mk a' f' b').shift_distinguished hT' m
      let eD : (D⟦-m⟧)⟦m⟧ ≅ D := shiftNegShift D m
      let u : D ⟶ D'⟦m⟧ := eD.inv ≫ q
      let T₂ : Triangle C := Triangle.mk (p ≫ eD.hom) u r
      have hT₂ : T₂ ∈ distTriang C := by
        apply isomorphic_distinguished S hS T₂
        exact Triangle.isoMk _ _ (Iso.refl _) eD.symm (Iso.refl _)
          (by
            change (p ≫ eD.hom) ≫ eD.inv = 𝟙 _ ≫ p
            rw [Category.id_comp, Category.assoc, eD.hom_inv_id, Category.comp_id])
          (by
            change (eD.inv ≫ q) ≫ 𝟙 _ = eD.inv ≫ q
            simp)
          (by
            change r ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 _) = 𝟙 _ ≫ r
            simp)
      obtain ⟨E₁, a₁, b₁, hT₁⟩ := distinguished_cocone_triangle₁ (f ≫ u)
      let o := Triangulated.someOctahedron' (rfl : f ≫ u = f ≫ u) hT hT₂ hT₁
      have hE'shift : envelope W.G (-W.A - m) (W.A - m) (E'⟦m⟧) :=
        map_shift_envelope W.G (-W.A) W.A m hE'
      have hEold : envelope W.G (1 - (m + 1) - W.A) W.A E :=
        lemma31_2_mono W.G (by omega) (by omega) E hE
      have hEnew : envelope W.G (1 - (m + 1) - W.A) W.A (E'⟦m⟧) :=
        lemma31_2_mono W.G (by omega) (by omega) (E'⟦m⟧) hE'shift
      have hE₁ : envelope W.G (1 - (m + 1) - W.A) W.A E₁ := by
        let _ := lemma_3_1_1_extensions W.G (1 - (m + 1) - W.A) W.A
        exact (envelope W.G (1 - (m + 1) - W.A) W.A).ext_of_isTriangulatedClosed₂
          o.triangle o.mem hEold hEnew
      have hD₁ : W.t.le (-(m + 1)) (D'⟦m⟧) := by
        have h := W.t.le_shift (-1) m (-1 - m) (by ring) D' hD'
        have heq : -(m + 1) = -1 - m := by ring
        rw [heq]
        exact h
      refine ⟨E₁, D'⟦m⟧, a₁, f ≫ u, b₁, hT₁, hE₁, ?_, hD₁⟩
      exact mem_le_zero_of_distinguished_triangle W.t a₁ (f ≫ u) b₁ hT₁
        (by omega) hF hD₁

end RelativeWeakApprox
