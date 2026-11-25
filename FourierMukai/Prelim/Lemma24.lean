/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Prelim.Lemma25
import WeakApprox.GeneratorBridge

/-!
# Lemma 2.4: compact generation by one object versus localizing generation

**Lemma 2.4** (`lem:localizing_iff_cpt_gen`) of

  E. Guisado Villalgordo, P. Lank, *Relative Fourier--Mukai theory for algebraic spaces*:

in a compactly generated triangulated category `T`, a compact object `G`
compactly generates `T` if and only if the smallest localizing subcategory
containing `G` is all of `T`.

## Rendering

* "`G` compactly generates `T`" is zero detection by the shifts of `G`:
  `RelativeWeakApprox.IsPaperGenerator G`, i.e. `Hom(G⟦n⟧, E) = 0` for all `n : ℤ`
  implies `IsZero E`.
* "`⟨G⟩‾ = T`" is `ObjectProperty.IsLocalizingGenerator.{w} (singleton G)` of
  `Prelim/Lemma25.lean` (the language of Lemma 2.5): every triangulated,
  isomorphism-closed property closed under `w`-small coproducts and containing `G`
  holds everywhere.  This file also defines the paper's `⟨S⟩‾` itself,
  `localizingClosure P` (the intersection of all such properties), proves that it
  is localizing and contains `P` (so it is the smallest localizing subcategory
  containing `P`), and proves
  `IsLocalizingGenerator P ↔ localizingClosure P = ⊤`
  (`isLocalizingGenerator_iff_localizingClosure_eq_top`).

## What is proved, and what is assumed

* `isPaperGenerator_of_isLocalizingGenerator`: `⟨G⟩‾ = T ⇒ G detects zero`,
  unconditionally (no compactness, no coproducts, no compact generation).  For
  fixed `E`, the objects `A` with `Hom(A, E⟦n⟧) = 0` for all `n` form a localizing
  subcategory; this is `IsLocalizingGenerator.isZero_of_rightOrthogonal` of
  `Prelim/Lemma25.lean`, applied to the shift closure of `G`.
* `isLocalizingGenerator_of_isPaperGenerator`: the converse, from the named input
  `HasBousfieldTriangles G`: every `E` sits in a distinguished triangle
  `S → E → R → S⟦1⟧` with `S ∈ ⟨G⟩‾` and `Hom(G⟦n⟧, R) = 0` for all `n`.  This is
  the input the paper's proof takes from Neeman (*Triangulated categories*,
  Remark 1.16, Theorem 1.17 and Proposition 9.1.19: the Verdier quotient
  `T → T/⟨G⟩‾` has a right adjoint `Q`, and the triangle is
  `S_E → E → QπE → S_E⟦1⟧`).  Bousfield localization is not in Mathlib; the input
  is carried as a hypothesis, never as an axiom.
* `lemma_2_4`: the paper's equivalence, for a compact `G` in a category with
  `w`-small coproducts, from the named input `CompactBousfieldLocalization C`
  (Neeman's theorem for every compact object).

## Deviations from the paper's statement

* The paper's hypothesis "`T` is compactly generated" is not assumed: the proof
  uses it nowhere (Neeman's Theorem 1.17 needs only that `G` is compact and that
  `T` has small coproducts), so the Lean statement is stronger in this respect.
* The converse direction depends on the named input above.  The input asks only
  `R ∈ {G⟦n⟧}^⊥`, which is weaker than the `R ∈ ⟨G⟩‾^⊥` that Neeman provides.
* Neeman's theorem is stated for locally small categories with small coproducts,
  i.e. `w = v₁` here; `CompactBousfieldLocalization.{w}` is stated for an
  arbitrary coproduct universe `w`, as in `Prelim/Lemma25.lean`, and is a
  consequence of Neeman's theorem only in that case.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory Limits Pretriangulated RelativeWeakApprox ZeroObject

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace ObjectProperty

/-- The paper's `⟨S⟩‾` (Section 2.1): the intersection of all triangulated,
isomorphism-closed properties closed under `w`-small coproducts that contain `P`.
By `le_localizingClosure` and the instances below it is the smallest localizing
subcategory containing `P`. -/
def localizingClosure (P : CategoryTheory.ObjectProperty C) :
    CategoryTheory.ObjectProperty C := fun X =>
  ∀ (Q : CategoryTheory.ObjectProperty C), Q.IsTriangulated → Q.IsClosedUnderIsomorphisms →
    (∀ (J : Type w), Q.IsClosedUnderColimitsOfShape (Discrete J)) → P ≤ Q → Q X

variable (P : CategoryTheory.ObjectProperty C)

lemma le_localizingClosure : P ≤ localizingClosure.{w} P :=
  fun _ hX _ _ _ _ hPQ => hPQ _ hX

/-- `localizingClosure P` lies in every localizing property containing `P`. -/
lemma localizingClosure_le (Q : CategoryTheory.ObjectProperty C) [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] [∀ (J : Type w), Q.IsClosedUnderColimitsOfShape (Discrete J)]
    (hPQ : P ≤ Q) : localizingClosure.{w} P ≤ Q :=
  fun _ hX => hX Q inferInstance inferInstance (fun _ => inferInstance) hPQ

instance : (localizingClosure.{w} P).IsClosedUnderIsomorphisms where
  of_iso e hX Q hQ hQiso hQcolim hPQ := Q.prop_of_iso e (hX Q hQ hQiso hQcolim hPQ)

instance (J : Type w) : (localizingClosure.{w} P).IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := by
    rintro X ⟨h⟩ Q hQ hQiso hQcolim hPQ
    exact Q.prop_of_isColimit h.isColimit (fun j => h.prop_diag_obj j Q hQ hQiso hQcolim hPQ)

instance : (localizingClosure.{w} P).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, fun Q hQ hQiso _ _ => by
    obtain ⟨Z, hZ, hQZ⟩ := hQ.exists_zero
    exact Q.prop_of_iso (hZ.iso (isZero_zero C)) hQZ⟩
  isStableUnderShiftBy n := ⟨fun X hX Q hQ hQiso hQcolim hPQ =>
    Q.le_shift n X (hX Q hQ hQiso hQcolim hPQ)⟩
  ext₂' T hT h₁ h₃ := ⟨T.obj₂, fun Q hQ hQiso hQcolim hPQ => by
    have h := Q.ext_of_isTriangulatedClosed₂' T hT (h₁ Q hQ hQiso hQcolim hPQ)
      (h₃ Q hQ hQiso hQcolim hPQ)
    rwa [Q.isoClosure_eq_self] at h, ⟨Iso.refl _⟩⟩

/-- `P` generates by shifts, cones and `w`-small coproducts (`⟨P⟩‾ = T`, in the
universal-property form `IsLocalizingGenerator` of `Prelim/Lemma25.lean`) if and
only if its localizing closure is everything. -/
lemma isLocalizingGenerator_iff_localizingClosure_eq_top :
    IsLocalizingGenerator.{w} P ↔ localizingClosure.{w} P = ⊤ := by
  constructor
  · intro h
    ext X
    simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
    exact fun Q hQ hQiso hQcolim hPQ => h Q hQ hQiso hQcolim hPQ X
  · intro h Q hQ hQiso hQcolim hPQ X
    have hX : localizingClosure.{w} P X := by rw [h]; trivial
    exact hX Q hQ hQiso hQcolim hPQ

end ObjectProperty

open ObjectProperty in
/-- The input of the converse of **Lemma 2.4** (`lem:localizing_iff_cpt_gen`):
every object `E` sits in a distinguished triangle `S → E → R → S⟦1⟧` with `S` in
the localizing closure `⟨G⟩‾` of `G` and `R` right orthogonal to every shift of
`G`.

This is what the paper takes from Neeman, *Triangulated categories* (Ann. of
Math. Stud. 148, 2001), Remark 1.16, Theorem 1.17 and Proposition 9.1.19: for
compact `G` the Verdier quotient `π : T → T/⟨G⟩‾` has a right adjoint `Q`, and the
triangle is `S_E → E → QπE → S_E⟦1⟧` with `QπE ∈ ⟨G⟩‾^⊥`.  It is not in Mathlib
and is carried as a hypothesis, not as an axiom. -/
structure HasBousfieldTriangles (G : C) : Prop where
  exists_triangle (E : C) : ∃ (S R : C) (f : S ⟶ E) (g : E ⟶ R) (h : R ⟶ S⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C ∧
      localizingClosure.{w} (ObjectProperty.singleton G) S ∧
      ∀ (n : ℤ) (a : G⟦n⟧ ⟶ R), a = 0

/-- Neeman's Bousfield localization for compact objects, as a named input: every
`w`-compact object `G` has the triangles of `HasBousfieldTriangles`.  Neeman
(*Triangulated categories*, Remark 1.16, Theorem 1.17, Proposition 9.1.19) proves
this for a triangulated category with small coproducts, i.e. for `w = v₁` here;
see the module docstring. -/
def CompactBousfieldLocalization (C : Type u₁) [Category.{v₁} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] : Prop :=
  ∀ G : C, IsCompact.{w} G → HasBousfieldTriangles.{w} G

/-- **Lemma 2.4** (`lem:localizing_iff_cpt_gen`), direction `⟨G⟩‾ = T ⇒ G compactly
generates`: if `G` generates by shifts, cones and `w`-small coproducts, then `G`
detects zero objects through its shifts.  No compactness, coproducts or compact
generation is needed.  Reduced to `IsLocalizingGenerator.isZero_of_rightOrthogonal`
(`Prelim/Lemma25.lean`) for the shift closure of `G`. -/
theorem isPaperGenerator_of_isLocalizingGenerator {G : C}
    (hL : ObjectProperty.IsLocalizingGenerator.{w} (ObjectProperty.singleton G)) :
    IsPaperGenerator G := by
  intro E hE
  have hL' : ObjectProperty.IsLocalizingGenerator.{w}
      ((ObjectProperty.singleton G).shiftClosure ℤ) :=
    hL.mono ((ObjectProperty.singleton G).le_shiftClosure (A := ℤ))
  exact hL'.isZero_of_rightOrthogonal ((rightOrthogonal_shiftClosure_singleton_iff G E).2 hE)

/-- **Lemma 2.4** (`lem:localizing_iff_cpt_gen`), direction `G compactly generates ⇒
⟨G⟩‾ = T`, from the Bousfield triangles of `HasBousfieldTriangles G` (Neeman's
input, carried as a hypothesis).  In the triangle `S → E → R → S⟦1⟧` the object `R`
receives no nonzero maps from the shifts of `G`, so it is zero, so `S → E` is an
isomorphism and `E ∈ ⟨G⟩‾`. -/
theorem isLocalizingGenerator_of_isPaperGenerator {G : C}
    (hB : HasBousfieldTriangles.{w} G) (hG : IsPaperGenerator G) :
    ObjectProperty.IsLocalizingGenerator.{w} (ObjectProperty.singleton G) := by
  intro Q hQ hQiso hQcolim hGQ X
  obtain ⟨S, R, f, g, h, hT, hS, hR⟩ := hB.exists_triangle X
  have hRz : IsZero R := hG hR
  have : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hRz
  exact Q.prop_of_iso (asIso f) (hS Q hQ hQiso hQcolim hGQ)

/-- **Lemma 2.4** (`lem:localizing_iff_cpt_gen`), given the Bousfield triangles for
`G`: `G` detects zero through its shifts iff `⟨G⟩‾ = T`. -/
theorem isPaperGenerator_iff_isLocalizingGenerator {G : C}
    (hB : HasBousfieldTriangles.{w} G) :
    IsPaperGenerator G ↔
      ObjectProperty.IsLocalizingGenerator.{w} (ObjectProperty.singleton G) :=
  ⟨isLocalizingGenerator_of_isPaperGenerator hB, isPaperGenerator_of_isLocalizingGenerator⟩

/-- **Lemma 2.4** (`lem:localizing_iff_cpt_gen`), in the paper's form.  In a
triangulated category with `w`-small coproducts, a compact object `G` compactly
generates (detects zero through its shifts) if and only if `⟨G⟩‾ = T`.  The
converse direction uses Neeman's Bousfield localization, carried as the named
input `CompactBousfieldLocalization`; the paper's hypothesis that `T` is compactly
generated is not needed (see the module docstring). -/
theorem lemma_2_4 [HasCoproducts.{w} C] (hN : CompactBousfieldLocalization.{w} C)
    {G : C} (hG : IsCompact.{w} G) :
    IsPaperGenerator G ↔
      ObjectProperty.localizingClosure.{w} (ObjectProperty.singleton G) = ⊤ :=
  (isPaperGenerator_iff_isLocalizingGenerator (hN G hG)).trans
    (ObjectProperty.isLocalizingGenerator_iff_localizingClosure_eq_top _)

/-- **Lemma 2.4** (`lem:localizing_iff_cpt_gen`) in the language of Lemma 2.5: under
Neeman's input, `G` is a single compact generator in the sense of
`SinglyCompactlyGenerated` iff it is compact and detects zero through its shifts. -/
theorem singlyCompactlyGenerated_iff [HasCoproducts.{w} C]
    (hN : CompactBousfieldLocalization.{w} C) (G : C) :
    SinglyCompactlyGenerated.{w} C G ↔ IsCompact.{w} G ∧ IsPaperGenerator G :=
  ⟨fun h => ⟨h.1, isPaperGenerator_of_isLocalizingGenerator h.2⟩,
    fun h => ⟨h.1, isLocalizingGenerator_of_isPaperGenerator (hN G h.1) h.2⟩⟩

end RelativeFM
