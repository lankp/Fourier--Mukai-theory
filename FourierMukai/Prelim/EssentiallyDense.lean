/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Prelim.Generation
import FourierMukai.Prelim.Thickness

/-!
# Lemma 2.3(3): essentially dense functors detect isomorphisms

This file formalizes Lemma 2.3(3) of

  E. Guisado Villalgordo, P. Lank, *Relative Fourier--Mukai theory for algebraic spaces*.

The paper calls a triangulated functor `L : C ⥤ D` *essentially dense* when every
object of `D` lies in `⟨L(C)⟩₁`, the closure of the essential image under shifts,
finite coproducts and retracts.  In Mathlib that closure is stage `0` of the
triangulated envelope, `L.essImage.triangEnvelopeIter 0`; we call the resulting
property `EssentiallyDense₀` and prove the lemma for it.  The slightly weaker
condition "some finite stage `n` of the envelope is everything" (`EssentiallyDense`,
and the general `isIso_app_of_precomp_triangEnvelopeIter`) is proved at the same
time and is what the argument uses.

The proof was found by a member of the Ultramath run `smwufdjq4` (direction D7).

## Main results

* `RelativeFM.EssentiallyDense`, `RelativeFM.EssentiallyDense₀`
* `RelativeFM.Trinatural.isIso_app_of_precomp_triangEnvelopeIter`
* `RelativeFM.Trinatural.isIso_iff_of_precomp_essentiallyDense`
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory Limits Pretriangulated

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [HasZeroObject D] [HasZeroObject E] [HasShift D ℤ] [HasShift E ℤ]
  [Preadditive D] [Preadditive E]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor E n).Additive]
  [Pretriangulated D] [Pretriangulated E]

/-- A functor is *essentially dense* when stage `1` of the triangulated envelope
of its essential image is all of the target. -/
def EssentiallyDense (L : C ⥤ D) : Prop :=
  L.essImage.triangEnvelopeIter 1 = ⊤

/-- The literal `add`-density formulation matching the paper's `⟨L(C)⟩₁`: every
object is a retract of a finite product of shifts of objects in the essential
image.  This is stage `0` of Mathlib's envelope filtration. -/
def EssentiallyDense₀ (L : C ⥤ D) : Prop :=
  L.essImage.triangEnvelopeIter 0 = ⊤

namespace Trinatural

variable {F G : D ⥤ E} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]

/-- If one finite stage of the triangulated envelope of the essential image of
`L` is all of `D`, and every component of `η` on the image of `L` is an
isomorphism, then every component of `η` is an isomorphism. -/
theorem isIso_app_of_precomp_triangEnvelopeIter (η : Trinatural F G) (L : C ⥤ D)
    (n : ℕ) (hL : L.essImage.triangEnvelopeIter n = ⊤)
    (hη : ∀ X : C, IsIso (η.toNatTrans.app (L.obj X)))
    (Y : D) : IsIso (η.toNatTrans.app Y) := by
  have himage : L.essImage ≤ η.isoLocus := by
    rintro Z ⟨X, ⟨e⟩⟩
    exact η.isoLocus.prop_of_iso e (hη X)
  have henv : L.essImage.triangEnvelope ≤ η.isoLocus :=
    (ObjectProperty.triangEnvelope_le_iff
      (P := L.essImage) (Q := η.isoLocus)).mpr himage
  have htop : (⊤ : ObjectProperty D) ≤ η.isoLocus := by
    rw [← hL]
    exact (L.essImage.triangEnvelopeIter_le_triangEnvelope n).trans henv
  exact htop Y trivial

/-- **Lemma 2.3(3), component form.** -/
theorem isIso_app_of_precomp_essentiallyDense (η : Trinatural F G) (L : C ⥤ D)
    (hL : EssentiallyDense L) (hη : ∀ X : C, IsIso (η.toNatTrans.app (L.obj X)))
    (Y : D) : IsIso (η.toNatTrans.app Y) :=
  η.isIso_app_of_precomp_triangEnvelopeIter L 1 hL hη Y

/-- **Lemma 2.3(3)**, reflection direction: a trinatural transformation which
becomes an isomorphism after precomposition with an essentially dense functor is
itself an isomorphism. -/
theorem isIso_of_precomp_essentiallyDense (η : Trinatural F G) (L : C ⥤ D)
    (hL : EssentiallyDense L) (hη : ∀ X : C, IsIso (η.toNatTrans.app (L.obj X))) :
    IsIso (show F ⟶ G from η.toNatTrans) := by
  haveI : ∀ Y : D, IsIso (η.toNatTrans.app Y) :=
    η.isIso_app_of_precomp_essentiallyDense L hL hη
  exact NatIso.isIso_of_isIso_app η.toNatTrans

/-- **Lemma 2.3(3), `add`-density form**: the conclusion holds when stage `0` of
the essential image's envelope is all of `D`, which is the paper's hypothesis
`⟨L(C)⟩₁ = ⊤`. -/
theorem isIso_of_precomp_essentiallyDense₀ (η : Trinatural F G) (L : C ⥤ D)
    (hL : EssentiallyDense₀ L) (hη : ∀ X : C, IsIso (η.toNatTrans.app (L.obj X))) :
    IsIso (show F ⟶ G from η.toNatTrans) := by
  haveI : ∀ Y : D, IsIso (η.toNatTrans.app Y) :=
    η.isIso_app_of_precomp_triangEnvelopeIter L 0 hL hη
  exact NatIso.isIso_of_isIso_app η.toNatTrans

/-- **Lemma 2.3(3)**, as an equivalence, in the paper's `add`-density form. -/
theorem isIso_iff_of_precomp_essentiallyDense₀ (η : Trinatural F G) (L : C ⥤ D)
    (hL : EssentiallyDense₀ L) :
    IsIso (show F ⟶ G from η.toNatTrans) ↔
      ∀ X : C, IsIso (η.toNatTrans.app (L.obj X)) := by
  refine ⟨fun h X => ?_, η.isIso_of_precomp_essentiallyDense₀ L hL⟩
  haveI := h
  infer_instance

end Trinatural

end RelativeFM
