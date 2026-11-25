/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.AffineDiagonal
import FourierMukai.Scheme.AffineConvolution
import FourierMukai.Scheme.ConvolutionCounterexample
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Audit of the other GL26 targets for Noetherian schemes

This module does two things which can be checked independently of the remaining
geometric formalization.

* It gives a proper-flat, affine-Noetherian countermodel to the bare
  `lemma_2_25Statement`.  The diagonal scheme identities in `DiagonalFMData`
  do not determine the derived tensor, pull, and push functors.
* It supplies precisely the missing derived compatibility data and deduces the
  same `lemma_2_25Statement` from the landed `DiagonalIdentityData.identityIso`.
  The projection-formula input used by that structure is Stacks **08IN**; the
  tensor-unit and derived diagonal identities are separately recorded data,
  not hypotheses asserting the conclusion.

For completeness, `lemma_2_26Statement_of_correction` reexports the already
landed corresponding bridge for Lemma 2.26 (Stacks **07A4**, **08IN**, **08IR**,
**0D6D**, **0D6E**).  The other eight numbered targets remain specifications;
none is claimed here.

Found by member m6 of run `smww27cuj`, direction (d6).
-/

@[expose] public section

namespace RelativeFM.GL26OtherTargetsSmww27cujM6

open CategoryTheory
open AlgebraicGeometry
open RelativeFM.Noetherian

universe w u v

/-! ## The bare Lemma 2.25 rendering has a countermodel -/

namespace BareDiagonalCounterexample

open RelativeFM.Convolution.Counterexample

/-- All three functors used by the transform are identity except that tensoring
with any kernel is constant at `PUnit`. -/
noncomputable def badTensor : Type 0 → Type 0 ⥤ Type 0 :=
  fun _ => (Functor.const (Type 0)).obj PUnit

/-- The chosen context has identity scheme maps on `Spec ℤ`. -/
noncomputable abbrev context : Noetherian.FMContext (Type 0) (Type 0) (Type 0) :=
  testContext badTensor

/-- Legal diagonal data: every scheme identity holds, but the derived functors
are not related by the projection formula or the diagonal identities. -/
noncomputable def diagonal : DiagonalFMData context where
  sameSchemes := rfl
  sameFamily := by
    simp only [context, testContext, Category.comp_id]
    exact (eqToHom_refl baseScheme _).symm
  sameSubcats := rfl
  diagonal := 𝟙 baseScheme
  diagonalPr1 := by simp [context, testContext]
  diagonalPr2 := by
    simp only [context, testContext, Category.id_comp]
    exact (eqToHom_refl baseScheme _).symm
  push := 𝟭 (Type 0)
  unit := PUnit

/-- Properness and flatness do not repair the missing derived compatibility. -/
theorem context_isProperFlat : context.IsProperFlat :=
  testContext_isProperFlat badTensor

/-- The target evaluates the constant-`PUnit` transform at `PEmpty`, so no
isomorphism with the identity functor can exist. -/
theorem bare_lemma_2_25_has_countermodel
    (h : lemma_2_25Statement context context_isProperFlat diagonal) : False := by
  obtain ⟨e⟩ := h
  exact PEmpty.elim ((e.app PEmpty).hom PUnit.unit)

end BareDiagonalCounterexample

/-! ## Lemma 2.25 after adding the actual derived inputs -/

/-- Derived data missing from bare `DiagonalFMData`.  The first field is the
landed categorical diagonal package; the remaining equalities only identify
its functors with those in the Noetherian statement layer. -/
structure CorrectedDiagonalData {D DP : Type u} [Category.{v} D] [Category.{v} DP]
    (C : Noetherian.FMContext.{w, u, v} D D DP) (Δ : DiagonalFMData C) where
  /-- Projection formula (08IN), tensor unit, and the two derived diagonal
  identities. -/
  core : RelativeFM.DiagonalIdentityData D DP Δ.unit
  tensor_eq : C.tensorRight = core.tensorRight
  pull_eq : C.pullFromOne = core.pull
  push_eq : C.pushToTwo = core.push
  diagonal_eq : Δ.push = core.diagonal

/-- **GL26 Lemma 2.25 in the exact existing statement-layer form**, after the
corrected derived diagonal package is supplied.  Properness and flatness are
used to construct such a package geometrically, not in this categorical step. -/
theorem lemma_2_25Statement_of_correction
    {D DP : Type u} [Category.{v} D] [Category.{v} DP]
    {C : Noetherian.FMContext.{w, u, v} D D DP} {Δ : DiagonalFMData C}
    (E : CorrectedDiagonalData C Δ) (hC : C.IsProperFlat) :
    lemma_2_25Statement C hC Δ := by
  unfold lemma_2_25Statement Noetherian.FMContext.transform
  rw [E.tensor_eq, E.pull_eq, E.push_eq, E.diagonal_eq]
  exact E.core.identity_transform_isId

/-- The already landed Lemma 2.26 bridge, kept beside the new diagonal bridge
so that both statement-layer corrections have one audit point. -/
theorem lemma_2_26Statement_of_correction
    {D₁ D₂ D₃ D₁₂ D₂₃ D₁₃ : Type u}
    [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃]
    [Category.{v} D₁₂] [Category.{v} D₂₃] [Category.{v} D₁₃]
    {B : ConvolutionData.{w, u, v}
      (D1 := D₁) (D2 := D₂) (D3 := D₃)
      (DP12 := D₁₂) (DP23 := D₂₃) (DP13 := D₁₃)}
    (E : RelativeFM.Convolution.NoetherianBridge.CorrectedConvolutionData B)
    (h12 : B.C12.IsProperFlat) (h23 : B.C23.IsProperFlat)
    (h13 : B.C13.IsProperFlat) (K₁ : D₁₂) (K₂ : D₂₃) :
    lemma_2_26Statement B h12 h23 h13 K₁ K₂ :=
  RelativeFM.Convolution.NoetherianBridge.lemma_2_26_of_correction
    E h12 h23 h13 K₁ K₂

/-! ## Elementary, unconditional facts about the fibre-locus statements -/

/-- At a closed point of any scheme, the canonical residue-field representative
is locally of finite type: the point is a closed immersion, and closed
immersions are locally of finite type.  No Noetherian or Jacobson hypothesis is
needed for this direction. -/
theorem canonical_locallyOfFiniteType_of_isClosed {S : Scheme.{w}} {p : S}
    (hp : IsClosed ({p} : Set S)) :
    LocallyOfFiniteType (PointRepresentative.canonical p).map := by
  letI : IsClosedImmersion (S.fromSpecResidueField p) :=
    isClosed_singleton_iff_isClosedImmersion.mp hp
  change LocallyOfFiniteType (S.fromSpecResidueField p)
  infer_instance

/-- The universal finite-type closed-fibre criterion always implies the
existential closed-fibre criterion, using the canonical residue field.  This is
one half of the second equivalence in `DescentAscentStatement`; the other half
still needs representative independence. -/
theorem someClosedFibre_of_everyFiniteTypeClosedFibre
    (X : Noetherian.FMSetup.{w, u, v}) (P : ∀ {p : X.ctx.Base}, PointRepresentative p → Prop)
    (h : EveryFiniteTypeClosedFibre X P) : SomeClosedFibre X P := by
  intro p hp
  exact ⟨PointRepresentative.canonical p,
    h p hp (PointRepresentative.canonical p)
      (canonical_locallyOfFiniteType_of_isClosed hp)⟩

/-- Independence of an arbitrary fibre property under changing the chosen field
representative at a fixed point. -/
def PairwiseIndependent (X : Noetherian.FMSetup.{w, u, v})
    (P : ∀ {p : X.ctx.Base}, PointRepresentative p → Prop) : Prop :=
  ∀ {p : X.ctx.Base} (t t' : PointRepresentative p), P t ↔ P t'

/-- For a representative-independent property, the universal finite-type and
existential closed-fibre formulations are equivalent.  The forward implication
uses the actual closed-immersion geometry above; the reverse implication is
representative independence. -/
theorem everyFiniteTypeClosedFibre_iff_someClosedFibre
    (X : Noetherian.FMSetup.{w, u, v})
    (P : ∀ {p : X.ctx.Base}, PointRepresentative p → Prop)
    (hP : PairwiseIndependent X P) :
    EveryFiniteTypeClosedFibre X P ↔ SomeClosedFibre X P := by
  constructor
  · exact someClosedFibre_of_everyFiniteTypeClosedFibre X P
  · intro h p hp t _ht
    obtain ⟨t', ht'⟩ := h p hp
    exact (hP t' t).mp ht'

/-- With representative independence, the existential definition of `FM` can be
rewritten using the canonical residue field. -/
theorem mem_FM_iff_canonical_of_repIndependent
    (X : Noetherian.FMSetup.{w, u, v}) {K : X.DP} (hK : X.RepIndependent K)
    {p : X.ctx.Base} :
    p ∈ X.FM K ↔ X.EquivalenceAt K (PointRepresentative.canonical p) := by
  constructor
  · rintro ⟨t, ht⟩
    exact (hK t (PointRepresentative.canonical p)).2.mp ht
  · intro hp
    exact ⟨PointRepresentative.canonical p, hp⟩

/-- The corresponding canonical-residue-field normal form for `fm`. -/
theorem mem_fm_iff_canonical_of_repIndependent
    (X : Noetherian.FMSetup.{w, u, v}) {K : X.DP} (hK : X.RepIndependent K)
    {p : X.ctx.Base} :
    p ∈ X.fm K ↔ X.FullyFaithfulAt K (PointRepresentative.canonical p) := by
  constructor
  · rintro ⟨t, ht⟩
    exact (hK t (PointRepresentative.canonical p)).1.mp ht
  · intro hp
    exact ⟨PointRepresentative.canonical p, hp⟩

/-- An equivalence fibre is fully faithful, hence `FM(K) ⊆ fm(K)` exactly as
expected from the notation in GL26. -/
theorem FM_subset_fm (X : Noetherian.FMSetup.{w, u, v}) (K : X.DP) : X.FM K ⊆ X.fm K := by
  rintro p ⟨t, ht⟩
  refine ⟨t, ?_⟩
  letI : (X.fibreTransform K t).IsEquivalence := ht
  exact ⟨inferInstance, inferInstance⟩

end RelativeFM.GL26OtherTargetsSmww27cujM6

#print axioms RelativeFM.GL26OtherTargetsSmww27cujM6.BareDiagonalCounterexample.bare_lemma_2_25_has_countermodel
#print axioms RelativeFM.GL26OtherTargetsSmww27cujM6.lemma_2_25Statement_of_correction
#print axioms RelativeFM.GL26OtherTargetsSmww27cujM6.lemma_2_26Statement_of_correction
#print axioms RelativeFM.GL26OtherTargetsSmww27cujM6.canonical_locallyOfFiniteType_of_isClosed
#print axioms RelativeFM.GL26OtherTargetsSmww27cujM6.someClosedFibre_of_everyFiniteTypeClosedFibre
#print axioms RelativeFM.GL26OtherTargetsSmww27cujM6.everyFiniteTypeClosedFibre_iff_someClosedFibre
#print axioms RelativeFM.GL26OtherTargetsSmww27cujM6.mem_FM_iff_canonical_of_repIndependent
#print axioms RelativeFM.GL26OtherTargetsSmww27cujM6.mem_fm_iff_canonical_of_repIndependent
#print axioms RelativeFM.GL26OtherTargetsSmww27cujM6.FM_subset_fm
