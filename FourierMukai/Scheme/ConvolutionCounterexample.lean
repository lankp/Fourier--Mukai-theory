/-
Copyright (c) 2026 Formalization of Relative Fourier--Mukai theory.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.Statements

/-!
# Why the bare `ConvolutionData` cannot prove GL26 Lemma 2.26

This diagnostic file gives a legal `RelativeFM.Noetherian.ConvolutionData`
whose scheme maps are identities on `Spec ℤ` but for which the stated transform
isomorphism is false.  Thus affine_Noetherian bases, properness and flatness do
not repair the missing compatibility fields in the statement interface.
-/

@[expose] public section

namespace RelativeFM.Convolution.Counterexample

open CategoryTheory
open AlgebraicGeometry
open RelativeFM.Noetherian

universe u v

/-- The scheme in the countermodel. -/
noncomputable def baseScheme : Scheme.{0} := Spec (CommRingCat.of ℤ)

/-- Nonvacuous predicates; their values are irrelevant to Lemma 2.26. -/
def typeSubcats : RelativeFM.Subcats (Type 0) where
  DbQc X := Nonempty X
  Dcoh X := Nonempty X
  Perf X := Nonempty X
  IsPseudocoherent X := Nonempty X

/-- A scheme-level FM context with prescribed, completely free tensor functors. -/
noncomputable def testContext (tensor : Type 0 → Type 0 ⥤ Type 0) :
    RelativeFM.Noetherian.FMContext (Type 0) (Type 0) (Type 0) where
  Base := baseScheme
  Y1 := baseScheme
  Y2 := baseScheme
  Prod := baseScheme
  noetherianBase := isNoetherian_Spec.mpr inferInstance
  noetherianY1 := isNoetherian_Spec.mpr inferInstance
  noetherianY2 := isNoetherian_Spec.mpr inferInstance
  noetherianProd := isNoetherian_Spec.mpr inferInstance
  f1 := 𝟙 baseScheme
  f2 := 𝟙 baseScheme
  pr1 := 𝟙 baseScheme
  pr2 := 𝟙 baseScheme
  square := IsPullback.of_id_snd
  pullFromOne := 𝟭 _
  pushToOne := 𝟭 _
  adjOne := Adjunction.id
  pullFromTwo := 𝟭 _
  pushToTwo := 𝟭 _
  adjTwo := Adjunction.id
  tensorRight := tensor
  S1 := typeSubcats
  S2 := typeSubcats
  SP := typeSubcats

/-- Identity scheme maps make every test context proper and flat. -/
theorem testContext_isProperFlat (tensor : Type 0 → Type 0 ⥤ Type 0) :
    (testContext tensor).IsProperFlat := by
  unfold RelativeFM.Noetherian.FMContext.IsProperFlat
  dsimp [testContext]
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Two identity transforms, followed by a constant third transform. -/
noncomputable def badConvolutionData : RelativeFM.Noetherian.ConvolutionData.{0, 1, 0}
    (D1 := Type 0) (D2 := Type 0) (D3 := Type 0)
    (DP12 := Type 0) (DP23 := Type 0) (DP13 := Type 0) where
  C12 := testContext (fun _ => 𝟭 _)
  C23 := testContext (fun _ => 𝟭 _)
  C13 := testContext (fun _ => (Functor.const (Type 0)).obj PUnit)
  sameBase12 := rfl
  sameBase13 := rfl
  sameMiddle := rfl
  sameSource := rfl
  sameTarget := rfl
  sameMiddleSubcats := rfl
  sameSourceSubcats := rfl
  sameTargetSubcats := rfl
  conv _ _ := PUnit

/-- The old bare proposition is not valid for arbitrary legal
`ConvolutionData`, even over affine Noetherian bases with proper flat families. -/
theorem bare_lemma_2_26_has_countermodel
    (h : RelativeFM.Noetherian.lemma_2_26Statement badConvolutionData
      (testContext_isProperFlat _) (testContext_isProperFlat _)
      (testContext_isProperFlat _) PUnit PUnit) : False := by
  obtain ⟨e⟩ := h
  exact PEmpty.elim ((e.app PEmpty).inv PUnit.unit)

end RelativeFM.Convolution.Counterexample

#print axioms RelativeFM.Convolution.Counterexample.testContext_isProperFlat
#print axioms RelativeFM.Convolution.Counterexample.bare_lemma_2_26_has_countermodel
