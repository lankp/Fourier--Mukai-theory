/-
Copyright (c) 2026 Formalization of Relative Fourier--Mukai theory.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.Duality
import FourierMukai.Scheme.Statements
import FourierMukai.Scheme.Affine
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# GL26 Lemma 2.26: convolution of Fourier--Mukai kernels

This file supplies the categorical calculation missing from the statement layer.
`RelativeFM.Noetherian.ConvolutionData` has only an unrelated object-level
operation `conv`, so its displayed Lemma 2.26 proposition is not derivable from
properness and flatness.  Here the triple fibre product and the compatibility
of its derived functors are explicit.

The theorem `convolution_transform` proves
`Φ_{K₂} ∘ Φ_{K₁} ≅ Φ_{K₂ ⋆ K₁}` from the two projection formulas, monoidality of
derived pullback, pseudofunctoriality, and invertibility of the canonical
base-change mate.  The last condition is Stacks Tag 08IR for a tor-independent
square (flatness of the three structure morphisms gives tor-independence in the
geometric application).  No field of the input structure asserts the conclusion.

The proof is functor-level throughout.  In particular, it does not choose a
pointwise isomorphism and then attempt to infer naturality.
-/

@[expose] public section

namespace RelativeFM.Convolution

open CategoryTheory
open scoped MonoidalCategory

universe v u

/-! ## Specializations of bifunctorial isomorphisms -/

section Specializations

variable {DX DY : Type u} [Category.{v} DX] [Category.{v} DY]
  {TX : DerivedTensorHomData DX} {TY : DerivedTensorHomData DY}

/-- Monoidality of derived pullback with the second tensor factor fixed. -/
def pullTensorRight (M : DerivedMorphismData TX TY) (K : DX) :
    M.pull ⋙ TY.tensorRight (M.pull.obj K) ≅ TX.tensorRight K ⋙ M.pull :=
  NatIso.ofComponents (fun X => M.pullTensor.app (X, K)) (by
    intro X Y f
    simpa using M.pullTensor.hom.naturality ((f, 𝟙 K) : (X, K) ⟶ (Y, K)))

/-- The projection formula with the object on the base fixed. -/
def projectionFormulaRight (M : DerivedMorphismData TX TY) (K : DX) :
    TY.tensorRight (M.pull.obj K) ⋙ M.push ≅ M.push ⋙ TX.tensorRight K :=
  NatIso.ofComponents (fun F => M.projectionFormulaObj F K) (by
    intro F F' f
    simpa [DerivedMorphismData.projectionFormulaObj] using
      M.projectionFormula.hom.naturality ((f, 𝟙 K) : (F, K) ⟶ (F', K)))

/-- Symmetry with the second tensor factor fixed. -/
def symmetryRight {D : Type u} [Category.{v} D]
    (T : DerivedTensorHomData D) (F : D) : T.tensorRight F ≅ T.tensorLeft F := by
  letI := T.monoidal
  letI := T.symmetric
  exact NatIso.ofComponents (fun X => β_ X F)

/-- The projection formula with the object on the source fixed. -/
def projectionFormulaLeftDirect (M : DerivedMorphismData TX TY) (F : DY) :
    M.pull ⋙ TY.tensorLeft F ⋙ M.push ≅ TX.tensorLeft (M.push.obj F) :=
  NatIso.ofComponents (fun G => M.projectionFormulaObj F G) (by
    intro G G' g
    simpa [DerivedMorphismData.projectionFormulaObj] using
      M.projectionFormula.hom.naturality ((𝟙 F, g) : (F, G) ⟶ (F, G')))

/-- The projection formula with the object on the source fixed, after using
symmetry to put the variable base object on the left. -/
def projectionFormulaLeft (M : DerivedMorphismData TX TY) (F : DY) :
    M.pull ⋙ TY.tensorRight F ⋙ M.push ≅ TX.tensorRight (M.push.obj F) := by
  let e := NatIso.hcomp (NatIso.hcomp (Iso.refl M.pull) (symmetryRight TY F))
    (Iso.refl M.push)
  exact e ≪≫ projectionFormulaLeftDirect M F ≪≫ (symmetryRight TX (M.push.obj F)).symm

end Specializations

/-- The associator with the last two tensor factors fixed. -/
def associatorRight {D : Type u} [Category.{v} D]
    (T : DerivedTensorHomData D) (Y Z : D) :
    T.tensorRight Y ⋙ T.tensorRight Z ≅ T.tensorRight (T.tensor.obj (Y, Z)) := by
  letI := T.monoidal
  exact NatIso.ofComponents (fun X => α_ X Y Z)

/-! ## The derived triple fibre-product cube -/

/-- The derived functors needed for GL26 Lemma 2.26.

For `i < j`, `pij_i` and `pij_j` are the two projections from `Yᵢ ×ₛ Yⱼ`.
The functors `p123_ij` are the projections from the triple product, and
`p13_1`, `p13_3` are the projections used by the convolution transform.

`square` is the Cartesian square comparing the middle projection of `Y₁₂`, the
first projection of `Y₂₃`, and the two projections from the triple product.
Its canonical mate is the base-change transformation of Stacks Tag 08IR.
In every `DerivedMorphismData`, the fields actually used below are the
bifunctorial pullback--tensor isomorphism (Stacks 07A4), the projection formula
(Stacks 08IN), and, for the mate, the derived adjunction (Stacks 07A6). -/
structure ConvolutionCube
    (D₁ D₂ D₃ D₁₂ D₂₃ D₁₂₃ D₁₃ : Type u)
    [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃]
    [Category.{v} D₁₂] [Category.{v} D₂₃] [Category.{v} D₁₂₃] [Category.{v} D₁₃]
    (T₁ : DerivedTensorHomData D₁) (T₂ : DerivedTensorHomData D₂)
    (T₃ : DerivedTensorHomData D₃) (T₁₂ : DerivedTensorHomData D₁₂)
    (T₂₃ : DerivedTensorHomData D₂₃) (T₁₂₃ : DerivedTensorHomData D₁₂₃)
    (T₁₃ : DerivedTensorHomData D₁₃) where
  p12_1 : DerivedMorphismData T₁ T₁₂
  p12_2 : DerivedMorphismData T₂ T₁₂
  p23_2 : DerivedMorphismData T₂ T₂₃
  p23_3 : DerivedMorphismData T₃ T₂₃
  p123_12 : DerivedMorphismData T₁₂ T₁₂₃
  p123_23 : DerivedMorphismData T₂₃ T₁₂₃
  p123_13 : DerivedMorphismData T₁₃ T₁₂₃
  p13_1 : DerivedMorphismData T₁ T₁₃
  p13_3 : DerivedMorphismData T₃ T₁₃
  square : BaseChangeSquare p12_2 p123_23 p23_2 p123_12
  /-- Stacks 08IR: the canonical mate (built using the 07A6 adjunctions and
  the 0D6D pullback composition recorded in `square`) is invertible for the
  tor-independent square arising from the flat structure morphisms. -/
  [square_isIso : IsIso square.theta]
  /-- Stacks 0D6D for the two maps `Y₁₂₃ ⟶ Y₁`. -/
  pullFirst : p13_1.pull ⋙ p123_13.pull ≅ p12_1.pull ⋙ p123_12.pull
  /-- Stacks 0D6E for the two maps `Y₁₂₃ ⟶ Y₃`. -/
  pushLast : p123_23.push ⋙ p23_3.push ≅ p123_13.push ⋙ p13_3.push

namespace ConvolutionCube

variable {D₁ D₂ D₃ D₁₂ D₂₃ D₁₂₃ D₁₃ : Type u}
  [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃]
  [Category.{v} D₁₂] [Category.{v} D₂₃] [Category.{v} D₁₂₃] [Category.{v} D₁₃]
  {T₁ : DerivedTensorHomData D₁} {T₂ : DerivedTensorHomData D₂}
  {T₃ : DerivedTensorHomData D₃} {T₁₂ : DerivedTensorHomData D₁₂}
  {T₂₃ : DerivedTensorHomData D₂₃} {T₁₂₃ : DerivedTensorHomData D₁₂₃}
  {T₁₃ : DerivedTensorHomData D₁₃}
  (C : ConvolutionCube D₁ D₂ D₃ D₁₂ D₂₃ D₁₂₃ D₁₃ T₁ T₂ T₃ T₁₂ T₂₃ T₁₂₃ T₁₃)

/-- The actual convolution `K₂ ⋆ K₁` on `Y₁ ×ₛ Y₃`. -/
def convolution (K₁ : D₁₂) (K₂ : D₂₃) : D₁₃ :=
  C.p123_13.push.obj (T₁₂₃.tensor.obj
    (C.p123_12.pull.obj K₁, C.p123_23.pull.obj K₂))

/-- The invertible canonical base-change mate. -/
noncomputable def baseChangeIso :
    C.p12_2.push ⋙ C.p23_2.pull ≅ C.p123_12.pull ⋙ C.p123_23.push := by
  letI := C.square_isIso
  exact asIso C.square.theta

/-- **GL26 Lemma 2.26**, in a fully explicit derived six-functor interface.

No affine-specific hypothesis is needed: the argument is valid for Noetherian
schemes and, after the same geometric inputs are supplied, algebraic spaces.
The affine case is obtained by using the derived module categories on the four
tensor products of the three algebras. -/
noncomputable def convolution_transform (K₁ : D₁₂) (K₂ : D₂₃) :
    tensorTransform C.p12_1 C.p12_2 K₁ ⋙ tensorTransform C.p23_2 C.p23_3 K₂ ≅
      tensorTransform C.p13_1 C.p13_3 (C.convolution K₁ K₂) := by
  let W := C.p12_1.pull ⋙ T₁₂.tensorRight K₁
  let B := T₁₂₃.tensor.obj (C.p123_12.pull.obj K₁, C.p123_23.pull.obj K₂)
  let step1 := NatIso.hcomp (NatIso.hcomp (Iso.refl W) C.baseChangeIso)
    (Iso.refl (T₂₃.tensorRight K₂ ⋙ C.p23_3.push))
  let step2 := NatIso.hcomp
    (NatIso.hcomp (Iso.refl (W ⋙ C.p123_12.pull))
      (projectionFormulaRight C.p123_23 K₂).symm) (Iso.refl C.p23_3.push)
  let step3 := NatIso.hcomp
    (Iso.refl (W ⋙ C.p123_12.pull ⋙ T₁₂₃.tensorRight (C.p123_23.pull.obj K₂)))
    C.pushLast
  let step4 := NatIso.hcomp
    (NatIso.hcomp (Iso.refl C.p12_1.pull) (pullTensorRight C.p123_12 K₁).symm)
    (Iso.refl (T₁₂₃.tensorRight (C.p123_23.pull.obj K₂) ⋙
      C.p123_13.push ⋙ C.p13_3.push))
  let step5 := NatIso.hcomp
    (NatIso.hcomp (Iso.refl (C.p12_1.pull ⋙ C.p123_12.pull))
      (associatorRight T₁₂₃ (C.p123_12.pull.obj K₁) (C.p123_23.pull.obj K₂)))
    (Iso.refl (C.p123_13.push ⋙ C.p13_3.push))
  let step6 := NatIso.hcomp C.pullFirst.symm
    (Iso.refl (T₁₂₃.tensorRight B ⋙ C.p123_13.push ⋙ C.p13_3.push))
  let step7 := NatIso.hcomp
    (NatIso.hcomp (Iso.refl C.p13_1.pull) (projectionFormulaLeft C.p123_13 B))
    (Iso.refl C.p13_3.push)
  exact step1 ≪≫ step2 ≪≫ step3 ≪≫ step4 ≪≫ step5 ≪≫ step6 ≪≫ step7

/-- Proposition form used by the paper statements. -/
theorem convolution_transform_nonempty (K₁ : D₁₂) (K₂ : D₂₃) :
    Nonempty (tensorTransform C.p12_1 C.p12_2 K₁ ⋙
      tensorTransform C.p23_2 C.p23_3 K₂ ≅
        tensorTransform C.p13_1 C.p13_3 (C.convolution K₁ K₂)) :=
  ⟨C.convolution_transform K₁ K₂⟩

end ConvolutionCube



/-! ## Bridge to the existing Noetherian statement layer -/

namespace NoetherianBridge

universe w

variable {D₁ D₂ D₃ D₁₂ D₂₃ D₁₃ : Type u}
  [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃]
  [Category.{v} D₁₂] [Category.{v} D₂₃] [Category.{v} D₁₃]

/-- A correction of `RelativeFM.Noetherian.ConvolutionData` by an actual derived
triple-product cube.  The final ten fields merely identify the old statement's
free operations with the corrected ones; none is a transform isomorphism. -/
structure CorrectedConvolutionData
    (B : RelativeFM.Noetherian.ConvolutionData.{w, u, v}
      (D1 := D₁) (D2 := D₂) (D3 := D₃)
      (DP12 := D₁₂) (DP23 := D₂₃) (DP13 := D₁₃)) where
  D123 : Type u
  [cat123 : Category.{v} D123]
  T1 : DerivedTensorHomData D₁
  T2 : DerivedTensorHomData D₂
  T3 : DerivedTensorHomData D₃
  T12 : DerivedTensorHomData D₁₂
  T23 : DerivedTensorHomData D₂₃
  T123 : DerivedTensorHomData D123
  T13 : DerivedTensorHomData D₁₃
  cube : ConvolutionCube D₁ D₂ D₃ D₁₂ D₂₃ D123 D₁₃ T1 T2 T3 T12 T23 T123 T13
  tensor12_eq : B.C12.tensorRight = T12.tensorRight
  pull12_eq : B.C12.pullFromOne = cube.p12_1.pull
  push12_eq : B.C12.pushToTwo = cube.p12_2.push
  tensor23_eq : B.C23.tensorRight = T23.tensorRight
  pull23_eq : B.C23.pullFromOne = cube.p23_2.pull
  push23_eq : B.C23.pushToTwo = cube.p23_3.push
  tensor13_eq : B.C13.tensorRight = T13.tensorRight
  pull13_eq : B.C13.pullFromOne = cube.p13_1.pull
  push13_eq : B.C13.pushToTwo = cube.p13_3.push
  conv_eq : B.conv = fun K₁ K₂ => cube.convolution K₁ K₂

attribute [instance] CorrectedConvolutionData.cat123

/-- The exact proposition already stated in `Scheme/Statements.lean`, after
supplying the compatibility data missing from its bare object-level `conv`. -/
theorem lemma_2_26_of_correction
    {B : RelativeFM.Noetherian.ConvolutionData.{w, u, v}
      (D1 := D₁) (D2 := D₂) (D3 := D₃)
      (DP12 := D₁₂) (DP23 := D₂₃) (DP13 := D₁₃)}
    (E : CorrectedConvolutionData B)
    (h12 : B.C12.IsProperFlat) (h23 : B.C23.IsProperFlat) (h13 : B.C13.IsProperFlat)
    (K₁ : D₁₂) (K₂ : D₂₃) :
    RelativeFM.Noetherian.lemma_2_26Statement B h12 h23 h13 K₁ K₂ := by
  unfold RelativeFM.Noetherian.lemma_2_26Statement
  unfold RelativeFM.Noetherian.FMContext.transform
  rw [E.tensor12_eq, E.pull12_eq, E.push12_eq,
    E.tensor23_eq, E.pull23_eq, E.push23_eq,
    E.tensor13_eq, E.pull13_eq, E.push13_eq, E.conv_eq]
  exact E.cube.convolution_transform_nonempty K₁ K₂

end NoetherianBridge

/-! ## The affine model -/

open scoped TensorProduct

/-- Derived modules on `Spec (A ⊗[R] B)`, modelling the derived category on the
fibre product of two affine families. -/
abbrev AffinePairD (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] : Type (u + 1) := AffineD (A ⊗[R] B)

/-- The chosen associated model of the triple affine fibre product. -/
abbrev AffineTripleD (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [Algebra R A] [Algebra R B] [Algebra R C] : Type (u + 1) :=
  AffineD ((A ⊗[R] B) ⊗[R] C)

/-- The derived cube over `Spec R` for three affine families `Spec A`, `Spec B`,
and `Spec C`.  The ordinary tensor products fix the meaning of every category;
the fields of `cube` are the remaining derived-geometric inputs. -/
structure AffineConvolutionInput (R A B C : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] where
  T1 : DerivedTensorHomData (AffineD A)
  T2 : DerivedTensorHomData (AffineD B)
  T3 : DerivedTensorHomData (AffineD C)
  T12 : DerivedTensorHomData (AffinePairD R A B)
  T23 : DerivedTensorHomData (AffinePairD R B C)
  T123 : DerivedTensorHomData (AffineTripleD R A B C)
  T13 : DerivedTensorHomData (AffinePairD R A C)
  cube : ConvolutionCube (AffineD A) (AffineD B) (AffineD C)
    (AffinePairD R A B) (AffinePairD R B C) (AffineTripleD R A B C)
    (AffinePairD R A C) T1 T2 T3 T12 T23 T123 T13

namespace AffineConvolutionInput

variable {R A B C : Type u}
  [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  (X : AffineConvolutionInput R A B C)

/-- **GL26 Lemma 2.26 for affine families.**  Noetherianness, properness and
flatness are used by the geometric construction of `X.cube` (in particular to
invoke Stacks 08IR), but are not needed for this categorical deduction. -/
noncomputable def affine_convolution_transform
    (K₁ : AffinePairD R A B) (K₂ : AffinePairD R B C) :
    tensorTransform X.cube.p12_1 X.cube.p12_2 K₁ ⋙
      tensorTransform X.cube.p23_2 X.cube.p23_3 K₂ ≅
    tensorTransform X.cube.p13_1 X.cube.p13_3 (X.cube.convolution K₁ K₂) :=
  X.cube.convolution_transform K₁ K₂

/-- Proposition form of `affine_convolution_transform`. -/
theorem affine_lemma_2_26
    (K₁ : AffinePairD R A B) (K₂ : AffinePairD R B C) :
    Nonempty (tensorTransform X.cube.p12_1 X.cube.p12_2 K₁ ⋙
      tensorTransform X.cube.p23_2 X.cube.p23_3 K₂ ≅
    tensorTransform X.cube.p13_1 X.cube.p13_3 (X.cube.convolution K₁ K₂)) :=
  ⟨X.affine_convolution_transform K₁ K₂⟩

end AffineConvolutionInput

end RelativeFM.Convolution

#print axioms RelativeFM.Convolution.pullTensorRight
#print axioms RelativeFM.Convolution.projectionFormulaRight
#print axioms RelativeFM.Convolution.projectionFormulaLeft
#print axioms RelativeFM.Convolution.associatorRight
#print axioms RelativeFM.Convolution.ConvolutionCube.convolution_transform
#print axioms RelativeFM.Convolution.ConvolutionCube.convolution_transform_nonempty
#print axioms RelativeFM.Convolution.AffineConvolutionInput.affine_convolution_transform
#print axioms RelativeFM.Convolution.AffineConvolutionInput.affine_lemma_2_26
#print axioms RelativeFM.Convolution.NoetherianBridge.lemma_2_26_of_correction
