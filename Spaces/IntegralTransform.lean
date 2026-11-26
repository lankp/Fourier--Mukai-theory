/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Functors
import StacksFrontier.AlgebraicGeometry.Spaces.Limits

/-!
# Integral transforms over algebraic spaces

GL26 §2.3 (`sec:prelim_fm_setup`): for algebraic spaces `Y₁`, `Y₂` over the base and a
kernel `K ∈ D(Y₁ ×_S Y₂)`, the integral transform
`Φ_K = Rp₂_*(Lp₁^*(-) ⊗^L K) : D(Y₁) ⥤ D(Y₂)`, where `p₁`, `p₂` are the two projections.

* `fibreProduct Y₁ Y₂` is `Y₁ ×_S Y₂`: AxiomMath's `AlgebraicSpaces.product`, the presheaf
  product (a presheaf on `(Sch/S)_fppf`, so the product is the fibre product over `S`), which
  is a product in `AlgebraicSpaces B S hS` (`AlgebraicSpaces.isLimitBinaryFanProduct`,
  Stacks 02X0).  `proj₁`, `proj₂` are its projections.
* `transform K` is `Φ_K` on all of `D(𝒪)`.
* `transformOver g₁ g₂ K` is the same construction for `Y₁ ×_Z Y₂` along `g₁ : Y₁ ⟶ Z`,
  `g₂ : Y₂ ⟶ Z` (the pullback in `AlgebraicSpaces B S hS`, AxiomMath's `hasPullbacks`), for
  the relative setting of `setup:fm_cube_pullback`.

GL26 considers `Φ_K` on `D_qc`; that `Φ_K` preserves `D_qc` (for `K ∈ D_qc` and
`Y₁ ×_S Y₂ → Y₂` qcqs) follows from the tagged inputs 08F4, 08F5 and 08FA
(`Spaces/AxiomMathInputs.lean`) and is not needed for the definition.

Proved here: `Φ_0` is a zero functor (`isZero_transform_of_isZero`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `Y₁ ×_S Y₂` (GL26 §2.3): AxiomMath's product of algebraic spaces over `S`. -/
abbrev fibreProduct (Y₁ Y₂ : AlgebraicSpaces B S hS) : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.product B S hS Y₁ Y₂

/-- The first projection `p₁ : Y₁ ×_S Y₂ ⟶ Y₁`. -/
def proj₁ (Y₁ Y₂ : AlgebraicSpaces B S hS) : fibreProduct Y₁ Y₂ ⟶ Y₁ :=
  ObjectProperty.homMk (prod.fst : Y₁.obj ⨯ Y₂.obj ⟶ Y₁.obj)

/-- The second projection `p₂ : Y₁ ×_S Y₂ ⟶ Y₂`. -/
def proj₂ (Y₁ Y₂ : AlgebraicSpaces B S hS) : fibreProduct Y₁ Y₂ ⟶ Y₂ :=
  ObjectProperty.homMk (prod.snd : Y₁.obj ⨯ Y₂.obj ⟶ Y₂.obj)

/-- `(Y₁ ×_S Y₂, p₁, p₂)` is a product in `AlgebraicSpaces B S hS` (Stacks 02X0). -/
def isLimitFibreProduct (Y₁ Y₂ : AlgebraicSpaces B S hS) :
    IsLimit (BinaryFan.mk (proj₁ Y₁ Y₂) (proj₂ Y₁ Y₂)) :=
  AlgebraicSpaces.isLimitBinaryFanProduct B S hS Y₁ Y₂

/-- The functor `E ↦ Rq_*(Lp^*E ⊗^L K)` for a span `Y₁ ←p− W −q→ Y₂` and `K ∈ D(W)`. -/
def spanTransform {Y₁ Y₂ W : AlgebraicSpaces B S hS} (p : W ⟶ Y₁) (q : W ⟶ Y₂)
    (K : D B S hS W) : D B S hS Y₁ ⥤ D B S hS Y₂ :=
  pull p ⋙ (tensor W).flip.obj K ⋙ push q

theorem spanTransform_obj {Y₁ Y₂ W : AlgebraicSpaces B S hS} (p : W ⟶ Y₁) (q : W ⟶ Y₂)
    (K : D B S hS W) (E : D B S hS Y₁) :
    (spanTransform p q K).obj E = (push q).obj (tensorObj ((pull p).obj E) K) := rfl

/-- **The integral transform** `Φ_K = Rp₂_*(Lp₁^*(-) ⊗^L K) : D(Y₁) ⥤ D(Y₂)` with kernel
`K ∈ D(Y₁ ×_S Y₂)` (GL26 §2.3, `sec:prelim_fm_setup`). -/
def transform {Y₁ Y₂ : AlgebraicSpaces B S hS} (K : D B S hS (fibreProduct Y₁ Y₂)) :
    D B S hS Y₁ ⥤ D B S hS Y₂ :=
  spanTransform (proj₁ Y₁ Y₂) (proj₂ Y₁ Y₂) K

/-- The integral transform relative to a base space `Z`: kernel on the fibre product
`Y₁ ×_Z Y₂` (pullback in `AlgebraicSpaces B S hS`) of `g₁ : Y₁ ⟶ Z` and `g₂ : Y₂ ⟶ Z`. -/
def transformOver {Y₁ Y₂ Z : AlgebraicSpaces B S hS} (g₁ : Y₁ ⟶ Z) (g₂ : Y₂ ⟶ Z)
    (K : D B S hS (pullback g₁ g₂)) : D B S hS Y₁ ⥤ D B S hS Y₂ :=
  spanTransform (pullback.fst g₁ g₂) (pullback.snd g₁ g₂) K

/-- A span transform with zero kernel sends every object to a zero object. -/
theorem isZero_spanTransform_obj {Y₁ Y₂ W : AlgebraicSpaces B S hS} (p : W ⟶ Y₁)
    (q : W ⟶ Y₂) {K : D B S hS W} (hK : IsZero K) (E : D B S hS Y₁) :
    IsZero ((spanTransform p q K).obj E) :=
  isZero_push_obj q (isZero_tensorObj_right _ hK)

/-- **`Φ_0 ≅ 0`**: the integral transform with a zero kernel is a zero functor. -/
theorem isZero_transform_of_isZero {Y₁ Y₂ : AlgebraicSpaces B S hS}
    {K : D B S hS (fibreProduct Y₁ Y₂)} (hK : IsZero K) : IsZero (transform K) :=
  Functor.isZero _ fun E => isZero_spanTransform_obj _ _ hK E

/-- The relative integral transform with a zero kernel is a zero functor. -/
theorem isZero_transformOver_of_isZero {Y₁ Y₂ Z : AlgebraicSpaces B S hS} (g₁ : Y₁ ⟶ Z)
    (g₂ : Y₂ ⟶ Z) {K : D B S hS (pullback g₁ g₂)} (hK : IsZero K) :
    IsZero (transformOver g₁ g₂ K) :=
  Functor.isZero _ fun E => isZero_spanTransform_obj _ _ hK E

end RelativeFM.Spaces
