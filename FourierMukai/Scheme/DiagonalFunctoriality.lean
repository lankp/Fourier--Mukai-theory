/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.DiagonalIdentity
import Mathlib.CategoryTheory.EqToHom

/-!
# The diagonal identities of GL26 Lemma 2.25, derived from functoriality

`DiagonalIdentityData` records `LΔ* L(f₁')* ≅ 1` and
`R(f₂')* RΔ* ≅ 1` directly.  This module derives those two fields from
identity and composition comparison isomorphisms for derived pullback and
pushforward, together with the scheme identities `Δ ≫ fᵢ' = 𝟙 Y`.
It then constructs a `DiagonalIdentityData` whose only other geometric inputs
are the projection formula (Stacks **08IN**) and the derived tensor unit.

`DerivedFunctorialityData` is the limited comparison-data interface needed for
this argument, not a claim to have formalized all coherence laws of a
pseudofunctor.  Its instances still have to be supplied by derived algebraic
geometry.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory

universe w s u v

noncomputable section

/-- A family of derived categories with derived pullback and pushforward
functors, equipped with the identity and composition comparison isomorphisms.

For `f : X ⟶ Y` and `g : Y ⟶ Z`, pullback is contravariant and pushforward is
covariant.  Thus `pullComp f g` has source `pull g ⋙ pull f`, while
`pushComp f g` has source `push f ⋙ push g`. -/
structure DerivedFunctorialityData {Spaces : Type w} [Category.{s} Spaces]
    (D : Spaces → Type u) [∀ X, Category.{v} (D X)] where
  /-- Derived pullback `Lf* : D(Y) ⥤ D(X)` for `f : X ⟶ Y`. -/
  pull {X Y : Spaces} : (X ⟶ Y) → D Y ⥤ D X
  /-- Derived pushforward `Rf* : D(X) ⥤ D(Y)` for `f : X ⟶ Y`. -/
  push {X Y : Spaces} : (X ⟶ Y) → D X ⥤ D Y
  /-- Derived pullback of an identity morphism. -/
  pullId (X : Spaces) : pull (𝟙 X) ≅ 𝟭 (D X)
  /-- Derived pushforward of an identity morphism. -/
  pushId (X : Spaces) : push (𝟙 X) ≅ 𝟭 (D X)
  /-- Composition compatibility `Lf* Lg* ≅ L(g ∘ f)*`. -/
  pullComp {X Y Z : Spaces} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull g ⋙ pull f ≅ pull (f ≫ g)
  /-- Composition compatibility `Rg* Rf* ≅ R(g ∘ f)*`. -/
  pushComp {X Y Z : Spaces} (f : X ⟶ Y) (g : Y ⟶ Z) :
    push f ⋙ push g ≅ push (f ≫ g)

namespace DerivedFunctorialityData

variable {Spaces : Type w} [Category.{s} Spaces]
  {D : Spaces → Type u} [∀ X, Category.{v} (D X)]
  (F : DerivedFunctorialityData D)

/-- A geometric retraction `p ∘ i = 1` gives `Li* Lp* ≅ 1` by
pseudofunctoriality of derived pullback. -/
def pullRetraction {X Y : Spaces} (i : X ⟶ Y) (p : Y ⟶ X)
    (h : i ≫ p = 𝟙 X) :
    F.pull p ⋙ F.pull i ≅ 𝟭 (D X) :=
  F.pullComp i p ≪≫
    eqToIso (congrArg (fun q : X ⟶ X => F.pull q) h) ≪≫
    F.pullId X

/-- A geometric retraction `p ∘ i = 1` gives `Rp* Ri* ≅ 1` by
pseudofunctoriality of derived pushforward. -/
def pushRetraction {X Y : Spaces} (i : X ⟶ Y) (p : Y ⟶ X)
    (h : i ≫ p = 𝟙 X) :
    F.push i ⋙ F.push p ≅ 𝟭 (D X) :=
  F.pushComp i p ≪≫
    eqToIso (congrArg (fun q : X ⟶ X => F.push q) h) ≪≫
    F.pushId X

end DerivedFunctorialityData

/-- Inputs for GL26 Lemma 2.25 with the two diagonal identities derived rather
than postulated.  Here `Δ : Y ⟶ P` is the diagonal and `p₁,p₂ : P ⟶ Y` are the
projections.  The functor comparisons in `F` are the pseudofunctoriality used
in the paper. -/
structure DiagonalFunctorialityInput {Spaces : Type w} [Category.{s} Spaces]
    {D : Spaces → Type u} [∀ X, Category.{v} (D X)]
    (F : DerivedFunctorialityData D) {Y P : Spaces}
    (Δ : Y ⟶ P) (p₁ p₂ : P ⟶ Y) (unit : D Y) where
  /-- `K ↦ K ⊗^L (-)` on the fibre-product category. -/
  tensorRight : D P → D P ⥤ D P
  /-- `E ↦ E ⊗^L (-)` on the source. -/
  tensorSource : D Y → D Y ⥤ D Y
  /-- The diagonal projection formula used in line one of the proof,
  Stacks **08IN**. -/
  projectionFormula :
    F.pull p₁ ⋙ tensorRight ((F.push Δ).obj unit) ≅
      F.pull p₁ ⋙ F.pull Δ ⋙ tensorSource unit ⋙ F.push Δ
  /-- The derived tensor unit `O_Y ⊗^L (-) ≅ 1`. -/
  tensorUnit : tensorSource unit ≅ 𝟭 (D Y)
  /-- The first projection is a retraction of the diagonal. -/
  diagonalPr₁ : Δ ≫ p₁ = 𝟙 Y
  /-- The second projection is a retraction of the diagonal. -/
  diagonalPr₂ : Δ ≫ p₂ = 𝟙 Y

namespace DiagonalFunctorialityInput

variable {Spaces : Type w} [Category.{s} Spaces]
  {D : Spaces → Type u} [∀ X, Category.{v} (D X)]
  {F : DerivedFunctorialityData D} {Y P : Spaces}
  {Δ : Y ⟶ P} {p₁ p₂ : P ⟶ Y} {unit : D Y}
  (I : DiagonalFunctorialityInput F Δ p₁ p₂ unit)

/-- Construct the old diagonal interface, deriving both of its retraction
fields from comparison data instead of assuming them separately. -/
def toDiagonalIdentityData : DiagonalIdentityData (D Y) (D P) unit where
  tensorRight := I.tensorRight
  tensorSource := I.tensorSource
  pull := F.pull p₁
  push := F.push p₂
  diagonal := F.push Δ
  diagonalPull := F.pull Δ
  projectionFormula := I.projectionFormula
  tensorUnit := I.tensorUnit
  pull_diagonal := F.pullRetraction Δ p₁ I.diagonalPr₁
  diagonal_push := F.pushRetraction Δ p₂ I.diagonalPr₂

/-- The identity transform for the diagonal kernel, now using only the
projection formula (Stacks 08IN), tensor unit, pseudofunctor comparison data,
and the two geometric retraction equations. -/
def identityTransformIso :
    F.pull p₁ ⋙ I.tensorRight ((F.push Δ).obj unit) ⋙ F.push p₂ ≅ 𝟭 (D Y) :=
  I.toDiagonalIdentityData.identityIso

/-- Nonempty packaging matching the repository's statement layer. -/
theorem lemma_2_25_of_functoriality :
    Nonempty (F.pull p₁ ⋙ I.tensorRight ((F.push Δ).obj unit) ⋙ F.push p₂ ≅
      𝟭 (D Y)) :=
  ⟨I.identityTransformIso⟩

end DiagonalFunctorialityInput

end

end RelativeFM

#print axioms RelativeFM.DerivedFunctorialityData.pullRetraction
#print axioms RelativeFM.DerivedFunctorialityData.pushRetraction
#print axioms RelativeFM.DiagonalFunctorialityInput.toDiagonalIdentityData
#print axioms RelativeFM.DiagonalFunctorialityInput.identityTransformIso
#print axioms RelativeFM.DiagonalFunctorialityInput.lemma_2_25_of_functoriality
