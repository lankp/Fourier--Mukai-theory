/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.DiagonalIdentity
import FourierMukai.Scheme.Duality
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# GL26 Lemma 2.25 from `DerivedMorphismData` for the projections and the diagonal

`DiagonalIdentityData` (`Scheme/DiagonalIdentity.lean`) states the lemma's three
inputs as data.  This module derives two of the three from interfaces the
repository already has:

* `DerivedDiagonalData.projectionFormula` turns
  `DerivedMorphismData.projectionFormula` -- Stacks 08IN in two-variable form, for
  the diagonal `Δ` -- into the ordered single-variable form that
  `DiagonalIdentityData` wants, using symmetry of the derived tensor; naturality
  comes from the braiding.
* `toDiagonalIdentityData` takes the tensor unit to be the monoidal right unitor,
  not a new hypothesis.
* Together with `Scheme/DiagonalFunctoriality.lean`, which derives the two
  diagonal retractions from comparison data and `Δ ≫ prᵢ = 𝟙`, the interface is
  constructible from three `DerivedMorphismData` packages, that comparison data
  and the two retraction equations.  No properness, flatness or Noetherian
  hypothesis is used.

`DerivedDiagonalInput.identityIso` is then Lemma 2.25 for such a model.
`unitCounitIso` records the separate closed-immersion corollary
`LΔ^*RΔ_*O_Y ≅ O_Y`; it is *not* a step of the paper's four-line proof, which
uses no full faithfulness of `RΔ_*`.

Found by member m3 of run `smww35xg3` (direction d1).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory

universe u v
noncomputable section

namespace FullyFaithfulAdjunction

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {L : C ⥤ D} {R : D ⥤ C}

/-- The objectwise counit isomorphism for an adjunction whose right adjoint is
fully faithful.  No triangulated or monoidal structure is needed. -/
def pullPushObjIso (adj : L ⊣ R) (hR : R.FullyFaithful) (X : D) :
    L.obj (R.obj X) ≅ X := by
  letI : R.Full := hR.full
  letI : R.Faithful := hR.faithful
  exact asIso (adj.counit.app X)

/-- The natural counit isomorphism for an adjunction whose right adjoint is
fully faithful. -/
def pullPushIso (adj : L ⊣ R) (hR : R.FullyFaithful) :
    R ⋙ L ≅ 𝟭 D := by
  letI : R.Full := hR.full
  letI : R.Faithful := hR.faithful
  exact asIso adj.counit

end FullyFaithfulAdjunction

namespace DerivedMorphismData

variable {DX DY : Type u} [Category.{v} DX] [Category.{v} DY]
  {TX : DerivedTensorHomData DX} {TY : DerivedTensorHomData DY}

/-- Specialization of the categorical counit isomorphism to `Lf^* ⊣ Rf_*`.
For a diagonal modelled by a closed immersion, full faithfulness of `push` is
the geometric input; everything else in this statement is formal. -/
def pullPushObjIso (M : DerivedMorphismData TX TY)
    (hM : M.push.FullyFaithful) (X : DY) :
    M.pull.obj (M.push.obj X) ≅ X :=
  FullyFaithfulAdjunction.pullPushObjIso M.pullPushAdj hM X

/-- The same specialization as a natural isomorphism `Lf^*Rf_* ≅ 𝟭`. -/
def pullPushIso (M : DerivedMorphismData TX TY)
    (hM : M.push.FullyFaithful) : M.push ⋙ M.pull ≅ 𝟭 DY :=
  FullyFaithfulAdjunction.pullPushIso M.pullPushAdj hM

/-- In particular, a fully faithful diagonal pushforward gives the unit
identity `LΔ^*RΔ_*O_Y ≅ O_Y`.  This is a consequence additional to, not a
step displayed in, GL26's four-line proof of Lemma 2.25. -/
def diagonalUnitIso (M : DerivedMorphismData TX TY)
    (hM : M.push.FullyFaithful) :
    M.pull.obj (M.push.obj TY.unit) ≅ TY.unit :=
  M.pullPushObjIso hM TY.unit

end DerivedMorphismData

namespace DerivedDiagonalData

variable {D DP : Type u} [Category.{v} D] [Category.{v} DP]
  (TD : DerivedTensorHomData D) (TP : DerivedTensorHomData DP)

/-- The diagonal projection formula in the right-tensor orientation used by
`DiagonalIdentityData`.  Its proof uses `DerivedMorphismData.projectionFormula`
and symmetry; no additional projection-formula axiom is introduced. -/
def projectionComponent (p₁ : DerivedMorphismData TD TP)
    (Δ : DerivedMorphismData TP TD) (E : D) :
    (TP.tensorRight (Δ.push.obj TD.unit)).obj (p₁.pull.obj E) ≅
      Δ.push.obj ((TD.tensorRight TD.unit).obj (Δ.pull.obj (p₁.pull.obj E))) :=
  (TP.symmetry (Δ.push.obj TD.unit) (p₁.pull.obj E)).symm ≪≫
    (Δ.projectionFormulaObj TD.unit (p₁.pull.obj E)).symm ≪≫
    Δ.push.mapIso (TD.symmetry (Δ.pull.obj (p₁.pull.obj E)) TD.unit).symm

/-- Naturality is supplied by the two-variable projection formula and by
naturality of the braiding. -/
def projectionFormula (p₁ : DerivedMorphismData TD TP)
    (Δ : DerivedMorphismData TP TD) :
    p₁.pull ⋙ TP.tensorRight (Δ.push.obj TD.unit) ≅
      p₁.pull ⋙ Δ.pull ⋙ TD.tensorRight TD.unit ⋙ Δ.push := by
  letI : MonoidalCategory D := TD.monoidal
  letI : SymmetricCategory D := TD.symmetric
  letI : MonoidalCategory DP := TP.monoidal
  letI : SymmetricCategory DP := TP.symmetric
  refine NatIso.ofComponents (projectionComponent TD TP p₁ Δ) (naturality := ?_)
  intro X Y f
  have hp :
      MonoidalCategoryStruct.whiskerLeft (Δ.push.obj TD.unit) (p₁.pull.map f) ≫
          Δ.projectionFormula.inv.app (TD.unit, p₁.pull.obj Y) =
        Δ.projectionFormula.inv.app (TD.unit, p₁.pull.obj X) ≫
          Δ.push.map (MonoidalCategoryStruct.whiskerLeft TD.unit
            (Δ.pull.map (p₁.pull.map f))) := by
    have h := Δ.projectionFormula.inv.naturality
      (X := (TD.unit, p₁.pull.obj X)) (Y := (TD.unit, p₁.pull.obj Y))
      (𝟙 TD.unit, p₁.pull.map f)
    simpa using h
  simp only [projectionComponent, DerivedMorphismData.projectionFormulaObj,
    DerivedTensorHomData.symmetry, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.comp_map, Category.assoc]
  change (MonoidalCategoryStruct.whiskerRight (p₁.pull.map f)
    (Δ.push.obj TD.unit)) ≫ _ = _
  rw [BraidedCategory.braiding_inv_naturality_left_assoc]
  rw [reassoc_of% hp]
  simp only [← Functor.map_comp]
  rw [BraidedCategory.braiding_inv_naturality_right]
  dsimp only [Functor.prod_obj, Functor.id_obj, DerivedTensorHomData.tensorRight,
    MonoidalCategory.tensorRight, MonoidalCategory.curriedTensor, Functor.flip]

end DerivedDiagonalData

/-- The three derived-morphism packages and the two retraction comparisons
needed by the paper's displayed proof of Lemma 2.25.  Here `D` models
`D_qc(Y)`, `DP` models `D_qc(Y ×_S Y)`, and `first`, `second`, `diagonal` model
the two projections and the diagonal.  The only projection formula used is
Stacks 08IN, already carried by `diagonal.projectionFormula`.

Full faithfulness of `diagonal.push` is deliberately *not* a field: it yields
the separate counit corollary below, but the paper's four-line transform
computation does not use it.  Properness and flatness are likewise absent. -/
structure DerivedDiagonalInput {D DP : Type u} [Category.{v} D] [Category.{v} DP]
    (TD : DerivedTensorHomData D) (TP : DerivedTensorHomData DP) where
  /-- Derived functors for the first projection `f₁'`. -/
  first : DerivedMorphismData TD TP
  /-- Derived functors for the second projection `f₂'`. -/
  second : DerivedMorphismData TD TP
  /-- Derived functors for the diagonal `Δ`. -/
  diagonal : DerivedMorphismData TP TD
  /-- Pseudofunctoriality of pullback and `f₁' ∘ Δ = 𝟙`. -/
  pull_diagonal : first.pull ⋙ diagonal.pull ≅ 𝟭 D
  /-- Pseudofunctoriality of pushforward and `f₂' ∘ Δ = 𝟙`. -/
  diagonal_push : diagonal.push ⋙ second.push ≅ 𝟭 D

namespace DerivedDiagonalInput

variable {D DP : Type u} [Category.{v} D] [Category.{v} DP]
  {TD : DerivedTensorHomData D} {TP : DerivedTensorHomData DP}
  (C : DerivedDiagonalInput TD TP)

/-- Package the derived-morphism inputs as the repository's existing diagonal
interface.  The tensor unit is the monoidal right unitor, not a new axiom. -/
def toDiagonalIdentityData : DiagonalIdentityData D DP TD.unit where
  tensorRight := TP.tensorRight
  tensorSource := TD.tensorRight
  pull := C.first.pull
  push := C.second.push
  diagonal := C.diagonal.push
  diagonalPull := C.diagonal.pull
  projectionFormula := DerivedDiagonalData.projectionFormula TD TP C.first C.diagonal
  tensorUnit := by
    letI : MonoidalCategory D := TD.monoidal
    exact MonoidalCategory.rightUnitorNatIso D
  pull_diagonal := C.pull_diagonal
  diagonal_push := C.diagonal_push

/-- GL26 Lemma 2.25 for a derived-morphism model.  The transform is naturally
isomorphic to the identity functor, not merely objectwise isomorphic. -/
def identityIso :
    C.first.pull ⋙ TP.tensorRight (C.diagonal.push.obj TD.unit) ⋙ C.second.push ≅
      𝟭 D :=
  C.toDiagonalIdentityData.identityIso

theorem identity_transform_isId :
    Nonempty (C.first.pull ⋙ TP.tensorRight (C.diagonal.push.obj TD.unit) ⋙
      C.second.push ≅ 𝟭 D) :=
  ⟨C.identityIso⟩

/-- The independent closed-immersion/counit corollary.  A geometric model must
supply full faithfulness of derived diagonal pushforward; no assumption is made
here that an arbitrary `DerivedMorphismData` has this property. -/
def unitCounitIso (hΔ : C.diagonal.push.FullyFaithful) :
    C.diagonal.pull.obj (C.diagonal.push.obj TD.unit) ≅ TD.unit :=
  C.diagonal.diagonalUnitIso hΔ

end DerivedDiagonalInput

#print axioms RelativeFM.FullyFaithfulAdjunction.pullPushObjIso
#print axioms RelativeFM.DerivedDiagonalData.projectionFormula
#print axioms RelativeFM.DerivedDiagonalInput.identityIso
#print axioms RelativeFM.DerivedDiagonalInput.unitCounitIso

end
end RelativeFM
