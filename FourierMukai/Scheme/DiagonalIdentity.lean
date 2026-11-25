/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.NatIso
import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# The diagonal identity data behind GL26 Lemma 2.25

GL26's Lemma 2.25 (`lem:funct_on_kernel`) says that for a proper flat morphism
`f : Y ⟶ S` of Noetherian algebraic spaces, the transform with kernel
`RΔ_*O_Y` along the diagonal `Δ : Y ⟶ Y ×_S Y` is the identity functor on
`D_qc(Y)`.  **The lemma is correct**, and its four-line proof uses exactly three
inputs:

* the projection formula for `Δ` (Stacks 08IN);
* the derived tensor unit `O_Y ⊗^L (-) ≅ 𝟭`;
* `f'_1 ∘ Δ = f'_2 ∘ Δ = 𝟙`, i.e. functoriality of `L(-)^*` and `R(-)_*`.

Properness and flatness are not used in that computation.  In the paper they
enter elsewhere -- chiefly in bounded pseudocoherence of the kernel `RΔ_*O_Y`
(Stacks 08GK), which is what makes `RΔ_*O_Y` an admissible kernel at all.

This module isolates those three inputs as `DiagonalIdentityData` and derives
the identity transform from them (`identityIso`).  The data are *not*
consequences of a free choice of `pull`, `push` and `tensorRight`: an interface
that leaves those functors arbitrary cannot imply the lemma.  That refutation --
`FourierMukai/Paper/InterfaceAudit.lean` and the first section of
`FourierMukai/Scheme/GL26OtherTargets.lean` -- is about the interface, not about
the lemma.

The structure lives here rather than in `AffineDiagonal.lean` so that both
statement layers (`FourierMukai/Scheme/Statements.lean`,
`FourierMukai/Paper/Statements.lean`) can state Lemma 2.25 in its faithful form
and prove it.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory

universe u v

noncomputable section

/-- The geometric input for GL26 Lemma 2.25.  Here `unit` is intended to be
`O_Y`; in the affine specialization it is definitionally `affineUnit A`.

`projectionFormula` is the diagonal case of Stacks 08IN.  The other three fields
are the tensor-unit isomorphism and the two derived diagonal identities.  All
are natural isomorphisms, so their naturality, not merely objectwise existence,
is available in the proof. -/
structure DiagonalIdentityData (D DP : Type u) [Category.{v} D] [Category.{v} DP]
    (unit : D) where
  /-- `K ↦ K ⊗^L (-)` on the fibre-product category. -/
  tensorRight : DP → DP ⥤ DP
  /-- `E ↦ E ⊗^L (-)` on the source, used at the structure unit. -/
  tensorSource : D → D ⥤ D
  /-- Derived pullback along the first projection, `L(f₁')^*`. -/
  pull : D ⥤ DP
  /-- Derived pushforward along the second projection, `R(f₂')_*`. -/
  push : DP ⥤ D
  /-- `RΔ_*`; the identity kernel is `diagonal.obj unit`. -/
  diagonal : D ⥤ DP
  /-- `LΔ^*`. -/
  diagonalPull : DP ⥤ D
  /-- Stacks 08IN for `RΔ_* O_Y`: the first line of the kernel computation. -/
  projectionFormula :
    pull ⋙ tensorRight (diagonal.obj unit) ≅
      pull ⋙ diagonalPull ⋙ tensorSource unit ⋙ diagonal
  /-- The derived tensor unit `O_Y ⊗^L (-) ≅ 1`, used in line 1532 of GL26. -/
  tensorUnit : tensorSource unit ≅ 𝟭 D
  /-- Pseudofunctoriality and `f₁' ∘ Δ = 1`: `LΔ^* L(f₁')^* ≅ 1`. -/
  pull_diagonal : pull ⋙ diagonalPull ≅ 𝟭 D
  /-- Pseudofunctoriality and `f₂' ∘ Δ = 1`: `R(f₂')_* RΔ_* ≅ 1`. -/
  diagonal_push : diagonal ⋙ push ≅ 𝟭 D

namespace DiagonalIdentityData

variable {D DP : Type u} [Category.{v} D] [Category.{v} DP] {unit : D}
  (C : DiagonalIdentityData D DP unit)

/-- The objectwise GL26 Lemma 2.25 computation.  This is the promised kernel
calculation: no object is identified by fiat with the identity transform. -/
noncomputable def identityComponent (E : D) :
    C.push.obj ((C.tensorRight (C.diagonal.obj unit)).obj (C.pull.obj E)) ≅ E :=
  C.push.mapIso (C.projectionFormula.app E) ≪≫
    C.push.mapIso (C.diagonal.mapIso
      (((C.tensorSource unit).mapIso (C.pull_diagonal.app E)) ≪≫
        C.tensorUnit.app E)) ≪≫
    C.diagonal_push.app E

/-- **GL26 Lemma 2.25 (`lem:funct_on_kernel`), categorical computation.**

The explicit isomorphisms `identityComponent` assemble into a natural
isomorphism.  The proof uses exactly the naturality of the projection formula,
the two diagonal identities, and the tensor unit. -/
noncomputable def identityIso :
    C.pull ⋙ C.tensorRight (C.diagonal.obj unit) ⋙ C.push ≅ 𝟭 D := by
  refine NatIso.ofComponents C.identityComponent (naturality := ?_)
  intro X Y f
  have hp := C.projectionFormula.hom.naturality f
  have hpd := C.pull_diagonal.hom.naturality f
  have htu := C.tensorUnit.hom.naturality f
  have hdp := C.diagonal_push.hom.naturality f
  simp only [Functor.comp_map, Functor.id_map] at hp hpd htu hdp
  dsimp [identityComponent]
  simp only [Category.assoc]
  rw [← hdp]
  simp only [← C.push.map_comp_assoc]
  congr 1
  rw [reassoc_of% hp]
  apply congrArg C.push.map
  simp only [← C.diagonal.map_comp]
  rw [← (C.tensorSource unit).map_comp_assoc]
  rw [hpd]
  rw [(C.tensorSource unit).map_comp_assoc]
  rw [htu]
  simp only [Category.assoc]

/-- `identityIso` is an isomorphism onto the identity functor, not merely an
objectwise assertion. -/
theorem identity_transform_isId :
    Nonempty (C.pull ⋙ C.tensorRight (C.diagonal.obj unit) ⋙ C.push ≅ 𝟭 D) :=
  ⟨C.identityIso⟩

end DiagonalIdentityData

end

end RelativeFM
