/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.Duality
import WeakApprox.GeneratorBridge
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# GL26 Lemma 5.4: external tensor product of compact generators

The main theorem is `externalTensor_compactlyGenerates`: if `P₁` and `P₂`
are compact generators in the paper's zero-detection sense, their external
tensor is compact and again detects zero objects.  This is the formulation
used in the proof of Guisado Villalgordo--Lank, Lemma 5.4 (arXiv:2609.01298v5).

The formal content includes:

* the shifted tensor/symmetry/`RHom`/pull--push Hom equivalence
  `firstPushHomEquiv` and its zero-detection corollary;
* the unit/global-sections equivalence `secondPushHomEquiv`, including the
  conversion between source-shift and target-shift vanishing;
* `CoverComparisonInput.comparisonIso`, assembled from flat base change,
  perfect pullback of `RHom`, and pseudofunctoriality of pullback;
* the full affine-cover/quasi-affine-conservativity/faithfully-flat-cover
  argument in `isPaperGenerator_externalTensor`;
* the perfect-tensor and perfect-compact wrapper theorems.

The categories are parameters intended to be instantiated by the relevant
`D_qc` categories.  Their derived six-functor packages come from
`Scheme/Duality.lean`; this file does not pretend that Mathlib already has a
concrete derived tensor on schemes.  The residual geometry is explicitly
packaged in `CoverComparisonInput` and `ProductPerfectCompactInput`.

`externalTensor_isGenerator_of_upgrade` records the stronger separation form.
No general equivalence between zero detection and `IsGenerator` is claimed:
`WeakApprox/GeneratorBridge.lean` explains the ghost-morphism obstruction.
The compact-generation conclusion of the main theorem therefore uses the
paper's exact `IsPaperGenerator` predicate, not a silently weakened alias of
`IsGenerator`.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox
open scoped ZeroObject MonoidalCategory

universe v u

namespace Lemma54

variable {D₁ D : Type u} [Category.{v} D₁] [Category.{v} D]
  [HasZeroObject D₁] [HasZeroObject D] [Preadditive D₁] [Preadditive D]
  [HasShift D₁ ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D₁] [Pretriangulated D]
  {T₁ : DerivedTensorHomData D₁} {T : DerivedTensorHomData D}
  (g₁ : DerivedMorphismData T₁ T) (g₁t : TriangulatedMorphismData g₁)
  (Tt : TriangulatedTensorHomData T)

variable (P₁ : D₁) (P₂ : D) (B E : D)

/-- The tensor factor `B` need not be a pullback for this calculation; in the
application it is `Lg₂* P₂`. -/
noncomputable def externalTensor : D := T.tensor.obj (g₁.pull.obj P₁, B)

/-- The commutation isomorphism which moves a shift from the left tensor factor
to the whole tensor product. -/
noncomputable def tensorShiftIso (n : ℤ) :
    T.tensor.obj ((g₁.pull.obj P₁)⟦n⟧, B) ≅ (externalTensor g₁ P₁ B)⟦n⟧ := by
  letI := T.monoidal
  letI := (Tt.tensorRightExact B).commShift
  exact ((T.tensorRight B).commShiftIso n).app (g₁.pull.obj P₁)

/-- The pull--push/tensor--Hom adjunction chain in GL26 Lemma 5.4, including
both the tensor symmetry and the two shift coherence isomorphisms. -/
noncomputable def firstPushHomEquiv (n : ℤ) :
    ((externalTensor g₁ P₁ B)⟦n⟧ ⟶ E) ≃
      (P₁⟦n⟧ ⟶ g₁.push.obj (T.rhomObj B E)) := by
  letI := T.monoidal
  letI := T.symmetric
  letI := (Tt.tensorRightExact B).commShift
  letI := (Tt.tensorRightExact B).isTriangulated
  letI := (Tt.tensorLeftExact B).isTriangulated
  letI := g₁t.pullExact.commShift
  letI := g₁t.pullExact.isTriangulated
  let eT := (tensorShiftIso g₁ Tt P₁ B n).homCongr (Iso.refl E)
  let eS := (T.symmetry B ((g₁.pull.obj P₁)⟦n⟧)).homCongr (Iso.refl E)
  let eP := ((g₁.pull.commShiftIso n).app P₁).symm.homCongr
    (Iso.refl (T.rhomObj B E))
  exact eT.symm.trans <| eS.symm.trans <| (T.homEquiv B _ E).trans <|
    eP.trans (g₁.pullPushAdj.homEquiv _ _)

include g₁t Tt in
@[simp] theorem firstPushHomEquiv_zero (n : ℤ) :
    firstPushHomEquiv g₁ g₁t Tt P₁ B E n 0 = 0 := by
  letI := T.monoidal
  letI := T.symmetric
  letI := (Tt.tensorRightExact B).commShift
  letI := (Tt.tensorRightExact B).isTriangulated
  letI := (Tt.tensorLeftExact B).isTriangulated
  letI := g₁t.pullExact.commShift
  letI := g₁t.pullExact.isTriangulated
  letI : (T.tensorLeft B).CommShift ℤ := (Tt.tensorLeftExact B).commShift
  letI : (T.tensorLeft B).IsTriangulated := (Tt.tensorLeftExact B).isTriangulated
  letI : (T.tensorLeft B).Additive := inferInstance
  have hT : (T.homEquiv B ((g₁.pull.obj P₁)⟦n⟧) E) 0 = 0 :=
    (T.tensorHomAdj B).homAddEquiv_zero _ _
  have hG : (g₁.pullPushAdj.homEquiv (P₁⟦n⟧) (T.rhomObj B E)) 0 = 0 :=
    g₁.pullPushAdj.homAddEquiv_zero _ _
  simp [firstPushHomEquiv, hT, hG]

include g₁t Tt in
/-- Vanishing of the external-tensor Homs implies vanishing of all Homs from
shifts of `P₁` into the first derived pushforward. -/
theorem firstPush_hom_eq_zero (n : ℤ)
    (h : ∀ f : (externalTensor g₁ P₁ B)⟦n⟧ ⟶ E, f = 0)
    (f : P₁⟦n⟧ ⟶ g₁.push.obj (T.rhomObj B E)) : f = 0 := by
  let e := firstPushHomEquiv g₁ g₁t Tt P₁ B E n
  have hf : e.symm f = 0 := h _
  have he := congrArg e hf
  rw [e.apply_symm_apply] at he
  have he0 : e 0 = 0 := by
    dsimp [e]
    apply firstPushHomEquiv_zero
  exact he.trans he0

/-! ### Source-shift versus target-shift zero detection -/

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Target-shift vanishing is equivalent to the source-shift vanishing used in
`IsPaperGenerator`. -/
theorem isZero_of_paperGenerator_of_target_shift_hom_eq_zero {P : C}
    (hP : IsPaperGenerator P) {F : C}
    (h : ∀ n : ℤ, ∀ f : P ⟶ F⟦n⟧, f = 0) : IsZero F := by
  apply hP
  intro n f
  letI : (shiftEquiv C n).functor.Additive := (inferInstance : (shiftFunctor C n).Additive)
  obtain ⟨g, rfl⟩ := ((shiftEquiv C n).toAdjunction.homEquiv P F).symm.surjective f
  rw [h _ g]
  apply Adjunction.homAddEquiv_symm_zero

/-! ### The affine-projection Hom calculation -/

section SecondPush

variable {D₂ DU DT : Type u} [Category.{v} D₂] [Category.{v} DU] [Category.{v} DT]
  [HasZeroObject D₂] [HasZeroObject DU] [HasZeroObject DT]
  [Preadditive D₂] [Preadditive DU] [Preadditive DT]
  [HasShift D₂ ℤ] [HasShift DU ℤ] [HasShift DT ℤ]
  [∀ n : ℤ, (shiftFunctor D₂ n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [∀ n : ℤ, (shiftFunctor DT n).Additive]
  [Pretriangulated D₂] [Pretriangulated DU] [Pretriangulated DT]
  {T₂ : DerivedTensorHomData D₂} {TU : DerivedTensorHomData DU}
  {TT : DerivedTensorHomData DT}
  (h₁ : DerivedMorphismData TU TT) (h₁t : TriangulatedMorphismData h₁)
  (h₂ : DerivedMorphismData T₂ TT) (h₂t : TriangulatedMorphismData h₂)
  (TTt : TriangulatedTensorHomData TT)

variable (P₂ : D₂) (B F : DT)

include h₁t h₂t TTt

/-- Global sections through an affine projection: tensoring with the unit,
`RHom`'s covariant shift compatibility, and the two pull--push adjunctions
identify maps `P₂ ⟶ Rh₂_* F[n]` with maps from the unit on `U` into
`Rh₁_* RHom(B,F)[n]`.  In the application `B = Lh₂* P₂` and `F = Lt* E`. -/
noncomputable def secondPushHomEquiv (eB : h₂.pull.obj P₂ ≅ B) (n : ℤ) :
    (P₂ ⟶ h₂.push.obj (F⟦n⟧)) ≃
      (TU.unit ⟶ h₁.push.obj ((TT.rhomObj B F)⟦n⟧)) := by
  letI := TT.monoidal
  letI := h₂t.pullExact.commShift
  letI := h₂t.pullExact.isTriangulated
  letI := h₁t.pullExact.commShift
  letI := h₁t.pullExact.isTriangulated
  letI := (TTt.rhomExact B).commShift
  letI : (TT.tensorLeft B).CommShift ℤ := (TTt.tensorLeftExact B).commShift
  letI : (TT.tensorLeft B).IsTriangulated := (TTt.tensorLeftExact B).isTriangulated
  let e₂ := (h₂.pullPushAdj.homEquiv P₂ (F⟦n⟧)).symm
  let eB' := eB.homCongr (Iso.refl (F⟦n⟧))
  let eunit := (ρ_ B).homCongr (Iso.refl (F⟦n⟧))
  let eR := (Iso.refl TT.unit).homCongr (((TT.rhom.obj (.op B)).commShiftIso n).app F)
  let eU := h₁.pullUnit.symm.homCongr (Iso.refl ((TT.rhomObj B F)⟦n⟧))
  exact e₂.trans <| eB'.trans <| eunit.symm.trans <| (TT.homEquiv B TT.unit (F⟦n⟧)).trans <|
    eR.trans <| eU.trans (h₁.pullPushAdj.homEquiv _ _)

include h₁t h₂t TTt in
@[simp] theorem secondPushHomEquiv_zero (eB : h₂.pull.obj P₂ ≅ B) (n : ℤ) :
    secondPushHomEquiv h₁ h₂ TTt P₂ B F eB n 0 = 0 := by
  letI := TT.monoidal
  letI := h₂t.pullExact.commShift
  letI := h₂t.pullExact.isTriangulated
  letI := h₁t.pullExact.commShift
  letI := h₁t.pullExact.isTriangulated
  letI := (TTt.rhomExact B).commShift
  letI : (TT.tensorLeft B).CommShift ℤ := (TTt.tensorLeftExact B).commShift
  letI : (TT.tensorLeft B).IsTriangulated := (TTt.tensorLeftExact B).isTriangulated
  letI : (TT.tensorLeft B).Additive := inferInstance
  have hT : (TT.homEquiv B TT.unit (F⟦n⟧)) 0 = 0 :=
    (TT.tensorHomAdj B).homAddEquiv_zero _ _
  have hH : (h₁.pullPushAdj.homEquiv TU.unit ((TT.rhomObj B F)⟦n⟧)) 0 = 0 :=
    h₁.pullPushAdj.homAddEquiv_zero _ _
  have hTwo : (h₂.pullPushAdj.homEquiv P₂ (F⟦n⟧)).symm 0 = 0 :=
    h₂.pullPushAdj.homAddEquiv_symm_zero _ _
  simp [secondPushHomEquiv, hT, hH, hTwo]

include h₁t h₂t TTt in
/-- If `Rh₁_* RHom(B,F)` is zero, then every map `P₂ ⟶ Rh₂_* F[n]`
vanishes. -/
theorem secondPush_hom_eq_zero (R : DT) (hR : R = TT.rhomObj B F)
    (eB : h₂.pull.obj P₂ ≅ B) (hz : IsZero (h₁.push.obj R)) (n : ℤ)
    (f : P₂ ⟶ h₂.push.obj (F⟦n⟧)) : f = 0 := by
  subst R
  let e := secondPushHomEquiv h₁ h₂ TTt P₂ B F eB n
  letI := h₁t.pushExact.commShift
  letI := h₁t.pushExact.isTriangulated
  have hzshift : IsZero ((h₁.push.obj (TT.rhomObj B F))⟦n⟧) :=
    (shiftFunctor DU n).map_isZero hz
  have hz' : IsZero (h₁.push.obj ((TT.rhomObj B F)⟦n⟧)) :=
    hzshift.of_iso ((h₁.push.commShiftIso n).app (TT.rhomObj B F))
  have he : e f = 0 := hz'.eq_of_tgt _ _
  have he0 : e 0 = 0 := by
    simpa [e] using (secondPushHomEquiv_zero h₁ h₁t h₂ h₂t TTt P₂ B F eB n)
  exact e.injective (he.trans he0.symm)

include h₁t h₂t TTt in
/-- The second compact-generation step in GL26 Lemma 5.4. -/
theorem secondPush_isZero (eB : h₂.pull.obj P₂ ≅ B) (hP₂ : IsPaperGenerator P₂)
    (hz : IsZero (h₁.push.obj (TT.rhomObj B F))) : IsZero (h₂.push.obj F) := by
  apply isZero_of_paperGenerator_of_target_shift_hom_eq_zero hP₂
  letI := h₂t.pushExact.commShift
  intro n f
  rw [← cancel_mono ((h₂.push.commShiftIso n).app F).inv]
  simpa using (secondPush_hom_eq_zero h₁ h₁t h₂ h₂t TTt P₂ B F
    (TT.rhomObj B F) rfl eB hz n (f ≫ ((h₂.push.commShiftIso n).app F).inv))

end SecondPush

/-! ### The cover square and compactness inputs -/

section Main

variable {D₁ D₂ DP DU DT : Type u}
  [Category.{v} D₁] [Category.{v} D₂] [Category.{v} DP]
  [Category.{v} DU] [Category.{v} DT]
  [HasZeroObject D₁] [HasZeroObject D₂] [HasZeroObject DP]
  [HasZeroObject DU] [HasZeroObject DT]
  [Preadditive D₁] [Preadditive D₂] [Preadditive DP] [Preadditive DU] [Preadditive DT]
  [HasShift D₁ ℤ] [HasShift D₂ ℤ] [HasShift DP ℤ] [HasShift DU ℤ] [HasShift DT ℤ]
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [∀ n : ℤ, (shiftFunctor D₂ n).Additive]
  [∀ n : ℤ, (shiftFunctor DP n).Additive] [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [∀ n : ℤ, (shiftFunctor DT n).Additive]
  [Pretriangulated D₁] [Pretriangulated D₂] [Pretriangulated DP]
  [Pretriangulated DU] [Pretriangulated DT]
  {T₁ : DerivedTensorHomData D₁} {T₂ : DerivedTensorHomData D₂}
  {TP : DerivedTensorHomData DP} {TU : DerivedTensorHomData DU}
  {TT : DerivedTensorHomData DT}
  (g₁ : DerivedMorphismData T₁ TP) (g₂ : DerivedMorphismData T₂ TP)
  (s : DerivedMorphismData T₁ TU) (t : DerivedMorphismData TP TT)
  (h₁ : DerivedMorphismData TU TT) (h₂ : DerivedMorphismData T₂ TT)

/-- The geometric part of the cover argument in GL26 Lemma 5.4.  The flat
base-change isomorphism is Stacks 08IR in the flat case; `pullComp` is
pseudofunctoriality of derived pullback.  The two conservativity fields are
respectively GL26 Lemma 3.2 for the quasi-affine `h₂`, and conservativity of
derived pullback along a faithfully flat cover. -/
structure CoverComparisonInput where
  /-- `Ls* Rg₁* ≅ Rh₁* Lt*` (flat base change). -/
  flatBaseChange : g₁.push ⋙ s.pull ≅ t.pull ⋙ h₁.push
  /-- `Lt* Lg₂* ≅ Lh₂*` (composition of derived pullbacks). -/
  pullComp : g₂.pull ⋙ t.pull ≅ h₂.pull
  /-- GL26 Lemma 3.2: `Rh₂*` is conservative because `h₂` is quasi-affine. -/
  h₂_push_reflectsZero : ∀ {F : DT}, IsZero (h₂.push.obj F) → IsZero F
  /-- `Lt*` is conservative because the cover is faithfully flat. -/
  t_pull_reflectsZero : ∀ {E : DP}, IsZero (t.pull.obj E) → IsZero E

namespace CoverComparisonInput

variable (C : CoverComparisonInput g₁ g₂ s t h₁ h₂)

/-- Pullback of internal Hom along `t`, with its perfect-first-variable
hypothesis kept explicit (GL26 `lem:gortz_wedhorn_internal_hom`). -/
noncomputable def pullRHomIso {P : DP} (hP : t.Perf P) (E : DP) :
    t.pull.obj (TP.rhomObj P E) ≅ TT.rhomObj (t.pull.obj P) (t.pull.obj E) := by
  letI := t.pullRHom_isIso_of_perfect P hP
  exact asIso ((t.pullRHom P).app E)

/-- The comparison which transports the first pushforward vanishing along the
affine cover.  It is assembled from flat base change, perfect pullback of
`RHom`, and the composition isomorphism for derived pullbacks. -/
noncomputable def comparisonIso {P₂ : D₂} (hP : t.Perf (g₂.pull.obj P₂)) (E : DP) :
    s.pull.obj (g₁.push.obj (TP.rhomObj (g₂.pull.obj P₂) E)) ≅
      h₁.push.obj (TT.rhomObj (h₂.pull.obj P₂) (t.pull.obj E)) := by
  exact (C.flatBaseChange.app (TP.rhomObj (g₂.pull.obj P₂) E)) ≪≫
    h₁.push.mapIso (pullRHomIso t hP E) ≪≫
    h₁.push.mapIso ((TT.rhom.mapIso (C.pullComp.app P₂).op).symm.app (t.pull.obj E))

end CoverComparisonInput

/-- The perfect/compact calculus used in the first sentence of GL26 Lemma
5.4.  Compact objects are perfect (Stacks 09M1 in the qcqs scheme case),
derived pullbacks and derived tensor preserve perfectness, and perfect objects
are compact (Stacks 09M8).  These are geometric closure facts, not axioms
about the particular external-tensor generator. -/
structure ProductPerfectCompactInput where
  /-- Compact objects on the first factor are perfect. -/
  perfect_of_compact₁ : ∀ {P : D₁}, IsCompactAb P → g₁.Perf P
  /-- Compact objects on the second factor are perfect. -/
  perfect_of_compact₂ : ∀ {P : D₂}, IsCompactAb P → g₂.Perf P
  /-- `Lg₁*` preserves perfect complexes. -/
  pull_perfect₁ : ∀ {P : D₁}, g₁.Perf P → t.Perf (g₁.pull.obj P)
  /-- `Lg₂*` preserves perfect complexes. -/
  pull_perfect₂ : ∀ {P : D₂}, g₂.Perf P → t.Perf (g₂.pull.obj P)
  /-- Derived tensor preserves perfect complexes. -/
  tensor_perfect : ∀ {A B : DP}, t.Perf A → t.Perf B → t.Perf (TP.tensor.obj (A, B))
  /-- Every perfect object on the product is compact. -/
  perfect_compact : ∀ {G : DP}, t.Perf G → IsCompactAb G

namespace ProductPerfectCompactInput

variable (I : ProductPerfectCompactInput g₁ g₂ t)

include I

/-- Tensor of two perfect objects is perfect, in the exact product
instantiation needed by Lemma 5.4. -/
theorem externalTensor_perfect {P₁ : D₁} {P₂ : D₂}
    (hP₁ : g₁.Perf P₁) (hP₂ : g₂.Perf P₂) :
    t.Perf (externalTensor g₁ P₁ (g₂.pull.obj P₂)) :=
  ProductPerfectCompactInput.tensor_perfect I
    (ProductPerfectCompactInput.pull_perfect₁ I hP₁)
    (ProductPerfectCompactInput.pull_perfect₂ I hP₂)

/-- A perfect external tensor is compact. -/
theorem externalTensor_compact_of_perfect {P₁ : D₁} {P₂ : D₂}
    (hP : t.Perf (externalTensor g₁ P₁ (g₂.pull.obj P₂))) :
    IsCompactAb (externalTensor g₁ P₁ (g₂.pull.obj P₂)) :=
  ProductPerfectCompactInput.perfect_compact I hP

/-- Compact generators on the two factors give a perfect, hence compact,
external tensor on the product. -/
theorem externalTensor_compact {P₁ : D₁} {P₂ : D₂}
    (hP₁ : IsCompactAb P₁) (hP₂ : IsCompactAb P₂) :
    IsCompactAb (externalTensor g₁ P₁ (g₂.pull.obj P₂)) :=
  externalTensor_compact_of_perfect g₁ g₂ t I
    (externalTensor_perfect g₁ g₂ t I
      (ProductPerfectCompactInput.perfect_of_compact₁ I hP₁)
      (ProductPerfectCompactInput.perfect_of_compact₂ I hP₂))

/-- The perfectness needed for pulling back `RHom` along the cover. -/
theorem secondFactor_pull_perfect {P₂ : D₂} (hP₂ : IsCompactAb P₂) :
    t.Perf (g₂.pull.obj P₂) :=
  ProductPerfectCompactInput.pull_perfect₂ I
    (ProductPerfectCompactInput.perfect_of_compact₂ I hP₂)

end ProductPerfectCompactInput

/-- **GL26 Lemma 5.4: zero detection on the product.**  This is the full
cover argument.  Only the named flat-base-change, conservativity,
quasi-affineness and perfect/compact inputs remain geometric; all Hom
adjunctions, shift coherences and transports along isomorphisms are proved. -/
theorem isPaperGenerator_externalTensor
    (g₁t : TriangulatedMorphismData g₁) (st : TriangulatedMorphismData s)
    (h₁t : TriangulatedMorphismData h₁) (h₂t : TriangulatedMorphismData h₂)
    (TPt : TriangulatedTensorHomData TP) (TTt : TriangulatedTensorHomData TT)
    (C : CoverComparisonInput g₁ g₂ s t h₁ h₂)
    (I : ProductPerfectCompactInput g₁ g₂ t)
    {P₁ : D₁} {P₂ : D₂} (hP₁ : IsCompactAb P₁) (hP₂ : IsCompactAb P₂)
    (hgen₁ : IsPaperGenerator P₁) (hgen₂ : IsPaperGenerator P₂) (E : DP)
    (hE : ∀ n : ℤ, ∀ f : (externalTensor g₁ P₁ (g₂.pull.obj P₂))⟦n⟧ ⟶ E, f = 0) :
    IsZero E := by
  letI := st.pullExact.commShift
  letI := st.pullExact.isTriangulated
  have hz₁ : IsZero (g₁.push.obj (TP.rhomObj (g₂.pull.obj P₂) E)) := by
    apply hgen₁
    intro n f
    exact firstPush_hom_eq_zero g₁ g₁t TPt P₁ (g₂.pull.obj P₂) E n
      (fun k => hE n k) f
  have hzpull : IsZero (s.pull.obj (g₁.push.obj (TP.rhomObj (g₂.pull.obj P₂) E))) :=
    s.pull.map_isZero hz₁
  have hzcover : IsZero
      (h₁.push.obj (TT.rhomObj (h₂.pull.obj P₂) (t.pull.obj E))) :=
    hzpull.of_iso (CoverComparisonInput.comparisonIso g₁ g₂ s t h₁ h₂ C
      (ProductPerfectCompactInput.secondFactor_pull_perfect g₁ g₂ t I hP₂) E).symm
  have hz₂ : IsZero (h₂.push.obj (t.pull.obj E)) :=
    secondPush_isZero h₁ h₁t h₂ h₂t TTt P₂
      (h₂.pull.obj P₂) (t.pull.obj E) (Iso.refl _)
      hgen₂ hzcover
  exact C.t_pull_reflectsZero (C.h₂_push_reflectsZero hz₂)

/-- **GL26 Lemma 5.4, compact-generation form in the paper's zero-detection
sense.** -/
theorem externalTensor_compactlyGenerates
    (g₁t : TriangulatedMorphismData g₁) (st : TriangulatedMorphismData s)
    (h₁t : TriangulatedMorphismData h₁) (h₂t : TriangulatedMorphismData h₂)
    (TPt : TriangulatedTensorHomData TP) (TTt : TriangulatedTensorHomData TT)
    (C : CoverComparisonInput g₁ g₂ s t h₁ h₂)
    (I : ProductPerfectCompactInput g₁ g₂ t)
    {P₁ : D₁} {P₂ : D₂} (hP₁ : IsCompactAb P₁) (hP₂ : IsCompactAb P₂)
    (hgen₁ : IsPaperGenerator P₁) (hgen₂ : IsPaperGenerator P₂) :
    IsCompactAb (externalTensor g₁ P₁ (g₂.pull.obj P₂)) ∧
      IsPaperGenerator (externalTensor g₁ P₁ (g₂.pull.obj P₂)) := by
  refine ⟨ProductPerfectCompactInput.externalTensor_compact g₁ g₂ t I hP₁ hP₂, ?_⟩
  intro E hE
  exact isPaperGenerator_externalTensor g₁ g₂ s t h₁ h₂ g₁t st h₁t h₂t
    TPt TTt C I hP₁ hP₂ hgen₁ hgen₂ E hE

/-- Compact generation in the repo's stronger morphism-separation sense,
conditionally on the additional zero-detection/separation upgrade.  No such
upgrade is claimed in general: see `GeneratorBridge.lean`. -/
theorem externalTensor_isGenerator_of_upgrade
    (g₁t : TriangulatedMorphismData g₁) (st : TriangulatedMorphismData s)
    (h₁t : TriangulatedMorphismData h₁) (h₂t : TriangulatedMorphismData h₂)
    (TPt : TriangulatedTensorHomData TP) (TTt : TriangulatedTensorHomData TT)
    (C : CoverComparisonInput g₁ g₂ s t h₁ h₂)
    (I : ProductPerfectCompactInput g₁ g₂ t)
    {P₁ : D₁} {P₂ : D₂} (hP₁ : IsCompactAb P₁) (hP₂ : IsCompactAb P₂)
    (hgen₁ : IsPaperGenerator P₁) (hgen₂ : IsPaperGenerator P₂)
    (upgrade : IsPaperGenerator (externalTensor g₁ P₁ (g₂.pull.obj P₂)) →
      IsGenerator (externalTensor g₁ P₁ (g₂.pull.obj P₂))) :
    IsGenerator (externalTensor g₁ P₁ (g₂.pull.obj P₂)) :=
  upgrade (externalTensor_compactlyGenerates g₁ g₂ s t h₁ h₂ g₁t st h₁t h₂t
    TPt TTt C I hP₁ hP₂ hgen₁ hgen₂).2

end Main

end Lemma54
end RelativeFM

#print axioms RelativeFM.Lemma54.firstPushHomEquiv
#print axioms RelativeFM.Lemma54.secondPushHomEquiv
#print axioms RelativeFM.Lemma54.CoverComparisonInput.comparisonIso
#print axioms RelativeFM.Lemma54.ProductPerfectCompactInput.externalTensor_compact
#print axioms RelativeFM.Lemma54.externalTensor_compactlyGenerates
