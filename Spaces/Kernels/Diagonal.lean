/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Kernels.Basic
import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# GL26 Lemma 2.25 (`lem:funct_on_kernel`) over algebraic spaces

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), §2.3,
`sec:funct_on_kernel`, **Lemma 2.25**: for a proper flat morphism `f : Y → S` of Noetherian
algebraic spaces, with diagonal `Δ : Y → Y ×_S Y`,

`Φ_{RΔ_* 𝒪_Y} ≅ id_{D_qc(Y)}`.

## Proof (the paper's)

With `p₁, p₂ : Y ×_S Y ⟶ Y` the projections,
`Φ_{RΔ_*𝒪_Y}(E) = Rp₂_*(Lp₁^*E ⊗^L RΔ_*𝒪_Y) ≅ Rp₂_*RΔ_*(LΔ^*Lp₁^*E ⊗^L 𝒪_Y)` (projection formula,
Stacks 08IN, for `Δ`) `≅ R(p₂Δ)_* L(p₁Δ)^* E = E`.  Here the natural transformation
`diagTrans : Φ_{RΔ_*𝒪_Y} ⟶ 𝟭` is built on all of `D(𝒪_Y)` from

* the symmetry of `⊗^L` (`tensorBraiding`), to put the kernel on the left as in AxiomMath's
  projection map;
* the projection map for `Δ` at `𝒪_Y`, natural in the pulled-back variable (`projNatRight`);
* the unit law `𝒪_Y ⊗^L - ≅ -` (`tensorLeftUnitor`);
* the pseudofunctoriality of `L(-)^*` and `R(-)_*` (`pullComp`, `pushComp`, Stacks 0D6D, 0D6E) and
  `Δ ≫ p₁ = Δ ≫ p₂ = 𝟙`;

and only the projection map is not invertible in general.  It is invertible at `E ∈ D_qc(Y)`
(`isIso_diagTrans_app`): `𝒪_Y ∈ D_qc(Y)` (`Dqc_structureObj`), `Lp₁^*E ∈ D_qc` (Stacks 08F4), and
`Δ` is quasi-compact (its presheaf diagonal is a closed immersion since `f` is separated, Stacks
04CG) and quasi-separated (a monomorphism).

## Inputs

The tagged AxiomMath inputs `Tag08INInput` (Stacks 08IN, `Spaces/BaseChange/Inputs.lean`) and
`Tag08F4Input` (Stacks 08F4, `Spaces/AxiomMathInputs.lean`); no new input.

## Differences from GL26

* "`Φ ≅ id_{D_qc(Y)}`" is rendered as an isomorphism of functors `D_qc(Y) ⥤ D(𝒪_Y)`,
  `(Dqc Y).ι ⋙ Φ_{RΔ_*𝒪_Y} ≅ (Dqc Y).ι` (`lemma_2_25Iso`); since `(Dqc Y).ι` is fully faithful, this
  is the same as an isomorphism of the induced functor `D_qc(Y) ⥤ D_qc(Y)` with the identity
  (`lemma_2_25IsoQc`).
* The base `S` of GL26 is an object `S'` of `AlgebraicSpaces B S hS` (`Spaces/Statements/Main.lean`,
  common conventions); `Y ×_{S'} Y` is `pullback f f` and `Δ` is Mathlib's `pullback.diagonal f`.
* The proof uses only that `f` is separated (part of proper).  The theorem `lemma_2_25` carries the
  paper's hypotheses (Noetherian `S'`, `Y`; `f` proper and flat); `lemma_2_25_of_isProper` is the
  form with only properness.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Kernels

open RelativeFM.Spaces RelativeFM.Spaces.BaseChange RelativeFM.Spaces.Statements

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {S' Y : AlgebraicSpaces B S hS} (f : Y ⟶ S')

/-- **The kernel `RΔ_*𝒪_Y ∈ D(Y ×_S Y)`** (GL26 Lemma 2.25), `Δ = pullback.diagonal f`. -/
abbrev diagKernel : D B S hS (pullback f f) :=
  (push (pullback.diagonal f)).obj (structureObj Y)

/-! ### The diagonal is quasi-compact and quasi-separated -/

/-- The diagonal `Δ : Y ⟶ Y ×_{S'} Y` of a separated morphism is quasi-compact: up to the
identification of `Y ×_{S'} Y` with the presheaf fibre product (Stacks 02X2), it is the presheaf
diagonal, a closed immersion, hence quasi-compact (Stacks 04CG). -/
theorem isQuasiCompact_diagonal (hf : IsProperHom f) :
    IsQuasiCompact B S hS (pullback.diagonal f).hom := by
  have hP := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f f)
  have hd : IsQuasiCompact B S hS (pullback.diagonal f.hom) :=
    isQuasiCompact_of_isClosedImmersion' B S hS hf.1
  have hw : (pullback.diagonal f).hom ≫ hP.isoPullback.hom = pullback.diagonal f.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.diagonal_fst,
        ← ObjectProperty.FullSubcategory.comp_hom, pullback.diagonal_fst]
      rfl
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.diagonal_snd,
        ← ObjectProperty.FullSubcategory.comp_hom, pullback.diagonal_snd]
      rfl
  have sq : IsPullback (𝟙 Y.obj) (pullback.diagonal f).hom (pullback.diagonal f.hom)
      hP.isoPullback.hom :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hw]⟩
  exact IsQuasiCompact.of_isPullback B S hS sq hd

/-- The diagonal is quasi-separated: it is a monomorphism (`Δ ≫ p₁ = 𝟙`), and monomorphisms are
quasi-separated (AxiomMath's `isQuasiSeparated_of_mono`). -/
theorem isQuasiSeparated_diagonal :
    IsQuasiSeparated B S hS (pullback.diagonal f).hom := by
  have h : (pullback.diagonal f).hom ≫ (pullback.fst f f).hom = 𝟙 Y.obj := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, pullback.diagonal_fst]
    rfl
  exact isQuasiSeparated_of_mono B S hS _ (mono_of_mono_fac h)

/-! ### The comparison `Φ_{RΔ_*𝒪_Y} ⟶ 𝟭` -/

/-- `Lp₁^* ⋙ LΔ^* ≅ 𝟭`, from `L(Δ ≫ p₁)^* ≅ LΔ^* Lp₁^*` (Stacks 0D6D), `Δ ≫ p₁ = 𝟙` and
`L(𝟙)^* ≅ 𝟭`. -/
def diagPullIso :
    pull (pullback.fst f f) ⋙ pull (pullback.diagonal f) ≅ 𝟭 (D B S hS Y) :=
  (pullComp B S hS (pullback.diagonal f) (pullback.fst f f)).symm ≪≫
    eqToIso (by rw [pullback.diagonal_fst]) ≪≫ (canon B S hS).idIso Y

/-- `RΔ_* ⋙ Rp₂_* ≅ 𝟭`, from `R(Δ ≫ p₂)_* ≅ Rp₂_* RΔ_*` (Stacks 0D6E), `Δ ≫ p₂ = 𝟙` and
`R(𝟙)_* ≅ 𝟭`. -/
def diagPushIso :
    push (pullback.diagonal f) ⋙ push (pullback.snd f f) ≅ 𝟭 (D B S hS Y) :=
  ((pullPushData B S hS).pushComp (pullback.diagonal f) (pullback.snd f f)).symm ≪≫
    eqToIso (by rw [pullback.diagonal_snd]) ≪≫ (pullPushData B S hS).pushId Y

/-- First step: `Φ_K = Rp₂_*(Lp₁^*(-) ⊗ K) ≅ Rp₂_*(K ⊗ Lp₁^*(-))` (symmetry of `⊗^L`). -/
def diagStep₁ :
    transformOver f f (diagKernel f) ≅
      pull (pullback.fst f f) ⋙ (tensor (pullback f f)).obj (diagKernel f) ⋙
        push (pullback.snd f f) :=
  Functor.isoWhiskerLeft (pull (pullback.fst f f))
    (Functor.isoWhiskerRight ((tensorBraiding (pullback f f)).app (diagKernel f)).symm
      (push (pullback.snd f f)))

/-- Second step: the projection map for `Δ` at `𝒪_Y`,
`Rp₂_*(RΔ_*𝒪_Y ⊗ A) ⟶ Rp₂_*RΔ_*(𝒪_Y ⊗ LΔ^*A)` at `A = Lp₁^*E` (Stacks 08IN). -/
def diagStep₂ :
    pull (pullback.fst f f) ⋙ (tensor (pullback f f)).obj (diagKernel f) ⋙
        push (pullback.snd f f) ⟶
      pull (pullback.fst f f) ⋙ (pull (pullback.diagonal f) ⋙
        (tensor Y).obj (structureObj Y) ⋙ push (pullback.diagonal f)) ⋙
          push (pullback.snd f f) :=
  Functor.whiskerLeft (pull (pullback.fst f f))
    (Functor.whiskerRight (projNatRight (pullback.diagonal f) (structureObj Y))
      (push (pullback.snd f f)))

/-- Third step: the unit law and pseudofunctoriality,
`Rp₂_*RΔ_*(𝒪_Y ⊗ LΔ^*Lp₁^*(-)) ≅ R(p₂Δ)_*L(p₁Δ)^* = 𝟭`. -/
def diagStep₃ :
    pull (pullback.fst f f) ⋙ (pull (pullback.diagonal f) ⋙
        (tensor Y).obj (structureObj Y) ⋙ push (pullback.diagonal f)) ⋙
          push (pullback.snd f f) ≅ 𝟭 (D B S hS Y) :=
  Functor.isoWhiskerLeft (pull (pullback.fst f f))
      (Functor.isoWhiskerRight (Functor.isoWhiskerLeft (pull (pullback.diagonal f))
        (Functor.isoWhiskerRight (tensorLeftUnitor Y) (push (pullback.diagonal f)) ≪≫
          Functor.leftUnitor _)) (push (pullback.snd f f))) ≪≫
    Functor.isoWhiskerLeft (pull (pullback.fst f f))
      (Functor.associator (pull (pullback.diagonal f)) (push (pullback.diagonal f))
        (push (pullback.snd f f))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (diagPushIso f) ≪≫ Functor.rightUnitor _ ≪≫ diagPullIso f

/-- **The comparison `Φ_{RΔ_*𝒪_Y} ⟶ 𝟭`** on `D(𝒪_Y)` (GL26's proof of Lemma 2.25). -/
def diagTrans : transformOver f f (diagKernel f) ⟶ 𝟭 (D B S hS Y) :=
  (diagStep₁ f).hom ≫ diagStep₂ f ≫ (diagStep₃ f).hom

/-- The comparison is invertible at every `E ∈ D_qc(Y)`: its only non-invertible constituent, the
projection map for `Δ` at `(𝒪_Y, Lp₁^*E)`, is invertible by Stacks 08IN, since `Δ` is quasi-compact
and quasi-separated, `𝒪_Y ∈ D_qc` and `Lp₁^*E ∈ D_qc` (Stacks 08F4). -/
theorem isIso_diagTrans_app (h4 : Tag08F4Input B S hS) (hIN : Tag08INInput B S hS)
    (hf : IsProperHom f) {E : D B S hS Y} (hE : Dqc Y E) : IsIso ((diagTrans f).app E) := by
  have : IsIso (projectionFormulaMap (pullback.diagonal f) (structureObj Y)
      ((pull (pullback.fst f f)).obj E)) :=
    hIN _ (isQuasiCompact_diagonal f hf) (isQuasiSeparated_diagonal f) _ (Dqc_structureObj Y) _
      (h4 _ E hE)
  have : IsIso ((diagStep₂ f).app E) :=
    inferInstanceAs (IsIso ((push (pullback.snd f f)).map
      (projectionFormulaMap (pullback.diagonal f) (structureObj Y)
        ((pull (pullback.fst f f)).obj E))))
  rw [diagTrans, NatTrans.comp_app, NatTrans.comp_app]
  infer_instance

/-- **Lemma 2.25** (`lem:funct_on_kernel`), as an isomorphism: `Φ_{RΔ_*𝒪_Y} ≅ id` on `D_qc(Y)`,
rendered as `(Dqc Y).ι ⋙ Φ_{RΔ_*𝒪_Y} ≅ (Dqc Y).ι`, for a proper `f : Y ⟶ S'`.  Inputs: Stacks 08F4,
08IN. -/
def lemma_2_25Iso (h4 : Tag08F4Input B S hS) (hIN : Tag08INInput B S hS) (hf : IsProperHom f) :
    (Dqc Y).ι ⋙ transformOver f f (diagKernel f) ≅ (Dqc Y).ι :=
  haveI : ∀ E, IsIso ((Functor.whiskerLeft (Dqc Y).ι (diagTrans f)).app E) :=
    fun E => isIso_diagTrans_app f h4 hIN hf E.property
  haveI : IsIso (Functor.whiskerLeft (Dqc Y).ι (diagTrans f)) := NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerLeft (Dqc Y).ι (diagTrans f)) ≪≫ Functor.rightUnitor _

/-- `Φ_{RΔ_*𝒪_Y}` maps `D_qc(Y)` into `D_qc(Y)` (it is isomorphic to the identity there). -/
theorem transform_diagKernel_mem (h4 : Tag08F4Input B S hS) (hIN : Tag08INInput B S hS)
    (hf : IsProperHom f) (E : D B S hS Y) (hE : Dqc Y E) :
    Dqc Y ((transformOver f f (diagKernel f)).obj E) :=
  Dqc_of_iso ((lemma_2_25Iso f h4 hIN hf).app ⟨E, hE⟩).symm hE

/-- **Lemma 2.25** (`lem:funct_on_kernel`), for the induced functor `D_qc(Y) ⥤ D_qc(Y)`:
`Φ_{RΔ_*𝒪_Y}|_{D_qc} ≅ 𝟭`. -/
def lemma_2_25IsoQc (h4 : Tag08F4Input B S hS) (hIN : Tag08INInput B S hS) (hf : IsProperHom f) :
    (Dqc Y).lift ((Dqc Y).ι ⋙ transformOver f f (diagKernel f))
        (fun E => transform_diagKernel_mem f h4 hIN hf E.obj E.property) ≅ 𝟭 _ :=
  ((Functor.FullyFaithful.whiskeringRight (Dqc Y).fullyFaithfulι _).preimageIso
    ((Dqc Y).liftCompιIso _ _ ≪≫ lemma_2_25Iso f h4 hIN hf ≪≫ (Functor.leftUnitor _).symm))

/-- **Lemma 2.25** (`lem:funct_on_kernel`) with only the hypothesis its proof uses: for a proper
morphism `f : Y ⟶ S'` of algebraic spaces, `Φ_{RΔ_*𝒪_Y} ≅ id` on `D_qc(Y)`. -/
theorem lemma_2_25_of_isProper (h4 : Tag08F4Input B S hS) (hIN : Tag08INInput B S hS)
    (hf : IsProperHom f) :
    Nonempty ((Dqc Y).ι ⋙ transformOver f f (diagKernel f) ≅ (Dqc Y).ι) :=
  ⟨lemma_2_25Iso f h4 hIN hf⟩

/-- **Lemma 2.25** (`lem:funct_on_kernel`).  Let `f : Y ⟶ S'` be a proper flat morphism of
Noetherian algebraic spaces and `Δ : Y ⟶ Y ×_{S'} Y` the diagonal.  Then
`Φ_{RΔ_*𝒪_Y} ≅ id_{D_qc(Y)}`, as an isomorphism `(Dqc Y).ι ⋙ Φ_{RΔ_*𝒪_Y} ≅ (Dqc Y).ι` of functors
on `D_qc(Y)` (equivalently, `lemma_2_25IsoQc`, of the induced endofunctor of `D_qc(Y)` with the
identity).  Inputs: the tagged AxiomMath theorems Stacks 08F4 and 08IN. -/
theorem lemma_2_25 (h4 : Tag08F4Input B S hS) (hIN : Tag08INInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (_hS' : IsNoetherianSpace hZ S')
    (_hY : IsNoetherianSpace hZ Y) (hf : IsProperHom f) (_hfl : IsFlatHom f) :
    Nonempty ((Dqc Y).ι ⋙ transformOver f f (diagKernel f) ≅ (Dqc Y).ι) :=
  lemma_2_25_of_isProper f h4 hIN hf

end RelativeFM.Spaces.Kernels
