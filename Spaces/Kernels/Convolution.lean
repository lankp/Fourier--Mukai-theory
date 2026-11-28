/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Kernels.Basic

/-!
# GL26 Lemma 2.26 (`lem:convolution`) over algebraic spaces

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), §2.3,
`sec:funct_on_kernel`.  Let `f_i : Y_i → S` (`i = 1, 2, 3`) be proper flat morphisms of Noetherian
algebraic spaces and `K₁ ∈ D_qc(Y₁ ×_S Y₂)`, `K₂ ∈ D_qc(Y₂ ×_S Y₃)`.  The **convolution**
`K₂ ⋆ K₁ = Rp₁₃_*(Lp₁₂^*K₁ ⊗^L Lp₂₃^*K₂) ∈ D_qc(Y₁ ×_S Y₃)` (`convolution`), and **Lemma 2.26**:
`Φ_{K₂} ∘ Φ_{K₁} ≅ Φ_{K₂ ⋆ K₁}` on `D_qc`.

## Proof

GL26 refers to Huybrechts, *Fourier–Mukai transforms in algebraic geometry*, Proposition 5.10,
whose proof uses the projection formula (Stacks 08IN) and flat base change (Stacks 08IR).  With
`q₁, q₂` the projections of `Y₁₂ = Y₁ ×_S Y₂`, `r₂, r₃` those of `Y₂₃`, `s₁, s₃` those of `Y₁₃`
and `Y₁₂₃ = Y₁₂ ×_{Y₂} Y₂₃` (`triple`), for `E ∈ D_qc(Y₁)`:

`Φ_{K₂}Φ_{K₁}E = Rr₃_*(Lr₂^*Rq₂_*(Lq₁^*E ⊗ K₁) ⊗ K₂)`
`  ⟶ Rr₃_*(Rp₂₃_*Lp₁₂^*(Lq₁^*E ⊗ K₁) ⊗ K₂)` (base change for the cartesian square `Y₁₂₃`, `q₂` flat)
`  ⟶ Rr₃_*Rp₂₃_*(Lp₁₂^*(Lq₁^*E ⊗ K₁) ⊗ Lp₂₃^*K₂)` (projection formula for `p₂₃`)
`  ≅ Rs₃_*Rp₁₃_*(Lp₁₃^*Ls₁^*E ⊗ (Lp₁₂^*K₁ ⊗ Lp₂₃^*K₂))` (07A4, associativity, 0D6D, 0D6E)
`  ⟵ Rs₃_*(Ls₁^*E ⊗ Rp₁₃_*(Lp₁₂^*K₁ ⊗ Lp₂₃^*K₂)) = Φ_{K₂⋆K₁}E` (symmetry, projection formula for `p₁₃`).

Both comparisons are natural transformations on all of `D(𝒪_{Y₁})`: the left one is written out in
the proof of `lemma_2_26_of` (see the note before `convLeft₀`), the right one is `convRight`.  They
are invertible at objects of `D_qc(Y₁)` (in `lemma_2_26_of`, and `isIso_convRight_app`).  The
morphism conditions: `q₂` is a base change of `f₁`, hence flat, quasi-compact and quasi-separated;
`p₂₃` is a base change of `q₂`; `p₁₃` is a base change of `f₂` (`isPullback_triple`); proper
morphisms are quasi-compact and quasi-separated.

## Inputs

The tagged AxiomMath inputs `FlatBaseChangeInput` (Stacks 0A1K/08IR, the pushed morphism flat),
`CompIsoAgreeInput` (Stacks 0D6D, AxiomMath's two spellings of the composition isomorphism agree;
used, as in `Spaces/BaseChange/Cube.lean`, to identify AxiomMath's base change map with `θ_□`) and
`Tag08INInput` (Stacks 08IN), all of `Spaces/BaseChange/Inputs.lean`, and `Tag08F4Input`,
`Tag08F5Input` (Stacks 08F4, 08F5) of `Spaces/AxiomMathInputs.lean`; no new input.

## Differences from GL26

* The isomorphism "on `D_qc`" is an isomorphism of functors `D_qc(Y₁) ⥤ D(𝒪_{Y₃})`,
  `(Dqc Y₁).ι ⋙ Φ_{K₁} ⋙ Φ_{K₂} ≅ (Dqc Y₁).ι ⋙ Φ_{K₂⋆K₁}` (Mathlib's diagrammatic order: `Φ_{K₁}`
  first).  Both sides land in `D_qc(Y₃)` (Stacks 08F4, 08F5, 08FA), so this is the paper's
  isomorphism of functors `D_qc(Y₁) → D_qc(Y₃)`.
* The base `S` of GL26 is an object `S'` of `AlgebraicSpaces B S hS`; `Y_i ×_{S'} Y_j` is
  `pullback f_i f_j`, and `Y₁ ×_{S'} Y₂ ×_{S'} Y₃` is modelled as `(Y₁ ×_{S'} Y₂) ×_{Y₂}
  (Y₂ ×_{S'} Y₃)`, with `p₁₂`, `p₂₃` its projections and `p₁₃` the induced map (any two models are
  canonically isomorphic).
* The proof uses that `f₁` is proper and flat and that `f₂` is proper.  `lemma_2_26` carries the
  paper's hypotheses (all three `f_i` proper flat, all spaces Noetherian); `lemma_2_26_of` the
  ones used.
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
variable {S' Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S') (f₃ : Y₃ ⟶ S')

/-- `M₀ = Lp₁₂^*K₁ ⊗^L Lp₂₃^*K₂ ∈ D(Y₁ ×_S Y₂ ×_S Y₃)`. -/
abbrev convMiddle (K₁ : D B S hS (pullback f₁ f₂)) (K₂ : D B S hS (pullback f₂ f₃)) :
    D B S hS (triple f₁ f₂ f₃) :=
  tensorObj ((pull (p₁₂ f₁ f₂ f₃)).obj K₁) ((pull (p₂₃ f₁ f₂ f₃)).obj K₂)

/-- **The convolution of kernels** (GL26 §2.3, before Lemma 2.26):
`K₂ ⋆ K₁ = Rp₁₃_*(Lp₁₂^*K₁ ⊗^L Lp₂₃^*K₂) ∈ D(Y₁ ×_S Y₃)`. -/
def convolution (K₁ : D B S hS (pullback f₁ f₂)) (K₂ : D B S hS (pullback f₂ f₃)) :
    D B S hS (pullback f₁ f₃) :=
  (push (p₁₃ f₁ f₂ f₃)).obj (convMiddle f₁ f₂ f₃ K₁ K₂)

variable (K₁ : D B S hS (pullback f₁ f₂)) (K₂ : D B S hS (pullback f₂ f₃))

/-! ### The common target `N` -/

/-- The functor `E ↦ Rs₃_*Rp₁₃_*(Lp₁₃^*Ls₁^*E ⊗^L M₀)` through which both sides are compared. -/
abbrev convTarget : D B S hS Y₁ ⥤ D B S hS Y₃ :=
  pull (pullback.fst f₁ f₃) ⋙ pull (p₁₃ f₁ f₂ f₃) ⋙ (tensor _).flip.obj (convMiddle f₁ f₂ f₃ K₁ K₂) ⋙
    push (p₁₃ f₁ f₂ f₃) ⋙ push (pullback.snd f₁ f₃)

/-! ### The left-hand side -/

/-- `Lq₁^* ⋙ Lp₁₂^* ≅ Ls₁^* ⋙ Lp₁₃^*` (Stacks 0D6D and `p₁₃ ≫ s₁ = p₁₂ ≫ q₁`). -/
def convPullIso :
    pull (pullback.fst f₁ f₂) ⋙ pull (p₁₂ f₁ f₂ f₃) ≅
      pull (pullback.fst f₁ f₃) ⋙ pull (p₁₃ f₁ f₂ f₃) :=
  (pullComp B S hS (p₁₂ f₁ f₂ f₃) (pullback.fst f₁ f₂)).symm ≪≫
    eqToIso (by rw [p₁₃_fst]) ≪≫ pullComp B S hS (p₁₃ f₁ f₂ f₃) (pullback.fst f₁ f₃)

/-- `Rp₂₃_* ⋙ Rr₃_* ≅ Rp₁₃_* ⋙ Rs₃_*` (Stacks 0D6E and `p₁₃ ≫ s₃ = p₂₃ ≫ r₃`). -/
def convPushIso :
    push (p₂₃ f₁ f₂ f₃) ⋙ push (pullback.snd f₂ f₃) ≅
      push (p₁₃ f₁ f₂ f₃) ⋙ push (pullback.snd f₁ f₃) :=
  ((pullPushData B S hS).pushComp (p₂₃ f₁ f₂ f₃) (pullback.snd f₂ f₃)).symm ≪≫
    eqToIso (by rw [p₁₃_snd]) ≪≫ (pullPushData B S hS).pushComp (p₁₃ f₁ f₂ f₃) (pullback.snd f₁ f₃)

/-! The two non-invertible steps of the left comparison, base change and the projection map
for `p₂₃`, are the `θ_□` and `projMap` of `tensorPullPushData` (identified with AxiomMath's maps by
`theta_app_eq_baseChangeMap` and `projMap_app_eq`, `Spaces/BaseChange/Cube.lean`), whiskered.  They
are written out inside the proofs below (`convLeft_spec`, `lemma_2_26_of`) rather than as
definitions: a definition's value has its nested instance proofs abstracted into auxiliary
constants, after which its components no longer match the (instantiated) AxiomMath inputs
syntactically and the kernel times out comparing them.  The identity steps below fix the spelling
of the functors between consecutive steps, so that consecutive steps share their boundary verbatim.
-/

/-- Left step 0 (an identity): `Φ_{K₁} ⋙ Φ_{K₂}` unfolded to the source of the base change step. -/
def convLeft₀ :
    transformOver f₁ f₂ K₁ ⋙ transformOver f₂ f₃ K₂ ≅
      (pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁) ⋙
        (((tensorPullPushData B S hS).push (pullback.snd f₁ f₂) ⋙ (tensorPullPushData B S hS).pull (pullback.fst f₂ f₃)) ⋙
          ((tensor (pullback f₂ f₃)).flip.obj K₂ ⋙ push (pullback.snd f₂ f₃))) :=
  Iso.refl _

/-- Left identity step 1 (respelling, after base change). -/
def convLeftId₁ :
    ((pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁) ⋙
        (((tensorPullPushData B S hS).pull (p₁₂ f₁ f₂ f₃) ⋙ (tensorPullPushData B S hS).push (p₂₃ f₁ f₂ f₃)) ⋙
          ((tensor (pullback f₂ f₃)).flip.obj K₂ ⋙ push (pullback.snd f₂ f₃)))) ≅
      ((pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁) ⋙ pull (p₁₂ f₁ f₂ f₃)) ⋙
        (((tensorPullPushData B S hS).push (p₂₃ f₁ f₂ f₃) ⋙ (tensorPullPushData B S hS).tensorRight (pullback f₂ f₃) K₂) ⋙
          push (pullback.snd f₂ f₃)) :=
  Iso.refl _

/-- Left identity step 2 (respelling, after the projection map). -/
def convLeftId₂ :
    (((pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁) ⋙ pull (p₁₂ f₁ f₂ f₃)) ⋙
        (((tensorPullPushData B S hS).tensorRight (triple f₁ f₂ f₃) (((tensorPullPushData B S hS).pull (p₂₃ f₁ f₂ f₃)).obj K₂) ⋙
          (tensorPullPushData B S hS).push (p₂₃ f₁ f₂ f₃)) ⋙ push (pullback.snd f₂ f₃))) ≅
      pull (pullback.fst f₁ f₂) ⋙ (tensor _).flip.obj K₁ ⋙ pull (p₁₂ f₁ f₂ f₃) ⋙
        ((tensor _).flip.obj ((pull (p₂₃ f₁ f₂ f₃)).obj K₂) ⋙ push (p₂₃ f₁ f₂ f₃)) ⋙
          push (pullback.snd f₂ f₃) :=
  Iso.refl _

/-- Left step 3 (invertible): Stacks 07A4 for `p₁₂`, associativity of `⊗^L`, 0D6D and 0D6E. -/
def convLeft₃ :
    pull (pullback.fst f₁ f₂) ⋙ (tensor _).flip.obj K₁ ⋙ pull (p₁₂ f₁ f₂ f₃) ⋙
        ((tensor _).flip.obj ((pull (p₂₃ f₁ f₂ f₃)).obj K₂) ⋙ push (p₂₃ f₁ f₂ f₃)) ⋙
          push (pullback.snd f₂ f₃) ≅
      convTarget f₁ f₂ f₃ K₁ K₂ :=
  Functor.isoWhiskerLeft (pull (pullback.fst f₁ f₂))
      (Functor.isoWhiskerRight ((tensorPullPushData B S hS).pullTensorRight (p₁₂ f₁ f₂ f₃) K₁)
        ((tensor _).flip.obj ((pull (p₂₃ f₁ f₂ f₃)).obj K₂) ⋙ push (p₂₃ f₁ f₂ f₃) ⋙
          push (pullback.snd f₂ f₃))) ≪≫
    Functor.isoWhiskerLeft (pull (pullback.fst f₁ f₂) ⋙ pull (p₁₂ f₁ f₂ f₃))
      (Functor.isoWhiskerRight (tensorAssoc ((pull (p₁₂ f₁ f₂ f₃)).obj K₁)
        ((pull (p₂₃ f₁ f₂ f₃)).obj K₂)) (push (p₂₃ f₁ f₂ f₃) ⋙ push (pullback.snd f₂ f₃))) ≪≫
    Functor.isoWhiskerRight (convPullIso f₁ f₂ f₃)
      ((tensor _).flip.obj (convMiddle f₁ f₂ f₃ K₁ K₂) ⋙ push (p₂₃ f₁ f₂ f₃) ⋙
        push (pullback.snd f₂ f₃)) ≪≫
    Functor.isoWhiskerLeft
      ((pull (pullback.fst f₁ f₃) ⋙ pull (p₁₃ f₁ f₂ f₃)) ⋙
        (tensor _).flip.obj (convMiddle f₁ f₂ f₃ K₁ K₂))
      (convPushIso f₁ f₂ f₃)

/-! ### The right-hand side -/

/-- Right step 1 (invertible): symmetry, `Ls₁^*E ⊗ (K₂⋆K₁) ≅ (K₂⋆K₁) ⊗ Ls₁^*E`. -/
def convRight₁ :
    transformOver f₁ f₃ (convolution f₁ f₂ f₃ K₁ K₂) ≅
      pull (pullback.fst f₁ f₃) ⋙ (tensor (pullback f₁ f₃)).obj (convolution f₁ f₂ f₃ K₁ K₂) ⋙
        push (pullback.snd f₁ f₃) :=
  Functor.isoWhiskerLeft (pull (pullback.fst f₁ f₃))
    (Functor.isoWhiskerRight
      ((tensorBraiding (pullback f₁ f₃)).app (convolution f₁ f₂ f₃ K₁ K₂)).symm
      (push (pullback.snd f₁ f₃)))

/-- Right step 2: the projection formula for `p₁₃`,
`Rp₁₃_*M₀ ⊗ A ⟶ Rp₁₃_*(M₀ ⊗ Lp₁₃^*A)` (Stacks 08IN), natural in `A`. -/
def convRight₂ :
    pull (pullback.fst f₁ f₃) ⋙ (tensor (pullback f₁ f₃)).obj (convolution f₁ f₂ f₃ K₁ K₂) ⋙
        push (pullback.snd f₁ f₃) ⟶
      pull (pullback.fst f₁ f₃) ⋙ (pull (p₁₃ f₁ f₂ f₃) ⋙
        (tensor (triple f₁ f₂ f₃)).obj (convMiddle f₁ f₂ f₃ K₁ K₂) ⋙ push (p₁₃ f₁ f₂ f₃)) ⋙
          push (pullback.snd f₁ f₃) :=
  Functor.whiskerLeft (pull (pullback.fst f₁ f₃))
    (Functor.whiskerRight (projNatRight (p₁₃ f₁ f₂ f₃) (convMiddle f₁ f₂ f₃ K₁ K₂))
      (push (pullback.snd f₁ f₃)))

/-- Right step 3 (invertible): symmetry, `M₀ ⊗ Lp₁₃^*A ≅ Lp₁₃^*A ⊗ M₀`. -/
def convRight₃ :
    pull (pullback.fst f₁ f₃) ⋙ (pull (p₁₃ f₁ f₂ f₃) ⋙
        (tensor (triple f₁ f₂ f₃)).obj (convMiddle f₁ f₂ f₃ K₁ K₂) ⋙ push (p₁₃ f₁ f₂ f₃)) ⋙
          push (pullback.snd f₁ f₃) ≅ convTarget f₁ f₂ f₃ K₁ K₂ :=
  Functor.isoWhiskerLeft (pull (pullback.fst f₁ f₃))
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft (pull (p₁₃ f₁ f₂ f₃))
      (Functor.isoWhiskerRight
        ((tensorBraiding (triple f₁ f₂ f₃)).app (convMiddle f₁ f₂ f₃ K₁ K₂))
        (push (p₁₃ f₁ f₂ f₃)))) (push (pullback.snd f₁ f₃)))

/-- **The right comparison** `Φ_{K₂⋆K₁} ⟶ N`. -/
def convRight : transformOver f₁ f₃ (convolution f₁ f₂ f₃ K₁ K₂) ⟶ convTarget f₁ f₂ f₃ K₁ K₂ :=
  (convRight₁ f₁ f₂ f₃ K₁ K₂).hom ≫ convRight₂ f₁ f₂ f₃ K₁ K₂ ≫ (convRight₃ f₁ f₂ f₃ K₁ K₂).hom

/-! ### Invertibility on `D_qc` -/

section Iso

variable {f₁ f₂ f₃}

theorem isQuasiCompact_q₂ (hf₁ : IsProperHom f₁) :
    IsQuasiCompact B S hS (pullback.snd f₁ f₂).hom :=
  isQuasiCompact_of_isPullback' (IsPullback.of_hasPullback f₁ f₂) (isQuasiCompact_of_isProper hf₁)

theorem isQuasiSeparated_q₂ (hf₁ : IsProperHom f₁) :
    IsQuasiSeparated B S hS (pullback.snd f₁ f₂).hom :=
  isQuasiSeparated_of_isPullback' (IsPullback.of_hasPullback f₁ f₂)
    (isQuasiSeparated_of_isProper hf₁)

theorem isFlat_q₂ (hfl₁ : IsFlatHom f₁) : IsFlatHom (pullback.snd f₁ f₂) :=
  isFlat_of_isPullback' (IsPullback.of_hasPullback f₁ f₂) hfl₁

theorem isQuasiCompact_p₂₃ (hf₁ : IsProperHom f₁) :
    IsQuasiCompact B S hS (p₂₃ f₁ f₂ f₃).hom :=
  isQuasiCompact_of_isPullback' (isPullback_triple₁ f₁ f₂ f₃) (isQuasiCompact_q₂ hf₁)

theorem isQuasiSeparated_p₂₃ (hf₁ : IsProperHom f₁) :
    IsQuasiSeparated B S hS (p₂₃ f₁ f₂ f₃).hom :=
  isQuasiSeparated_of_isPullback' (isPullback_triple₁ f₁ f₂ f₃) (isQuasiSeparated_q₂ hf₁)

theorem isQuasiCompact_p₁₃ (hf₂ : IsProperHom f₂) :
    IsQuasiCompact B S hS (p₁₃ f₁ f₂ f₃).hom :=
  isQuasiCompact_of_isPullback' (isPullback_triple f₁ f₂ f₃) (isQuasiCompact_of_isProper hf₂)

theorem isQuasiSeparated_p₁₃ (hf₂ : IsProperHom f₂) :
    IsQuasiSeparated B S hS (p₁₃ f₁ f₂ f₃).hom :=
  isQuasiSeparated_of_isPullback' (isPullback_triple f₁ f₂ f₃) (isQuasiSeparated_of_isProper hf₂)

variable {K₁ K₂}

/-- A component of `L ⋙ τ ⋙ R` is invertible when the component of `τ` at `L E` is. (Used to keep the
kernel from comparing differently-spelled objects.) -/
lemma isIso_whiskerLeft_whiskerRight_app {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] (L : C₁ ⥤ C₂) {F G : C₂ ⥤ C₃} (τ : F ⟶ G) (R : C₃ ⥤ C₄)
    (E : C₁) [IsIso (τ.app (L.obj E))] :
    IsIso ((Functor.whiskerLeft L (Functor.whiskerRight τ R)).app E) := by
  dsimp
  infer_instance

/-- Flat base change for a cartesian square of algebraic spaces whose pushed morphism `f` is flat,
quasi-compact and quasi-separated, for `θ_□` of `tensorPullPushData`: from AxiomMath's
`FlatBaseChangeInput` (Stacks 0A1K/08IR) and `CompIsoAgreeInput` (Stacks 0D6D), as in
`flatBaseChangeRightQc_of_isFlat`. -/
theorem isIso_theta_app (hF : FlatBaseChangeInput B S hS) (hA : CompIsoAgreeInput B S hS)
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (hqc : IsQuasiCompact B S hS f.hom)
    (hqs : IsQuasiSeparated B S hS f.hom) (hfl : IsFlatHom f) (E : D B S hS X) (hE : Dqc X E) :
    IsIso (((tensorPullPushData B S hS).theta sq.flip.toCommSq).app E) :=
  (congrArg IsIso (theta_app_eq_baseChangeMap hA sq.flip.toCommSq sq.w E)).mpr
    (hF sq hqc hqs hfl E hE)

/-- The right comparison is invertible at every `E ∈ D_qc(Y₁)`: the projection formula for `p₁₃`
(qcqs, as a base change of the proper `f₂`; Stacks 08IN) at `M₀ ∈ D_qc`, `Ls₁^*E ∈ D_qc`. -/
theorem isIso_convRight_app (hIN : Tag08INInput B S hS) (h4 : Tag08F4Input B S hS)
    (h5 : Tag08F5Input B S hS) (hf₂ : IsProperHom f₂) (hK₁ : Dqc _ K₁) (hK₂ : Dqc _ K₂)
    {E : D B S hS Y₁} (hE : Dqc Y₁ E) : IsIso ((convRight f₁ f₂ f₃ K₁ K₂).app E) := by
  have hM : Dqc _ (convMiddle f₁ f₂ f₃ K₁ K₂) := h5 _ _ _ (h4 _ _ hK₁) (h4 _ _ hK₂)
  have : IsIso ((projNatRight (p₁₃ f₁ f₂ f₃) (convMiddle f₁ f₂ f₃ K₁ K₂)).app
      ((pull (pullback.fst f₁ f₃)).obj E)) :=
    hIN _ (isQuasiCompact_p₁₃ hf₂) (isQuasiSeparated_p₁₃ hf₂) _ hM _ (h4 _ E hE)
  have : IsIso ((convRight₂ f₁ f₂ f₃ K₁ K₂).app E) :=
    isIso_whiskerLeft_whiskerRight_app _ _ _ _
  rw [convRight, NatTrans.comp_app, NatTrans.comp_app]
  infer_instance

/-- **Lemma 2.26** (`lem:convolution`) with only the hypotheses its proof uses: `f₁` proper and
flat, `f₂` proper, `K₁`, `K₂` in `D_qc`.  The isomorphism is the composite, on `D_qc(Y₁)`, of the
left comparison `Φ_{K₂} ∘ Φ_{K₁} ⟶ N` (base change for `Y₁₂₃`, the projection formula for `p₂₃`,
07A4, associativity, 0D6D, 0D6E) and the inverse of the right comparison `Φ_{K₂⋆K₁} ⟶ N`
(`convRight`).  Inputs: Stacks 0A1K/08IR (`FlatBaseChangeInput`), 0D6D (`CompIsoAgreeInput`), 08IN,
08F4, 08F5. -/
theorem lemma_2_26_of (hF : FlatBaseChangeInput B S hS) (hA : CompIsoAgreeInput B S hS)
    (hIN : Tag08INInput B S hS) (h4 : Tag08F4Input B S hS) (h5 : Tag08F5Input B S hS)
    (hf₁ : IsProperHom f₁) (hfl₁ : IsFlatHom f₁) (hf₂ : IsProperHom f₂) (hK₁ : Dqc _ K₁)
    (hK₂ : Dqc _ K₂) :
    Nonempty ((Dqc Y₁).ι ⋙ transformOver f₁ f₂ K₁ ⋙ transformOver f₂ f₃ K₂ ≅
      (Dqc Y₁).ι ⋙ transformOver f₁ f₃ (convolution f₁ f₂ f₃ K₁ K₂)) := by
  have hL : ∀ E : (Dqc Y₁).FullSubcategory, IsIso ((Functor.whiskerLeft (Dqc Y₁).ι
      ((convLeft₀ f₁ f₂ f₃ K₁ K₂).hom ≫
      (Functor.whiskerLeft (pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁)
        (Functor.whiskerRight ((tensorPullPushData B S hS).theta (isPullback_triple₁ f₁ f₂ f₃).flip.toCommSq)
          ((tensor (pullback f₂ f₃)).flip.obj K₂ ⋙ push (pullback.snd f₂ f₃)))) ≫
      (convLeftId₁ f₁ f₂ f₃ K₁ K₂).hom ≫
      (Functor.whiskerLeft ((pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁) ⋙ pull (p₁₂ f₁ f₂ f₃))
        (Functor.whiskerRight ((tensorPullPushData B S hS).projMap (p₂₃ f₁ f₂ f₃) K₂) (push (pullback.snd f₂ f₃)))) ≫
      (convLeftId₂ f₁ f₂ f₃ K₁ K₂).hom ≫ (convLeft₃ f₁ f₂ f₃ K₁ K₂).hom :
        transformOver f₁ f₂ K₁ ⋙ transformOver f₂ f₃ K₂ ⟶
        convTarget f₁ f₂ f₃ K₁ K₂)).app E) := by
    intro E
    have hE : Dqc Y₁ ((Dqc Y₁).ι.obj E) := E.property
    have hX : Dqc _ ((pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁).obj ((Dqc Y₁).ι.obj E)) := by
      rw [Functor.comp_obj, Functor.flip_obj_obj]
      exact h5 _ _ _ (h4 _ _ hE) hK₁
    have hY : Dqc _ (((pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁) ⋙ pull (p₁₂ f₁ f₂ f₃)).obj ((Dqc Y₁).ι.obj E)) := by
      rw [Functor.comp_obj]
      exact h4 _ _ hX
    have := isIso_theta_app hF hA (isPullback_triple₁ f₁ f₂ f₃) (isQuasiCompact_q₂ hf₁)
      (isQuasiSeparated_q₂ hf₁) (isFlat_q₂ hfl₁) _ hX
    have : IsIso ((Functor.whiskerLeft (pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁)
        (Functor.whiskerRight ((tensorPullPushData B S hS).theta (isPullback_triple₁ f₁ f₂ f₃).flip.toCommSq)
          ((tensor (pullback f₂ f₃)).flip.obj K₂ ⋙ push (pullback.snd f₂ f₃)))).app ((Dqc Y₁).ι.obj E)) :=
      isIso_whiskerLeft_whiskerRight_app _ _ _ _
    have := isIso_projMap_app (p₂₃ f₁ f₂ f₃) hIN (isQuasiCompact_p₂₃ hf₁)
      (isQuasiSeparated_p₂₃ hf₁) hK₂ hY
    have : IsIso ((Functor.whiskerLeft ((pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁) ⋙ pull (p₁₂ f₁ f₂ f₃))
        (Functor.whiskerRight ((tensorPullPushData B S hS).projMap (p₂₃ f₁ f₂ f₃) K₂) (push (pullback.snd f₂ f₃)))).app ((Dqc Y₁).ι.obj E)) :=
      isIso_whiskerLeft_whiskerRight_app _ _ _ _
    rw [Functor.whiskerLeft_app, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
      NatTrans.comp_app, NatTrans.comp_app]
    infer_instance
  have hR : ∀ E : (Dqc Y₁).FullSubcategory,
      IsIso ((Functor.whiskerLeft (Dqc Y₁).ι (convRight f₁ f₂ f₃ K₁ K₂)).app E) :=
    fun E => isIso_convRight_app hIN h4 h5 hf₂ hK₁ hK₂ E.property
  have := NatIso.isIso_of_isIso_app (Functor.whiskerLeft (Dqc Y₁).ι
      ((convLeft₀ f₁ f₂ f₃ K₁ K₂).hom ≫
      (Functor.whiskerLeft (pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁)
        (Functor.whiskerRight ((tensorPullPushData B S hS).theta (isPullback_triple₁ f₁ f₂ f₃).flip.toCommSq)
          ((tensor (pullback f₂ f₃)).flip.obj K₂ ⋙ push (pullback.snd f₂ f₃)))) ≫
      (convLeftId₁ f₁ f₂ f₃ K₁ K₂).hom ≫
      (Functor.whiskerLeft ((pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁) ⋙ pull (p₁₂ f₁ f₂ f₃))
        (Functor.whiskerRight ((tensorPullPushData B S hS).projMap (p₂₃ f₁ f₂ f₃) K₂) (push (pullback.snd f₂ f₃)))) ≫
      (convLeftId₂ f₁ f₂ f₃ K₁ K₂).hom ≫ (convLeft₃ f₁ f₂ f₃ K₁ K₂).hom :
        transformOver f₁ f₂ K₁ ⋙ transformOver f₂ f₃ K₂ ⟶
        convTarget f₁ f₂ f₃ K₁ K₂))
  have := NatIso.isIso_of_isIso_app (Functor.whiskerLeft (Dqc Y₁).ι (convRight f₁ f₂ f₃ K₁ K₂))
  exact ⟨asIso (Functor.whiskerLeft (Dqc Y₁).ι
      ((convLeft₀ f₁ f₂ f₃ K₁ K₂).hom ≫
      (Functor.whiskerLeft (pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁)
        (Functor.whiskerRight ((tensorPullPushData B S hS).theta (isPullback_triple₁ f₁ f₂ f₃).flip.toCommSq)
          ((tensor (pullback f₂ f₃)).flip.obj K₂ ⋙ push (pullback.snd f₂ f₃)))) ≫
      (convLeftId₁ f₁ f₂ f₃ K₁ K₂).hom ≫
      (Functor.whiskerLeft ((pull (pullback.fst f₁ f₂) ⋙ (tensor (pullback f₁ f₂)).flip.obj K₁) ⋙ pull (p₁₂ f₁ f₂ f₃))
        (Functor.whiskerRight ((tensorPullPushData B S hS).projMap (p₂₃ f₁ f₂ f₃) K₂) (push (pullback.snd f₂ f₃)))) ≫
      (convLeftId₂ f₁ f₂ f₃ K₁ K₂).hom ≫ (convLeft₃ f₁ f₂ f₃ K₁ K₂).hom :
        transformOver f₁ f₂ K₁ ⋙ transformOver f₂ f₃ K₂ ⟶
        convTarget f₁ f₂ f₃ K₁ K₂)) ≪≫
    (asIso (Functor.whiskerLeft (Dqc Y₁).ι (convRight f₁ f₂ f₃ K₁ K₂))).symm⟩

/-- **Lemma 2.26** (`lem:convolution`).  Let `f_i : Y_i ⟶ S'` (`i = 1, 2, 3`) be proper flat
morphisms of Noetherian algebraic spaces, `K₁ ∈ D_qc(Y₁ ×_{S'} Y₂)` and
`K₂ ∈ D_qc(Y₂ ×_{S'} Y₃)`.  Then there is an isomorphism on `D_qc`
`Φ_{K₂} ∘ Φ_{K₁} ≅ Φ_{K₂ ⋆ K₁}`, rendered as
`(Dqc Y₁).ι ⋙ Φ_{K₁} ⋙ Φ_{K₂} ≅ (Dqc Y₁).ι ⋙ Φ_{K₂⋆K₁}` (module docstring).  Inputs: the tagged
AxiomMath theorems Stacks 0A1K/08IR (`FlatBaseChangeInput`), 08IN, 08F4, 08F5. -/
theorem lemma_2_26 (hF : FlatBaseChangeInput B S hS) (hA : CompIsoAgreeInput B S hS)
    (hIN : Tag08INInput B S hS)
    (h4 : Tag08F4Input B S hS) (h5 : Tag08F5Input B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (_hS' : IsNoetherianSpace hZ S') (_hY₁ : IsNoetherianSpace hZ Y₁)
    (_hY₂ : IsNoetherianSpace hZ Y₂) (_hY₃ : IsNoetherianSpace hZ Y₃)
    (hf₁ : IsProperHom f₁) (hfl₁ : IsFlatHom f₁) (hf₂ : IsProperHom f₂) (_hfl₂ : IsFlatHom f₂)
    (_hf₃ : IsProperHom f₃) (_hfl₃ : IsFlatHom f₃) (hK₁ : Dqc _ K₁) (hK₂ : Dqc _ K₂) :
    Nonempty ((Dqc Y₁).ι ⋙ transformOver f₁ f₂ K₁ ⋙ transformOver f₂ f₃ K₂ ≅
      (Dqc Y₁).ι ⋙ transformOver f₁ f₃ (convolution f₁ f₂ f₃ K₁ K₂)) :=
  lemma_2_26_of hF hA hIN h4 h5 hf₁ hfl₁ hf₂ hK₁ hK₂

end Iso

end RelativeFM.Spaces.Kernels
