/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as
described in the file LICENSE. -/
import FourierMukai.Prelim.BaseChangeMates
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Integral transforms and base change in the Fourier--Mukai cube (GL26 §6, §10)

E. Guisado Villalgordo and P. Lank, *Relative Fourier--Mukai theory for algebraic spaces* (GL26):

* **Setup 2.20** (`setup:fm_cube_pullback`): `FMCube`;
* **Lemma 6.11** (`lem:fm_cube_flat_base_change_natural_isomorphism`): `FMCube.alpha`,
  `FMCube.lemma_6_11`, the natural isomorphism `α^K : L t₂^* ∘ Φ_K ≅ Φ_{L(t')^*K} ∘ L t₁^*`;
* **Lemma 10.1** (`lem:fm_cube_pullback_natural_isomorphism`): `FMCube.beta`,
  `FMCube.lemma_10_1`, the natural isomorphism `β^K : Φ_K ∘ R(t₁)_* ≅ R(t₂)_* ∘ Φ_{L(t')^*K}`;
* **Lemma 10.2** (`lem:integral_transform_is_morphism_of_adjoints`): `FMCube.lemma_10_2`,
  `β^K` is the (right) mate of `α^K` under the square with horizontal sides `Φ_K`,
  `Φ_{L(t')^*K}` and vertical adjunctions `L t₁^* ⊣ R(t₁)_*`, `L t₂^* ⊣ R(t₂)_*`
  (equivalently, `α^K` is the left mate of `β^K`: `lemma_10_2'`).

## Setting (six-functor form)

The categories `D_qc(-)`, the functors `L(-)^*`, `R(-)_*` and their pseudofunctoriality are a
`PullPushData` (`Prelim/BaseChangeMates.lean`, the abstract setting of GL26 §7.2), extended in
`TensorPullPushData` by a bifunctor `⊗` on each `D_qc(X)` and the monoidality isomorphism
`L f^*(A ⊗ B) ≅ L f^*A ⊗ L f^*B`, natural in both variables.  The integral transform is
`Φ_K = R(p₂)_* (L(p₁)^*(-) ⊗ K)`, `TensorPullPushData.transform`, as in the paper.

`FMCube` is the diagram of Setup 2.20 in the category of spaces: the four fibre products are
`IsPullback` squares, as are the two faces of the cube used in the proofs.

## Inputs

The proofs use exactly the four inputs named in the paper:

* pseudofunctoriality: the data and axioms of `PullPushData`;
* monoidality of derived pullback: the field `TensorPullPushData.pullTensor`;
* flat base change (Stacks 08IR, Tor-independent base change; the squares are Tor-independent
  because `f'₁`, `f'₂` are flat): the `Prop`s `FMCube.FlatBaseChangeLeft`,
  `FMCube.FlatBaseChangeRight`, invertibility of the base change map `θ_□` of GL26
  Lemma-Definition 7.13 (`PullPushData.theta`) for the two faces;
* the projection formula (Stacks 08EU for schemes, 08IN for algebraic spaces): the `Prop`
  `FMCube.ProjectionFormula`, invertibility of the projection map
  `R t'_* E ⊗ K ⟶ R t'_*(E ⊗ L t'^* K)`, defined (as in Stacks) as the adjoint of
  `L t'^*(R t'_*E ⊗ K) ≅ L t'^*R t'_*E ⊗ L t'^*K ⟶ E ⊗ L t'^*K`, i.e. as the mate of
  monoidality (`TensorPullPushData.projMap`).

Lemma 6.11 uses only `FlatBaseChangeRight`; Lemma 10.1 uses `FlatBaseChangeLeft` and
`ProjectionFormula`.  **Lemma 10.2 uses no input**: it holds for the underlying natural
transformations, before invertibility is known.  No coherence between flat base change and the
projection formula is needed: because the base change maps and the projection map are *defined*
as mates (Lemma-Definition 7.13), the mate of the pasting `α^K` is the pasting of the mates
(Mathlib `mateEquiv_vcomp`), which is `β^K` by Lemma 7.13 (`PullPushData.lemma_7_13`).

## Deviations from the paper

* Six-functor form: the categories and functors are parameters; the hypotheses "Noetherian",
  "proper", "flat" of Setup 2.20 enter only through the inputs above, which are what the paper's
  proofs use them for.  The tensor product is an arbitrary bifunctor (no associativity or unit
  constraints are needed) and monoidality is natural in both variables, as in the paper.
* Mathlib composes functors diagrammatically: `Φ_K ⋙ L t₂^*` is the paper's `L t₂^* ∘ Φ_K`.
* `α^K` and `β^K` are written as pastings (`TwoSquare.hComp`, `TwoSquare.vComp`) of the three
  isomorphisms of the paper's proofs, in the paper's order.

## Non-vacuity

`constTensorPullPushData` (constant categories, identity functors, an arbitrary bifunctor) with
the all-identity cube `constFMCube` satisfies all three inputs (`constFMCube_flatBaseChangeLeft`,
`constFMCube_flatBaseChangeRight`, `constFMCube_projectionFormula`); a concrete instance with
`C = Type` and the cartesian product is given at the end.
-/

@[expose] public section

namespace RelativeFM

namespace FMCube

open CategoryTheory CategoryTheory.Functor BaseChangeMates

universe v u v₁ u₁

set_option linter.checkUnivs false in
/-- `PullPushData` (`D_qc(-)`, `L(-)^*`, `R(-)_*`, pseudofunctoriality, `L f^* ⊣ R f_*`) together
with the derived tensor product `⊗^L` on every `D_qc(X)` (as a bifunctor) and the monoidality
isomorphism of derived pullback `L f^*(A ⊗ B) ≅ L f^*A ⊗ L f^*B`, natural in `A` and `B`
(Stacks 07A4; for algebraic spaces the same statement on the small étale site). -/
structure TensorPullPushData (S : Type u) [Category.{v} S] extends
    PullPushData.{v, u, v₁, u₁} S where
  /-- The derived tensor product on `obj X`, curried: `(tensor X).obj A).obj B = A ⊗ B`. -/
  tensor (X : S) : obj X ⥤ obj X ⥤ obj X
  /-- Monoidality of derived pullback: `L f^*(A ⊗ B) ≅ L f^*A ⊗ L f^*B`, natural in `A`, `B`. -/
  pullTensor {X Y : S} (f : X ⟶ Y) :
    tensor Y ⋙ (whiskeringRight _ _ _).obj (pull f) ≅
      pull f ⋙ tensor X ⋙ (whiskeringLeft _ _ _).obj (pull f)

namespace TensorPullPushData

variable {S : Type u} [Category.{v} S] (P : TensorPullPushData.{v, u, v₁, u₁} S)

/-- `- ⊗ K` on `obj X`. -/
abbrev tensorRight (X : S) (K : P.obj X) : P.obj X ⥤ P.obj X := (P.tensor X).flip.obj K

/-- Monoidality with the second factor fixed:
`L f^*(- ⊗ K) ≅ L f^*(-) ⊗ L f^*K`, a 2-square with vertical sides `L f^*`. -/
def pullTensorRight {X Y : S} (f : X ⟶ Y) (K : P.obj Y) :
    P.tensorRight Y K ⋙ P.pull f ≅ P.pull f ⋙ P.tensorRight X ((P.pull f).obj K) :=
  NatIso.ofComponents (fun A => ((P.pullTensor f).app A).app K) (by
    intro A A' g
    exact congr_app ((P.pullTensor f).hom.naturality g) K)

/-- The projection map `R f_* E ⊗ K ⟶ R f_*(E ⊗ L f^*K)` (Stacks 08EU, 08IN): by definition the
mate of the monoidality isomorphism `pullTensorRight f K` under `L f^* ⊣ R f_*` on both sides,
i.e. the adjoint of `L f^*(R f_*E ⊗ K) ≅ L f^*R f_*E ⊗ L f^*K ⟶ E ⊗ L f^*K`. -/
def projMap {X Y : S} (f : X ⟶ Y) (K : P.obj Y) :
    P.push f ⋙ P.tensorRight Y K ⟶ P.tensorRight X ((P.pull f).obj K) ⋙ P.push f :=
  mateEquiv (P.adj f) (P.adj f) (P.pullTensorRight f K).hom

/-- The integral transform `Φ_K(E) = R(p₂)_*(L(p₁)^*E ⊗^L K)` with kernel `K` on `X`, for
`p₁ : X ⟶ Y₁`, `p₂ : X ⟶ Y₂` (GL26 Setup 2.20, with `p₁ = f'₂`, `p₂ = f'₁`). -/
abbrev transform {X Y₁ Y₂ : S} (p₁ : X ⟶ Y₁) (p₂ : X ⟶ Y₂) (K : P.obj X) :
    P.obj Y₁ ⥤ P.obj Y₂ :=
  P.pull p₁ ⋙ P.tensorRight X K ⋙ P.push p₂

end TensorPullPushData

/-- **Setup 2.20** (`setup:fm_cube_pullback`), the diagram in the category of spaces: a base
`S₀`, `t : T ⟶ S₀`, `f₁ : Y₁ ⟶ S₀`, `f₂ : Y₂ ⟶ S₀`, the fibre products
`Y₁₂ = Y₁ ×_{S₀} Y₂` (projections `f'₂ : Y₁₂ ⟶ Y₁`, `f'₁ : Y₁₂ ⟶ Y₂`),
`Y₁T = Y₁ ×_{S₀} T` (`t₁`, `g₁`), `Y₂T = Y₂ ×_{S₀} T` (`t₂`, `g₂`), and
`Y₁₂T = Y₁ ×_{S₀} Y₂ ×_{S₀} T` with `t' : Y₁₂T ⟶ Y₁₂`, `g'₂ : Y₁₂T ⟶ Y₁T`, `g'₁ : Y₁₂T ⟶ Y₂T`.
The faces `sq₁` (`Y₁₂T = Y₁₂ ×_{Y₁} Y₁T`) and `sq₂` (`Y₁₂T = Y₁₂ ×_{Y₂} Y₂T`) are the squares used
in the proofs.  "Noetherian", "proper", "flat" are not recorded here: they enter through the
inputs `FlatBaseChangeLeft`, `FlatBaseChangeRight`, `ProjectionFormula`. -/
structure _root_.RelativeFM.FMCube (S : Type u) [Category.{v} S] where
  /-- The base `S`. -/
  S₀ : S
  /-- The base change `T`. -/
  T : S
  /-- `Y₁`. -/
  Y₁ : S
  /-- `Y₂`. -/
  Y₂ : S
  /-- `Y₁ ×_S Y₂`. -/
  Y₁₂ : S
  /-- `Y₁ ×_S T`. -/
  Y₁T : S
  /-- `Y₂ ×_S T`. -/
  Y₂T : S
  /-- `Y₁ ×_S Y₂ ×_S T`. -/
  Y₁₂T : S
  t : T ⟶ S₀
  f₁ : Y₁ ⟶ S₀
  f₂ : Y₂ ⟶ S₀
  f'₁ : Y₁₂ ⟶ Y₂
  f'₂ : Y₁₂ ⟶ Y₁
  t₁ : Y₁T ⟶ Y₁
  t₂ : Y₂T ⟶ Y₂
  t' : Y₁₂T ⟶ Y₁₂
  g₁ : Y₁T ⟶ T
  g₂ : Y₂T ⟶ T
  g'₁ : Y₁₂T ⟶ Y₂T
  g'₂ : Y₁₂T ⟶ Y₁T
  /-- `Y₁₂ = Y₁ ×_S Y₂`. -/
  isPullback_Y₁₂ : IsPullback f'₂ f'₁ f₁ f₂
  /-- `Y₁T = Y₁ ×_S T`. -/
  isPullback_Y₁T : IsPullback t₁ g₁ f₁ t
  /-- `Y₂T = Y₂ ×_S T`. -/
  isPullback_Y₂T : IsPullback t₂ g₂ f₂ t
  /-- The face `Y₁₂T = Y₁₂ ×_{Y₁} Y₁T`. -/
  isPullback₁ : IsPullback t' g'₂ f'₂ t₁
  /-- The face `Y₁₂T = Y₁₂ ×_{Y₂} Y₂T`. -/
  isPullback₂ : IsPullback t' g'₁ f'₁ t₂
  /-- The two maps `Y₁₂T ⟶ T` agree. -/
  comm_T : g'₂ ≫ g₁ = g'₁ ≫ g₂

variable {S : Type u} [Category.{v} S] {P : TensorPullPushData.{v, u, v₁, u₁} S} (C : FMCube S)

/-- The face `sq₁`, oriented as in GL26 Lemma-Definition 7.13 with `p = t₁`, `q = f'₂`:
its base change map is `θ₁ : L(f'₂)^* R(t₁)_* ⟶ R t'_* L(g'₂)^*`. -/
lemma sq₁ : CommSq C.t' C.g'₂ C.f'₂ C.t₁ := C.isPullback₁.toCommSq

/-- The face `sq₂`, oriented with `p = f'₁`, `q = t₂`: its base change map is
`θ₂ : L t₂^* R(f'₁)_* ⟶ R(g'₁)_* L t'^*`. -/
lemma sq₂ : CommSq C.g'₁ C.t' C.t₂ C.f'₁ := C.isPullback₂.toCommSq.flip

variable (P)

/-- `Φ_K : D_qc(Y₁) ⥤ D_qc(Y₂)`. -/
abbrev Φ (K : P.obj C.Y₁₂) : P.obj C.Y₁ ⥤ P.obj C.Y₂ := P.transform C.f'₂ C.f'₁ K

/-- `Φ_{L(t')^*K} : D_qc(Y₁ ×_S T) ⥤ D_qc(Y₂ ×_S T)`. -/
abbrev ΦT (K : P.obj C.Y₁₂) : P.obj C.Y₁T ⥤ P.obj C.Y₂T :=
  P.transform C.g'₂ C.g'₁ ((P.pull C.t').obj K)

/-- **Flat base change** (Stacks 08IR) for the face `sq₁`: `L(f'₂)^* R(t₁)_* ⟶ R t'_* L(g'₂)^*`
is invertible.  The square is Tor-independent since `f'₂` is flat. -/
def FlatBaseChangeLeft : Prop := IsIso (P.theta C.sq₁)

/-- **Flat base change** (Stacks 08IR) for the face `sq₂`: `L t₂^* R(f'₁)_* ⟶ R(g'₁)_* L t'^*`
is invertible.  The square is Tor-independent since `f'₁` is flat. -/
def FlatBaseChangeRight : Prop := IsIso (P.theta C.sq₂)

/-- **Projection formula** (Stacks 08EU, 08IN) for `t'`: for every `K`, the projection map
`R t'_* E ⊗ K ⟶ R t'_*(E ⊗ L t'^*K)` is invertible. -/
def ProjectionFormula : Prop := ∀ K : P.obj C.Y₁₂, IsIso (P.projMap C.t' K)

/-- The 2-cell `α^K : L t₂^* ∘ Φ_K ⟶ Φ_{L(t')^*K} ∘ L t₁^*` of **Lemma 6.11**
(`lem:fm_cube_flat_base_change_natural_isomorphism`): the pasting, in the order of the paper's
proof, of flat base change `θ₂` for `sq₂`, monoidality of `L t'^*`, and the pseudofunctoriality
isomorphism `λ_{sq₁} : L t'^* L(f'₂)^* ≅ L(g'₂)^* L t₁^*`. -/
def alpha (K : P.obj C.Y₁₂) : C.Φ P K ⋙ P.pull C.t₂ ⟶ P.pull C.t₁ ⋙ C.ΦT P K :=
  TwoSquare.hComp (P.lam C.sq₁).hom
    (TwoSquare.hComp (P.pullTensorRight C.t' K).hom (P.theta C.sq₂))

/-- The 2-cell `β^K : Φ_K ∘ R(t₁)_* ⟶ R(t₂)_* ∘ Φ_{L(t')^*K}` of **Lemma 10.1**
(`lem:fm_cube_pullback_natural_isomorphism`): the pasting, in the order of the paper's proof,
of flat base change `θ₁` for `sq₁`, the projection map for `t'`, and the pseudofunctoriality
isomorphism `ρ_{sq₂} : R(f'₁)_* R t'_* ≅ R(t₂)_* R(g'₁)_*`. -/
def beta (K : P.obj C.Y₁₂) : P.push C.t₁ ⋙ C.Φ P K ⟶ C.ΦT P K ⋙ P.push C.t₂ :=
  TwoSquare.vComp (P.theta C.sq₁)
    (TwoSquare.vComp (P.projMap C.t' K) (P.rho C.sq₂).hom)

/-- `α^K` is invertible under flat base change for `sq₂`. -/
lemma isIso_alpha (h : C.FlatBaseChangeRight P) (K : P.obj C.Y₁₂) : IsIso (C.alpha P K) := by
  have : IsIso (P.theta C.sq₂) := h
  unfold alpha TwoSquare.hComp
  infer_instance

/-- `β^K` is invertible under flat base change for `sq₁` and the projection formula for `t'`. -/
lemma isIso_beta (h : C.FlatBaseChangeLeft P) (hp : C.ProjectionFormula P)
    (K : P.obj C.Y₁₂) : IsIso (C.beta P K) := by
  have : IsIso (P.theta C.sq₁) := h
  have : IsIso (P.projMap C.t' K) := hp K
  unfold beta TwoSquare.vComp
  infer_instance

/-- **Lemma 6.11** (`lem:fm_cube_flat_base_change_natural_isomorphism`), the isomorphism
`α^K : L t₂^* ∘ Φ_K ≅ Φ_{L(t')^*K} ∘ L t₁^*` (input: flat base change for `sq₂`). -/
noncomputable def alphaIso (h : C.FlatBaseChangeRight P) (K : P.obj C.Y₁₂) :
    C.Φ P K ⋙ P.pull C.t₂ ≅ P.pull C.t₁ ⋙ C.ΦT P K :=
  haveI := C.isIso_alpha P h K
  asIso (C.alpha P K)

/-- **Lemma 10.1** (`lem:fm_cube_pullback_natural_isomorphism`), the isomorphism
`β^K : Φ_K ∘ R(t₁)_* ≅ R(t₂)_* ∘ Φ_{L(t')^*K}` (inputs: flat base change for `sq₁`, projection
formula for `t'`). -/
noncomputable def betaIso (h : C.FlatBaseChangeLeft P) (hp : C.ProjectionFormula P)
    (K : P.obj C.Y₁₂) : P.push C.t₁ ⋙ C.Φ P K ≅ C.ΦT P K ⋙ P.push C.t₂ :=
  haveI := C.isIso_beta P h hp K
  asIso (C.beta P K)

/-- **Lemma 6.11** (`lem:fm_cube_flat_base_change_natural_isomorphism`): in the situation of
Setup 2.20, for every `K ∈ D_qc(Y₁ ×_S Y₂)` there is a natural isomorphism
`L t₂^* ∘ Φ_K ≅ Φ_{L(t')^*K} ∘ L t₁^*` (namely `alphaIso`).  Input: flat base change (Stacks 08IR)
for the face `Y₁₂T = Y₁₂ ×_{Y₂} Y₂T`. -/
theorem lemma_6_11 (h : C.FlatBaseChangeRight P) (K : P.obj C.Y₁₂) :
    Nonempty (C.Φ P K ⋙ P.pull C.t₂ ≅ P.pull C.t₁ ⋙ C.ΦT P K) :=
  ⟨C.alphaIso P h K⟩

/-- **Lemma 10.1** (`lem:fm_cube_pullback_natural_isomorphism`): in the situation of Setup 2.20,
for every `K ∈ D_qc(Y₁ ×_S Y₂)` there is a natural isomorphism
`Φ_K ∘ R(t₁)_* ≅ R(t₂)_* ∘ Φ_{L(t')^*K}` (namely `betaIso`).  Inputs: flat base change
(Stacks 08IR) for the face `Y₁₂T = Y₁₂ ×_{Y₁} Y₁T` and the projection formula (Stacks 08EU,
08IN) for `t'`. -/
theorem lemma_10_1 (h : C.FlatBaseChangeLeft P) (hp : C.ProjectionFormula P)
    (K : P.obj C.Y₁₂) :
    Nonempty (P.push C.t₁ ⋙ C.Φ P K ≅ C.ΦT P K ⋙ P.push C.t₂) :=
  ⟨C.betaIso P h hp K⟩

/-- The mate of `θ₂` is the pseudofunctoriality isomorphism `ρ_{sq₂}` (Lemma 7.13). -/
lemma mateEquiv_theta_sq₂ :
    mateEquiv (P.adj C.t') (P.adj C.t₂) (P.theta C.sq₂) = (P.rho C.sq₂).hom := by
  rw [← P.lemma_7_13 C.sq₂]
  exact Equiv.apply_symm_apply _ _

/-- **Lemma 10.2** (`lem:integral_transform_is_morphism_of_adjoints`): `β^K` is the right mate of
`α^K` under the square with top `Φ_K`, bottom `Φ_{L(t')^*K}`, and vertical adjunctions
`L t₁^* ⊣ R(t₁)_*`, `L t₂^* ⊣ R(t₂)_*`.

Holds for the natural transformations, without any input.  Proof: mates of horizontal pastings
are vertical pastings of mates (Mathlib `mateEquiv_vcomp`, the part of GL26 Lemma 7.8 used);
the mate of `λ_{sq₁}` is `θ₁` by Lemma-Definition 7.13(2) (definition of `theta`), the mate of
monoidality is the projection map (definition of `projMap`), and the mate of `θ₂` is `ρ_{sq₂}`
by Lemma 7.13 (`lemma_7_13`). -/
theorem lemma_10_2 (K : P.obj C.Y₁₂) :
    mateEquiv (P.adj C.t₁) (P.adj C.t₂) (C.alpha P K) = C.beta P K := by
  have h₁ := mateEquiv_vcomp (P.adj C.t₁) (P.adj C.t') (P.adj C.t₂) (P.lam C.sq₁).hom
    (TwoSquare.hComp (P.pullTensorRight C.t' K).hom (P.theta C.sq₂))
  have h₂ := mateEquiv_vcomp (P.adj C.t') (P.adj C.t') (P.adj C.t₂)
    (P.pullTensorRight C.t' K).hom (P.theta C.sq₂)
  exact h₁.trans (congrArg (TwoSquare.vComp _)
    (h₂.trans (congrArg (TwoSquare.vComp _) (mateEquiv_theta_sq₂ P C))))

/-- **Lemma 10.2** (`lem:integral_transform_is_morphism_of_adjoints`), the other half: `α^K` is
the left mate of `β^K`. -/
theorem lemma_10_2' (K : P.obj C.Y₁₂) :
    (mateEquiv (P.adj C.t₁) (P.adj C.t₂)).symm (C.beta P K) = C.alpha P K := by
  rw [← C.lemma_10_2 P K]
  exact Equiv.symm_apply_apply _ _

/-- **Lemma 10.2** for the isomorphisms of Lemmas 6.11 and 10.1. -/
theorem lemma_10_2_iso (h : C.FlatBaseChangeRight P) (h' : C.FlatBaseChangeLeft P)
    (hp : C.ProjectionFormula P) (K : P.obj C.Y₁₂) :
    mateEquiv (P.adj C.t₁) (P.adj C.t₂) (C.alphaIso P h K).hom = (C.betaIso P h' hp K).hom :=
  C.lemma_10_2 P K

end FMCube

/-! ### Non-vacuity -/

namespace FMCube

open CategoryTheory CategoryTheory.Functor BaseChangeMates

universe v u v₁ u₁

section Example

variable (S : Type u) [Category.{v} S] (C : Type u₁) [Category.{v₁} C] (T : C ⥤ C ⥤ C)

/-- The constant data: every space ↦ `C`, `L f^* = R f_* = 𝟭`, tensor `T`, monoidality the
identity. -/
def constTensorPullPushData : TensorPullPushData.{v, u, v₁, u₁} S where
  toPullPushData := constPullPushData S C
  tensor _ := T
  pullTensor _ := Iso.refl _

/-- The all-identity cube on an object `X` of `S`. -/
def constFMCube (X : S) : FMCube S where
  S₀ := X
  T := X
  Y₁ := X
  Y₂ := X
  Y₁₂ := X
  Y₁T := X
  Y₂T := X
  Y₁₂T := X
  t := 𝟙 X
  f₁ := 𝟙 X
  f₂ := 𝟙 X
  f'₁ := 𝟙 X
  f'₂ := 𝟙 X
  t₁ := 𝟙 X
  t₂ := 𝟙 X
  t' := 𝟙 X
  g₁ := 𝟙 X
  g₂ := 𝟙 X
  g'₁ := 𝟙 X
  g'₂ := 𝟙 X
  isPullback_Y₁₂ := IsPullback.id_vert (𝟙 X)
  isPullback_Y₁T := IsPullback.id_vert (𝟙 X)
  isPullback_Y₂T := IsPullback.id_vert (𝟙 X)
  isPullback₁ := IsPullback.id_vert (𝟙 X)
  isPullback₂ := IsPullback.id_vert (𝟙 X)
  comm_T := rfl

lemma constFMCube_flatBaseChangeLeft (X : S) :
    (constFMCube S X).FlatBaseChangeLeft (constTensorPullPushData S C T) :=
  constPullPushData_isIso_theta S C _

lemma constFMCube_flatBaseChangeRight (X : S) :
    (constFMCube S X).FlatBaseChangeRight (constTensorPullPushData S C T) :=
  constPullPushData_isIso_theta S C _

lemma constFMCube_projectionFormula (X : S) :
    (constFMCube S X).ProjectionFormula (constTensorPullPushData S C T) := by
  intro K
  have hu : IsIso (Adjunction.id (C := C)).unit := by
    rw [Adjunction.id_unit]; infer_instance
  have hc : IsIso (Adjunction.id (C := C)).counit := by
    rw [Adjunction.id_counit]; infer_instance
  let P := constTensorPullPushData S C T
  have : IsIso (P.adj (𝟙 X)).unit := hu
  have : IsIso (P.adj (𝟙 X)).counit := hc
  exact isIso_mate (P.adj (𝟙 X)) (P.adj (𝟙 X)) (P.pullTensorRight (𝟙 X) K).hom

/-- All inputs of Lemmas 6.11, 10.1, 10.2 hold simultaneously in a concrete example
(`S = C = Type`, tensor the cartesian product). -/
example :
    (constFMCube Type PUnit).FlatBaseChangeLeft
        (constTensorPullPushData Type Type (MonoidalCategory.curriedTensor Type)) ∧
      (constFMCube Type PUnit).FlatBaseChangeRight
        (constTensorPullPushData Type Type (MonoidalCategory.curriedTensor Type)) ∧
      (constFMCube Type PUnit).ProjectionFormula
        (constTensorPullPushData Type Type (MonoidalCategory.curriedTensor Type)) :=
  ⟨constFMCube_flatBaseChangeLeft _ _ _ _, constFMCube_flatBaseChangeRight _ _ _ _,
    constFMCube_projectionFormula _ _ _ _⟩

end Example

end FMCube

end RelativeFM
