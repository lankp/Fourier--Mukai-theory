/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Prelim.Mates
import FourierMukai.Scheme.FMCube
import Spaces.AxiomMathInputs
import Spaces.NonVacuity
import Spaces.BaseChange.Inputs
import Spaces.BaseChange.PullPush

/-!
# GL26 Setup 2.20, Lemmas 6.11 and 10.1 for algebraic spaces

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26):

* **Setup 2.20** (`setup:fm_cube_pullback`): a cube of algebraic spaces is an
  `FMCube (AlgebraicSpaces B S hS)` (`FourierMukai/Scheme/FMCube.lean`); the functors are those of
  `tensorPullPushData B S hS`: `D(𝒪_X)`, `Lf^*`, `Rf_*`, `⊗^L` and Stacks 07A4 of AxiomMath, with
  the pseudofunctoriality of `Spaces/BaseChange/PullPush.lean`;
* **Lemma 6.11** (`lem:fm_cube_flat_base_change_natural_isomorphism`): `lemma_6_11`,
  `lemma_6_11_of_isFlat`;
* **Lemma 10.1** (`lem:fm_cube_pullback_natural_isomorphism`): `lemma_10_1`, `lemma_10_1_of`;
* **Lemma 10.2** (`lem:integral_transform_is_morphism_of_adjoints`): `lemma_10_2` (no input).

The 2-cells are literally `FMCube.alpha`, `FMCube.beta` (the pastings of the paper's proofs) for
`P = tensorPullPushData B S hS`.

## Inputs

Over spaces, flat base change and the projection formula hold on `D_qc`, not on all of `D(𝒪)`,
so the abstract inputs `FMCube.FlatBaseChangeLeft`/`Right`, `ProjectionFormula` (invertibility
on `D(𝒪)`) are replaced by their `D_qc` forms, written out as hypotheses (`∀ E, Dqc E → IsIso …`),
and Lemmas 6.11 and 10.1 are stated objectwise on `D_qc`.

* Flat base change for the face `Y₁₂T = Y₁₂ ×_{Y₂} Y₂T` (used by 6.11) is **proved** from the
  tagged AxiomMath inputs `FlatBaseChangeInput` (Stacks 0A1K/08IR, pushed morphism flat) and
  `CompIsoAgreeInput` (the two AxiomMath spellings of Stacks 0D6D agree), for `f'₁` flat,
  quasi-compact and quasi-separated: `flatBaseChangeRightQc_of_isFlat`.  It rests on
  `theta_app_eq_baseChangeMap`: AxiomMath's base change map is the `θ_□` of GL26
  Lemma-Definition 7.13 built here.
* The projection formula for `t'` (used by 10.1) is **proved** from the tagged input
  `Tag08INInput` (Stacks 08IN) for `t'` quasi-compact and quasi-separated:
  `projectionFormulaQc_of`, through `projMap_app_eq` (the projection map of `FMCube`, the mate of
  Stacks 07A4, is AxiomMath's).
* Flat base change for the face `Y₁₂T = Y₁₂ ×_{Y₁} Y₁T` (used by 10.1) is **a hypothesis, an
  open item**: it is Stacks 08IR for a square whose *pulled* morphism `f'₂` is flat while the
  pushed morphism `t₁` is not.  AxiomMath proves it as the composite of
  `isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent` (08IR), `torIndependent_of_isFlat_left`
  and `TorIndependent.symm`, all stated through `AlgebraicGeometry.Space.TorIndependent`
  (`Spaces/TorIndependence.lean`, Stacks 08IP), a definition outside the `Spaces` import list whose
  body involves `Tor` of étale local rings, so it cannot be written out here.  Adding
  `StacksFrontier.AlgebraicGeometry.Spaces.TorIndependence` (7 new modules in the closure) to
  `scripts/axiommath/spaces-imports.txt` would make the three verbatim tagged inputs, and the
  hypothesis would then be discharged exactly as for the other face.
* Stacks 08F4, 08F5 (`Tag08F4Input`, `Tag08F5Input`, `Spaces/AxiomMathInputs.lean`): the
  objects at which flat base change and the projection formula are applied lie in `D_qc`.

## Deviations from GL26

* Objectwise on `D_qc`: Lemmas 6.11 and 10.1 say that `α^K`, `β^K` (natural transformations of
  functors on `D(𝒪)`) are invertible at every object of `D_qc`, i.e. restrict to natural
  isomorphisms on `D_qc`, which is the paper's statement (that `Φ` lands in `D_qc` is
  Stacks 08FA for `f'₁`, and is not needed for invertibility).
* "Noetherian", "proper", "flat" of Setup 2.20 are replaced by the properties of individual
  morphisms that the proofs use: `f'₁` flat, quasi-compact, quasi-separated (6.11); `t'`
  quasi-compact, quasi-separated (10.1).  They follow from Setup 2.20 by stability of flatness and
  of quasi-compact quasi-separated morphisms under base change; that implication is not formalized
  here.
* Mathlib conventions as in `FourierMukai/Scheme/FMCube.lean`.

## Implementation note

The `Spaces` layer elaborates `D(𝒪_X)` with `SheafOfModules.instAbelian` at high priority.  The
kernel then becomes very slow (it unfolds AxiomMath's derived categories) when it has to identify
components (`.app E`) of natural transformations built through different spellings
(`(tensorPullPushData …).pull f` against `Spaces.pull f`, a named `Prop` against its body).  The
bridges are therefore proved as equalities of natural transformations, then specialised with
`congrArg`, and the `D_qc` hypotheses are written out rather than named.

## Non-vacuity

The identity cube on any algebraic space (`FMCube.constFMCube`) satisfies all three `D_qc`
hypotheses (`constFMCube_flatBaseChangeRightQc`, `…LeftQc`, `…projectionFormulaQc`: the base change
and projection maps of identity squares are invertible), and `D_qc` contains a zero object, so
Lemmas 6.11 and 10.1 apply (`lemma_6_11_id`, `lemma_10_1_id`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Space
  RelativeFM.BaseChangeMates RelativeFM.FMCube
open scoped CategoryTheory.Prod

namespace RelativeFM.Spaces.BaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Two generic lemmas on mates and pastings -/

section Generic

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Category C₅] [Category C₆]

/-- The components of a mate (Mathlib's `mateEquiv`), through `mate_app` of
`FourierMukai/Prelim/Mates.lean`. -/
lemma mateEquiv_app_eq {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (d : C₂) :
    (mateEquiv adj₁ adj₂ α).app d = adj₂.unit.app (G.obj (R₁.obj d)) ≫
      R₂.map (α.app (R₁.obj d)) ≫ R₂.map (H.map (adj₁.counit.app d)) :=
  mate_app adj₁ adj₂ α d

/-- A component of a horizontal pasting of 2-squares is invertible when the two relevant
components are. -/
lemma isIso_hComp_app {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆} (w : TwoSquare T L R B)
    (w' : TwoSquare T' R R' B') (X : C₁) [IsIso (w.app X)] [IsIso (w'.app (T.obj X))] :
    IsIso ((TwoSquare.hComp w w').app X) := by
  simp only [TwoSquare.hComp, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app]
  infer_instance

/-- A component of a vertical pasting of 2-squares is invertible when the two relevant
components are. -/
lemma isIso_vComp_app {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    {L' : C₃ ⥤ C₅} {R'' : C₄ ⥤ C₆} {B'' : C₅ ⥤ C₆} (w : TwoSquare T L R B)
    (w' : TwoSquare B L' R'' B'') (X : C₁) [IsIso (w.app X)] [IsIso (w'.app (L.obj X))] :
    IsIso ((TwoSquare.vComp w w').app X) := by
  simp only [TwoSquare.vComp, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app]
  infer_instance

end Generic

/-! ### The tensor product and Stacks 07A4 -/

/-- **Stacks 07A4**, curried: `Lf^*(A ⊗^L K) ≅ Lf^*A ⊗^L Lf^*K`, natural in `A` and `K`; the
components are those of AxiomMath's `smallEtaleDerivedPullbackTensorIso f`. -/
def pullTensor {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    tensor Y ⋙ (whiskeringRight _ _ _).obj (pull f) ≅
      pull f ⋙ tensor X ⋙ (whiskeringLeft _ _ _).obj (pull f) :=
  NatIso.ofComponents
    (fun A => NatIso.ofComponents
      (fun K => (smallEtaleDerivedPullbackTensorIso f).app (A, K))
      (fun {K K'} k => by
        have h := (smallEtaleDerivedPullbackTensorIso f).hom.naturality
          ((𝟙 A, k) : (A, K) ⟶ (A, K'))
        simpa using h))
    (fun {A A'} a => by
      ext K
      have h := (smallEtaleDerivedPullbackTensorIso f).hom.naturality
        ((a, 𝟙 K) : (A, K) ⟶ (A', K))
      simpa using h)

variable (B S hS) in
/-- **The six-functor data of GL26 Setup 2.20 for algebraic spaces**: `pullPushData` (derived
categories, `Lf^*`, `Rf_*`, pseudofunctoriality) with `⊗^L` and Stacks 07A4. -/
abbrev tensorPullPushData : TensorPullPushData (AlgebraicSpaces B S hS) where
  toPullPushData := pullPushData B S hS
  tensor X := tensor X
  pullTensor f := pullTensor f

variable (C : FMCube (AlgebraicSpaces B S hS))

/-! ### AxiomMath's base change map and projection map are those of GL26 §7.2 -/

/-- AxiomMath's canonical identification of a factorisation, unfolded. -/
lemma canon_iso_eq_compIso {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (b : Y ⟶ Z) (k : X ⟶ Z)
    (h : a ≫ b = k) :
    (canon B S hS).iso a b k h = smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS a b ≪≫
      eqToIso (congrArg (fun m => smallEtaleDerivedModulePullback B S hS m) h) := rfl

/-- `λ_□` of `pullPushData` through AxiomMath's canonical composition isomorphisms. -/
lemma lam_hom_eq {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : CommSq f' g' g f) (w : g' ≫ f = f' ≫ g) :
    ((tensorPullPushData B S hS).toPullPushData.lam sq).hom =
      (smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS f' g).hom ≫
        (smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS g' f ≪≫
          eqToIso (congrArg (fun f ↦ pull f) w)).inv := by
  change ((canon B S hS).iso f' g _ rfl).hom ≫ eqToHom (by rw [sq.w]) ≫
    ((canon B S hS).iso g' f _ rfl).inv = _
  rw [canon_iso_eq_compIso, canon_iso_eq_compIso]
  simp only [Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, Category.assoc,
    eqToHom_refl, Category.id_comp]

/-- Stacks' base change map is the mate of the comparison of the two composites. -/
lemma baseChangeMap_eq_mate {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (w : g' ≫ f = f' ≫ g) (E : D B S hS X) :
    Stacks.CategoryTheory.BaseChange.map (pullPushAdj f) (pullPushAdj f') (moduleCompIso f' g)
        (moduleCompIso g' f ≪≫ eqToIso (congrArg (fun f ↦ pull f) w)) E =
      (mateEquiv (pullPushAdj f) (pullPushAdj f') ((moduleCompIso f' g).hom ≫
        (moduleCompIso g' f ≪≫ eqToIso (congrArg (fun f ↦ pull f) w)).inv)).app E := rfl

lemma comparison_eq (hA : CompIsoAgreeInput B S hS) {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (w : g' ≫ f = f' ≫ g) :
    ((moduleCompIso f' g).hom ≫
        (moduleCompIso g' f ≪≫ eqToIso (congrArg (fun f ↦ pull f) w)).inv) =
      (smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS f' g).hom ≫
        (smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS g' f ≪≫
          eqToIso (congrArg (fun f ↦ pull f) w)).inv := by
  rw [hA, hA]

lemma theta_eq_mate {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq f' g' g f) :
    (tensorPullPushData B S hS).toPullPushData.theta sq =
      mateEquiv (pullPushAdj f) (pullPushAdj f')
        ((tensorPullPushData B S hS).toPullPushData.lam sq).hom := rfl

lemma lam_hom_eq_moduleCompIso (hA : CompIsoAgreeInput B S hS)
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : CommSq f' g' g f) (w : g' ≫ f = f' ≫ g) :
    ((tensorPullPushData B S hS).toPullPushData.lam sq).hom =
      (moduleCompIso f' g).hom ≫
        (moduleCompIso g' f ≪≫ eqToIso (congrArg (fun f ↦ pull f) w)).inv :=
  (lam_hom_eq sq w).trans (comparison_eq hA w).symm

lemma mate_lam_eq (hA : CompIsoAgreeInput B S hS) {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq f' g' g f)
    (w : g' ≫ f = f' ≫ g) :
    mateEquiv (pullPushAdj f) (pullPushAdj f')
        ((tensorPullPushData B S hS).toPullPushData.lam sq).hom =
      mateEquiv (pullPushAdj f) (pullPushAdj f') ((moduleCompIso f' g).hom ≫
        (moduleCompIso g' f ≪≫ eqToIso (congrArg (fun f ↦ pull f) w)).inv) :=
  congrArg (mateEquiv (pullPushAdj f) (pullPushAdj f')) (lam_hom_eq_moduleCompIso hA sq w)

lemma twoSquare_eq_mate {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (w : g' ≫ f = f' ≫ g) :
    Stacks.CategoryTheory.BaseChange.twoSquare (pullPushAdj f) (pullPushAdj f')
        (moduleCompIso f' g) (moduleCompIso g' f ≪≫ eqToIso (congrArg (fun f ↦ pull f) w)) =
      mateEquiv (pullPushAdj f) (pullPushAdj f') ((moduleCompIso f' g).hom ≫
        (moduleCompIso g' f ≪≫ eqToIso (congrArg (fun f ↦ pull f) w)).inv) := rfl

/-- **AxiomMath's base change map is `θ_□`** (GL26 Lemma-Definition 7.13, `PullPushData.theta`):
for a commutative square `g' ≫ f = f' ≫ g` of algebraic spaces (Mathlib's `CommSq f' g' g f`),
the component at `E` of the base change map of `tensorPullPushData` is AxiomMath's
`smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w E` (Stacks 07A7; written by its body, as
in `FlatBaseChangeInput`), granted that AxiomMath's two spellings of Stacks 0D6D agree
(`CompIsoAgreeInput`).  (Proved through equalities of natural transformations: comparing the
components directly makes the kernel unfold AxiomMath's derived categories.) -/
theorem theta_app_eq_baseChangeMap (hA : CompIsoAgreeInput B S hS)
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : CommSq f' g' g f) (w : g' ≫ f = f' ≫ g) (E : D B S hS X) :
    ((tensorPullPushData B S hS).toPullPushData.theta sq).app E =
      Stacks.CategoryTheory.BaseChange.map (pullPushAdj f) (pullPushAdj f') (moduleCompIso f' g)
        (moduleCompIso g' f ≪≫ eqToIso (congrArg (fun f ↦ pull f) w)) E :=
  congrArg (fun t => NatTrans.app t E)
    ((theta_eq_mate sq).trans ((mate_lam_eq hA sq w).trans (twoSquare_eq_mate w).symm))

/-- AxiomMath's flat base change (`FlatBaseChangeInput`), for the face `Y₁₂T = Y₁₂ ×_{Y₂} Y₂T`. -/
theorem isIso_baseChangeMap_sq₂ (hF : FlatBaseChangeInput B S hS) (hfl : IsFlat B S hS C.f'₁.hom)
    (hqc : IsQuasiCompact B S hS C.f'₁.hom) (hqs : IsQuasiSeparated B S hS C.f'₁.hom)
    (E : D B S hS C.Y₁₂) (hE : Dqc C.Y₁₂ E) :
    IsIso (Stacks.CategoryTheory.BaseChange.map (pullPushAdj C.f'₁) (pullPushAdj C.g'₁)
      (moduleCompIso C.g'₁ C.t₂) (moduleCompIso C.t' C.f'₁ ≪≫
        eqToIso (congrArg (fun f ↦ pull f) C.isPullback₂.w)) E) :=
  hF C.isPullback₂ hqc hqs hfl E hE

/-- **Flat base change on `D_qc` for the face `Y₁₂T = Y₁₂ ×_{Y₂} Y₂T`, from AxiomMath**: if
`f'₁ : Y₁₂ ⟶ Y₂` is flat, quasi-compact and quasi-separated, then
`θ₂ : L t₂^* R(f'₁)_* E ⟶ R(g'₁)_* L t'^* E` is invertible for every `E ∈ D_qc(Y₁₂)`.  Inputs:
`FlatBaseChangeInput` (Stacks 0A1K/08IR), `CompIsoAgreeInput` (Stacks 0D6D). -/
theorem flatBaseChangeRightQc_of_isFlat (hF : FlatBaseChangeInput B S hS)
    (hA : CompIsoAgreeInput B S hS) (hfl : IsFlat B S hS C.f'₁.hom)
    (hqc : IsQuasiCompact B S hS C.f'₁.hom) (hqs : IsQuasiSeparated B S hS C.f'₁.hom) :
    ∀ E : D B S hS C.Y₁₂, Dqc C.Y₁₂ E →
      IsIso (((tensorPullPushData B S hS).theta C.sq₂).app E) := fun E hE =>
  (congrArg IsIso (theta_app_eq_baseChangeMap hA C.sq₂ C.isPullback₂.w E)).mpr
    (isIso_baseChangeMap_sq₂ C hF hfl hqc hqs E hE)

lemma projMap_eq_mate {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (K : D B S hS Y) :
    (tensorPullPushData B S hS).projMap f K =
      mateEquiv (pullPushAdj f) (pullPushAdj f) ((tensorPullPushData B S hS).pullTensorRight f K).hom :=
  rfl

/-- **AxiomMath's projection map is that of `FMCube`**: the component at `E` of
`TensorPullPushData.projMap f K` (the mate of Stacks 07A4 under `Lf^* ⊣ Rf_*`) is AxiomMath's
`smallEtaleProjectionFormulaMap B S hS f E K` (written by its body). -/
theorem projMap_app_eq {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (K : D B S hS Y)
    (E : D B S hS X) :
    ((tensorPullPushData B S hS).projMap f K).app E = projectionFormulaMap f E K := by
  rw [projMap_eq_mate, mateEquiv_app_eq, projectionFormulaMap, Adjunction.homEquiv_unit,
    Functor.map_comp]
  simp [TensorPullPushData.pullTensorRight, tensorPullPushData, pullTensor]

/-- **The projection formula on `D_qc` for `t'`, from AxiomMath**: if `t' : Y₁₂T ⟶ Y₁₂` is
quasi-compact and quasi-separated, `R t'_* E ⊗^L K ⟶ R t'_*(E ⊗^L L t'^* K)` is invertible for
`E ∈ D_qc(Y₁₂T)`, `K ∈ D_qc(Y₁₂)`.  Input: `Tag08INInput` (Stacks 08IN). -/
theorem projectionFormulaQc_of (h : Tag08INInput B S hS) (hqc : IsQuasiCompact B S hS C.t'.hom)
    (hqs : IsQuasiSeparated B S hS C.t'.hom) :
    ∀ K : D B S hS C.Y₁₂, Dqc C.Y₁₂ K → ∀ E : D B S hS C.Y₁₂T, Dqc C.Y₁₂T E →
      IsIso (((tensorPullPushData B S hS).projMap C.t' K).app E) := fun K hK E hE =>
  (congrArg IsIso (projMap_app_eq C.t' K E)).mpr (h C.t' hqc hqs E hE K hK)

/-! ### Lemmas 6.11 and 10.1 -/

/-- The components of `α^K` at objects of `D_qc(Y₁)` are invertible, for `K ∈ D_qc(Y₁₂)`. -/
theorem isIso_alpha_app (h : ∀ E : D B S hS C.Y₁₂, Dqc C.Y₁₂ E →
      IsIso (((tensorPullPushData B S hS).theta C.sq₂).app E)) (h4 : Tag08F4Input B S hS)
    (h5 : Tag08F5Input B S hS) {K : D B S hS C.Y₁₂} (hK : Dqc C.Y₁₂ K) {E : D B S hS C.Y₁}
    (hE : Dqc C.Y₁ E) : IsIso ((C.alpha (tensorPullPushData B S hS) K).app E) := by
  have : IsIso (((tensorPullPushData B S hS).theta C.sq₂).app
      (((tensorPullPushData B S hS).tensorRight C.Y₁₂ K).obj
        (((tensorPullPushData B S hS).pull C.f'₂).obj E))) :=
    h _ (h5 C.Y₁₂ _ _ (h4 C.f'₂ E hE) hK)
  have : IsIso ((TwoSquare.hComp ((tensorPullPushData B S hS).pullTensorRight C.t' K).hom
      ((tensorPullPushData B S hS).theta C.sq₂)).app
        (((tensorPullPushData B S hS).pull C.f'₂).obj E)) := isIso_hComp_app _ _ _
  exact isIso_hComp_app _ _ _

/-- The components of `β^K` at objects of `D_qc(Y₁T)` are invertible, for `K ∈ D_qc(Y₁₂)`. -/
theorem isIso_beta_app (h : ∀ E : D B S hS C.Y₁T, Dqc C.Y₁T E →
      IsIso (((tensorPullPushData B S hS).theta C.sq₁).app E)) (hp : ∀ K : D B S hS C.Y₁₂, Dqc C.Y₁₂ K → ∀ E : D B S hS C.Y₁₂T, Dqc C.Y₁₂T E →
      IsIso (((tensorPullPushData B S hS).projMap C.t' K).app E))
    (h4 : Tag08F4Input B S hS) {K : D B S hS C.Y₁₂} (hK : Dqc C.Y₁₂ K) {E : D B S hS C.Y₁T}
    (hE : Dqc C.Y₁T E) : IsIso ((C.beta (tensorPullPushData B S hS) K).app E) := by
  have : IsIso (((tensorPullPushData B S hS).theta C.sq₁).app E) := h E hE
  have : IsIso (((tensorPullPushData B S hS).projMap C.t' K).app
      (((tensorPullPushData B S hS).pull C.g'₂).obj E)) := hp K hK _ (h4 C.g'₂ E hE)
  have : IsIso ((TwoSquare.vComp ((tensorPullPushData B S hS).projMap C.t' K)
      ((tensorPullPushData B S hS).rho C.sq₂).hom).app
        (((tensorPullPushData B S hS).pull C.g'₂).obj E)) := isIso_vComp_app _ _ _
  exact isIso_vComp_app _ _ _

/-- **Lemma 6.11** (`lem:fm_cube_flat_base_change_natural_isomorphism`) for algebraic spaces: in
the situation of Setup 2.20, for `K ∈ D_qc(Y₁ ×_S Y₂)` the natural transformation
`α^K : L t₂^* ∘ Φ_K ⟶ Φ_{L(t')^*K} ∘ L t₁^*` (`FMCube.alpha`, of functors `D(Y₁) ⥤ D(Y₂ ×_S T)`) is
invertible at every object of `D_qc(Y₁)`; i.e. it restricts to a natural isomorphism of functors on
`D_qc(Y₁)`, which is the paper's statement.  Hypotheses: flat base change on `D_qc` for the face
`Y₁₂T = Y₁₂ ×_{Y₂} Y₂T` (`flatBaseChangeRightQc_of_isFlat`, used by `lemma_6_11_of_isFlat`),
Stacks 08F4 and 08F5. -/
theorem lemma_6_11 (h : ∀ E : D B S hS C.Y₁₂, Dqc C.Y₁₂ E →
      IsIso (((tensorPullPushData B S hS).theta C.sq₂).app E)) (h4 : Tag08F4Input B S hS)
    (h5 : Tag08F5Input B S hS) {K : D B S hS C.Y₁₂} (hK : Dqc C.Y₁₂ K) :
    ∀ E : D B S hS C.Y₁, Dqc C.Y₁ E → IsIso ((C.alpha (tensorPullPushData B S hS) K).app E) :=
  fun _ hE => isIso_alpha_app C h h4 h5 hK hE

/-- **Lemma 6.11** (`lem:fm_cube_flat_base_change_natural_isomorphism`) for algebraic spaces, with
the flatness hypothesis of Setup 2.20 in the form the proof uses: `f'₁ : Y₁ ×_S Y₂ ⟶ Y₂` flat,
quasi-compact and quasi-separated.  Only AxiomMath is assumed: the tagged inputs 0A1K/08IR
(`FlatBaseChangeInput`), 0D6D (`CompIsoAgreeInput`), 08F4, 08F5. -/
theorem lemma_6_11_of_isFlat (hF : FlatBaseChangeInput B S hS) (hA : CompIsoAgreeInput B S hS)
    (h4 : Tag08F4Input B S hS) (h5 : Tag08F5Input B S hS) (hfl : IsFlat B S hS C.f'₁.hom)
    (hqc : IsQuasiCompact B S hS C.f'₁.hom) (hqs : IsQuasiSeparated B S hS C.f'₁.hom)
    {K : D B S hS C.Y₁₂} (hK : Dqc C.Y₁₂ K) :
    ∀ E : D B S hS C.Y₁, Dqc C.Y₁ E → IsIso ((C.alpha (tensorPullPushData B S hS) K).app E) :=
  lemma_6_11 C (flatBaseChangeRightQc_of_isFlat C hF hA hfl hqc hqs) h4 h5 hK

/-- **Lemma 10.1** (`lem:fm_cube_pullback_natural_isomorphism`) for algebraic spaces: in the
situation of Setup 2.20, for `K ∈ D_qc(Y₁ ×_S Y₂)` the natural transformation
`β^K : Φ_K ∘ R(t₁)_* ⟶ R(t₂)_* ∘ Φ_{L(t')^*K}` (`FMCube.beta`, of functors `D(Y₁ ×_S T) ⥤ D(Y₂)`)
is invertible at every object of `D_qc(Y₁ ×_S T)`, i.e. restricts to a natural isomorphism on
`D_qc(Y₁ ×_S T)`.  Hypotheses: flat base change on `D_qc` for the face
`Y₁₂T = Y₁₂ ×_{Y₁} Y₁T` (**an open item**, see the module docstring), the projection formula on
`D_qc` for `t'` (`projectionFormulaQc_of`, used by `lemma_10_1_of`), and Stacks 08F4. -/
theorem lemma_10_1 (h : ∀ E : D B S hS C.Y₁T, Dqc C.Y₁T E →
      IsIso (((tensorPullPushData B S hS).theta C.sq₁).app E)) (hp : ∀ K : D B S hS C.Y₁₂, Dqc C.Y₁₂ K → ∀ E : D B S hS C.Y₁₂T, Dqc C.Y₁₂T E →
      IsIso (((tensorPullPushData B S hS).projMap C.t' K).app E))
    (h4 : Tag08F4Input B S hS) {K : D B S hS C.Y₁₂} (hK : Dqc C.Y₁₂ K) :
    ∀ E : D B S hS C.Y₁T, Dqc C.Y₁T E → IsIso ((C.beta (tensorPullPushData B S hS) K).app E) :=
  fun _ hE => isIso_beta_app C h hp h4 hK hE

/-- **Lemma 10.1** (`lem:fm_cube_pullback_natural_isomorphism`) for algebraic spaces, with the
projection formula discharged by AxiomMath (`Tag08INInput`, Stacks 08IN) for `t'` quasi-compact
and quasi-separated.  Still conditional on flat base change for the face
`Y₁₂T = Y₁₂ ×_{Y₁} Y₁T` (Stacks 08IR for a flat pulled morphism; an open item). -/
theorem lemma_10_1_of (h : ∀ E : D B S hS C.Y₁T, Dqc C.Y₁T E →
      IsIso (((tensorPullPushData B S hS).theta C.sq₁).app E)) (hIN : Tag08INInput B S hS)
    (h4 : Tag08F4Input B S hS) (hqc : IsQuasiCompact B S hS C.t'.hom)
    (hqs : IsQuasiSeparated B S hS C.t'.hom) {K : D B S hS C.Y₁₂} (hK : Dqc C.Y₁₂ K) :
    ∀ E : D B S hS C.Y₁T, Dqc C.Y₁T E → IsIso ((C.beta (tensorPullPushData B S hS) K).app E) :=
  lemma_10_1 C h (projectionFormulaQc_of C hIN hqc hqs) h4 hK

/-- **Lemma 10.2** (`lem:integral_transform_is_morphism_of_adjoints`) for algebraic spaces: `β^K`
is the right mate of `α^K` (no input; `FMCube.lemma_10_2` for `tensorPullPushData`). -/
theorem lemma_10_2 (K : D B S hS C.Y₁₂) :
    mateEquiv (pullPushAdj C.t₁) (pullPushAdj C.t₂) (C.alpha (tensorPullPushData B S hS) K) =
      C.beta (tensorPullPushData B S hS) K :=
  C.lemma_10_2 (tensorPullPushData B S hS) K

/-! ### Non-vacuity: the identity cube -/

section NonVacuity

variable (X : AlgebraicSpaces B S hS)

instance isIso_pullPushAdj_id_unit : IsIso (pullPushAdj (𝟙 X)).unit := by
  have hff : (pull (𝟙 X)).FullyFaithful :=
    (Functor.FullyFaithful.id (D B S hS X)).ofIso ((canon B S hS).idIso X).symm
  have := hff.full
  have := hff.faithful
  infer_instance

instance isIso_pullPushAdj_id_counit : IsIso (pullPushAdj (𝟙 X)).counit := by
  have hff : (push (𝟙 X)).FullyFaithful :=
    (Functor.FullyFaithful.id (D B S hS X)).ofIso ((pullPushData B S hS).pushId X).symm
  have := hff.full
  have := hff.faithful
  infer_instance

lemma isIso_theta_const_sq₂ :
    IsIso ((tensorPullPushData B S hS).theta (constFMCube (AlgebraicSpaces B S hS) X).sq₂) := by
  rw [theta_eq_mate]
  exact isIso_mate (pullPushAdj (𝟙 X)) (pullPushAdj (𝟙 X))
    ((tensorPullPushData B S hS).toPullPushData.lam _).hom

lemma isIso_theta_const_sq₁ :
    IsIso ((tensorPullPushData B S hS).theta (constFMCube (AlgebraicSpaces B S hS) X).sq₁) := by
  rw [theta_eq_mate]
  exact isIso_mate (pullPushAdj (𝟙 X)) (pullPushAdj (𝟙 X))
    ((tensorPullPushData B S hS).toPullPushData.lam _).hom

lemma isIso_projMap_id (K : D B S hS X) :
    IsIso ((tensorPullPushData B S hS).projMap (𝟙 X) K) := by
  rw [projMap_eq_mate]
  exact isIso_mate (pullPushAdj (𝟙 X)) (pullPushAdj (𝟙 X))
    ((tensorPullPushData B S hS).pullTensorRight (𝟙 X) K).hom

/-- In the identity cube on `X` (`FMCube.constFMCube`), flat base change holds for both faces
and the projection formula for `t' = 𝟙`: the hypotheses of `lemma_6_11` and `lemma_10_1` are
satisfiable. -/
theorem constFMCube_flatBaseChangeRightQc :
    ∀ E : D B S hS X, Dqc X E → IsIso (((tensorPullPushData B S hS).theta
      (constFMCube (AlgebraicSpaces B S hS) X).sq₂).app E) := fun E _ =>
  @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (isIso_theta_const_sq₂ X) E

theorem constFMCube_flatBaseChangeLeftQc :
    ∀ E : D B S hS X, Dqc X E → IsIso (((tensorPullPushData B S hS).theta
      (constFMCube (AlgebraicSpaces B S hS) X).sq₁).app E) := fun E _ =>
  @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (isIso_theta_const_sq₁ X) E

theorem constFMCube_projectionFormulaQc :
    ∀ K : D B S hS X, Dqc X K → ∀ E : D B S hS X, Dqc X E →
      IsIso (((tensorPullPushData B S hS).projMap (𝟙 X) K).app E) := fun K _ E _ =>
  @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (isIso_projMap_id X K) E

/-- A zero object of `D(𝒪_X)` (the derived category has one). -/
noncomputable def zeroObj : D B S hS X :=
  Classical.choose (Limits.HasZeroObject.zero (C := D B S hS X))

lemma isZero_zeroObj : Limits.IsZero (zeroObj X) :=
  Classical.choose_spec (Limits.HasZeroObject.zero (C := D B S hS X))

/-- Lemma 6.11 applies to the identity cube, at a zero kernel. -/
theorem lemma_6_11_id (h4 : Tag08F4Input B S hS) (h5 : Tag08F5Input B S hS) :
    ∀ E : D B S hS X, Dqc X E → IsIso (((constFMCube (AlgebraicSpaces B S hS) X).alpha
      (tensorPullPushData B S hS) (zeroObj X)).app E) :=
  lemma_6_11 (constFMCube (AlgebraicSpaces B S hS) X) (constFMCube_flatBaseChangeRightQc X) h4 h5
    (Dqc_of_isZero (isZero_zeroObj X))

/-- Lemma 10.1 applies to the identity cube, at a zero kernel. -/
theorem lemma_10_1_id (h4 : Tag08F4Input B S hS) :
    ∀ E : D B S hS X, Dqc X E → IsIso (((constFMCube (AlgebraicSpaces B S hS) X).beta
      (tensorPullPushData B S hS) (zeroObj X)).app E) :=
  lemma_10_1 (constFMCube (AlgebraicSpaces B S hS) X) (constFMCube_flatBaseChangeLeftQc X)
    (constFMCube_projectionFormulaQc X) h4 (Dqc_of_isZero (isZero_zeroObj X))

end NonVacuity

end RelativeFM.Spaces.BaseChange
