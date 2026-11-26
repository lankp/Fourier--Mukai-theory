/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.RelativePerfect
import Spaces.IntegralTransform
import StacksFrontier.AlgebraicGeometry.Spaces.Flat
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# The notions of GL26's headline statements over algebraic spaces

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26).  The
vocabulary that the statements of `Spaces/Statements/Main.lean` need beyond `Spaces/`:
Noetherian algebraic spaces, proper, flat, finite type and quasi-affine morphisms, the space
`|X|` of points with its topology, representatives `Spec k ⟶ X` of points (GL26 §2.2,
`sec:prelim_stacks_notions`, and §2.3, `sec:prelim_fm_setup`), the base-change cube of
**Setup 2.20** (`setup:fm_cube_pullback`) with the base-changed kernel `L(t')^*K` and the
fibre transform `Φ_{L(t')^*K}`, restriction of a functor to full subcategories ("fully
faithful / an equivalence on `D_qc`, on `D^b_coh`"), and the loci `fm(K)`, `FM(K)` of
**Definition 12.1** (`def:fm_locus`).

Everything here is a *definition* built from AxiomMath/Stacks' definitions (modules of
`scripts/axiommath/spaces-imports.txt`) and Mathlib; nothing is assumed and no AxiomMath
theorem is used.

## Dictionary

| GL26 | here | AxiomMath / Mathlib |
|---|---|---|
| `X` Noetherian (Stacks 03EA) | `IsNoetherianSpace hZ X` | `Space.IsNoetherian B S hS hZ X.1` |
| `f` proper (03ZM) | `IsProperHom f` | `Space.IsProper B S hS f.hom` |
| `f` flat (03MK, 03ML(1)) | `IsFlatHom f` | `Space.IsFlat B S hS f.hom` |
| `f` of finite type (03XF) | `IsFiniteTypeHom f` | `Space.IsFiniteType B S hS f.hom` |
| `f` quasi-affine (03WL) | `IsQuasiAffineHom f` | the body of `Space.IsQuasiAffineHom` (see below) |
| `|X|` (03BT, 03BU) and its topology (03BY) | `Pts X`, `ptsTopology X` | `points`, `pointTopology` |
| `|f| : |X| → |Y|` | `ptsMap f` | `pointsMap` |
| representative `t : Spec k ⟶ X` of `p ∈ |X|` | `x : Representative X`, `x.hom`, `x.Represents p` | `FieldValuedPoint`, its class |
| `Y₁ ×_S T`, `g_i`, `t_i`, `t'` of Setup 2.20 | `pullback f₁ t`, `pullback.snd f₁ t`, `pullback.fst f₁ t`, `cubeMap f₁ f₂ t` | Mathlib's `pullback` in `AlgebraicSpaces B S hS` |
| `L(t')^*K` | `baseChangeKernel f₁ f₂ t K` | `pull` |
| `Φ_{L(t')^*K}` | `fibreTransform f₁ f₂ t K` | `transformOver` |
| "`F` is fully faithful (an equivalence) on `P → Q`" | `FullyFaithfulOn P Q F` (`IsEquivalenceOn P Q F`) | Mathlib's `ObjectProperty.lift` |
| `fm(K)`, `FM(K)` (Def 12.1) | `fmLocus f₁ f₂ K`, `FMLocus f₁ f₂ K` | |

## Conventions and differences from GL26

* **The base.**  GL26 works over a fixed base scheme; here it is AxiomMath's
  `(B, S, hS)` (`Spaces/Categories.lean`), and GL26's base algebraic space (also called `S`
  in the paper) is an object `S'` of `AlgebraicSpaces B S hS`.  Fibre products `Y₁ ×_{S'} Y₂`
  are pullbacks in `AlgebraicSpaces B S hS` (AxiomMath's `hasPullbacks`, Stacks 02X2/04TJ).
* **Noetherian** is AxiomMath's `IsNoetherian` (Stacks 03EA: quasi-compact, quasi-separated
  in the absolute sense of 03BS(3), locally Noetherian).  Its absolute quasi-separatedness
  needs the terminal scheme in the site, `hZ : B.Contains (⊤_ Scheme)`; the statements take
  `hZ` as an argument.  AxiomMath proves that every big fppf site contains it
  (`AlgebraicGeometry.BigFppfSite.contains_terminal`), so this is no restriction, and the
  proposition does not depend on the proof `hZ`.
* **Points and representatives.**  `|X|` is AxiomMath's quotient of field-valued points
  (Stacks 03BT/03BU): a field `k` whose spectrum lies in the site, a structure morphism
  `Spec k ⟶ S` and a section of `X` over it.  By the Yoneda lemma such a section is a
  morphism of algebraic spaces `Spec k ⟶ X` (`Representative.hom`), and it *represents* its
  class.  Fields are restricted to those whose spectrum is an object of the site (AxiomMath's
  model of `|X|`); GL26's statements quantify over representatives, so they are read in that
  model.
* **Restriction to subcategories.**  GL26's `Φ_K` is a functor `D_qc(Y₁) → D_qc(Y₂)`;
  `transformOver` is defined on all of `D(𝒪)`.  "`Φ` is fully faithful (an equivalence) on
  `D_qc`" is rendered as: `Φ` maps `D_qc(Y₁)` into `D_qc(Y₂)` and the induced functor is fully
  faithful (an equivalence) — `FullyFaithfulOn (Dqc _) (Dqc _) Φ`.  The first clause holds in
  every situation the statements consider (`K ∈ D_qc` and the projections are proper, hence
  qcqs: Stacks 08F4, 08F5, 08FA, the tagged inputs of `Spaces/AxiomMathInputs.lean`), so it
  is part of the meaning, not an extra hypothesis.  "on `D^b_coh`" is the same with `DbCoh`
  (GL26: "restricts to a fully faithful functor (resp. an equivalence) on `D^b_coh`",
  `lem:equivalences_induced`).
* **Quasi-affine.**  AxiomMath's `Space.IsQuasiAffineHom` (Stacks 03WL) lives in
  `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiAffine`, which is outside the import
  list; `IsQuasiAffineHom` below is its body, written out verbatim (it uses only Mathlib's
  `Scheme.IsQuasiAffine` and AxiomMath definitions already in the import closure).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space Opposite

namespace RelativeFM.Spaces.Statements

open RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

/-! ### Restricting a functor to full subcategories -/

section Restriction

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- `F` maps `P` into `Q`, and the induced functor `P ⥤ Q` (Mathlib's `ObjectProperty.lift`
of `P.ι ⋙ F`) is fully faithful: "`F` restricts to a fully faithful functor `P → Q`". -/
def FullyFaithfulOn (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D) : Prop :=
  ∃ h : ∀ X, P X → Q (F.obj X),
    (Q.lift (P.ι ⋙ F) fun X => h X.obj X.property).Full ∧
      (Q.lift (P.ι ⋙ F) fun X => h X.obj X.property).Faithful

/-- `F` maps `P` into `Q`, and the induced functor `P ⥤ Q` is an equivalence: "`F` restricts
to an equivalence `P → Q`". -/
def IsEquivalenceOn (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D) : Prop :=
  ∃ h : ∀ X, P X → Q (F.obj X),
    (Q.lift (P.ι ⋙ F) fun X => h X.obj X.property).IsEquivalence

/-- GL26's "fully faithful (resp. an equivalence)": `FullyFaithfulOn` for `equiv = false`,
`IsEquivalenceOn` for `equiv = true`.  Used to state the two readings of a "resp." statement
at once. -/
def FFOrEquivOn (equiv : Bool) (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D) :
    Prop :=
  match equiv with
  | false => FullyFaithfulOn P Q F
  | true => IsEquivalenceOn P Q F

@[simp] theorem fFOrEquivOn_false (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D) :
    FFOrEquivOn false P Q F = FullyFaithfulOn P Q F := rfl

@[simp] theorem fFOrEquivOn_true (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D) :
    FFOrEquivOn true P Q F = IsEquivalenceOn P Q F := rfl

end Restriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Properties of algebraic spaces and their morphisms -/

section Properties

variable {X Y : AlgebraicSpaces B S hS}

/-- **Noetherian algebraic space** (Stacks 03EA; GL26 §2.2): AxiomMath's `IsNoetherian`
(quasi-compact, absolutely quasi-separated, étale-locally Noetherian). -/
abbrev IsNoetherianSpace (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS) : Prop :=
  Space.IsNoetherian B S hS hZ X.1

/-- **Proper morphism** of algebraic spaces (Stacks 03ZM): separated, of finite type and
universally closed; AxiomMath's `IsProper`. -/
abbrev IsProperHom (f : X ⟶ Y) : Prop :=
  Space.IsProper B S hS f.hom

/-- **Flat morphism** of algebraic spaces (Stacks 03MK, 03ML(1), via 03MJ): AxiomMath's `IsFlat`. -/
abbrev IsFlatHom (f : X ⟶ Y) : Prop :=
  Space.IsFlat B S hS f.hom

/-- **Morphism of finite type** of algebraic spaces (Stacks 03XF(3)): AxiomMath's
`IsFiniteType`. -/
abbrev IsFiniteTypeHom (f : X ⟶ Y) : Prop :=
  Space.IsFiniteType B S hS f.hom

/-- **Quasi-affine morphism** of algebraic spaces (Stacks 03WL): every base change to an
affine scheme is represented by a quasi-affine scheme.  This is, verbatim, the body of
AxiomMath's `AlgebraicGeometry.Space.IsQuasiAffineHom B S hS f.hom`
(`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/QuasiAffine.lean`, outside the import
list). -/
def IsQuasiAffineHom (f : X ⟶ Y) : Prop :=
  ∀ (Z : BigAffineFppf B S hS)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ Y.1),
    ∃ W : BigFppfOver B S hS,
      Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
        Nonempty (yoneda.obj W ≅ pullback g f.hom)

end Properties

/-! ### Points and representatives -/

section Points

/-- `|X|`, the set of points of an algebraic space (Stacks 03BT, 03BU): AxiomMath's
`points`. -/
abbrev Pts (X : AlgebraicSpaces B S hS) : Type (u + 1) :=
  points B S hS X.1

/-- The topology on `|X|` (Stacks 03BY): AxiomMath's `pointTopology`. -/
instance ptsTopology (X : AlgebraicSpaces B S hS) : TopologicalSpace (Pts X) :=
  pointTopology B S hS X.1

/-- `|f| : |X| → |Y|`: AxiomMath's `pointsMap`. -/
abbrev ptsMap {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Pts X → Pts Y :=
  pointsMap B S hS X.1 f.hom

/-- A representative of a point of `X`: a field `k` (with `Spec k` in the site), a structure
morphism `Spec k ⟶ S` and a section of `X` over `Spec k` (AxiomMath's `FieldValuedPoint`).
By the Yoneda lemma it is a morphism `Spec k ⟶ X` of algebraic spaces, `Representative.hom`. -/
abbrev Representative (X : AlgebraicSpaces B S hS) : Type (u + 1) :=
  FieldValuedPoint B S hS X.1

namespace Representative

variable {X : AlgebraicSpaces B S hS}

/-- `Spec k` as an algebraic space over the base (the representable sheaf of `Spec k ⟶ S`,
Stacks 025Z). -/
abbrev space (x : Representative X) : AlgebraicSpaces B S hS :=
  yonedaSpace B S hS (x.siteObject B S hS X.1)

/-- The morphism `t : Spec k ⟶ X` of algebraic spaces given by a representative (Yoneda). -/
def hom (x : Representative X) : x.space ⟶ X :=
  ObjectProperty.homMk (yonedaEquiv.symm x.value)

/-- The point `[x] ∈ |X|` of a representative. -/
abbrev point (x : Representative X) : Pts X :=
  x.class B S hS X.1

/-- `x` represents `p ∈ |X|` (Stacks 03BT): its class is `p`. -/
abbrev Represents (x : Representative X) (p : Pts X) : Prop :=
  x.point = p

end Representative

/-- A **closed point** of `|X|`. -/
abbrev IsClosedPt {X : AlgebraicSpaces B S hS} (p : Pts X) : Prop :=
  IsClosed ({p} : Set (Pts X))

end Points

/-! ### The base-change cube of Setup 2.20 -/

section Cube

variable {S' Y₁ Y₂ T : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S')

/-- The relatively perfect kernels "over `Y₁`": perfect relative to the first projection
`Y₁ ×_{S'} Y₂ ⟶ Y₁` (GL26, introduction and §3: "relatively perfect over `Y_i`" means
perfect relative to the projection onto `Y_i`; Definition 4.1). -/
abbrev IsRelPerfOverFst (K : D B S hS (pullback f₁ f₂)) : Prop :=
  IsRelativelyPerfect (pullback.fst f₁ f₂) K

/-- Relatively perfect over `Y₂`: perfect relative to the second projection. -/
abbrev IsRelPerfOverSnd (K : D B S hS (pullback f₁ f₂)) : Prop :=
  IsRelativelyPerfect (pullback.snd f₁ f₂) K

variable (t : T ⟶ S')

/-- The morphism `t' : (Y₁ ×_{S'} T) ×_T (Y₂ ×_{S'} T) ⟶ Y₁ ×_{S'} Y₂` of the cube of
Setup 2.20 (`setup:fm_cube_pullback`), induced by `t₁ = pullback.fst f₁ t`,
`t₂ = pullback.fst f₂ t` and `t`.  GL26 writes its source `Y₁ ×_S Y₂ ×_S T`. -/
def cubeMap :
    pullback (pullback.snd f₁ t) (pullback.snd f₂ t) ⟶ pullback f₁ f₂ :=
  pullback.map (pullback.snd f₁ t) (pullback.snd f₂ t) f₁ f₂ (pullback.fst f₁ t)
    (pullback.fst f₂ t) t pullback.condition.symm pullback.condition.symm

/-- **The base-changed kernel** `L(t')^*K ∈ D(Y₁ ×_{S'} Y₂ ×_{S'} T)` (GL26 §2.3). -/
def baseChangeKernel (K : D B S hS (pullback f₁ f₂)) :
    D B S hS (pullback (pullback.snd f₁ t) (pullback.snd f₂ t)) :=
  (pull (cubeMap f₁ f₂ t)).obj K

/-- **The fibre transform** `Φ_{L(t')^*K} : D(Y₁ ×_{S'} T) ⥤ D(Y₂ ×_{S'} T)`, the integral
transform over `T` of the base-changed kernel, along `g_i = pullback.snd f_i t`
(GL26 §2.3; for `t` a representative of a point, the *fibre* of `Φ_K` at `t`). -/
def fibreTransform (K : D B S hS (pullback f₁ f₂)) :
    D B S hS (pullback f₁ t) ⥤ D B S hS (pullback f₂ t) :=
  transformOver (pullback.snd f₁ t) (pullback.snd f₂ t) (baseChangeKernel f₁ f₂ t K)

end Cube

/-! ### The loci of Definition 12.1 -/

section Loci

variable {S' Y₁ Y₂ : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S')

/-- **`fm(K)`** (Definition 12.1, `def:fm_locus`): the points `p ∈ |S'|` at which `Φ_K` is
fully faithful, i.e. for which `Φ_{L(t')^*K}` is fully faithful on `D_qc` for *some*
representative `t` of `p`. -/
def fmLocus (K : D B S hS (pullback f₁ f₂)) : Set (Pts S') :=
  {p | ∃ x : Representative S', x.Represents p ∧
    FullyFaithfulOn (Dqc _) (Dqc _) (fibreTransform f₁ f₂ x.hom K)}

/-- **`FM(K)`** (Definition 12.1, `def:fm_locus`): the points at which `Φ_K` is an
equivalence, i.e. `Φ_{L(t')^*K}` is an equivalence on `D_qc` for some representative `t`. -/
def FMLocus (K : D B S hS (pullback f₁ f₂)) : Set (Pts S') :=
  {p | ∃ x : Representative S', x.Represents p ∧
    IsEquivalenceOn (Dqc _) (Dqc _) (fibreTransform f₁ f₂ x.hom K)}

end Loci

end RelativeFM.Spaces.Statements
