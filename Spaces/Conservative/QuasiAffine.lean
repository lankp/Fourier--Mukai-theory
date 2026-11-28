/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Conservative.Inputs

/-!
# GL26 Lemmas 2.18 and 3.2: quasi-affine morphisms

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26):

* **Lemma 2.18** (`lem:quasi-affine_via_diagonal`): for morphisms `g : Z ⟶ Y`, `f : Y ⟶ X`,
  `h : Z ⟶ X` of algebraic spaces with `g ≫ f = h`, if `h` and the diagonal `Δ_f` are
  quasi-affine then so is `g` (`lemma_2_18`).  Proved, as stated.
* **Lemma 3.2** (`lem:quasi-affine_is_conservative`): for a quasi-affine morphism `f : Y ⟶ X`
  of quasi-compact quasi-separated algebraic spaces, `Rf_*` is conservative on `D_qc(Y)`
  (`Rf_*E ≅ 0 ⇒ E ≅ 0`).  **Proved only for a morphism given with a factorization**
  `f = j ≫ p`, `j` a quasi-compact open immersion and `p` affine
  (`lemma_3_2_of_factorization`); see "What is missing".

## Proofs

*Lemma 2.18*, as in GL26: `p₂ : Z ×_X Y ⟶ Y` is the base change of `h` along `f`, quasi-affine
by Stacks 03WO (AxiomMath's `IsQuasiAffineHom.of_isPullback`, in the import closure); the graph
`(1, g) : Z ⟶ Z ×_X Y` is the base change of `Δ_f` along `Z ×_X Y ⟶ Y ×_X Y` (Mathlib's
`pullback_lift_diagonal_isPullback`), hence quasi-affine; and `g = (1, g) ≫ p₂` is quasi-affine
by Stacks 03WN (`QuasiAffineCompInput`).  Pullbacks in `AlgebraicSpaces` are presheaf pullbacks
(AxiomMath's `AlgebraicSpaces.isPullback_hom`), which is where AxiomMath's quasi-affineness lives.

*Lemma 3.2*, GL26's argument after the factorization: `R(j ≫ p)_* ≅ Rp_* Rj_*` (Stacks 0D6E,
in the import closure); `Rj_*E ∈ D_qc` (Stacks 08FA, `Spaces.Tag08FAInput`; `j` is quasi-compact,
and quasi-separated as a monomorphism); `Rp_*` is conservative on `D_qc` for affine `p`
(Stacks 0E4R, `AffinePushforwardConservativeInput`); and `Rj_*` is fully faithful for an open
immersion (`Lj^* Rj_* ≅ id`, `LP26.pushFullyFaithful` from `LP26.OpenImmersionCounitInput`), so
it reflects zero objects.

## What is missing for Lemma 3.2 as stated

The canonical factorization `Y ⟶ \underline{Spec}_X(f_*𝒪_Y) ⟶ X` of a quasi-compact
quasi-separated `f` (Stacks 081X, AxiomMath's `directImageSpec`, `toDirectImageSpec`,
`Spaces/DirectImageSpecFactorization.lean`), and Stacks 086S (`toDirectImageSpec` is an open
immersion iff `f` is quasi-affine, AxiomMath's
`isQuasiAffineHom_iff_isOpenImmersion_toDirectImageSpec`,
`Spaces/QuasiAffineCanonicalFactorization.lean`).  These definitions are outside the import
list, and their import closure contains `StacksFrontier.RingTheory.MilnorPatching.Relative`
(1 912 modules beyond the current closure); the relative spectrum `boundedRelativeSpec` they are
built from has the same closure, so they cannot be written out by their bodies either.  The
remaining step (in `SpacesVerified`, where these modules may be imported): for `f` quasi-affine
and qcqs, take `j = (toDirectImageSpec f).left`, `p` the structure morphism of
`directImageSpec f`; `j` is an open immersion by 086S, quasi-compact because `f = j ≫ p` is and
`p` is separated, and `p` is affine; then apply `lemma_3_2_of_factorization`.

## Rendering

* Quasi-affine is `Statements.IsQuasiAffineHom` (the body of AxiomMath's `IsQuasiAffineHom`, on
  the underlying presheaf morphism); `Δ_f` is Mathlib's `pullback.diagonal f` in
  `AlgebraicSpaces B S hS`.
* `Rf_*` is `Spaces.push f` on all of `D(𝒪_Y)`; "conservative" is GL26's "`Rf_*E ≅ 0` implies
  `E ≅ 0`" for `E ∈ D_qc(Y)`.
* `lemma_3_2_of_factorization` needs no quasi-compactness or quasi-separatedness of `Y`, `X`.

## Assumptions

`QuasiAffineCompInput` (2.18); `Spaces.Tag08FAInput`, `LP26.OpenImmersionCounitInput`,
`AffinePushforwardConservativeInput` (3.2).  Nothing else.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Conservative

open RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Lemma 2.18 -/

/-- **Lemma 2.18** (`lem:quasi-affine_via_diagonal`): given `g : Z ⟶ Y`, `f : Y ⟶ X` and
`h : Z ⟶ X` of algebraic spaces with `g ≫ f = h`, if `h` and `Δ_f : Y ⟶ Y ×_X Y` are
quasi-affine then `g` is quasi-affine. -/
theorem lemma_2_18 (hcomp : QuasiAffineCompInput B S hS) {X Y Z : AlgebraicSpaces B S hS}
    (g : Z ⟶ Y) (h : Z ⟶ X) (f : Y ⟶ X) (w : g ≫ f = h)
    (hh : Statements.IsQuasiAffineHom h)
    (hΔ : Statements.IsQuasiAffineHom (pullback.diagonal f)) :
    Statements.IsQuasiAffineHom g := by
  subst w
  -- `p₂ : Z ×_X Y ⟶ Y` is the base change of `h = g ≫ f` along `f`.
  have hp₂ : Space.IsQuasiAffineHom B S hS (pullback.snd (g ≫ f) f).hom :=
    IsQuasiAffineHom.of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback (g ≫ f) f)) hh
  -- the graph `(1, g)` is the base change of `Δ_f`.
  have hγ : Space.IsQuasiAffineHom B S hS
      (pullback.lift (𝟙 Z) g (by simp) : Z ⟶ pullback (g ≫ f) f).hom :=
    IsQuasiAffineHom.of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS (pullback_lift_diagonal_isPullback g f)) hΔ
  have e : g = (pullback.lift (𝟙 Z) g (by simp) : Z ⟶ pullback (g ≫ f) f) ≫
      pullback.snd (g ≫ f) f := by simp
  rw [e]
  exact hcomp Z.2 (pullback (g ≫ f) f).2 Y.2 hγ hp₂

/-! ### Lemma 3.2 -/

/-- A fully faithful functor between categories with zero morphisms reflects zero objects. -/
theorem isZero_of_fullyFaithful {C : Type*} [Category* C] [Preadditive C] {D : Type*}
    [Category* D] [Preadditive D] {F : C ⥤ D} [F.Additive] (hF : F.FullyFaithful) {E : C}
    (h : IsZero (F.obj E)) : IsZero E := by
  rw [IsZero.iff_id_eq_zero]
  exact hF.map_injective (by rw [F.map_id, F.map_zero]; exact h.eq_of_src _ _)

/-- **Lemma 3.2** (`lem:quasi-affine_is_conservative`), **for a morphism given with its
factorization** `f = j ≫ p` through a quasi-compact open immersion `j : Y ⟶ P` and an affine
morphism `p : P ⟶ X`: for `E ∈ D_qc(Y)`, `R(j ≫ p)_*E ≅ 0` implies `E ≅ 0`.  This is GL26's
proof after Stacks 081X/086S; that every quasi-affine morphism of qcqs spaces has such a
factorization is not proved here (module docstring, "What is missing"), so this is not yet
GL26's Lemma 3.2. -/
theorem lemma_3_2_of_factorization (h08FA : Tag08FAInput B S hS)
    (hcounit : LP26.OpenImmersionCounitInput B S hS)
    (haff : AffinePushforwardConservativeInput B S hS) {Y P X : AlgebraicSpaces B S hS}
    (j : Y ⟶ P) (p : P ⟶ X) (hj : IsOpenImmersion B S hS j.hom)
    (hjqc : IsQuasiCompact B S hS j.hom) (hp : IsAffineHom B S hS p.hom) (E : D B S hS Y)
    (hE : Dqc Y E) (h : IsZero ((push (j ≫ p)).obj E)) : IsZero E := by
  have h₁ : IsZero ((push p).obj ((push j).obj E)) :=
    h.of_iso ((smallEtaleDerivedPushforwardCompIso B S hS j p).app E)
  have hqc : Dqc P ((push j).obj E) :=
    h08FA j hjqc (LP26.isQuasiSeparated_of_isOpenImmersion j hj) E hE
  have h₂ : IsZero ((push j).obj E) := haff p hp _ hqc h₁
  exact isZero_of_fullyFaithful (LP26.pushFullyFaithful hcounit j hj) h₂

end RelativeFM.Spaces.Conservative
