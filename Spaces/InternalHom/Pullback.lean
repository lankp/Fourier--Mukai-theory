/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.InternalHom.Basic

/-!
# GL26 Lemma 2.16 (`lem:gortz_wedhorn_internal_hom`)

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), §2.2,
**Lemma 2.16**: for a morphism `f : Y ⟶ X` of quasi-compact quasi-separated algebraic spaces, the
canonical morphism

`Lf^* 𝐑𝓗om(E, G) ⟶ 𝐑𝓗om(Lf^*E, Lf^*G)`

(of internal Homs of `D_qc`) is an isomorphism if (1) `E ∈ Perf(X)` and `G ∈ D_qc(X)`, or (2) `E`
is pseudo-coherent, `G ∈ D^+_qc(X)` and `f` has finite Tor dimension.

## The canonical morphism

With coherators `adjX : i_X ⊣ Q_X`, `adjY : i_Y ⊣ Q_Y` and `𝐑𝓗om = Q ∘ R𝓗om ∘ (i × i)`
(`qcHom`, GL26 Lemma 2.11), the morphism `qcHomPullbackMap` is the map of `D_qc(Y)` adjoint (under
`i_Y ⊣ Q_Y`) to

`Lf^* i Q R𝓗om(E, G) ⟶ Lf^* R𝓗om(E, G) ⟶ R𝓗om(Lf^*E, Lf^*G)`,

the pullback of the counit followed by the map `ρ_f` of Stacks 08I3 / 08JF (AxiomMath's
`smallEtaleDerivedPullbackSheafHomMap`).  Its source lies in `D_qc(Y)` by Stacks 08F4
(`Tag08F4Input`).  It is defined for every pair `E, G ∈ D_qc(X)`; under the hypotheses of the lemma
it is the composite of GL26's square (`qcHomPullbackMap_comp_counit`), whose other three sides are
the isomorphisms of Lemma 2.11 and `ρ_f`.

## What is proved

* `isIso_qcHomPullbackMap_of_isIso`: the reduction of GL26's proof ("it suffices to prove that
  `ρ_f` is an isomorphism"): if `R𝓗om(E, G)` has quasi-coherent cohomology and `ρ_f` is
  invertible at `(E, G)`, the canonical morphism is an isomorphism.
* **`lemma_2_16_perfect`: case (1)**, from Stacks 0A8A (`Tag0A8AInput`) and Stacks 08I3 out of a
  perfect object (`Tag08I3PerfectInput`, AxiomMath's
  `isIso_smallEtaleDerivedPullbackSheafHomMap_of_isPerfect`).
* `lemma_2_16_perfect_qcqs`: case (1) with the coherators of Stacks 0CR4 for qcqs `X, Y`.
* `lemma_2_16_pseudoCoherent_of_isIso`: case (2) given the invertibility of `ρ_f` at `(E, G)`.

## Not proved: case (2)

Case (2) needs `ρ_f` invertible for `E` pseudo-coherent, `G ∈ D^+_qc(X)` and `f` of finite Tor
dimension.  AxiomMath (commit `f56a316`) proves this for ringed spaces
(`isIso_derivedPullbackSheafHomMap_of_hasFiniteTorDimensionOverInverseImage`, Stacks 0GM7) and,
over algebraic spaces, for *affine* `f` (`isIso_smallEtaleDerivedPullbackSheafHomMap_of_isAffineHom_of_isPseudoCoherent`)
and in the base-change form of Stacks 0DKI (3) (`geometricPointwiseBaseChange_sheafHom_of_isPseudoCoherent`),
but not for a general morphism of algebraic spaces.  So case (2) is stated here only conditionally
on that invertibility, and remains open.

## Differences from GL26

* The coherators are data (`adjX`, `adjY`); the lemma holds for every `f : Y ⟶ X` for which they
  exist, in particular for qcqs `X`, `Y` (GL26's hypothesis), see `lemma_2_16_perfect_qcqs`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space Opposite

namespace RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS}

/-- **The map `ρ_f` of Stacks 08I3 / 08JF**, `Lf^*R𝓗om(E, G) ⟶ R𝓗om(Lf^*E, Lf^*G)` on `D(Y)`, for
`f : Y ⟶ X`: AxiomMath's `smallEtaleDerivedPullbackSheafHomMap`. -/
abbrev sheafHomPullbackMap (f : Y ⟶ X) (E G : D B S hS X) :
    (pull f).obj (sheafHomObj E G) ⟶ sheafHomObj ((pull f).obj E) ((pull f).obj G) :=
  smallEtaleDerivedPullbackSheafHomMap f E G

/-- **The canonical morphism of GL26 Lemma 2.16**, `Lf^*𝐑𝓗om(E, G) ⟶ 𝐑𝓗om(Lf^*E, Lf^*G)` in
`D_qc(Y)`, for coherators `adjX`, `adjY`: adjoint under `i_Y ⊣ Q_Y` to the pullback of the
counit `i_X Q_X R𝓗om(E, G) ⟶ R𝓗om(E, G)` followed by `ρ_f`. -/
def qcHomPullbackMap (h4 : Tag08F4Input B S hS) (f : Y ⟶ X)
    {QX : D B S hS X ⥤ (Dqc X).FullSubcategory} (adjX : (Dqc X).ι ⊣ QX)
    {QY : D B S hS Y ⥤ (Dqc Y).FullSubcategory} (adjY : (Dqc Y).ι ⊣ QY)
    (E G : (Dqc X).FullSubcategory) :
    (pullQc h4 f).obj ((qcHom adjX E).obj G) ⟶
      (qcHom adjY ((pullQc h4 f).obj E)).obj ((pullQc h4 f).obj G) :=
  adjY.homEquiv _ _
    ((pull f).map (adjX.counit.app (sheafHomObj E.obj G.obj)) ≫ sheafHomPullbackMap f E.obj G.obj)

/-- **GL26's square in the proof of Lemma 2.16**: the canonical morphism followed by the counit
`i_Y Q_Y R𝓗om(Lf^*E, Lf^*G) ⟶ R𝓗om(Lf^*E, Lf^*G)` is the pullback of the counit of `X` followed
by `ρ_f`. -/
theorem qcHomPullbackMap_comp_counit (h4 : Tag08F4Input B S hS) (f : Y ⟶ X)
    {QX : D B S hS X ⥤ (Dqc X).FullSubcategory} (adjX : (Dqc X).ι ⊣ QX)
    {QY : D B S hS Y ⥤ (Dqc Y).FullSubcategory} (adjY : (Dqc Y).ι ⊣ QY)
    (E G : (Dqc X).FullSubcategory) :
    (Dqc Y).ι.map (qcHomPullbackMap h4 f adjX adjY E G) ≫
        adjY.counit.app (sheafHomObj ((pull f).obj E.obj) ((pull f).obj G.obj)) =
      (pull f).map (adjX.counit.app (sheafHomObj E.obj G.obj)) ≫
        sheafHomPullbackMap f E.obj G.obj :=
  (adjY.homEquiv_counit (g := qcHomPullbackMap h4 f adjX adjY E G)).symm.trans
    (Equiv.symm_apply_apply _ _)

/-- **The reduction of GL26's proof of Lemma 2.16**: if `R𝓗om(E, G)` has quasi-coherent cohomology
and `ρ_f` is invertible at `(E, G)`, the canonical morphism `Lf^*𝐑𝓗om(E, G) ⟶ 𝐑𝓗om(Lf^*E, Lf^*G)`
is an isomorphism. -/
theorem isIso_qcHomPullbackMap_of_isIso (h4 : Tag08F4Input B S hS) (f : Y ⟶ X)
    {QX : D B S hS X ⥤ (Dqc X).FullSubcategory} (adjX : (Dqc X).ι ⊣ QX)
    {QY : D B S hS Y ⥤ (Dqc Y).FullSubcategory} (adjY : (Dqc Y).ι ⊣ QY)
    (E G : (Dqc X).FullSubcategory) (hEG : Dqc X (sheafHomObj E.obj G.obj))
    (hρ : IsIso (sheafHomPullbackMap f E.obj G.obj)) :
    IsIso (qcHomPullbackMap h4 f adjX adjY E G) := by
  have h1 : IsIso (adjX.counit.app (sheafHomObj E.obj G.obj)) := isIso_counit_app_of_mem adjX hEG
  -- the target `R𝓗om(Lf^*E, Lf^*G)` is isomorphic to `Lf^*R𝓗om(E, G)`, which lies in `D_qc(Y)`
  have h2 : IsIso (adjY.counit.app (sheafHomObj ((pull f).obj E.obj) ((pull f).obj G.obj))) :=
    adjY.isIso_counit_app_of_iso (Y := ⟨(pull f).obj (sheafHomObj E.obj G.obj),
      h4 f _ hEG⟩) (asIso (sheafHomPullbackMap f E.obj G.obj)).symm
  have h3 : IsIso ((Dqc Y).ι.map (qcHomPullbackMap h4 f adjX adjY E G) ≫
      adjY.counit.app (sheafHomObj ((pull f).obj E.obj) ((pull f).obj G.obj))) := by
    rw [qcHomPullbackMap_comp_counit h4 f adjX adjY E G]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso (pull f) _) hρ
  have := @IsIso.of_isIso_comp_right _ _ _ _ _
    ((Dqc Y).ι.map (qcHomPullbackMap h4 f adjX adjY E G))
    (adjY.counit.app (sheafHomObj ((pull f).obj E.obj) ((pull f).obj G.obj))) h2 h3
  exact (ObjectProperty.fullyFaithfulι (Dqc Y)).isIso_of_isIso_map _

/-- **Lemma 2.16 (1)** (`lem:gortz_wedhorn_internal_hom`, `lem:gortz_wedhorn_internal_hom1`).  Let
`f : Y ⟶ X` be a morphism of algebraic spaces with coherators `adjX`, `adjY` (they exist for `X`,
`Y` quasi-compact and quasi-separated, Stacks 0CR4; `lemma_2_16_perfect_qcqs`).  For
`E ∈ Perf(X)` and `G ∈ D_qc(X)`, the canonical morphism
`Lf^*𝐑𝓗om(E, G) ⟶ 𝐑𝓗om(Lf^*E, Lf^*G)` is an isomorphism. -/
theorem lemma_2_16_perfect (h4 : Tag08F4Input B S hS) (h0A8A : Tag0A8AInput B S hS)
    (h08I3 : Tag08I3PerfectInput B S hS) (f : Y ⟶ X)
    {QX : D B S hS X ⥤ (Dqc X).FullSubcategory} (adjX : (Dqc X).ι ⊣ QX)
    {QY : D B S hS Y ⥤ (Dqc Y).FullSubcategory} (adjY : (Dqc Y).ι ⊣ QY)
    (E G : (Dqc X).FullSubcategory) (hE : Perf X E.obj) :
    IsIso (qcHomPullbackMap h4 f adjX adjY E G) :=
  isIso_qcHomPullbackMap_of_isIso h4 f adjX adjY E G
    (sheafHomObj_mem_Dqc_of_perfect h0A8A hE G.property) (h08I3 f E.obj hE G.obj)

/-- **Lemma 2.16 (1)** (`lem:gortz_wedhorn_internal_hom1`) in GL26's setting: for
`f : Y ⟶ X` a morphism of quasi-compact quasi-separated algebraic spaces, with the coherators of
Stacks 0CR4 (`coheratorAdj`), `E ∈ Perf(X)` and `G ∈ D_qc(X)`, the canonical morphism
`Lf^*𝐑𝓗om(E, G) ⟶ 𝐑𝓗om(Lf^*E, Lf^*G)` is an isomorphism. -/
theorem lemma_2_16_perfect_qcqs (h4 : Tag08F4Input B S hS) (h0A8A : Tag0A8AInput B S hS)
    (h08I3 : Tag08I3PerfectInput B S hS) (h0CR4 : Tag0CR4Input B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (f : Y ⟶ X)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (E G : (Dqc X).FullSubcategory) (hE : Perf X E.obj) :
    IsIso (qcHomPullbackMap h4 f (coheratorAdj h0CR4 hZ X hXqc hXqs)
      (coheratorAdj h0CR4 hZ Y hYqc hYqs) E G) :=
  lemma_2_16_perfect h4 h0A8A h08I3 f _ _ E G hE

/-- **Lemma 2.16 (2)** (`lem:gortz_wedhorn_internal_hom2`), conditional on `ρ_f`: for `E`
pseudo-coherent and `G ∈ D^+_qc(X)` (Stacks 0A8A puts `R𝓗om(E, G)` in `D_qc(X)`), the canonical
morphism is an isomorphism as soon as `ρ_f` is invertible at `(E, G)`.  GL26 deduces that
invertibility from `f` having finite Tor dimension (Görtz–Wedhorn, Prop. 22.70, after reduction to
schemes); that step is not formalized (module docstring), so this is **not** case (2). -/
theorem lemma_2_16_pseudoCoherent_of_isIso (h4 : Tag08F4Input B S hS)
    (h0A8A : Tag0A8AInput B S hS) (f : Y ⟶ X)
    {QX : D B S hS X ⥤ (Dqc X).FullSubcategory} (adjX : (Dqc X).ι ⊣ QX)
    {QY : D B S hS Y ⥤ (Dqc Y).FullSubcategory} (adjY : (Dqc Y).ι ⊣ QY)
    (E G : (Dqc X).FullSubcategory) (hE : IsPseudoCoherent X E.obj) (hG : DplusQc X G.obj)
    (hρ : IsIso (sheafHomPullbackMap f E.obj G.obj)) :
    IsIso (qcHomPullbackMap h4 f adjX adjY E G) :=
  isIso_qcHomPullbackMap_of_isIso h4 f adjX adjY E G
    (sheafHomObj_mem_Dqc_of_isPseudoCoherent h0A8A hE hG) hρ

end RelativeFM.Spaces
