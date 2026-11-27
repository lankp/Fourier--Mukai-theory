/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.LP26.Inputs
import Spaces.Supported.CompactGeneration

/-!
# LP26 Lemma 5.7: `Rj_*` along a quasi-compact open immersion, over algebraic spaces

Lank–Pauwels, *Gluing weak approximability along recollements* (LP26), **Lemma 5.7**
(`lem:qcqs_open_pushforward`): for `j : U ⟶ X` a quasi-compact open immersion of
quasi-compact quasi-separated algebraic spaces,

1. `Rj_* : D_qc(U) ⥤ D_qc(X)` (it lands in `D_qc(X)`) preserves small coproducts;
2. there is `r ≥ 0` with `Rj_* D^{≤ 0}_qc(U) ⊆ D^{≤ r}_qc(X)`;
3. for `V ⊆ |U|` a quasi-compact open, the same holds for the restriction
   `Rj_* : D_{qc,|U| ∖ V}(U) ⥤ D_{qc,|X| ∖ V}(X)`.

`lemma_5_7` states 1–2 and the fact that `Rj_*` sends `D_{qc,|U| ∖ V}(U)` into
`D_{qc,|X| ∖ V}(X)`; `lemma_5_7_supported` states 1–2 for the restricted functor.

## Proof

LP26 proves the bound in 2 from Lipman's Proposition 3.9.2 on an affine étale chart, flat base
change (Stacks 08IR) and GL26 Lemma 2.15.  AxiomMath proves the uniform bound of Stacks 08FA (2)
for every quasi-compact quasi-separated morphism with quasi-compact target
(`Tag08FABoundInput`), which is used here instead.  1 is Stacks 08FB (`Tag08FBInput`), and the
support statement is Stacks 0AFJ (`Tag0AFJInput`) for the closed set `|X| ∖ j(V)`: `j(V)` is open
because the points map of an open immersion is open, and its preimage is `V` because the points
map of a monomorphism is injective (Stacks 06RV); both are AxiomMath theorems in the import
closure.  An open immersion is a monomorphism, hence quasi-separated
(`isQuasiSeparated_of_mono'`, AxiomMath's two-line proof, reproduced).

## Rendering and differences from LP26

* `Rj_*` is `Spaces.push j` (AxiomMath's `smallEtaleDerivedModulePushforward`) on all of `D(𝒪_U)`;
  that it lands in `D_qc(X)` is Stacks 08FA (1) (`Spaces.Tag08FAInput`).
* "Preserves small coproducts" is stated in `D(𝒪)`: for every `Type u`-indexed family of objects of
  `D_qc(U)`, `Rj_*` preserves its coproduct (`PreservesColimit (Discrete.functor E)`).  Direct
  sums in `D_qc(U)` and in `D_{qc,Z}(U)` are those of `D(𝒪_U)` (Stacks 08F3 and the remark before
  0AED, `Supported.Tag08F3Input`, `Supported.SupportedDirectSumsInput`), so this is LP26's
  statement; the reformulation as preservation by the restricted functor between the full
  subcategories is not written out.
* `D^{≤ n}` is `E.IsLE n` (Mathlib's standard `t`-structure on `D(𝒪)`).
* `j(V)` is the image of `V` under the points map of `j`, and `|X| ∖ V` is `(j '' V)ᶜ`.
* **Weaker hypotheses than LP26** (so the statement is stronger): `U` and `X` need not be
  quasi-separated, `U` need not be quasi-compact, and `V` need only be open.

## Assumptions

`Spaces.Tag08FAInput` and the tagged AxiomMath inputs `Tag08FBInput`, `Tag08FABoundInput`,
`Tag0AFJInput` (`Spaces/LP26/Inputs.lean`); nothing else.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.LP26

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

open Supported

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An isomorphism of presheaves on the big fppf site is quasi-compact.  This is AxiomMath's
`AlgebraicGeometry.Space.isQuasiCompact_of_isIso` (`Stacks/QuasiSeparatedDiagonal.lean`,
outside the import list), reproduced with its proof (Apache 2.0). -/
theorem isQuasiCompact_of_isIso' {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G)
    [IsIso e] : IsQuasiCompact B S hS e := by
  intro Z _ hqc g
  have : IsIso (pullback.fst g e) := (IsPullback.of_hasPullback g e).isIso_fst_of_isIso
  exact hqc.of_iso B S hS (asIso (pullback.fst g e)).symm

/-- A monomorphism of presheaves on the big fppf site is quasi-separated: its diagonal is an
isomorphism.  AxiomMath's `AlgebraicGeometry.Space.isQuasiSeparated_of_mono`
(`Stacks/QuasiSeparatedDiagonal.lean`, outside the import list), reproduced with its proof. -/
theorem isQuasiSeparated_of_mono' {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G)
    [Mono g] : IsQuasiSeparated B S hS g :=
  isQuasiCompact_of_isIso' (pullback.diagonal g)

section

variable {U X : AlgebraicSpaces B S hS} (j : U ⟶ X)

/-- An open immersion of algebraic spaces is quasi-separated. -/
theorem isQuasiSeparated_of_isOpenImmersion (hj : IsOpenImmersion B S hS j.hom) :
    IsQuasiSeparated B S hS j.hom :=
  have : Mono j.hom := mono_of_presheaf_isOpenImmersion hj
  isQuasiSeparated_of_mono' j.hom

/-- For an open immersion `j` and `V ⊆ |U|` open, `|X| ∖ j(V)` is closed and its preimage in
`|U|` is `|U| ∖ V`. -/
theorem isClosed_compl_image_and_preimage (hj : IsOpenImmersion B S hS j.hom)
    (V : Set (points B S hS U.1)) (hV : IsOpen V) :
    IsClosed (pointsMap B S hS U.1 j.hom '' V)ᶜ ∧
      pointsMap B S hS U.1 j.hom ⁻¹' (pointsMap B S hS U.1 j.hom '' V)ᶜ = Vᶜ := by
  have : Mono j.hom := mono_of_presheaf_isOpenImmersion hj
  refine ⟨(isOpenMap_pointsMap_of_isOpenImmersion B S hS j.hom hj V hV).isClosed_compl, ?_⟩
  rw [Set.preimage_compl,
    Set.preimage_image_eq V (pointsMap_injective_of_mono B S hS j.hom)]

/-- **Support under `Rj_*`** (part of Lemma 5.7): for `j` an open immersion and `V ⊆ |U|` open,
`Rj_*` sends `D_{qc,|U| ∖ V}(U)` into `D_{qc,|X| ∖ j(V)}(X)` as soon as `j` is quasi-compact
(Stacks 08FA (1) for `D_qc`, Stacks 0AFJ for the support). -/
theorem push_dqcSupported (h08FA : Tag08FAInput B S hS) (h0AFJ : Tag0AFJInput B S hS)
    (hj : IsOpenImmersion B S hS j.hom) (hjqc : IsQuasiCompact B S hS j.hom)
    (V : Set (points B S hS U.1)) (hV : IsOpen V) {E : D B S hS U}
    (hE : DqcSupported U Vᶜ E) :
    DqcSupported X (pointsMap B S hS U.1 j.hom '' V)ᶜ ((push j).obj E) := by
  obtain ⟨hT, hpre⟩ := isClosed_compl_image_and_preimage j hj V hV
  refine ⟨h08FA j hjqc (isQuasiSeparated_of_isOpenImmersion j hj) E hE.1, ?_⟩
  have := isGrothendieckAbelian_modules B S hS U.1 U.2
  have h := h0AFJ j _ hT
    (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS j))
    ((Stacks.DerivedFunctor.homotopyMap (modulePushforward B S hS j)).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))) E
    (by rw [hpre]; exact hE.2)
  exact (isClosedUnderIsomorphisms_cohomologySupportedOn' X _).of_iso
    ((smallEtaleDerivedModulePushforwardIso B S hS j).app E).symm h

end

/-- **Lemma 5.7** (`lem:qcqs_open_pushforward`): let `j : U ⟶ X` be a quasi-compact open
immersion of algebraic spaces with `X` quasi-compact.  Then

1. `Rj_*` sends `D_qc(U)` into `D_qc(X)`;
2. `Rj_*` preserves the (`Type u`-indexed) coproducts of objects of `D_qc(U)`;
3. there is `r ≥ 0` with `Rj_* D^{≤ 0}_qc(U) ⊆ D^{≤ r}(X)`;
4. for every open `V ⊆ |U|`, `Rj_*` sends `D_{qc,|U| ∖ V}(U)` into `D_{qc,|X| ∖ j(V)}(X)`.

LP26 assumes moreover `U`, `X` quasi-separated, `U` quasi-compact and `V` quasi-compact; these are
not needed.  The restricted functor of LP26's last clause is `lemma_5_7_supported`. -/
theorem lemma_5_7 (h08FA : Tag08FAInput B S hS) (h08FB : Tag08FBInput B S hS)
    (h08FAb : Tag08FABoundInput B S hS) (h0AFJ : Tag0AFJInput B S hS)
    {U X : AlgebraicSpaces B S hS} (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom)
    (hjqc : IsQuasiCompact B S hS j.hom) (hX : IsQuasiCompactSpace B S hS X.1) :
    (∀ E : D B S hS U, Dqc U E → Dqc X ((push j).obj E)) ∧
      (∀ {I : Type u} (E : I → D B S hS U), (∀ i, Dqc U (E i)) →
        PreservesColimit (Discrete.functor E) (push j)) ∧
      (∃ r : ℤ, 0 ≤ r ∧ ∀ E : D B S hS U, Dqc U E → E.IsLE 0 → ((push j).obj E).IsLE r) ∧
      (∀ V : Set (points B S hS U.1), IsOpen V → ∀ E : D B S hS U, DqcSupported U Vᶜ E →
        DqcSupported X (pointsMap B S hS U.1 j.hom '' V)ᶜ ((push j).obj E)) := by
  have hjqs := isQuasiSeparated_of_isOpenImmersion j hj
  refine ⟨fun E hE => h08FA j hjqc hjqs E hE, fun E hE => h08FB j hjqc hjqs E hE, ?_,
    fun V hV E hE => push_dqcSupported j h08FA h0AFJ hj hjqc V hV hE⟩
  obtain ⟨N, hN⟩ := h08FAb j hjqc hjqs hX
  refine ⟨max N 0, le_max_right _ _, fun E hE h0 => ?_⟩
  have := hN E hE 0 h0
  rw [zero_add] at this
  exact DerivedCategory.TStructure.t.isLE_of_le _ N (max N 0) (le_max_left _ _)

/-- **Lemma 5.7** (`lem:qcqs_open_pushforward`), last clause: for `j : U ⟶ X` a quasi-compact
open immersion with `X` quasi-compact and `V ⊆ |U|` open, the restriction
`Rj_* : D_{qc,|U| ∖ V}(U) ⥤ D_{qc,|X| ∖ j(V)}(X)` is defined (lands in the target), preserves the
coproducts of families of objects of `D_{qc,|U| ∖ V}(U)`, and there is `r ≥ 0` with
`Rj_* D^{≤ 0}_{qc,|U| ∖ V}(U) ⊆ D^{≤ r}_{qc,|X| ∖ j(V)}(X)`. -/
theorem lemma_5_7_supported (h08FA : Tag08FAInput B S hS) (h08FB : Tag08FBInput B S hS)
    (h08FAb : Tag08FABoundInput B S hS) (h0AFJ : Tag0AFJInput B S hS)
    {U X : AlgebraicSpaces B S hS} (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom)
    (hjqc : IsQuasiCompact B S hS j.hom) (hX : IsQuasiCompactSpace B S hS X.1)
    (V : Set (points B S hS U.1)) (hV : IsOpen V) :
    (∀ E : D B S hS U, DqcSupported U Vᶜ E →
        DqcSupported X (pointsMap B S hS U.1 j.hom '' V)ᶜ ((push j).obj E)) ∧
      (∀ {I : Type u} (E : I → D B S hS U), (∀ i, DqcSupported U Vᶜ (E i)) →
        PreservesColimit (Discrete.functor E) (push j)) ∧
      (∃ r : ℤ, 0 ≤ r ∧ ∀ E : D B S hS U, DqcSupported U Vᶜ E → E.IsLE 0 →
        DqcSupported X (pointsMap B S hS U.1 j.hom '' V)ᶜ ((push j).obj E) ∧
          ((push j).obj E).IsLE r) := by
  obtain ⟨-, hcop, ⟨r, hr, hb⟩, hsupp⟩ := lemma_5_7 h08FA h08FB h08FAb h0AFJ j hj hjqc hX
  exact ⟨hsupp V hV, fun E hE => hcop E fun i => (hE i).1,
    ⟨r, hr, fun E hE h0 => ⟨hsupp V hV E hE, hb E hE.1 h0⟩⟩⟩

end RelativeFM.Spaces.LP26
