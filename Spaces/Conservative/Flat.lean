/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Conservative.Inputs
import Spaces.Supported.Detecting

/-!
# GL26 Lemmas 2.14 and 2.15: faithfully flat pullback is conservative on `D_qc`

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26):

* **Lemma 2.14** (`lem:faithfully_flat_is_conservative`): for a faithfully flat morphism
  `f : Y ⟶ X` of algebraic spaces, `Lf^* : D_qc(X) → D_qc(Y)` is conservative
  (`lemma_2_14`: an object of `D_qc(X)` killed by `Lf^*` is zero; `lemma_2_14_isIso`:
  `Lf^*` reflects isomorphisms between objects of `D_qc(X)`).
* **Lemma 2.15** (`lem:zero_object_via_covers`): for `E ∈ D_qc(X)` the four conditions
  (1) `E ≅ 0`, (2) `Lf^*E ≅ 0` for all flat `f`, (3) `Lf^*E ≅ 0` for some smooth surjective `f`,
  (4) `Lf^*E ≅ 0` for some flat surjective `f`, are equivalent (`lemma_2_15`), and
  `Hʲ(Lf^*E) ≅ 0` implies `Hʲ(E) ≅ 0` for faithfully flat `f` (`lemma_2_15_homology`).

## Proof

Stalkwise, as AxiomMath already did it, rather than through GL26's reduction to schemes and
Görtz–Wedhorn, Proposition 14.11.  For flat `f`, `f^*` on modules is exact
(`FlatPullbackExactInput`), so `Lf^*` is the functor `f^*` induces on derived categories (the
argument of AxiomMath's `smallEtaleDerivedModulePullbackIsoEtale`, at a flat `f`) and
`Hʲ(Lf^*E) ≅ f^*Hʲ(E)` (`homologyPullIsoOfIsFlat`; this is AxiomMath's
`homologyDerivedPullbackIsoOfIsFlat`, whose module is outside the import closure, reproduced
from the input).  For quasi-coherent `F`, `Supp(f^*F) = |f|⁻¹ Supp(F)`
(`FlatPullbackSupportInput`), so `f^*F ≅ 0` and `|f|` surjective give `Supp F = ∅`, i.e. `F ≅ 0`
(Stacks 04K5, `LP26.SupportEmptyInput`).  An object of `D(𝒪_X)` with vanishing cohomology is
zero.

GL26 deduces (4) ⇒ (1) of Lemma 2.15 by composing with an étale presentation; here "faithfully
flat" is "flat and surjective" (Stacks 03ME, 03MK, AxiomMath's `IsFlat` and `IsSurjective`), so
(4) ⇒ (1) is Lemma 2.14 itself.  (1) ⇒ (2) is trivial; (2) ⇒ (3) takes `f = 𝟙 X`, smooth by
AxiomMath's `isSmooth_id` and surjective since `|𝟙 X| = id`; (3) ⇒ (4) is "smooth ⇒ flat"
(`FlatOfSmoothInput`).

## Rendering and differences from GL26

* `Lf^*` is `Spaces.pull f` on all of `D(𝒪_X)`; "conservative on `D_qc(X)`" is stated without
  the (true, Stacks 08F4) fact that `Lf^*` lands in `D_qc(Y)`, which is not needed.
* "Faithfully flat" is `IsFlatHom f ∧ IsSurjective B S hS f.hom`.
* **Weaker hypotheses than GL26** (so the statements are stronger): Lemma 2.15 does not need
  `X` quasi-compact and quasi-separated, and its last clause only needs `Hʲ(E)` quasi-coherent.
  The paper's form, with the hypothesis, is the special case.
* `lemma_2_14_isIso` takes `D_qc(X)` triangulated (`Spaces.Tag06UQInput`) to put the cone of a
  morphism of `D_qc(X)` in `D_qc(X)`.

## Assumptions

The tagged AxiomMath inputs `FlatPullbackExactInput`, `FlatPullbackSupportInput`,
`FlatOfSmoothInput` (`Spaces/Conservative/Inputs.lean`), `LP26.SupportEmptyInput`
(`Spaces/LP26/Inputs.lean`) and, for `lemma_2_14_isIso`, `Spaces.Tag06UQInput`; nothing else.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Conservative

open RelativeFM.Spaces RelativeFM.Spaces.Statements

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The cohomology of a flat pullback -/

section FlatHomology

variable (hex : FlatPullbackExactInput B S hS) {X Y : AlgebraicSpaces B S hS}

/-- `f^*` on modules is additive (a left adjoint), for every morphism `f`. -/
instance modulePullback_additive' (f : X ⟶ Y) : (modulePullback B S hS f).Additive :=
  haveI : (modulePullback B S hS f).IsLeftAdjoint :=
    (modulePullbackAdjunction B S hS f).isLeftAdjoint
  haveI : (modulePullback B S hS f).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  haveI : PreservesBinaryBiproducts (modulePullback B S hS f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

include hex in
/-- **`Hⁱ(Lf^*M) ≅ f^*Hⁱ(M)` for flat `f`** (AxiomMath's `homologyDerivedPullbackIsoOfIsFlat`,
`Spaces/Perfect/DerivedFibreBettiFieldSpaceInputs.lean`, outside the import closure; here from
`FlatPullbackExactInput`).  For flat `f`, `Lf^*` is the functor that the exact functor `f^*`
induces on derived categories (AxiomMath's argument for `smallEtaleDerivedModulePullbackIsoEtale`,
at a flat morphism), and that functor commutes with cohomology. -/
def homologyPullIsoOfIsFlat (f : X ⟶ Y) (hf : IsFlat B S hS f.hom) (i : ℤ) (M : D B S hS Y) :
    (DerivedCategory.homologyFunctor (Space.Modules.{u, u} B S hS X.1 X.2) i).obj
        ((pull f).obj M) ≅
      (modulePullback B S hS f).obj
        ((DerivedCategory.homologyFunctor (Space.Modules.{u, u} B S hS Y.1 Y.2) i).obj M) :=
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f).toModulesHom
  let G : type_of% F := modulePullback B S hS f
  haveI : G.Additive := modulePullback_additive' f
  haveI : PreservesFiniteLimits G := hex f hf
  haveI : G.IsLeftAdjoint := (modulePullbackAdjunction B S hS f).isLeftAdjoint
  haveI : PreservesFiniteColimits G := inferInstance
  let e : pull f ≅ G.mapDerivedCategory :=
    Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso F G
      (smallEtaleDerivedModulePullback B S hS f)
      (smallEtaleDerivedModulePullbackComparison B S hS f)
      (pullbackModulesIsoModulePullback B S hS f)
  (DerivedCategory.homologyFunctor _ i).mapIso (e.app M) ≪≫
    (G.mapDerivedCategoryHomologyIso i).app M

end FlatHomology

/-! ### Faithfully flat pullback detects zero -/

/-- An object of `D(𝒪_X)` all of whose cohomology sheaves vanish is zero (Mathlib's
`DerivedCategory.isIso_iff`; the argument of AxiomMath's
`Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj`). -/
theorem isZero_of_isZero_homology {X : AlgebraicSpaces B S hS} (E : D B S hS X)
    (h : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor (Space.Modules.{u, u} B S hS X.1 X.2) n).obj
      E)) : IsZero E := by
  have hiso : IsIso (0 : E ⟶ E) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    rw [Functor.map_zero]
    exact ⟨⟨0, (h n).eq_of_src _ _, (h n).eq_of_src _ _⟩⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : E ⟶ E), comp_zero]

variable (hex : FlatPullbackExactInput B S hS) (hsupp : FlatPullbackSupportInput B S hS)
  (hempty : LP26.SupportEmptyInput B S hS)

include hsupp hempty in
/-- **Faithfully flat pullback of quasi-coherent modules detects zero**: for `f` flat and
surjective and `F` quasi-coherent, `f^*F ≅ 0` implies `F ≅ 0`. -/
theorem isZero_of_isZero_modulePullback {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsFlatHom f) (hs : IsSurjective B S hS f.hom) (F : Space.Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (h : IsZero ((modulePullback B S hS f).obj F)) : IsZero F := by
  refine (hempty X F).1 ?_
  have h₁ := (hempty Y _).2 h
  rw [hsupp f hf F hF] at h₁
  exact Set.eq_empty_of_forall_notMem fun x hx => by
    obtain ⟨y, rfl⟩ := hs x
    exact (Set.eq_empty_iff_forall_notMem.1 h₁) y hx

include hex hsupp hempty in
/-- **Lemma 2.15, last clause** (`lem:zero_object_via_covers`): for `f : Y ⟶ X` faithfully
flat (flat and surjective) and `E ∈ D(𝒪_X)` with `Hʲ(E)` quasi-coherent, `Hʲ(Lf^*E) ≅ 0`
implies `Hʲ(E) ≅ 0`.  GL26 states it for `X` quasi-compact quasi-separated and `E ∈ D_qc(X)`;
neither is needed. -/
theorem lemma_2_15_homology {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsFlatHom f)
    (hs : IsSurjective B S hS f.hom) (E : D B S hS X) (j : ℤ)
    (hE : qcoh X ((DerivedCategory.homologyFunctor (Space.Modules.{u, u} B S hS X.1 X.2) j).obj E))
    (h : IsZero ((DerivedCategory.homologyFunctor (Space.Modules.{u, u} B S hS Y.1 Y.2) j).obj
      ((pull f).obj E))) :
    IsZero ((DerivedCategory.homologyFunctor (Space.Modules.{u, u} B S hS X.1 X.2) j).obj E) :=
  isZero_of_isZero_modulePullback hsupp hempty f hf hs _ hE
    (h.of_iso (homologyPullIsoOfIsFlat hex f hf j E).symm)

include hex hsupp hempty in
/-- **Lemma 2.14** (`lem:faithfully_flat_is_conservative`): for a faithfully flat (flat and
surjective) morphism `f : Y ⟶ X` of algebraic spaces, `Lf^*` is conservative on `D_qc(X)`, in
the form "an object `E ∈ D_qc(X)` with `Lf^*E ≅ 0` is zero" (the form GL26's proof proves, and
the meaning of "conservative" GL26 gives in Lemma 3.2).  The reflection of isomorphisms is
`lemma_2_14_isIso`. -/
theorem lemma_2_14 {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsFlatHom f)
    (hs : IsSurjective B S hS f.hom) (E : D B S hS X) (hE : Dqc X E)
    (h : IsZero ((pull f).obj E)) : IsZero E :=
  isZero_of_isZero_homology E fun j =>
    lemma_2_15_homology hex hsupp hempty f hf hs E j (hE j)
      ((DerivedCategory.homologyFunctor _ j).map_isZero h)

include hex hsupp hempty in
/-- **Lemma 2.14** (`lem:faithfully_flat_is_conservative`), as reflection of isomorphisms: for
`f : Y ⟶ X` faithfully flat and `φ : E ⟶ F` a morphism of `D_qc(X)`, if `Lf^*φ` is an
isomorphism then so is `φ`.  Uses that `D_qc(X)` is triangulated (Stacks 06UQ,
`Spaces.Tag06UQInput`) and that `Lf^*` is a triangulated functor (AxiomMath, in the import
closure). -/
theorem lemma_2_14_isIso (h06UQ : Tag06UQInput B S hS) {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : IsFlatHom f) (hs : IsSurjective B S hS f.hom) {E F : D B S hS X}
    (φ : E ⟶ F) (hE : Dqc X E) (hF : Dqc X F) (h : IsIso ((pull f).map φ)) : IsIso φ := by
  have := Dqc_isTriangulated h06UQ X
  obtain ⟨G, g, δ, hT⟩ := distinguished_cocone_triangle φ
  have : (Dqc X).IsClosedUnderIsomorphisms := Supported.isClosedUnderIsomorphisms_qcohDerived X
  have hG : Dqc X G := (Dqc X).ext_of_isTriangulatedClosed₃ _ hT hE hF
  have hT' := (pull f).map_distinguished _ hT
  have hzero : IsZero ((pull f).obj G) :=
    (Triangle.isZero₃_iff_isIso₁ _ hT').2 h
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 (lemma_2_14 hex hsupp hempty f hf hs G hG hzero)

variable (hsm : FlatOfSmoothInput B S hS)

include hex hsupp hempty hsm in
/-- **Lemma 2.15** (`lem:zero_object_via_covers`): for `E ∈ D_qc(X)` the following are
equivalent:
1. `E ≅ 0`;
2. `Lf^*E ≅ 0` for every flat morphism `f : Y ⟶ X` of algebraic spaces;
3. `Lf^*E ≅ 0` for some smooth surjective morphism `f : Y ⟶ X`;
4. `Lf^*E ≅ 0` for some flat surjective morphism `f : Y ⟶ X`.

GL26 assumes `X` quasi-compact and quasi-separated; the equivalence holds without it.  The last
clause of the lemma is `lemma_2_15_homology`. -/
theorem lemma_2_15 {X : AlgebraicSpaces B S hS} (E : D B S hS X) (hE : Dqc X E) :
    List.TFAE
      [IsZero E,
        ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X), IsFlatHom f → IsZero ((pull f).obj E),
        ∃ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X),
          IsSmooth B S hS f.hom ∧ IsSurjective B S hS f.hom ∧ IsZero ((pull f).obj E),
        ∃ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X),
          IsFlatHom f ∧ IsSurjective B S hS f.hom ∧ IsZero ((pull f).obj E)] := by
  have hid : IsSmooth B S hS (𝟙 X : X ⟶ X).hom := isSmooth_id B S hS X.2
  have hsurj : IsSurjective B S hS (𝟙 X : X ⟶ X).hom := by
    change Function.Surjective (pointsMap B S hS X.1 (𝟙 X.1))
    rw [pointsMap_id]
    exact Function.surjective_id
  tfae_have 1 → 2 := fun h Y f _ => isZero_pull_obj f h
  tfae_have 2 → 3 := fun h => ⟨X, 𝟙 X, hid, hsurj, h X (𝟙 X) (hsm _ hid)⟩
  tfae_have 3 → 4 := fun ⟨Y, f, hf, hs, h⟩ => ⟨Y, f, hsm _ hf, hs, h⟩
  tfae_have 4 → 1 := fun ⟨Y, f, hf, hs, h⟩ => lemma_2_14 hex hsupp hempty f hf hs E hE h
  tfae_finish

end RelativeFM.Spaces.Conservative
