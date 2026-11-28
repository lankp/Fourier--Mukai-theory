/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.InternalHom.Basic
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral

/-!
# GL26 Lemma 2.10 (`lem:rhom_tensor_morphism`)

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), §2.2,
`sec:prelim_stacks_internal_homs`, **Lemma 2.10**: for an algebraic space `X`, `K` perfect and
`L, M ∈ D(X)`, a functorial isomorphism

`K ⊗^L R𝓗om(M, L) ≅ R𝓗om(R𝓗om(K, M), L)`.

## Proof

GL26's chain is `K ⊗ R𝓗om(M, L) ≅ R𝓗om(K^∨, R𝓗om(M, L))` (08JJ for `K^∨`, `K^∨∨ ≅ K`)
`≅ R𝓗om(K^∨ ⊗ M, L)` (08J9) `≅ R𝓗om(R𝓗om(K, M), L)` (08JJ).  Here the last two steps are done
at once by uniqueness of adjoints: `L ↦ R𝓗om(K^∨, R𝓗om(M, L))` is right adjoint to
`A ↦ (A ⊗ K^∨) ⊗ M` (composite of two instances of Stacks 08J8), `L ↦ R𝓗om(R𝓗om(K, M), L)` is
right adjoint to `A ↦ A ⊗ R𝓗om(K, M)`, and these left adjoints are isomorphic by the associator
of `⊗^L` and `K^∨ ⊗ M ≅ R𝓗om(K, M)` (08JJ); `CategoryTheory.conjugateIsoEquiv` (Mathlib) turns
that into the isomorphism of right adjoints.  The first step uses 08JJ *natural in the target*,
`sheafHomIsoTensorDualRight`, which is assembled here from AxiomMath's model-level 08JJ and its
naturality (`RingedSite.derivedDualTensorSheafHomIso_naturality`), and the symmetry of `⊗^L`
(`tensorBraiding`, the commutativity constraint of Stacks 0FPT transported to `⊗^L`).

Everything used is in the `Spaces` import list (`scripts/axiommath/spaces-imports.txt`); there is
no tagged input.

## Differences from GL26

* "Functorial" is rendered as naturality in `L` (an isomorphism of functors of `L`, for fixed
  perfect `K` and fixed `M`).  Naturality in `M` (and in `K`) is not proved here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Space Opposite

namespace RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The derived dual `E^∨ = R𝓗om(E, 𝒪_X)` (AxiomMath's `smallEtaleDerivedDual`). -/
abbrev dual (E : D B S hS X) : D B S hS X := smallEtaleDerivedDual B S hS X E

/-- The dual of a perfect object is perfect (Stacks 08JJ, AxiomMath's
`isPerfect_smallEtaleDerivedDual`). -/
theorem perf_dual {E : D B S hS X} (hE : Perf X E) : Perf X (dual E) :=
  isPerfect_smallEtaleDerivedDual B S hS X E hE

/-- **Stacks 08JJ, natural in the target**: for `E` perfect, `R𝓗om(E, -) ≅ - ⊗^L E^∨` as functors
on `D(X)`.  Assembled from AxiomMath's model-level isomorphism
`RingedSite.derivedDualTensorSheafHomIso` (natural by
`RingedSite.derivedDualTensorSheafHomIso_naturality`), the identification of the duals
`smallEtaleModelDerivedDualIso`, and the comparison of tensor products
`smallEtaleDerivedTensorRightIso`, all read through the derived equivalence with the model by
which `R𝓗om` is defined. -/
def sheafHomIsoTensorDualRight (E : D B S hS X) (hE : Perf X E) :
    (sheafHom X).obj (op E) ≅ (tensor X).flip.obj (dual E) :=
  let e := smallEtaleModelDerivedEquivalence B S hS X
  let M := smallEtaleModelRingedSite B S hS X.1 X.2
  let hE' := isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE
  let nat : (Stacks.SheafOfModules.derivedTensorProductFunctor M).flip.obj
        (RingedSite.derivedDual M (e.functor.obj E)) ≅
      (RingedSite.derivedSheafHomBifunctor M).obj (op (e.functor.obj E)) :=
    NatIso.ofComponents
      (fun N => RingedSite.derivedDualTensorSheafHomIso M (e.functor.obj E) N hE')
      (fun f => RingedSite.derivedDualTensorSheafHomIso_naturality M (e.functor.obj E) hE' f)
  (Iso.refl _ : (sheafHom X).obj (op E) ≅
      e.functor ⋙ (RingedSite.derivedSheafHomBifunctor M).obj (op (e.functor.obj E)) ⋙
        e.inverse) ≪≫
    Functor.isoWhiskerLeft e.functor (Functor.isoWhiskerRight nat.symm e.inverse) ≪≫
    Functor.isoWhiskerLeft e.functor (Functor.isoWhiskerRight
      ((Stacks.SheafOfModules.derivedTensorProductFunctor M).flip.mapIso
        (smallEtaleModelDerivedDualIso B S hS X E).symm) e.inverse) ≪≫
    (smallEtaleDerivedTensorRightIso B S hS X (dual E)).symm

/-- `R𝓗om(K^∨, -) ≅ - ⊗^L K` for `K` perfect: `sheafHomIsoTensorDualRight` at `K^∨`, followed by
`K^∨∨ ≅ K` (AxiomMath's `smallEtaleDerivedBidualIso`). -/
def sheafHomDualIsoTensorRight (K : D B S hS X) (hK : Perf X K) :
    (sheafHom X).obj (op (dual K)) ≅ (tensor X).flip.obj K :=
  sheafHomIsoTensorDualRight (dual K) (perf_dual hK) ≪≫
    (tensor X).flip.mapIso (smallEtaleDerivedBidualIso B S hS X K hK)

/-- **The symmetry of `⊗^L`** on `D(X)`: `K ⊗^L - ≅ - ⊗^L K`, naturally in both variables.  The
commutativity constraint of the symmetric monoidal derived category of Stacks 0FPT
(`DerivedMonoidalGeneral.derivedSymmetric`), transported to `⊗^L` along AxiomMath's comparison
`DerivedTensorProduct.monoidalTensorIso`. -/
def tensorBraiding (X : AlgebraicSpaces B S hS) : tensor X ≅ (tensor X).flip :=
  letI := Stacks.SheafOfModules.DerivedMonoidalGeneral.derivedMonoidal
    (smallEtaleRingedSite B S hS X.1 X.2).O
  letI := Stacks.SheafOfModules.DerivedMonoidalGeneral.derivedSymmetric
    (smallEtaleRingedSite B S hS X.1 X.2).O
  (smallEtaleDerivedTensorProduct B S hS X).monoidalTensorIso.symm ≪≫
    BraidedCategory.curriedBraidingNatIso _ ≪≫
    (flipFunctor _ _ _).mapIso (smallEtaleDerivedTensorProduct B S hS X).monoidalTensorIso

/-- The associator `(A ⊗ P) ⊗ M ≅ A ⊗ (P ⊗ M)`, natural in `A` (AxiomMath's
`DerivedTensorProduct.associatorGeneral`, Stacks 0FPT). -/
def tensorAssoc (P M : D B S hS X) :
    (tensor X).flip.obj P ⋙ (tensor X).flip.obj M ≅ (tensor X).flip.obj (tensorObj P M) :=
  NatIso.ofComponents
    (fun A => (smallEtaleDerivedTensorProduct B S hS X).associatorGeneral A P M)
    (fun a => (smallEtaleDerivedTensorProduct B S hS X).associatorGeneral_naturality_left a P M)

/-- The left adjoints of the two sides of Lemma 2.10, identified: `A ⊗ R𝓗om(K, M) ≅
(A ⊗ K^∨) ⊗ M`, from `R𝓗om(K, M) ≅ K^∨ ⊗ M` (Stacks 08JJ, AxiomMath's
`smallEtaleDerivedSheafHomIsoTensorDual`) and the associator. -/
def lemma_2_10_leftAdjointIso (K M : D B S hS X) (hK : Perf X K) :
    (tensor X).flip.obj (sheafHomObj K M) ≅
      (tensor X).flip.obj (dual K) ⋙ (tensor X).flip.obj M :=
  (tensor X).flip.mapIso (smallEtaleDerivedSheafHomIsoTensorDual B S hS X K M hK) ≪≫
    (tensorAssoc (dual K) M).symm

/-- **Lemma 2.10** (`lem:rhom_tensor_morphism`).  Let `X` be an algebraic space, `K ∈ D(X)`
perfect and `M ∈ D(X)`.  There is an isomorphism, natural in `L ∈ D(X)`,

`K ⊗^L R𝓗om(M, L) ≅ R𝓗om(R𝓗om(K, M), L)`,

as an isomorphism of functors of `L`.  GL26 says "functorial"; naturality in `M` and `K` is not
part of this statement (module docstring). -/
def lemma_2_10 (K M : D B S hS X) (hK : Perf X K) :
    (sheafHom X).obj (op M) ⋙ (tensor X).obj K ≅ (sheafHom X).obj (op (sheafHomObj K M)) :=
  Functor.isoWhiskerLeft ((sheafHom X).obj (op M))
      ((tensorBraiding X).app K ≪≫ (sheafHomDualIsoTensorRight K hK).symm) ≪≫
    (conjugateIsoEquiv ((tensorSheafHomAdj (dual K)).comp (tensorSheafHomAdj M))
      (tensorSheafHomAdj (sheafHomObj K M))) (lemma_2_10_leftAdjointIso K M hK)

/-- **Lemma 2.10** (`lem:rhom_tensor_morphism`), at one object `L`:
`K ⊗^L R𝓗om(M, L) ≅ R𝓗om(R𝓗om(K, M), L)` for `K` perfect. -/
def lemma_2_10_app (K M L : D B S hS X) (hK : Perf X K) :
    tensorObj K (sheafHomObj M L) ≅ sheafHomObj (sheafHomObj K M) L :=
  (lemma_2_10 K M hK).app L

/-- The isomorphism of `lemma_2_10` is natural in `L`. -/
theorem lemma_2_10_naturality (K M : D B S hS X) (hK : Perf X K) {L L' : D B S hS X}
    (g : L ⟶ L') :
    ((tensor X).obj K).map (((sheafHom X).obj (op M)).map g) ≫
        (lemma_2_10_app K M L' hK).hom =
      (lemma_2_10_app K M L hK).hom ≫ ((sheafHom X).obj (op (sheafHomObj K M))).map g :=
  (lemma_2_10 K M hK).hom.naturality g

end RelativeFM.Spaces
