/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectObjects
import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces

/-!
# The categories of GL26 §2.2 over an algebraic space

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26),
§2.2 (`sec:preliminaries_stacks`), subsections `sec:prelim_stacks_categories` and
`sec:preliminaries_stacks_support`: for an algebraic space `X` over a base scheme, the
unbounded derived category `D(X) = D(𝒪_X)` of `𝒪_X`-modules on the small étale site, and
its full subcategories `D_qc(X)`, `D^b_qc(X)`, `D^-_coh(X)`, `D^b_coh(X)`, `Perf(X)` and
`D_{qc,Z}(X)`, together with the support of an object.

Everything here is a *definition* built from AxiomMath/Stacks' definitions (the import
list `scripts/axiommath/spaces-imports.txt`); nothing is assumed.  The fidelity verdicts
are those of `results/AXIOMMATH_MAP.md`, A.0 and A.3.

## The model

The base is fixed once and for all: `B : BigFppfSite.{u}` (Stacks 021R), a scheme `S`
with `hS : B.Contains S`, and algebraic spaces are objects of `AlgebraicSpaces B S hS`
(Stacks 025Y, 02X2).  `D X` is AxiomMath's canonical model of `D(𝒪_X)`
(`AXIOMMATH_MAP.md`, A.0): the derived category, at `HasDerivedCategory.standard`, of the
sheaves of modules over the structure sheaf of the small étale ringed topos of `X`.  It is
written in the spelling `SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)` in
which AxiomMath states `Lf^*`, `Rf_*`, `⊗^L` and `Lf^* ⊣ Rf_*`; it is definitionally the
spelling `DerivedCategory (Modules.{u, u} B S hS X.1 X.2)` in which `D_QCoh`, `Perf` and
support are stated (`D_eq_derivedModules` below checks this by `rfl`).

## Main definitions

* `D X`: `D(𝒪_X)`.
* `Dqc X`: `D_qc(X)`, objects whose cohomology sheaves are all quasi-coherent (Stacks
  06UP/071X); `Dqc X` *as a property* is AxiomMath's `QcohDerived`, and its full
  subcategory is AxiomMath's `QuasicoherentDerivedCategory` (`Dqc_fullSubcategory_eq`).
* `Dbqc X`: `D^b_qc(X)`; `DminusCoh X`: `D^-_coh(X)`; `DbCoh X`: `D^b_coh(X)`;
  `Perf X`: `Perf(X)` (Stacks 08G5); `IsPseudoCoherent X` (Stacks 08FT).
* `supp X E`: the support `⋃ⱼ Supp Hʲ(E) ⊆ |X|`; `DqcSupported X T`: `D_{qc,T}(X)`.

## Differences from GL26

* GL26 takes `Perf(X)`, `D^b_coh(X)`, … as subcategories of `D_qc(X)`.  `Perf X` is
  AxiomMath's perfectness on all of `D(𝒪_X)`; perfect objects lie in `D_qc` (AxiomMath's
  `qcohDerived_of_isPerfect_derivedCategoryB`, not needed here), so the two agree.
  `DbCoh X` and `DminusCoh X` include `D_qc` membership explicitly.
* `D^b_coh(X)`: GL26 defines it, for Noetherian `X`, as the bounded pseudo-coherent objects
  of `D_qc(X)`; `DbCoh X` is exactly that, for every `X` (GL26 only uses it for Noetherian
  `X`).  `D^-_coh(X)` is the bounded-above objects of `D_qc(X)` with coherent cohomology
  sheaves (convention recorded in `FourierMukai/Paper/DerivedSetup.lean`); on a Noetherian
  space the two readings of `D^b_coh` agree (Stacks 08IK, not used here).
* "Coherent" is `IsQuasicoherentOnSite ∧ IsCoherentOnSite` (Stacks 03DL(6), 03DL(8)),
  which is the body of AxiomMath's class `AlgebraicGeometry.Space.IsCoherent` (Stacks
  07UA); that class lives in a module outside the import list, so its two fields are
  used directly.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `D(X) = D(𝒪_X)`: the unbounded derived category of `𝒪_X`-modules on the small étale
site of the algebraic space `X` (GL26 §2.2, `sec:prelim_stacks_categories`), in
AxiomMath's canonical model (`AXIOMMATH_MAP.md`, A.0). -/
abbrev D (X : AlgebraicSpaces B S hS) : Type (u + 1) :=
  DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))

/-- `D X` is, by definition, AxiomMath's `DerivedCategory (Modules.{u, u} B S hS X.1 X.2)`. -/
theorem D_eq_derivedModules (X : AlgebraicSpaces B S hS) :
    D B S hS X = DerivedCategory (Modules.{u, u} B S hS X.1 X.2) := rfl

variable {B S hS}

/-- Quasi-coherence of a module on the small étale site of `X` (Stacks 03DL(6), as
AxiomMath's `SheafOfModules.isQuasicoherentOnSite` at the scheme universe). -/
abbrev qcoh (X : AlgebraicSpaces B S hS) :
    ObjectProperty (Modules.{u, u} B S hS X.1 X.2) :=
  SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)

/-- Coherence of a module on the small étale site of `X`: quasi-coherent and coherent in
the sense of Stacks 03DL(8).  This is the body of AxiomMath's `Space.IsCoherent`
(Stacks 07UA), whose module is outside the `Spaces` import list. -/
def coh (X : AlgebraicSpaces B S hS) : ObjectProperty (Modules.{u, u} B S hS X.1 X.2) :=
  fun M => SheafOfModules.IsQuasicoherentOnSite M ∧ SheafOfModules.IsCoherentOnSite M

/-- **`D_qc(X)`** (GL26 §2.2, `sec:prelim_stacks_categories`): the objects of `D(𝒪_X)`
all of whose cohomology sheaves are quasi-coherent.  Definitionally AxiomMath's
`QcohDerived B S hS X` (Stacks 071X). -/
abbrev Dqc (X : AlgebraicSpaces B S hS) : ObjectProperty (D B S hS X) :=
  DerivedCategoryB.derivedCategoryB (qcoh X)

/-- The full subcategory of `Dqc X` is AxiomMath's `QuasicoherentDerivedCategory`. -/
theorem Dqc_fullSubcategory_eq (X : AlgebraicSpaces B S hS) :
    (Dqc X).FullSubcategory = QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 := rfl

/-- **`D^b_qc(X)`**: cohomologically bounded objects of `D_qc(X)`. -/
abbrev Dbqc (X : AlgebraicSpaces B S hS) : ObjectProperty (D B S hS X) :=
  DerivedCategoryB.derivedCategoryBBounded (qcoh X)

/-- **`D^-_qc(X)`**: cohomologically bounded-above objects of `D_qc(X)`. -/
abbrev DminusQc (X : AlgebraicSpaces B S hS) : ObjectProperty (D B S hS X) :=
  DerivedCategoryB.derivedCategoryBMinus (qcoh X)

/-- **`D^-_coh(X)`**: bounded-above objects of `D(𝒪_X)` all of whose cohomology sheaves
are coherent (in particular quasi-coherent, so these lie in `D_qc(X)`). -/
abbrev DminusCoh (X : AlgebraicSpaces B S hS) : ObjectProperty (D B S hS X) :=
  DerivedCategoryB.derivedCategoryBMinus (coh X)

/-- **Pseudo-coherence** (Stacks 08FT) of an object of `D(𝒪_X)`, AxiomMath's
`RingedSite.IsPseudoCoherent` on the small étale ringed site. -/
def IsPseudoCoherent (X : AlgebraicSpaces B S hS) : ObjectProperty (D B S hS X) :=
  fun E => (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E

/-- **`D^b_coh(X)`** (GL26 §2.2): the bounded pseudo-coherent objects of `D_qc(X)`.  GL26
uses it for Noetherian `X`, where it is also `D^b_qc(X) ∩ D^-_coh(X)` (Stacks 08IK). -/
def DbCoh (X : AlgebraicSpaces B S hS) : ObjectProperty (D B S hS X) :=
  fun E => Dbqc X E ∧ IsPseudoCoherent X E

/-- **`Perf(X)`** (GL26 §2.2, Stacks 08G5): the perfect objects of `D(𝒪_X)`, AxiomMath's
`perfectProperty`. -/
abbrev Perf (X : AlgebraicSpaces B S hS) : ObjectProperty (D B S hS X) :=
  perfectProperty B S hS X

/-- **The support** of `E ∈ D(𝒪_X)` (GL26 `sec:preliminaries_stacks_support`): the union
over `j` of the supports `Supp Hʲ(E) ⊆ |X|` of its cohomology sheaves, each the support
of an abelian sheaf on the small étale site (AxiomMath's `supportOfSheaf`). -/
def supp (X : AlgebraicSpaces B S hS) (E : D B S hS X) : Set (points B S hS X.1) :=
  ⋃ j : ℤ, supportOfSheaf B S hS X.1
    ((SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) j).obj E))

/-- "`E` is supported on `T`" (AxiomMath's `CohomologySupportedOn`, Stacks 08GF) is
`supp E ⊆ T`. -/
theorem cohomologySupportedOn_iff_supp_subset (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (E : D B S hS X) :
    Space.CohomologySupportedOn.{u, u} B S hS X.1 X.2 T E ↔ supp X E ⊆ T :=
  Set.iUnion_subset_iff.symm

/-- **`D_{qc,T}(X)`** (GL26 §2.2, `sec:prelim_stacks_perfects`): objects of `D_qc(X)`
supported on `T ⊆ |X|`.  GL26 takes `T` closed with quasi-compact complement; the property
is defined for every `T`. -/
def DqcSupported (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) :
    ObjectProperty (D B S hS X) :=
  fun E => Dqc X E ∧ Space.CohomologySupportedOn.{u, u} B S hS X.1 X.2 T E

end RelativeFM.Spaces
