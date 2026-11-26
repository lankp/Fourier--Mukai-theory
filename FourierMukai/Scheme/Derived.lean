/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Triangulated.Subcategory

@[expose] public section

/-!
# `D(X)` and `D_qc(X)` for a scheme

`Derived X` is the unbounded derived category of sheaves of `O_X`-modules
(Mathlib's `DerivedCategory`), `cohomologySheaf` its cohomology sheaves, and
`IsDQCoh X` the object property "every cohomology sheaf is quasicoherent", using
Mathlib's `SheafOfModules.IsQuasicoherent` and the affine description `tildeEquiv`.
`Dqc X` is the full subcategory on that property and `dqcι X` its inclusion.

Proved: iso-, zero- and shift-closure, and closure under cones and retracts given
`QuasicoherentSerreInput` (Stacks 01LA: quasicoherent sheaves are closed under
extensions); the affine case `Qcoh(Spec R)` is proved closed under coproducts
outright.  `QuasicoherentSerreInput` is false for `Spec ℤ`
(`Scheme/RefuteQCohSerre.lean`); its consumer `isDQCohTriangulatedOfInput` and the
coproduct input `DQCohCoproductInput` were deleted in wave 6 (`results/OPEN_INPUTS.md`
rows 1.20, 7.10).

Found by a member of the Ultramath run `smwuyku7t` (direction R1).
-/

noncomputable section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry
open scoped ZeroObject

universe u v w v₁ w₁

/-! ## Cohomological full subcategories of a derived category -/

section CohomologyWithin

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Objects of the derived category all of whose cohomology objects satisfy `P`.
For the quasi-coherence predicate this is the definition of `D_qc(X)` in GL26,
Section `sec:prelim_stacks_categories`. -/
def cohomologyWithin (P : ObjectProperty C) : ObjectProperty (DerivedCategory C) :=
  fun E ↦ ∀ n : ℤ, P ((DerivedCategory.homologyFunctor C n).obj E)

variable (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]

instance cohomologyWithin_isClosedUnderIsomorphisms :
    (cohomologyWithin P).IsClosedUnderIsomorphisms where
  of_iso e hE n :=
    P.prop_of_iso ((DerivedCategory.homologyFunctor C n).mapIso e) (hE n)

instance cohomologyWithin_containsZero [P.ContainsZero] :
    (cohomologyWithin P).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun n ↦
    P.prop_of_isZero ((DerivedCategory.homologyFunctor C n).map_isZero (isZero_zero _))⟩

instance cohomologyWithin_isStableUnderShift :
    (cohomologyWithin P).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun E hE n ↦
    P.prop_of_iso
      (((DerivedCategory.homologyFunctor C 0).shiftIso a n (a + n) rfl).symm.app E)
      (hE (a + n))⟩

/-- If `P` is a Serre class, its cohomological inverse image is closed in the
middle position of distinguished triangles.  This is the long exact cohomology
sequence argument for `D_qc(X)`. -/
instance cohomologyWithin_isTriangulatedClosed₂ [P.IsSerreClass] :
    (cohomologyWithin P).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ n ↦
    P.prop_X₂_of_exact
      (DerivedCategory.HomologySequence.exact₂ T hT n) (h₁ n) (h₃ n))

/-- The cohomological inverse image of a Serre class is a triangulated
object property. -/
instance cohomologyWithin_isTriangulated [P.IsSerreClass] :
    (cohomologyWithin P).IsTriangulated where

/-- Cohomological inverse images of subobject-closed classes are also stable
under retracts.  In particular, `D_qc(X)` is thick once `Qcoh(X)` is a Serre
class. -/
instance cohomologyWithin_isStableUnderRetracts [P.IsClosedUnderSubobjects] :
    (cohomologyWithin P).IsStableUnderRetracts where
  of_retract r hE n :=
    P.prop_of_mono ((r.map (DerivedCategory.homologyFunctor C n)).i) (hE n)

/-- Coproduct (and more generally colimit) closure, with exactly the two inputs
needed: `P` is closed under the same colimits and every cohomology functor
preserves them. -/
instance cohomologyWithin_isClosedUnderColimitsOfShape
    (J : Type w₁) [Category.{v₁} J] [P.IsClosedUnderColimitsOfShape J]
    [∀ n : ℤ, PreservesColimitsOfShape J (DerivedCategory.homologyFunctor C n)] :
    (cohomologyWithin P).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨c⟩ n
    exact P.prop_of_isColimit
      (isColimitOfPreserves (DerivedCategory.homologyFunctor C n) c.isColimit)
      (fun j ↦ c.prop_diag_obj j n)

end CohomologyWithin

/-! ## The derived category of a scheme -/

/-- The standard choice of a derived category for sheaves of modules on a scheme.
The choice has homomorphisms in the same universe as the localized category.
No `.{v}`-smallness hypothesis on the geometry is needed. -/
noncomputable instance hasDerivedCategory_modules (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

/-- `D(X)`, the unbounded derived category of all sheaves of `𝒪_X`-modules
(GL26, Section `sec:prelim_stacks_categories`). -/
abbrev Derived (X : Scheme.{u}) : Type (u + 1) :=
  DerivedCategory.{u + 1} X.Modules

/-- The `n`-th cohomology-sheaf functor on `D(X)`. -/
abbrev cohomologySheafFunctor (X : Scheme.{u}) (n : ℤ) : Derived X ⥤ X.Modules :=
  DerivedCategory.homologyFunctor X.Modules n

/-- The `n`-th cohomology sheaf of an object of `D(X)`. -/
abbrev cohomologySheaf {X : Scheme.{u}} (E : Derived X) (n : ℤ) : X.Modules :=
  (cohomologySheafFunctor X n).obj E

/-- Mathlib's object property of quasi-coherent sheaves of modules.  It is
defined by local presentations by free sheaves (Stacks Tag 01BD), not by a new
ad hoc predicate. -/
abbrev quasiCoherent (X : Scheme.{u}) : ObjectProperty X.Modules :=
  SheafOfModules.isQuasicoherent X.ringCatSheaf

/-- `IsDQCoh E` says that every cohomology sheaf of `E` is quasi-coherent.
This is exactly the object condition for `D_qc(X)` in GL26, Section
`sec:prelim_stacks_categories`. -/
def IsDQCoh (X : Scheme.{u}) : ObjectProperty (Derived X) :=
  cohomologyWithin (quasiCoherent X)

/-- The full subcategory `D_qc(X)` of `D(X)`. -/
abbrev Dqc (X : Scheme.{u}) : Type (u + 1) := (IsDQCoh X).FullSubcategory

/-- The fully faithful inclusion `D_qc(X) ⥤ D(X)`. -/
abbrev dqcι (X : Scheme.{u}) : Dqc X ⥤ Derived X := (IsDQCoh X).ι

/-- Membership in `IsDQCoh` unfolds to quasi-coherence of every cohomology
sheaf. -/
theorem isDQCoh_iff {X : Scheme.{u}} {E : Derived X} :
    IsDQCoh X E ↔ ∀ n : ℤ, (cohomologySheaf E n).IsQuasicoherent :=
  Iff.rfl

/-- Quasi-coherence on an affine scheme is precisely membership in the essential
image of `M ↦ M^~` (Stacks Tag 01BD).  No replacement for `IsAffineOpen` or for
`tilde` was necessary. -/
theorem mem_essImage_tilde_iff {R : CommRingCat.{u}} {M : (Spec R).Modules} :
    (tilde.functor R).essImage M ↔ M.IsQuasicoherent := by
  rw [essImage_tilde]

/-- The affine equivalence between modules and quasi-coherent sheaves. -/
abbrev affineQCohEquivalence (R : CommRingCat.{u}) :
    ModuleCat R ≌ (quasiCoherent (Spec R)).FullSubcategory :=
  tildeEquiv

/-- On an affine scheme, `Qcoh(Spec R)` is closed under coproducts indexed
by the universe of `R`.  Indeed, `tilde` is a fully faithful left adjoint, so
its essential image is closed under the coproducts it preserves;
`essImage_tilde` identifies that essential image with quasi-coherent sheaves.
This proves the affine case of Stacks Tag 01LA(3).  The `Type u` indexing
condition is the same-universe smallness used by Mathlib's `tilde` API. -/
theorem quasiCoherent_spec_isClosedUnderCoproducts
    (R : CommRingCat.{u}) (ι : Type u) :
    (quasiCoherent (Spec R)).IsClosedUnderColimitsOfShape (Discrete ι) := by
  have h : (tilde.functor R).essImage.IsClosedUnderColimitsOfShape (Discrete ι) :=
    inferInstance
  simpa only [← essImage_tilde (R := R)] using h

/-! ## Closure of `D_qc(X)`

Mathematically, quasi-coherent sheaves on a scheme form a Serre class and are
closed under colimits (Stacks Tag 01LA, items (3)--(6), and Tag 01LB).  These
geometric theorems are not yet instances for Mathlib's
`SheafOfModules.isQuasicoherent`.  Consequently the corresponding instances
below take precisely these facts as hypotheses; no unproved geometric fact is
installed globally.
-/

/-- The geometric input required for the triangulated structure on `D_qc(X)`.
Its field says that `Qcoh(X)` is a Serre class: it contains zero and is stable
under subobjects, quotients, and extensions.  This is the content of Stacks Tag
01LA, items (3), (5), and (6), together with Tag 01LB. -/
structure QuasicoherentSerreInput (X : Scheme.{u}) : Prop where
  serreClass : (quasiCoherent X).IsSerreClass

/-- Quasi-coherence is invariant under isomorphism (already proved in Mathlib). -/
instance quasiCoherent_isClosedUnderIsomorphisms (X : Scheme.{u}) :
    (quasiCoherent X).IsClosedUnderIsomorphisms := by
  change (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderIsomorphisms
  infer_instance

/-- The zero sheaf is quasi-coherent.  We realize it as the free sheaf on an
empty type, whose local-free presentation has no generators or relations. -/
instance quasiCoherent_containsZero (X : Scheme.{u}) :
    (quasiCoherent X).ContainsZero := by
  let Z : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Empty)
  have hZ : IsInitial Z := IsInitial.ofUniqueHom (fun _ ↦ 0) (fun Y m ↦ by
    apply (SheafOfModules.freeHomEquiv Y).injective
    funext i
    exact i.down.elim)
  exact ⟨Z, hZ.isZero, inferInstance⟩

instance isDQCoh_isClosedUnderIsomorphisms (X : Scheme.{u}) :
    (IsDQCoh X).IsClosedUnderIsomorphisms :=
  cohomologyWithin_isClosedUnderIsomorphisms (C := X.Modules)
    (P := quasiCoherent X)

instance isDQCoh_containsZero (X : Scheme.{u}) :
    (IsDQCoh X).ContainsZero :=
  cohomologyWithin_containsZero (C := X.Modules)
    (P := quasiCoherent X)

/-- Shift-stability does not require the Serre-class input: it is immediate
from the canonical cohomology-shift isomorphisms. -/
instance isDQCoh_isStableUnderShift (X : Scheme.{u}) :
    (IsDQCoh X).IsStableUnderShift ℤ :=
  cohomologyWithin_isStableUnderShift (C := X.Modules)
    (P := quasiCoherent X)

/-- Once `Qcoh(X)` is known to be a Serre class, `D_qc(X)` is triangulated.
The proof is the long exact cohomology sequence for a distinguished triangle. -/
instance isDQCoh_isTriangulated (X : Scheme.{u}) [(quasiCoherent X).IsSerreClass] :
    (IsDQCoh X).IsTriangulated :=
  cohomologyWithin_isTriangulated (C := X.Modules)
    (P := quasiCoherent X)

/-- Under the same Serre-class input, `D_qc(X)` is thick: direct summands are
seen on cohomology, where they are subobjects. -/
instance isDQCoh_isStableUnderRetracts (X : Scheme.{u})
    [(quasiCoherent X).IsClosedUnderSubobjects] :
    (IsDQCoh X).IsStableUnderRetracts :=
  cohomologyWithin_isStableUnderRetracts (C := X.Modules)
    (P := quasiCoherent X)

/-- Colimit closure of `D_qc(X)`, conditional only on colimit closure of
`Qcoh(X)` and exactness of cohomology on the same diagram shape.  Taking
`J = Discrete ι` gives coproduct closure. -/
instance isDQCoh_isClosedUnderColimitsOfShape
    (X : Scheme.{u}) (J : Type w₁) [Category.{v₁} J]
    [(quasiCoherent X).IsClosedUnderColimitsOfShape J]
    [∀ n : ℤ, PreservesColimitsOfShape J (cohomologySheafFunctor X n)] :
    (IsDQCoh X).IsClosedUnderColimitsOfShape J :=
  cohomologyWithin_isClosedUnderColimitsOfShape (C := X.Modules)
    (P := quasiCoherent X) J

/-!
## What had to be added to Mathlib

| ingredient | status here |
|---|---|
| `D(X)` | defined directly as `DerivedCategory X.Modules`, using `HasDerivedCategory.standard` |
| cohomology sheaves | direct use of `DerivedCategory.homologyFunctor` |
| quasi-coherence | no new predicate: Mathlib already has `SheafOfModules.IsQuasicoherent`, including affine `tildeEquiv` |
| `D_qc(X)` | the new `IsDQCoh` and its full subcategory `Dqc` |
| iso, zero, shift closure | proved; zero uses a presentation with no generators |
| cone/extension closure | proved from `QuasicoherentSerreInput`; the missing geometric fact is Stacks Tag 01LA(5),(6) |
| thickness | proved from subobject closure in `Qcoh(X)` |
| coproduct/localizing closure | not proved here (the input `DQCohCoproductInput` was deleted in wave 6); the geometric content is Stacks Tag 01LA(3) and coproduct exactness of cohomology |

The `.{v}` universe appearing in `cohomologyWithin` is the morphism universe of
the abelian category.  Coproduct shapes have independent object and morphism
universes `w₁` and `v₁`; no smallness restriction is imposed on a scheme.
-/

/-! ### Axiom audit -/

end RelativeFM
