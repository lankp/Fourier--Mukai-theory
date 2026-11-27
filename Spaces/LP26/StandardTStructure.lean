/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Supported.CompactGeneration
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# The standard `t`-structure on `D_{qc,S}(X)` (LP26, remark before Definition 5.3)

Lank–Pauwels, *Gluing weak approximability along recollements* (LP26), §5, the remark preceding
Definition 5.3 (`def:wa_spaces`): for `X` an algebraic space and `S ⊆ |X|`, the standard
`t`-structure of `D(𝒪_X)` (`H^j(E) = 0` for `j > 0`, resp. `j < 0`) induces a `t`-structure on
`D_{qc,S}(X)`, because the canonical truncations of an object of `D_qc(X)` supported on `S` have
quasi-coherent cohomology supported on `S` (Stacks 0118).  This is the `t`-structure
`(D^{≤ 0}_{qc,S}(X), D^{≥ 0}_{qc,S}(X))` of LP26's "standard W.A.".

## Main definitions and results

* `hasInducedTStructure_inverseImage`: (general) if `P` has an induced `t`-structure and `Q` is
  stable under the truncations of objects of `P`, then `Q` (as a property of the full
  subcategory of `P`) has an induced `t`-structure for the induced one.
* `standardTStructureQc X`: the standard `t`-structure on `D_qc(X)`
  (AxiomMath's `QuasicoherentDerivedCategory`), induced by Mathlib's
  `DerivedCategory.TStructure.t`.
* `standardTStructure X T`: the standard `t`-structure on `D_{qc,T}(X)` (`Supported.DqcZ X T`),
  induced by `standardTStructureQc X`, for every `T ⊆ |X|`.
* `standardTStructure_le_iff`, `standardTStructure_ge_iff`: `E ∈ D^{≤ n}_{qc,T}(X)` iff
  `H^j(E) = 0` for `j > n` (Mathlib's `IsLE` of the underlying object of `D(𝒪_X)`), and dually.

## Assumptions

None beyond the two `Prop` instances that make `D_qc(X)` and `D_{qc,T}(X)` triangulated
(`(qcohDerived X).IsTriangulated`, Stacks 06UQ, and
`(CohomologySupportedOn … T).IsTriangulated`, which `Supported.isTriangulated_qcohDerived` and
`Supported.isTriangulated_support` provide from tagged AxiomMath inputs); they are instance
arguments, as in `Spaces/Supported/CompactGeneration.lean`.  The truncation statements are
proved here from Mathlib's `DerivedCategory.truncLTCompHomologyFunctorIso` and
`truncGECompHomologyFunctorIso`, following AxiomMath's
`DerivedCategoryB.derivedCategoryB_truncLT_obj` (`Algebra/Homology/DerivedCategory/
BoundedSerreInducedTStructure.lean`, outside the import list).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.LP26

universe u

section General

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Induced `t`-structures in two steps.**  Let `t` be a `t`-structure on `C`, `P` a
triangulated subcategory with an induced `t`-structure, and `Q` a property of `C`, closed under
isomorphisms, such that the `t`-truncations of an object satisfying `P` and `Q` satisfy `Q`.
Then `Q`, viewed in the full subcategory of `P`, has an induced `t`-structure for the one
induced by `t` on `P`. -/
theorem hasInducedTStructure_inverseImage (t : TStructure C) (P : ObjectProperty C)
    [P.IsTriangulated] [P.HasInducedTStructure t] (Q : ObjectProperty C)
    [Q.IsClosedUnderIsomorphisms] [(Q.inverseImage P.ι).IsTriangulated]
    (hQ : ∀ X : C, P X → Q X → ∀ n : ℤ, Q ((t.truncLE n).obj X) ∧ Q ((t.truncGE n).obj X)) :
    (Q.inverseImage P.ι).HasInducedTStructure (P.tStructure t) := by
  refine .mk' fun X hX n => ?_
  have key : ∀ a b : ℤ, a + 1 = b →
      Q (P.ι.obj (((P.tStructure t).truncLE a).obj X)) ∧
        Q (P.ι.obj (((P.tStructure t).truncGE b).obj X)) := fun a b h => by
    obtain ⟨e, -⟩ := t.triangle_iso_exists
      (P.ι.map_distinguished _ ((P.tStructure t).triangleLEGE_distinguished a b h X))
      (t.triangleLEGE_distinguished a b h X.obj) (Iso.refl _) a b
      (by
        change t.IsLE (((P.tStructure t).truncLE a).obj X).obj a
        rw [← P.tStructure_isLE_iff]; infer_instance)
      (by
        change t.IsGE (((P.tStructure t).truncGE b).obj X).obj b
        rw [← P.tStructure_isGE_iff]; infer_instance)
      (by change t.IsLE ((t.truncLE a).obj X.obj) a; infer_instance)
      (by change t.IsGE ((t.truncGE b).obj X.obj) b; infer_instance)
    obtain ⟨h₁, h₃⟩ := hQ X.obj X.property hX a
    have h₃' := (hQ X.obj X.property hX b).2
    exact ⟨Q.prop_of_iso (Triangle.π₁.mapIso e).symm h₁,
      Q.prop_of_iso (Triangle.π₃.mapIso e).symm h₃'⟩
  exact ⟨(key n (n + 1) rfl).1, (key (n - 1) n (by omega)).2⟩

end General

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

open Supported

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Truncation

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

/-- A property `R` of the objects of an abelian category `A`, closed under isomorphisms and
containing the zero objects, is inherited by the cohomology of the truncations: if every
`H^i(K)` satisfies `R`, so does every `H^i(τ^{≤ n} K)` and every `H^i(τ^{≥ n} K)`.  (In the
retained degrees the cohomology is that of `K`, in the others it is zero.) -/
theorem forall_homology_truncLE_truncGE (R : ObjectProperty A)
    (hiso : ∀ {M N : A}, (M ≅ N) → R M → R N) (hzero : ∀ M : A, IsZero M → R M)
    (K : DerivedCategory A) (hK : ∀ i, R ((DerivedCategory.homologyFunctor A i).obj K))
    (n : ℤ) :
    (∀ i, R ((DerivedCategory.homologyFunctor A i).obj
        ((DerivedCategory.TStructure.t.truncLE n).obj K))) ∧
      ∀ i, R ((DerivedCategory.homologyFunctor A i).obj
        ((DerivedCategory.TStructure.t.truncGE n).obj K)) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · by_cases hi : i < n + 1
    · exact hiso ((DerivedCategory.truncLTCompHomologyFunctorIso (n + 1) i hi).app K).symm (hK i)
    · exact hzero _ (DerivedCategory.isZero_of_isLE
        ((DerivedCategory.TStructure.t.truncLE n).obj K) n i (by omega))
  · by_cases hi : n ≤ i
    · exact hiso ((DerivedCategory.truncGECompHomologyFunctorIso n i hi).app K) (hK i)
    · exact hzero _ (DerivedCategory.isZero_of_isGE
        ((DerivedCategory.TStructure.t.truncGE n).obj K) n i (by omega))

end Truncation

variable (X : AlgebraicSpaces B S hS)

/-- A zero `𝒪_X`-module is quasi-coherent (from the zero object of the triangulated subcategory
`D_qc(X)`). -/
theorem isQuasicoherentOnSite_of_isZero [(qcohDerived X).IsTriangulated]
    {M : Modules.{u, u} B S hS X.1 X.2} (hM : IsZero M) : M.IsQuasicoherentOnSite := by
  obtain ⟨Z, hZ, hZq⟩ := ObjectProperty.ContainsZero.exists_zero (P := qcohDerived X)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((DerivedCategory.homologyFunctor _ 0).map_isZero hZ).iso hM) (hZq 0)

/-- A zero `𝒪_X`-module is supported on every `T` (from the zero object of the triangulated
subcategory `D_T(𝒪_X)`). -/
theorem supportOfSheaf_subset_of_isZero (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    {M : Modules.{u, u} B S hS X.1 X.2} (hM : IsZero M) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ⊆ T := by
  obtain ⟨Z, hZ, hZs⟩ :=
    ObjectProperty.ContainsZero.exists_zero (P := CohomologySupportedOn B S hS X.1 X.2 T)
  let φ := (SheafOfModules.toSheaf _).mapIso
    (((DerivedCategory.homologyFunctor _ 0).map_isZero hZ).iso hM)
  have : Mono φ.inv := ⟨fun g k w => by simpa using congrArg (· ≫ φ.hom) w⟩
  exact (@supportOfSheaf_subset_of_mono B S hS X.1 X.2 _ _ φ.inv this).trans (hZs 0)

/-- Support on `T`, for a module, is invariant under isomorphism. -/
theorem supportOfSheaf_subset_of_iso (T : Set (points B S hS X.1))
    {M N : Modules.{u, u} B S hS X.1 X.2} (e : M ≅ N)
    (hM : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ⊆ T) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj N) ⊆ T := by
  let φ := (SheafOfModules.toSheaf _).mapIso e
  have : Mono φ.inv := ⟨fun g k w => by simpa using congrArg (· ≫ φ.hom) w⟩
  exact (@supportOfSheaf_subset_of_mono B S hS X.1 X.2 _ _ φ.inv this).trans hM

/-- `D_qc(X)` is stable under the canonical truncations of `D(𝒪_X)`. -/
instance hasInducedTStructure_qcohDerived [(qcohDerived X).IsTriangulated] :
    (qcohDerived X).HasInducedTStructure
      (DerivedCategory.TStructure.t (C := Modules.{u, u} B S hS X.1 X.2)) :=
  .mk' fun K hK n =>
    forall_homology_truncLE_truncGE _ (fun e h => SheafOfModules.IsQuasicoherentOnSite.of_iso e h)
      (fun _ h => isQuasicoherentOnSite_of_isZero X h) K hK n

/-- **The standard `t`-structure on `D_qc(X)`**, induced by the canonical `t`-structure of
`D(𝒪_X)`. -/
abbrev standardTStructureQc [(qcohDerived X).IsTriangulated] :
    TStructure (QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :=
  (qcohDerived X).tStructure DerivedCategory.TStructure.t

/-- `D_{qc,T}(X)` is stable under the truncations of the standard `t`-structure of `D_qc(X)`. -/
instance hasInducedTStructure_qcSupportedOn [(qcohDerived X).IsTriangulated]
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)] :
    (qcSupportedOn X T).HasInducedTStructure (standardTStructureQc X) :=
  hasInducedTStructure_inverseImage _ (qcohDerived X) (CohomologySupportedOn B S hS X.1 X.2 T)
    fun K _ hK n =>
      forall_homology_truncLE_truncGE
        (fun M : Modules.{u, u} B S hS X.1 X.2 =>
          supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ⊆ T)
        (fun e h => supportOfSheaf_subset_of_iso X T e h)
        (fun _ h => supportOfSheaf_subset_of_isZero X T h) K hK n

/-- **The standard `t`-structure on `D_{qc,T}(X)`** (LP26, remark before Definition 5.3):
`(D^{≤ 0}_{qc,T}(X), D^{≥ 0}_{qc,T}(X))`, induced by the canonical `t`-structure of `D(𝒪_X)`
through `D_qc(X)`. -/
abbrev standardTStructure [(qcohDerived X).IsTriangulated] (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)] :
    TStructure (DqcZ X T) :=
  (qcSupportedOn X T).tStructure (standardTStructureQc X)

/-- `E ∈ D^{≤ n}_{qc,T}(X)` iff `H^j(E) = 0` for all `j > n`, in `D(𝒪_X)`. -/
theorem standardTStructure_isLE_iff [(qcohDerived X).IsTriangulated]
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (E : DqcZ X T) (n : ℤ) :
    (standardTStructure X T).IsLE E n ↔ E.obj.obj.IsLE n := by
  rw [ObjectProperty.tStructure_isLE_iff, ObjectProperty.tStructure_isLE_iff]

/-- `E ∈ D^{≥ n}_{qc,T}(X)` iff `H^j(E) = 0` for all `j < n`, in `D(𝒪_X)`. -/
theorem standardTStructure_isGE_iff [(qcohDerived X).IsTriangulated]
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (E : DqcZ X T) (n : ℤ) :
    (standardTStructure X T).IsGE E n ↔ E.obj.obj.IsGE n := by
  rw [ObjectProperty.tStructure_isGE_iff, ObjectProperty.tStructure_isGE_iff]

/-- `D^{≤ n}_{qc,T}(X)` in terms of cohomology sheaves: `E ∈ D^{≤ n}_{qc,T}(X)` iff
`H^j(E) = 0` for all `j > n`. -/
theorem standardTStructure_le_iff [(qcohDerived X).IsTriangulated]
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (E : DqcZ X T) (n : ℤ) :
    (standardTStructure X T).le n E ↔
      ∀ j : ℤ, n < j → IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) j).obj E.obj.obj) := by
  rw [TStructure.le_iff_isLE, standardTStructure_isLE_iff, DerivedCategory.isLE_iff]

/-- `D^{≥ n}_{qc,T}(X)` in terms of cohomology sheaves: `E ∈ D^{≥ n}_{qc,T}(X)` iff
`H^j(E) = 0` for all `j < n`. -/
theorem standardTStructure_ge_iff [(qcohDerived X).IsTriangulated]
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (E : DqcZ X T) (n : ℤ) :
    (standardTStructure X T).ge n E ↔
      ∀ j : ℤ, j < n → IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) j).obj E.obj.obj) := by
  rw [TStructure.ge_iff_isGE, standardTStructure_isGE_iff, DerivedCategory.isGE_iff]

end RelativeFM.Spaces.LP26
