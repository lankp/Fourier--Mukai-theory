/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Supported.CompactGeneration

/-!
# The standard `t`-structure on `D_{qc,Z}(X)`

GL26 **Lemma A.9** (`lem:preferred_eq_class`) speaks of "the standard `t`-structure" of
`D_{qc,Z}(X)`, for an algebraic space `X` and a closed `Z ⊆ |X|`.  This file constructs it:
it is the `t`-structure induced (Mathlib's `ObjectProperty.tStructure`) by the canonical
`t`-structure `DerivedCategory.TStructure.t` of `D(𝒪_X)` on `D_qc(X)`, and then on
`D_{qc,Z}(X)` (`stdT X Z`).  Its aisles and coaisles are read in `D(𝒪_X)`
(`stdT_isLE_iff`, `stdT_isGE_iff`): `E ∈ D_{qc,Z}(X)^{≤ n}` iff `Hⁱ(E) = 0` for `i > n`.

The content is that truncation preserves `D_qc(X)` and `D_{qc,Z}(X)`: both are defined by a
condition on every cohomology sheaf (quasi-coherence, Stacks 071X; support in `Z`, Stacks 08GF),
and the cohomology sheaves of a truncation are those of the object or zero
(`homologyProp_obj₁_of_triangle`, `homologyProp_obj₃_of_triangle`, from the long exact
cohomology sequence).

## Assumptions

None beyond those of `Spaces/Supported/CompactGeneration.lean`: `D_qc(X)` and `D_Z(X)` are
triangulated subcategories (instance arguments, from `Spaces.Tag06UQInput` and
`SupportTriangulatedInput`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Supported

universe u

/-! ### Cohomology of truncations -/

section Generic

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

open DerivedCategory

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` with `X₁ ∈ D^{≤ n}` and
`X₃ ∈ D^{≥ n+1}`, the first map induces isomorphisms on `Hⁱ` for `i ≤ n`. -/
lemma isIso_homologyMap_mor₁ (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
    (n : ℤ) [T.obj₃.IsGE (n + 1)] (i : ℤ) (hi : i ≤ n) :
    IsIso ((homologyFunctor A i).map T.mor₁) := by
  have hmono : Mono ((homologyFunctor A i).map T.mor₁) := by
    rw [HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)]
    exact (isZero_of_isGE T.obj₃ (n + 1) (i - 1) (by omega)).eq_of_src _ _
  have hepi : Epi ((homologyFunctor A i).map T.mor₁) := by
    rw [HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    exact (isZero_of_isGE T.obj₃ (n + 1) i (by omega)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` with `X₁ ∈ D^{≤ n}` and
`X₃ ∈ D^{≥ n+1}`, the second map induces isomorphisms on `Hⁱ` for `i ≥ n + 1`. -/
lemma isIso_homologyMap_mor₂ (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
    (n : ℤ) [T.obj₁.IsLE n] (i : ℤ) (hi : n + 1 ≤ i) :
    IsIso ((homologyFunctor A i).map T.mor₂) := by
  have hmono : Mono ((homologyFunctor A i).map T.mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff T hT i]
    exact (isZero_of_isLE T.obj₁ n i (by omega)).eq_of_src _ _
  have hepi : Epi ((homologyFunctor A i).map T.mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) (by omega)]
    exact (isZero_of_isLE T.obj₁ n (i + 1) (by omega)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

variable (Q : ObjectProperty A) [Q.IsClosedUnderIsomorphisms]

/-- If every cohomology object of `X₂` satisfies `Q` (a property closed under isomorphisms and
holding for the zero objects as soon as it holds for some object), so does every cohomology object
of the truncation `X₁` in a triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` with `X₁ ∈ D^{≤ n}`,
`X₃ ∈ D^{≥ n+1}`. -/
lemma homologyProp_obj₁_of_triangle (hQ0 : ∀ Z M : A, IsZero Z → Q M → Q Z)
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _) (n : ℤ)
    [T.obj₁.IsLE n] [T.obj₃.IsGE (n + 1)]
    (h : ∀ i : ℤ, Q ((homologyFunctor A i).obj T.obj₂)) (i : ℤ) :
    Q ((homologyFunctor A i).obj T.obj₁) := by
  by_cases hi : i ≤ n
  · have := isIso_homologyMap_mor₁ T hT n i hi
    exact Q.prop_of_iso (asIso ((homologyFunctor A i).map T.mor₁)).symm (h i)
  · exact hQ0 _ _ (isZero_of_isLE T.obj₁ n i (by omega)) (h i)

/-- The same for the third object `X₃` of such a triangle. -/
lemma homologyProp_obj₃_of_triangle (hQ0 : ∀ Z M : A, IsZero Z → Q M → Q Z)
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _) (n : ℤ)
    [T.obj₁.IsLE n] [T.obj₃.IsGE (n + 1)]
    (h : ∀ i : ℤ, Q ((homologyFunctor A i).obj T.obj₂)) (i : ℤ) :
    Q ((homologyFunctor A i).obj T.obj₃) := by
  by_cases hi : n + 1 ≤ i
  · have := isIso_homologyMap_mor₂ T hT n i hi
    exact Q.prop_of_iso (asIso ((homologyFunctor A i).map T.mor₂)) (h i)
  · exact hQ0 _ _ (isZero_of_isGE T.obj₃ (n + 1) i (by omega)) (h i)

end Generic

/-! ### The induced `t`-structures -/

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The condition "support in `T`" on one `𝒪_X`-module (the condition of Stacks 08GF on one
cohomology sheaf). -/
abbrev supportIn (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) :
    ObjectProperty (Modules.{u, u} B S hS X.1 X.2) := fun M =>
  supportOfSheaf B S hS X.1
    ((SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj M)
    ⊆ T

instance (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) :
    (supportIn X T).IsClosedUnderIsomorphisms where
  of_iso e h := by
    let φ := (SheafOfModules.toSheaf _).mapIso e
    have : Mono φ.inv := ⟨fun g k w => by simpa using congrArg (· ≫ φ.hom) w⟩
    exact (@supportOfSheaf_subset_of_mono B S hS X.1 X.2 _ _ φ.inv this).trans h

lemma supportIn_of_isZero (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1))
    (Z M : Modules.{u, u} B S hS X.1 X.2) (hZ : IsZero Z) (hM : supportIn X T M) :
    supportIn X T Z := by
  let F := SheafOfModules.toSheaf
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  have hZ' : IsZero (F.obj Z) := F.map_isZero hZ
  have : Mono (hZ'.to_ (F.obj M)) := ⟨fun g k _ => hZ'.eq_of_tgt g k⟩
  exact (@supportOfSheaf_subset_of_mono B S hS X.1 X.2 _ _ (hZ'.to_ (F.obj M)) this).trans hM

/-- Quasi-coherence of the zero module, from the zero object of the triangulated subcategory
`D_qc(X)`. -/
lemma qcoh_of_isZero (X : AlgebraicSpaces B S hS) [(qcohDerived X).IsTriangulated]
    (Z : Modules.{u, u} B S hS X.1 X.2) (hZ : IsZero Z) :
    SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) Z := by
  obtain ⟨Z₀, hZ₀, hZ₀q⟩ := (qcohDerived X).exists_prop_of_containsZero
  have h0 := hZ₀q 0
  exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_of_iso
    (hZ.iso (((DerivedCategory.homologyFunctor _ 0).map_isZero hZ₀))).symm h0

instance hasInducedTStructure_qcohDerived (X : AlgebraicSpaces B S hS)
    [(qcohDerived X).IsTriangulated] :
    (qcohDerived X).HasInducedTStructure DerivedCategory.TStructure.t :=
  .mk' fun E hE n => by
    have hQ0 : ∀ Z M : Modules.{u, u} B S hS X.1 X.2, IsZero Z →
        SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) M →
        SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) Z :=
      fun Z _ hZ _ => qcoh_of_isZero X Z hZ
    let t := DerivedCategory.TStructure.t (C := Modules.{u, u} B S hS X.1 X.2)
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hT := t.triangleLEGE_distinguished n (n + 1) rfl E
      have : ((t.triangleLEGE n (n + 1) rfl).obj E).obj₁.IsLE n := t.isLE_truncLE_obj E n n
      have : ((t.triangleLEGE n (n + 1) rfl).obj E).obj₃.IsGE (n + 1) :=
        inferInstanceAs (t.IsGE ((t.truncGE (n + 1)).obj E) (n + 1))
      exact homologyProp_obj₁_of_triangle _ hQ0 _ hT n hE i
    · have hT := t.triangleLEGE_distinguished (n - 1) n (by omega) E
      have : ((t.triangleLEGE (n - 1) n (by omega)).obj E).obj₁.IsLE (n - 1) :=
        t.isLE_truncLE_obj E (n - 1) (n - 1)
      have : ((t.triangleLEGE (n - 1) n (by omega)).obj E).obj₃.IsGE (n - 1 + 1) :=
        t.isGE_of_ge ((t.truncGE n).obj E) (n - 1 + 1) n (by omega)
      exact homologyProp_obj₃_of_triangle _ hQ0 _ hT (n - 1) hE i

/-- **The standard `t`-structure on `D_qc(X)`**, induced by the canonical `t`-structure of
`D(𝒪_X)`. -/
abbrev stdQc (X : AlgebraicSpaces B S hS) [(qcohDerived X).IsTriangulated] :
    TStructure (QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :=
  (qcohDerived X).tStructure DerivedCategory.TStructure.t

instance hasInducedTStructure_qcSupportedOn (X : AlgebraicSpaces B S hS)
    [(qcohDerived X).IsTriangulated] (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)] :
    (qcSupportedOn X T).HasInducedTStructure (stdQc X) :=
  .mk' fun E hE n => by
    let ι := (qcohDerived X).ι
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hT := ι.map_distinguished _ ((stdQc X).triangleLEGE_distinguished n (n + 1) rfl E)
      have : (ι.mapTriangle.obj ((stdQc X).triangleLEGE n (n + 1) rfl |>.obj E)).obj₁.IsLE n :=
        ((qcohDerived X).tStructure_isLE_iff _ _ _).1 ((stdQc X).isLE_truncLE_obj E n n)
      have : (ι.mapTriangle.obj ((stdQc X).triangleLEGE n (n + 1) rfl |>.obj E)).obj₃.IsGE
          (n + 1) :=
        ((qcohDerived X).tStructure_isGE_iff _ _ _).1
          (inferInstanceAs ((stdQc X).IsGE (((stdQc X).truncGE (n + 1)).obj E) (n + 1)))
      exact homologyProp_obj₁_of_triangle (supportIn X T) (supportIn_of_isZero X T) _ hT n hE i
    · have hT := ι.map_distinguished _
        ((stdQc X).triangleLEGE_distinguished (n - 1) n (by omega) E)
      have : (ι.mapTriangle.obj ((stdQc X).triangleLEGE (n - 1) n (by omega) |>.obj E)).obj₁.IsLE
          (n - 1) :=
        ((qcohDerived X).tStructure_isLE_iff _ _ _).1 ((stdQc X).isLE_truncLE_obj E (n - 1) (n - 1))
      have : (ι.mapTriangle.obj ((stdQc X).triangleLEGE (n - 1) n (by omega) |>.obj E)).obj₃.IsGE
          (n - 1 + 1) :=
        ((qcohDerived X).tStructure_isGE_iff _ _ _).1
          ((stdQc X).isGE_of_ge (((stdQc X).truncGE n).obj E) (n - 1 + 1) n (by omega))
      exact homologyProp_obj₃_of_triangle (supportIn X T) (supportIn_of_isZero X T) _ hT (n - 1)
        hE i

/-- **The standard `t`-structure on `D_{qc,T}(X)`** (GL26 §2.2, `sec:preliminaries_stacks`;
the `t`-structure of GL26 Lemma A.9, `lem:preferred_eq_class`): induced by the canonical
`t`-structure of `D(𝒪_X)`. -/
abbrev stdT (X : AlgebraicSpaces B S hS) [(qcohDerived X).IsTriangulated]
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)] :
    TStructure (DqcZ X T) :=
  (qcSupportedOn X T).tStructure (stdQc X)

variable (X : AlgebraicSpaces B S hS) [(qcohDerived X).IsTriangulated]
  (T : Set (points B S hS X.1))
  [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]

/-- The aisles of `stdT X T`, read in `D(𝒪_X)`. -/
lemma stdT_isLE_iff (E : DqcZ X T) (n : ℤ) :
    (stdT X T).IsLE E n ↔ ((ιZ X T).obj E).IsLE n := by
  rw [ObjectProperty.tStructure_isLE_iff, ObjectProperty.tStructure_isLE_iff]
  exact Iff.rfl

/-- The coaisles of `stdT X T`, read in `D(𝒪_X)`. -/
lemma stdT_isGE_iff (E : DqcZ X T) (n : ℤ) :
    (stdT X T).IsGE E n ↔ ((ιZ X T).obj E).IsGE n := by
  rw [ObjectProperty.tStructure_isGE_iff, ObjectProperty.tStructure_isGE_iff]
  exact Iff.rfl

end RelativeFM.Spaces.Supported
