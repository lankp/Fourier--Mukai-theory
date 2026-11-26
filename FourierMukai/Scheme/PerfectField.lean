/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.PerfectRing
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Perfect complexes over a field

The classification `Perf k = Dbcoh k` for a field `k`: perfect complexes are
exactly the complexes with bounded, degreewise finite-dimensional cohomology.

* `singleFinPowerZero_mem_perf`, `singleFiniteZero_mem_perf`,
  `singleFinite_mem_perf`: a finite-dimensional vector space concentrated in one
  degree is perfect.
* `perf_of_bounded_finite_cohomology_aux`: the truncation induction.  The
  top cohomology of a bounded complex with finite-dimensional cohomology is a
  finite single module; representing it by a finite complex and using the long
  exact cohomology sequence reduces the degree, so the complex is built from
  finitely many finite pieces.
* `dbcoh_le_perf` and `perf_eq_dbcoh`: hence `Dbcoh k ≤ Perf k`, and equality with
  the forward inclusion `perf_le_dbcoh` from `PerfectRing.lean`.
* The compact-object classification `compact_iff_dbcoh` (compact ⇔ bounded
  finite-dimensional cohomology, formerly `compact_iff_dbcoh_of_input`) is in
  `Scheme/Neeman32Inputs.lean`, with no input (moved there on
  `wave5/neeman-prune`, when the interface `CompactPerfectInput` it used to take
  was deleted).

Found by a member of the Ultramath run `smwv1bkrk` (direction AF3).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open RelativeWeakApprox
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- A finite direct power of the regular module, placed in degree zero, is
perfect.  Proved by induction using `Perf.perf_biprod`; no compactness input is
used. -/
theorem singleFinPowerZero_mem_perf (k : Type u) [Field k] (n : ℕ) :
    Perf k ((DerivedCategory.singleFunctor (ModuleCat k) 0).obj
      (ModuleCat.of k (Fin n → k))) := by
  induction n with
  | zero =>
      apply (Perf k).prop_of_isZero
      exact (DerivedCategory.singleFunctor (ModuleCat k) 0).map_isZero
        (ModuleCat.isZero_of_subsingleton _)
  | succ n ih =>
      let R := ModuleCat.of k k
      let P := ModuleCat.of k (Fin n → k)
      let e₁ : ModuleCat.of k (Fin n.succ → k) ≅ ModuleCat.of k (k × (Fin n → k)) :=
        (Fin.consLinearEquiv k (fun _ : Fin n.succ => k)).toModuleIso.symm
      let e₂ : ModuleCat.of k (k × (Fin n → k)) ≅ R ⊞ P :=
        (ModuleCat.biprodIsoProd R P).symm
      let e := (DerivedCategory.singleFunctor (ModuleCat k) 0).mapIso (e₁ ≪≫ e₂) ≪≫
        (DerivedCategory.singleFunctor (ModuleCat k) 0).mapBiprod R P
      apply (Perf k).prop_of_iso e.symm
      exact perf_biprod k (ringObject_mem_perf k) ih


/-- A finite-dimensional vector space in degree zero is perfect.  This is the
heart-generation step in the field case of Stacks Tag 09M1. -/
theorem singleFiniteZero_mem_perf (k : Type u) [Field k] (M : ModuleCat k)
    [Module.Finite k M] :
    Perf k ((DerivedCategory.singleFunctor (ModuleCat k) 0).obj M) := by
  let e : M ≅ ModuleCat.of k (Fin (Module.finrank k M) → k) :=
    (Module.finBasis k M).equivFun.toModuleIso
  exact (Perf k).prop_of_iso
    ((DerivedCategory.singleFunctor (ModuleCat k) 0).mapIso e).symm
    (singleFinPowerZero_mem_perf k (Module.finrank k M))

/-- A finite-dimensional vector space placed in any integer degree is perfect.
The shift compatibility is the canonical one for
`DerivedCategory.singleFunctors`. -/
theorem singleFinite_mem_perf (k : Type u) [Field k] (M : ModuleCat k)
    [Module.Finite k M] (n : ℤ) :
    Perf k ((DerivedCategory.singleFunctor (ModuleCat k) n).obj M) := by
  let e := ((DerivedCategory.singleFunctors (ModuleCat k)).shiftIso
    (-n) n 0 (by simp)).app M
  exact (Perf k).prop_of_iso e (perf_shift k (singleFiniteZero_mem_perf k M) (-n))


/-- Truncation induction with explicit bounds.  The lower truncation has
finite cohomology by exactness: below the cut its cohomology injects into that
of `X`, and above the cut it vanishes.  The top truncation is a single module,
which is finite by epimorphism exactness. -/
theorem perf_of_bounded_finite_cohomology_aux (k : Type u) [Field k]
    (a b : ℤ) (n : ℕ) (hn : b = a - 1 + (n : ℤ))
    (X : DerivedCategory (ModuleCat k))
    (hge : X.IsGE a) (hle : X.IsLE b)
    (hfin : ∀ i, Module.Finite k ((DerivedCategory.homologyFunctor (ModuleCat k) i).obj X)) :
    Perf k X := by
  induction n generalizing b X with
  | zero =>
      let _ : X.IsGE a := hge
      let _ : X.IsLE b := hle
      have hb : b = a - 1 := by simpa using hn
      subst b
      have _ : X.IsLE (a - 1) := by simpa using hle
      have hzL := DerivedCategory.TStructure.t.isZero_truncLE_obj_of_isGE
        (a - 1) a (by lia) X
      have hzX : IsZero X := hzL.of_iso
        (asIso ((DerivedCategory.TStructure.t.truncLEι (a - 1)).app X)).symm
      exact (Perf k).prop_of_isZero hzX
  | succ n ih =>
      let _ : X.IsGE a := hge
      let _ : X.IsLE b := hle
      have hb : b = a + (n : ℤ) := by
        push_cast at hn
        lia
      let T := (DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (by lia)).obj X
      have hT : T ∈ distTriang _ :=
        DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (by lia) X
      have hgeL : T.obj₁.IsGE a := by
        change DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj X) a
        infer_instance
      have hleL : T.obj₁.IsLE (b - 1) := by
        change DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj X) (b - 1)
        infer_instance
      have hgeY : T.obj₃.IsGE b := by
        change DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.TStructure.t.truncGE b).obj X) b
        infer_instance
      have hleY : T.obj₃.IsLE b := by
        change DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.TStructure.t.truncGE b).obj X) b
        infer_instance
      have hfinL : ∀ i, Module.Finite k
          ((DerivedCategory.homologyFunctor (ModuleCat k) i).obj T.obj₁) := by
        intro i
        by_cases hi : i < b
        · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat k) (i - 1)).obj T.obj₃) := by
            let _ : T.obj₃.IsGE b := hgeY
            exact DerivedCategory.isZero_of_isGE T.obj₃ b (i - 1) (by lia)
          have hδ : DerivedCategory.HomologySequence.δ T (i - 1) i (by lia) = 0 :=
            hz.eq_of_src _ _
          have _ : Mono ((DerivedCategory.homologyFunctor (ModuleCat k) i).map T.mor₁) :=
            (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
              T hT (i - 1) i (by lia)).2 hδ
          let _ : Module.Finite k
              ((DerivedCategory.homologyFunctor (ModuleCat k) i).obj T.obj₂) := hfin i
          exact Module.Finite.of_injective
            ((DerivedCategory.homologyFunctor (ModuleCat k) i).map T.mor₁).hom
            ((ModuleCat.mono_iff_injective
              ((DerivedCategory.homologyFunctor (ModuleCat k) i).map T.mor₁)).1 inferInstance)
        · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat k) i).obj T.obj₁) := by
            let _ : T.obj₁.IsLE (b - 1) := hleL
            exact DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) i (by lia)
          exact (FiniteModules k).prop_of_isZero hz
      have hperfL : Perf k T.obj₁ :=
        ih (b - 1) (by lia) T.obj₁ hgeL hleL hfinL
      let _ : T.obj₃.IsGE b := hgeY
      let _ : T.obj₃.IsLE b := hleY
      obtain ⟨M, ⟨e⟩⟩ :=
        DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ b
      have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat k) (b + 1)).obj T.obj₁) := by
        let _ : T.obj₁.IsLE (b - 1) := hleL
        exact DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) (b + 1) (by lia)
      have hδ : DerivedCategory.HomologySequence.δ T b (b + 1) (by lia) = 0 :=
        hz.eq_of_tgt _ _
      have _ : Epi ((DerivedCategory.homologyFunctor (ModuleCat k) b).map T.mor₂) :=
        (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
          T hT b (b + 1) (by lia)).2 hδ
      have hfinY : Module.Finite k
          ((DerivedCategory.homologyFunctor (ModuleCat k) b).obj T.obj₃) := by
        let _ : Module.Finite k
            ((DerivedCategory.homologyFunctor (ModuleCat k) b).obj T.obj₂) := hfin b
        exact Module.Finite.of_surjective
          ((DerivedCategory.homologyFunctor (ModuleCat k) b).map T.mor₂).hom
          ((ModuleCat.epi_iff_surjective
            ((DerivedCategory.homologyFunctor (ModuleCat k) b).map T.mor₂)).1 inferInstance)
      let eM : (DerivedCategory.homologyFunctor (ModuleCat k) b).obj T.obj₃ ≅ M :=
        (DerivedCategory.homologyFunctor (ModuleCat k) b).mapIso e ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat k) b).app M
      let _ : Module.Finite k M := by
        let _ : Module.Finite k
            ((DerivedCategory.homologyFunctor (ModuleCat k) b).obj T.obj₃) := hfinY
        exact Module.Finite.equiv eM.toLinearEquiv
      have hperfY : Perf k T.obj₃ :=
        (Perf k).prop_of_iso e.symm (singleFinite_mem_perf k M b)
      change Perf k T.obj₂
      exact (Perf k).ext_of_isTriangulatedClosed₂ T hT hperfL hperfY


/-- **Field case of the perfect-complex/finite-cohomology comparison.**
Every object with bounded, degreewise finite-dimensional cohomology is perfect.
The proof is entirely formal from the canonical `t`-structure and finite bases. -/
theorem dbcoh_le_perf (k : Type u) [Field k] : Dbcoh k ≤ Perf k := by
  rintro X ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hfin⟩
  let _ : X.IsGE a := ha
  let _ : X.IsLE b := hb
  let b' := max b (a - 1)
  have _ : X.IsLE b' := DerivedCategory.TStructure.t.isLE_of_le X b b' (le_max_left _ _)
  obtain ⟨n, hn⟩ := Int.le.dest (show a - 1 ≤ b' from le_max_right _ _)
  exact perf_of_bounded_finite_cohomology_aux k a b' n hn.symm X ha
    (inferInstance : X.IsLE b') hfin

/-- **Finite-cohomology form of the perfect-complex classification over a
field** (compare Tags 07LT and 09M1).  Perfect complexes are exactly the
objects with bounded, degreewise finite-dimensional cohomology.  The forward
inclusion is the repository's `perf_le_dbcoh`; the reverse is `dbcoh_le_perf`,
proved here without any compactness hypothesis. -/
theorem perf_iff_dbcoh (k : Type u) [Field k]
    (X : DerivedCategory (ModuleCat k)) : Perf k X ↔ Dbcoh k X :=
  ⟨perf_le_dbcoh k X, dbcoh_le_perf k X⟩

/-- Equality of the two object properties over a field; see `perf_iff_dbcoh`. -/
theorem perf_eq_dbcoh (k : Type u) [Field k] : Perf k = Dbcoh k :=
  le_antisymm (perf_le_dbcoh k) (dbcoh_le_perf k)


end RelativeFM
