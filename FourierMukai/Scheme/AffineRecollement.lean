/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.Affine
import FourierMukai.Scheme.Derived
import WeakApprox.Recollement
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The affine recollement

The recollement attached to an open immersion of affines `Spec A[1/f] → Spec A`,
in the orientation in which GL26 (Lemma `lem:spacey_recollement`) and LP
(Proposition `prop:A8`) use it:

  `D(A[1/f])  →  D(A)  →  D_Z(A)`,

where `D_Z(A)` is the full subcategory of complexes whose cohomology modules are
`f`-power torsion.  **The orientation matters.**  The "closed-left/open-right"
reading is not the same recollement: reversing it while identifying `j_!` with
`j_* = Rj_*` would make restriction of scalars left adjoint to extension of
scalars, which already fails for `ℤ → ℤ[1/p]` (it would give
`0 ≅ Hom_ℤ(ℤ[1/p], ℤ) ≅ Hom_{ℤ[1/p]}(ℤ[1/p], ℤ[1/p]) ≅ ℤ[1/p]`).

Proved here: the `f`-power-torsion Serre class (subobjects, quotients,
extensions) and the triangulated supported category; derived extension and
restriction of scalars and their adjunction, built on a degreewise
`Adjunction.mapComplex`; the derived counit isomorphism and full faithfulness of
`Rj_*`; `Lj^* i_* ≅ 0` by power-torsion acyclicity after localization; and
`RΓ_Z Rj_* ≅ 0` from the kernel characterization.

`AffineRecollementInput` is the remaining literature input, limited to `j^×`,
`RΓ_Z` and `i^*` with their exactness, adjunctions and counit condition, the
kernel, the mixed zero composite and the two gluing triangles, each citing
Gao–Psaroudakis 2018 Lemma 2.2(ii), Balmer–Dell'Ambrogio–Sanders 2016
Corollary 2.3 and Krause 2010 §4; no Stacks tag is claimed for the sequence, since
0BFF (Lemma 39.9.7) is about abelian varieties and is not this statement.
`AffineRecollementInput.toRecollement` assembles the exact
`RelativeWeakApprox.Recollement`, with all four adjunctions, all full
faithfulness fields, the kernel condition, the three zero composites and both
distinguished triangles, and identifies `Lj^*`, `Rj_*` and the supported
inclusion definitionally.

Found by a member of the Ultramath run `smwv1bkrk` (direction AF5).
-/

@[expose] public section

namespace RelativeFM

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The standard away-from-`f` localization, written `A[1/f]` in the paper. -/
abbrev Away (A : Type u) [CommRing A] (f : A) : Type u := Localization.Away f

/-- `f`-power-torsion modules, using Mathlib's torsion predicate.  This is the
abelian-category shadow of support in `V(f)`.-/
def PowerTorsion (A : Type u) [CommRing A] (f : A) :
    ObjectProperty (ModuleCat.{u} A) :=
  fun M ↦ Module.IsTorsion' M (Submonoid.powers f)

/-- Elementwise characterization of `f`-power torsion. -/
lemma powerTorsion_iff {A : Type u} [CommRing A] {f : A} {M : ModuleCat.{u} A} :
    PowerTorsion A f M ↔ ∀ x : M, ∃ n : ℕ, f ^ n • x = 0 :=
  Submodule.isTorsion'_powers_iff f

/-- Power-torsion modules contain a zero object. -/
instance powerTorsion_containsZero (A : Type u) [CommRing A] (f : A) :
    (PowerTorsion A f).ContainsZero where
  exists_zero :=
    let Z : ModuleCat.{u} A := ModuleCat.of A PUnit
    ⟨Z, ModuleCat.isZero_of_subsingleton _,
      powerTorsion_iff.mpr fun x ↦ ⟨0, by simpa using Subsingleton.elim x 0⟩⟩

/-- Power-torsion modules are closed under submodules. -/
instance powerTorsion_isClosedUnderSubobjects (A : Type u) [CommRing A] (f : A) :
    (PowerTorsion A f).IsClosedUnderSubobjects where
  prop_of_mono {M N} g _ hN := powerTorsion_iff.mpr fun x ↦ by
    obtain ⟨n, hn⟩ := powerTorsion_iff.mp hN (g x)
    refine ⟨n, (ModuleCat.mono_iff_injective g).mp inferInstance ?_⟩
    simpa using hn

/-- Power-torsion modules are closed under quotients. -/
instance powerTorsion_isClosedUnderQuotients (A : Type u) [CommRing A] (f : A) :
    (PowerTorsion A f).IsClosedUnderQuotients where
  prop_of_epi {M N} g _ hM := powerTorsion_iff.mpr fun y ↦ by
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective g).mp inferInstance y
    obtain ⟨n, hn⟩ := powerTorsion_iff.mp hM x
    exact ⟨n, by simpa using congrArg g hn⟩

/-- Power-torsion modules are closed under extensions.  The proof uses only
exactness in the middle and the two torsion hypotheses; Noetherianness is not
needed. -/
instance powerTorsion_isClosedUnderExtensions (A : Type u) [CommRing A] (f : A) :
    (PowerTorsion A f).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := powerTorsion_iff.mpr fun x ↦ by
    obtain ⟨n, hn⟩ := powerTorsion_iff.mp h₃ (S.g x)
    have hg : S.g (f ^ n • x) = 0 := by simpa using hn
    obtain ⟨y, hy⟩ := (S.moduleCat_exact_iff).mp hS.exact _ hg
    obtain ⟨m, hm⟩ := powerTorsion_iff.mp h₁ y
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_smul, ← hy, ← map_smul, hm, map_zero]

/-- The Serre class of `f`-power-torsion modules. -/
instance powerTorsion_isSerreClass (A : Type u) [CommRing A] (f : A) :
    (PowerTorsion A f).IsSerreClass where

/-- The object condition defining `D_Z(A)`, namely power torsion in every
cohomology degree (GL26, Lemma `lem:spacey_recollement`). -/
def AffineIsSupported (A : Type u) [CommRing A] (f : A) :
    ObjectProperty (AffineD A) :=
  cohomologyWithin (PowerTorsion A f)

/-- The full subcategory of `D(A)` supported on `V(f)`. -/
abbrev AffineDZ (A : Type u) [CommRing A] (f : A) : Type (u + 1) :=
  (AffineIsSupported A f).FullSubcategory

/-- The natural fully faithful inclusion of the supported derived category. -/
abbrev affineDZι (A : Type u) [CommRing A] (f : A) : AffineDZ A f ⥤ AffineD A :=
  (AffineIsSupported A f).ι

/-- The supported derived category is triangulated, proved from the Serre-class
argument above and the long exact cohomology sequence. -/
instance affineIsSupported_isTriangulated (A : Type u) [CommRing A] (f : A) :
    (AffineIsSupported A f).IsTriangulated := by
  unfold AffineIsSupported
  infer_instance

/-- Derived extension of scalars along `A → A[1/f]`.  Since a localization is
flat, this is computed degreewise and needs no resolutions (Stacks Tag 06Z0). -/
noncomputable def derivedExtensionScalars (A : Type u) [CommRing A] (f : A) :
    AffineD A ⥤ AffineD (Away A f) := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (ModuleCat.extendScalars (algebraMap A (Away A f))).mapDerivedCategory

/-- Derived restriction of scalars `Rj_* : D(A[1/f]) → D(A)`.  Restriction is
exact on the nose, so this is also computed degreewise. -/
noncomputable def derivedRestrictionScalars (A : Type u) [CommRing A] (f : A) :
    AffineD (Away A f) ⥤ AffineD A :=
  (ModuleCat.restrictScalars.{u} (algebraMap A (Away A f))).mapDerivedCategory

/-- Compatibility of derived extension of scalars with cochain complexes. -/
noncomputable abbrev derivedExtensionScalarsFactors (A : Type u) [CommRing A] (f : A) :
    DerivedCategory.Q ⋙ derivedExtensionScalars A f ≅
      (ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (ModuleCat.extendScalars (algebraMap A (Away A f))).mapDerivedCategoryFactors

/-- Compatibility of derived restriction of scalars with cochain complexes. -/
noncomputable abbrev derivedRestrictionScalarsFactors (A : Type u) [CommRing A] (f : A) :
    DerivedCategory.Q ⋙ derivedRestrictionScalars A f ≅
      (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapDerivedCategoryFactors


universe vC uC vD uD

/-- An adjunction between additive functors induces an adjunction degreewise on
homological complexes. -/
noncomputable def Adjunction.mapComplex
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    {E : C ⥤ D} {R : D ⥤ C} [E.Additive] [R.Additive]
    (adj : E ⊣ R) {ι : Type*} (c : ComplexShape ι) :
    E.mapHomologicalComplex c ⊣ R.mapHomologicalComplex c :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app K := {
        f := fun i ↦ adj.unit.app (K.X i)
        comm' := by
          intros i j hij
          exact (adj.unit.naturality (K.d i j)).symm }
      naturality := by
        intros K L φ
        ext i
        exact adj.unit.naturality (φ.f i) }
    counit := {
      app K := {
        f := fun i ↦ adj.counit.app (K.X i)
        comm' := by
          intros i j hij
          exact (adj.counit.naturality (K.d i j)).symm }
      naturality := by
        intros K L φ
        ext i
        exact adj.counit.naturality (φ.f i) }
    left_triangle := by
      ext K i
      simp
      exact adj.left_triangle_components (K.X i)
    right_triangle := by
      ext K i
      simp
      exact adj.right_triangle_components (K.X i) }

/-- The derived adjunction `Lj^* ⊣ Rj_*`.  Both exact functors descend to the
derived categories, so Mathlib's localization-of-adjunctions theorem applies;
this uses no Brown representability hypothesis. -/
noncomputable def derivedExtensionRestrictionAdjunction (A : Type u) [CommRing A] (f : A) :
    derivedExtensionScalars A f ⊣ derivedRestrictionScalars A f := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : CatCommSq ((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q (derivedExtensionScalars A f) :=
    ⟨(derivedExtensionScalarsFactors A f).symm⟩
  letI : CatCommSq ((ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q (derivedRestrictionScalars A f) :=
    ⟨(derivedRestrictionScalarsFactors A f).symm⟩
  exact (Adjunction.mapComplex (ModuleCat.extendRestrictScalarsAdj
    (algebraMap A (Away A f))) (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} (Away A f)) (ComplexShape.up ℤ))
    (derivedExtensionScalars A f) (derivedRestrictionScalars A f)


/-- A map between modules over a localization is automatically linear over the
localization.  Thus restriction of scalars is full; faithfulness is already in
Mathlib. -/
noncomputable def restrictionScalarsFull (A : Type u) [CommRing A] (f : A) :
    (ModuleCat.restrictScalars.{u} (algebraMap A (Away A f))).Full where
  map_surjective {M N} g := by
    letI : IsScalarTower A (Away A f)
        ((ModuleCat.restrictScalars (algebraMap A (Away A f))).obj M) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : IsScalarTower A (Away A f)
        ((ModuleCat.restrictScalars (algebraMap A (Away A f))).obj N) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    refine ⟨ModuleCat.ofHom
      (g.hom.extendScalarsOfIsLocalization (Submonoid.powers f) (Away A f)), ?_⟩
    ext x
    rfl

/-- The underived counit `A[1/f] ⊗[A] M → M` is an isomorphism for every
`A[1/f]`-module `M`, because `Rj_*` is fully faithful. -/
noncomputable instance underivedExtensionRestrictionCounitIsIso
    (A : Type u) [CommRing A] (f : A) :
    IsIso (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A (Away A f))).counit := by
  exact @Adjunction.counit_isIso_of_R_fully_faithful _ _ _ _ _ _ _
    (restrictionScalarsFull A f) inferInstance

/-- The counit of the derived open adjunction is an isomorphism.  On complexes
this follows by applying the underived componentwise counit; essential
surjectivity of the quotient by quasi-isomorphisms extends it to the whole
derived category. -/
noncomputable instance derivedExtensionRestrictionCounitIsIso
    (A : Type u) [CommRing A] (f : A) :
    IsIso (derivedExtensionRestrictionAdjunction A f).counit := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : CatCommSq ((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q (derivedExtensionScalars A f) :=
    ⟨(derivedExtensionScalarsFactors A f).symm⟩
  letI : CatCommSq ((ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q (derivedRestrictionScalars A f) :=
    ⟨(derivedRestrictionScalarsFactors A f).symm⟩
  have hcomplex (K : CochainComplex (ModuleCat.{u} (Away A f)) ℤ) :
      IsIso ((Adjunction.mapComplex (ModuleCat.extendRestrictScalarsAdj
        (algebraMap A (Away A f))) (ComplexShape.up ℤ)).counit.app K) := by
    letI : ∀ n, IsIso (((Adjunction.mapComplex (ModuleCat.extendRestrictScalarsAdj
        (algebraMap A (Away A f))) (ComplexShape.up ℤ)).counit.app K).f n) := by
      intro n
      change IsIso ((ModuleCat.extendRestrictScalarsAdj
        (algebraMap A (Away A f))).counit.app (K.X n))
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  have hQ (K : CochainComplex (ModuleCat.{u} (Away A f)) ℤ) :
      IsIso ((derivedExtensionRestrictionAdjunction A f).counit.app
        (DerivedCategory.Q.obj K)) := by
    letI := hcomplex K
    change IsIso (((Adjunction.mapComplex (ModuleCat.extendRestrictScalarsAdj
      (algebraMap A (Away A f))) (ComplexShape.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      DerivedCategory.Q
        (HomologicalComplex.quasiIso (ModuleCat.{u} (Away A f)) (ComplexShape.up ℤ))
      (derivedExtensionScalars A f) (derivedRestrictionScalars A f)).counit.app
        (DerivedCategory.Q.obj K))
    rw [Adjunction.localization_counit_app]
    infer_instance
  have hall : ∀ X, IsIso ((derivedExtensionRestrictionAdjunction A f).counit.app X) := by
    intro X
    rw [← NatTrans.isIso_app_iff_of_iso _
      (DerivedCategory.Q.objObjPreimageIso X)]
    exact hQ _
  exact NatIso.isIso_of_isIso_app _

/-- Derived restriction of scalars `Rj_*` is fully faithful, proved from the
derived counit rather than assumed. -/
noncomputable def derivedRestrictionScalarsFullyFaithful (A : Type u) [CommRing A] (f : A) :
    (derivedRestrictionScalars A f).FullyFaithful :=
  (derivedExtensionRestrictionAdjunction A f).fullyFaithfulROfIsIsoCounit

/-- Fullness of `Rj_*` in the form required by `WeakApprox.Recollement`. -/
noncomputable instance derivedRestrictionScalarsFull (A : Type u) [CommRing A] (f : A) :
    (derivedRestrictionScalars A f).Full :=
  (derivedRestrictionScalarsFullyFaithful A f).full

/-- Faithfulness of `Rj_*` in the form required by `WeakApprox.Recollement`. -/
noncomputable instance derivedRestrictionScalarsFaithful (A : Type u) [CommRing A] (f : A) :
    (derivedRestrictionScalars A f).Faithful :=
  (derivedRestrictionScalarsFullyFaithful A f).faithful



/-- Derived extension of scalars commutes with shifts (proved degreewise). -/
noncomputable instance derivedExtensionScalars_commShift (A : Type u) [CommRing A] (f : A) :
    (derivedExtensionScalars A f).CommShift ℤ := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  change (ModuleCat.extendScalars (algebraMap A (Away A f))).mapDerivedCategory.CommShift ℤ
  infer_instance

/-- Derived extension of scalars is triangulated (Stacks Tag 06Z0). -/
noncomputable instance derivedExtensionScalars_exact (A : Type u) [CommRing A] (f : A) :
    (derivedExtensionScalars A f).IsTriangulated := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  change (ModuleCat.extendScalars (algebraMap A (Away A f))).mapDerivedCategory.IsTriangulated
  infer_instance

/-- Derived restriction of scalars commutes with shifts. -/
noncomputable instance derivedRestrictionScalars_commShift (A : Type u) [CommRing A] (f : A) :
    (derivedRestrictionScalars A f).CommShift ℤ := by
  change (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapDerivedCategory.CommShift ℤ
  infer_instance

/-- Derived restriction of scalars is triangulated. -/
noncomputable instance derivedRestrictionScalars_exact (A : Type u) [CommRing A] (f : A) :
    (derivedRestrictionScalars A f).IsTriangulated := by
  change (ModuleCat.restrictScalars (algebraMap A (Away A f))).mapDerivedCategory.IsTriangulated
  infer_instance


/-- Extension of scalars to `A[1/f]` kills every `f`-power-torsion module. -/
lemma isZero_extendScalars_of_powerTorsion (A : Type u) [CommRing A] (f : A)
    (M : ModuleCat.{u} A) (hM : PowerTorsion A f M) :
    IsZero ((ModuleCat.extendScalars (algebraMap A (Away A f))).obj M) := by
  letI : Module (Away A f) (TensorProduct A
      ((ModuleCat.restrictScalars (algebraMap A (Away A f))).obj
        (ModuleCat.of (Away A f) (Away A f))) M) :=
    inferInstanceAs (Module (Away A f)
      ((ModuleCat.extendScalars (algebraMap A (Away A f))).obj M))
  letI : IsScalarTower A (Away A f) (TensorProduct A
      ((ModuleCat.restrictScalars (algebraMap A (Away A f))).obj
        (ModuleCat.of (Away A f) (Away A f))) M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hz : ∀ z : TensorProduct A
      ((ModuleCat.restrictScalars (algebraMap A (Away A f))).obj
        (ModuleCat.of (Away A f) (Away A f))) M, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul s m =>
      obtain ⟨n, hn⟩ := powerTorsion_iff.mp hM m
      have hu : IsUnit (algebraMap A (Away A f) (f ^ n)) :=
        IsLocalization.map_units (M := Submonoid.powers f) (Away A f) ⟨f ^ n, ⟨n, rfl⟩⟩
      apply hu.smul_eq_zero.mp
      rw [IsScalarTower.algebraMap_smul (Away A f), TensorProduct.smul_tmul',
        TensorProduct.smul_tmul, hn,
        TensorProduct.tmul_zero]
    | add x y hx hy => simp [hx, hy]
  letI : Subsingleton ((ModuleCat.extendScalars (algebraMap A (Away A f))).obj M) :=
    ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _


/-- Exact extension of scalars makes a complex acyclic in degree `n` whenever
its `n`-th homology is `f`-power torsion. -/
lemma exactAt_map_extendScalars_of_powerTorsion (A : Type u) [CommRing A] (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (hK : PowerTorsion A f (K.homology n)) :
    (((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).ExactAt n := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (isZero_extendScalars_of_powerTorsion A f _ hK).of_iso
    ((K.sc n).mapHomologyIso (ModuleCat.extendScalars (algebraMap A (Away A f))))

/-- Away-from-`f` localization kills a complex all of whose cohomology is
`f`-power torsion.  This is the affine support statement behind
`Lj^* i_* ≅ 0` (GL26, Lemma `lem:spacey_recollement`). -/
lemma isZero_derivedExtensionScalars_of_support (A : Type u) [CommRing A] (f : A)
    {X : AffineD A} (hX : AffineIsSupported A f X) :
    IsZero ((derivedExtensionScalars A f).obj X) := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hQK (n : ℤ) : PowerTorsion A f
      ((DerivedCategory.homologyFunctor _ n).obj (DerivedCategory.Q.obj K)) :=
    (PowerTorsion A f).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e.symm) (hX n)
  have hK (n : ℤ) : PowerTorsion A f (K.homology n) :=
    (PowerTorsion A f).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors _ n).app K) (hQK n)
  have hAcyclic :
      ((ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K |>.Acyclic := fun n ↦
    exactAt_map_extendScalars_of_powerTorsion A f K n (hK n)
  let EK := (ModuleCat.extendScalars (algebraMap A (Away A f))).mapHomologicalComplex
    (ComplexShape.up ℤ) |>.obj K
  letI : (DerivedCategory.Q.obj EK).IsLE 0 :=
    (DerivedCategory.isLE_Q_obj_iff EK 0).mpr (by
      rw [CochainComplex.isLE_iff]
      intro n hn
      exact hAcyclic n)
  letI : (DerivedCategory.Q.obj EK).IsGE 1 :=
    (DerivedCategory.isGE_Q_obj_iff EK 1).mpr (by
      rw [CochainComplex.isGE_iff]
      intro n hn
      exact hAcyclic n)
  have hzero : IsZero (DerivedCategory.Q.obj EK) :=
    DerivedCategory.TStructure.t.isZero _ 0 1 (by omega)
  exact hzero.of_iso ((derivedExtensionScalars A f).mapIso e.symm ≪≫
    (derivedExtensionScalarsFactors A f).app K)

/-- The zero-composite `Lj^* i_* ≅ 0` for the supported inclusion, proved from
cohomology rather than assumed as part of the recollement interface. -/
noncomputable def derivedExtensionScalars_affineDZι_isoZero (A : Type u) [CommRing A] (f : A) :
    affineDZι A f ⋙ derivedExtensionScalars A f ≅ 0 :=
  NatIso.ofComponents
    (fun X ↦ IsZero.iso (isZero_derivedExtensionScalars_of_support A f X.property)
      (Functor.zero_obj X))
    (fun {X _} _ ↦ (isZero_derivedExtensionScalars_of_support A f X.property).eq_of_src _ _)

/-- The affine recollement in the orientation of GL26, Lemma
`lem:spacey_recollement`, and LP, Proposition `prop:A8`. -/
abbrev AffineRecollement (A : Type u) [CommRing A] (f : A) : Type (u + 1) :=
  RelativeWeakApprox.Recollement (AffineD (Away A f)) (AffineD A) (AffineDZ A f)

/-- Remaining input for the affine recollement.  The concrete
`Lj^* = D(extendScalars)`, `Rj_* = D(restrictScalars)`, their adjunction, the
full faithfulness of `Rj_*`, and the supported inclusion are already proved in
this file and therefore are **not** fields.

These fields are the compactly-generated localization/colocalization package
used in the proof of GL26, Lemma `lem:spacey_recollement`: Gao--Psaroudakis
2018, Lemma 2.2(ii), Balmer--Dell'Ambrogio--Sanders 2016, Corollary 2.3, and
Krause 2010, §4.  The kernel and gluing-triangle statements are the usual
Verdier localization sequence.  No field
asserts weak approximability or another later theorem. -/
structure AffineRecollementInput (A : Type u) [CommRing A] (f : A) where
  /-- The exceptional inverse image `j^×`, right adjoint to `Rj_*`;
  existence is supplied by GL26, Lemma `lem:spacey_recollement`. -/
  iShriek : AffineD A ⥤ AffineD (Away A f)
  /-- Shift compatibility of `j^×`. -/
  [iShriek_commShift : iShriek.CommShift ℤ]
  /-- Exactness of `j^×`. -/
  [iShriek_exact : iShriek.IsTriangulated]
  /-- The second open adjunction `Rj_* ⊣ j^×`. -/
  iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek
  /-- The right adjoint `RΓ_Z` of the supported inclusion, supplied by the
  Verdier localization sequence in GL26, Lemma `lem:spacey_recollement`
  (Gao--Psaroudakis 2018, Lemma 2.2(ii)). -/
  jStar : AffineD A ⥤ AffineDZ A f
  /-- Shift compatibility of `RΓ_Z`. -/
  [jStar_commShift : jStar.CommShift ℤ]
  /-- Exactness of `RΓ_Z`. -/
  [jStar_exact : jStar.IsTriangulated]
  /-- The adjunction `i_* ⊣ RΓ_Z`. -/
  jShriekAdj : affineDZι A f ⊣ jStar
  /-- The other supported adjoint, denoted `i^*` in GL26's diagram; its
  existence follows there from Balmer--Dell'Ambrogio--Sanders 2016,
  Corollary 2.3 and Gao--Psaroudakis 2018, Lemma 2.2(ii). -/
  jUpper : AffineDZ A f ⥤ AffineD A
  /-- Shift compatibility of this supported adjoint. -/
  [jUpper_commShift : jUpper.CommShift ℤ]
  /-- Exactness of this supported adjoint. -/
  [jUpper_exact : jUpper.IsTriangulated]
  /-- The adjunction `RΓ_Z ⊣ i^*`. -/
  jStarAdj : jStar ⊣ jUpper
  /-- The counit of `RΓ_Z ⊣ i^*` is an isomorphism; equivalently `i^*` is
  fully faithful. -/
  [jStarAdj_isIso_counit : IsIso jStarAdj.counit]
  /-- The kernel of `RΓ_Z` is exactly the essential image of `Rj_*`, from the
  localization/colocalization sequence (Krause 2010, §4; GL26,
  Lemma `lem:spacey_recollement`). -/
  kernel (X : AffineD A) :
    Nonempty (jStar.obj X ≅ 0) ↔
      ∃ Y : AffineD (Away A f), Nonempty (X ≅ derivedRestrictionScalars A f |>.obj Y)
  /-- The mixed supported/open composite vanishes, from the same Verdier
  localization sequence (Krause 2010, §4; GL26, Lemma `lem:spacey_recollement`). -/
  iShriek_jUpper : jUpper ⋙ iShriek ≅ 0
  /-- First gluing connecting morphism of the localization triangle
  (LP Setup 4.1; GL26, Lemma `lem:spacey_recollement`). -/
  firstConnecting :
    derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f ⟶
      jStar ⋙ affineDZι A f ⋙ shiftFunctor (AffineD A) (1 : ℤ)
  /-- The first distinguished gluing triangle `i_*RΓ_Z(X) → X → Rj_*Lj^*(X)`.
  Its first two maps are definitionally the recollement units/counits. -/
  first_distinguished (X : AffineD A) :
    Triangle.mk (jShriekAdj.counit.app X)
      ((derivedExtensionRestrictionAdjunction A f).unit.app X)
      (firstConnecting.app X) ∈ distTriang (AffineD A)
  /-- Second gluing connecting morphism of the colocalization triangle
  (LP Setup 4.1; GL26, Lemma `lem:spacey_recollement`). -/
  secondConnecting :
    jStar ⋙ jUpper ⟶ iShriek ⋙ derivedRestrictionScalars A f ⋙
      shiftFunctor (AffineD A) (1 : ℤ)
  /-- The second distinguished gluing triangle, with adjunction maps as in LP
  Setup 4.1. -/
  second_distinguished (X : AffineD A) :
    Triangle.mk (iLowerAdj.counit.app X) (jStarAdj.unit.app X)
      (secondConnecting.app X) ∈ distTriang (AffineD A)

attribute [instance] AffineRecollementInput.iShriek_commShift
  AffineRecollementInput.iShriek_exact AffineRecollementInput.jStar_commShift
  AffineRecollementInput.jStar_exact AffineRecollementInput.jUpper_commShift
  AffineRecollementInput.jUpper_exact AffineRecollementInput.jStarAdj_isIso_counit

namespace AffineRecollementInput

variable {A : Type u} [CommRing A] {f : A} (I : AffineRecollementInput A f)

include I

/-- Full faithfulness of the last supported adjoint follows from invertibility
of the counit of `jStarAdj`; it is not an extra hypothesis. -/
noncomputable def jUpperFullyFaithful : I.jUpper.FullyFaithful :=
  I.jStarAdj.fullyFaithfulROfIsIsoCounit

/-- Local cohomology vanishes on `Rj_*`, obtained from the kernel
characterization and hence not an additional recollement hypothesis. -/
noncomputable def jStarRestrictionIsoZero :
    derivedRestrictionScalars A f ⋙ I.jStar ≅ 0 := by
  have hzero (Y : AffineD (Away A f)) : IsZero (I.jStar.obj
      ((derivedRestrictionScalars A f).obj Y)) := by
    have hmem : ∃ Z : AffineD (Away A f),
        Nonempty ((derivedRestrictionScalars A f).obj Y ≅
          (derivedRestrictionScalars A f).obj Z) := ⟨Y, ⟨Iso.refl _⟩⟩
    obtain ⟨e⟩ := (I.kernel _).mpr hmem
    exact (isZero_zero _).of_iso e
  exact NatIso.ofComponents
    (fun Y ↦ IsZero.iso (hzero Y) (Functor.zero_obj Y))
    (fun {X _} _ ↦ (hzero X).eq_of_src _ _)

/-- Assemble the precise `WeakApprox.Recollement` structure.  All four
adjunctions, all full-faithfulness fields, the kernel condition, all three zero
composites, and both natural distinguished triangles are preserved verbatim. -/
noncomputable def toRecollement : AffineRecollement A f where
  iStar := derivedExtensionScalars A f
  iLower := derivedRestrictionScalars A f
  iShriek := I.iShriek
  jShriek := affineDZι A f
  jStar := I.jStar
  jUpper := I.jUpper
  iStarAdj := derivedExtensionRestrictionAdjunction A f
  iLowerAdj := I.iLowerAdj
  jShriekAdj := I.jShriekAdj
  jStarAdj := I.jStarAdj
  iLower_full := derivedRestrictionScalarsFull A f
  iLower_faithful := derivedRestrictionScalarsFaithful A f
  jShriek_full := inferInstance
  jShriek_faithful := inferInstance
  jUpper_full := I.jUpperFullyFaithful.full
  jUpper_faithful := I.jUpperFullyFaithful.faithful
  kernel := I.kernel
  jStar_iLower := I.jStarRestrictionIsoZero
  iShriek_jUpper := I.iShriek_jUpper
  iStar_jShriek := derivedExtensionScalars_affineDZι_isoZero A f
  firstConnecting := I.firstConnecting
  first_distinguished := I.first_distinguished
  secondConnecting := I.secondConnecting
  second_distinguished := I.second_distinguished

/-- The first functor `i^*` is exactly derived extension of scalars. -/
theorem toRecollement_iStar : I.toRecollement.iStar = derivedExtensionScalars A f := rfl

/-- The inclusion `i_*` is exactly derived restriction of scalars. -/
theorem toRecollement_iLower : I.toRecollement.iLower = derivedRestrictionScalars A f := rfl

/-- The supported inclusion `j_!` is exactly the full-subcategory inclusion. -/
theorem toRecollement_jShriek : I.toRecollement.jShriek = affineDZι A f := rfl

end AffineRecollementInput


/-! ## Axiom audit -/


end
end RelativeFM
