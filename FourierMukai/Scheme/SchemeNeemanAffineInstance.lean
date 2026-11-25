import FourierMukai.Scheme.SchemeNeemanTransport
import FourierMukai.Scheme.AffineNeemanEndpointM3
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# Affine weak approximation in the scheme model

This file bundles the transported affine package as
`PaperM2.PaperWeakApproximationData`.  Generation is Neeman's zero-detection
predicate `IsPaperGenerator`, not the stronger `IsGenerator`.

The all-sheaves affine comparison is explicitly parameterized by
`AffineDerivedGammaInput` (Stacks 06Z0, using 079W/08D4/01XB), and the current
large-Hom package is parameterized by compactness of the regular module (the
regular-module case of perfect-to-compact, Stacks 09M8).  No unproved instance
of either input is manufactured here.  In particular, the small-Hom
compactness theorem is not incorrectly used in the large-Hom coproduct-index
universe.
-/

@[expose] public section

namespace RelativeFM.SchemeNeemanAffineInstanceM2

open RelativeFM RelativeWeakApprox
open RelativeFM.SchemeNeemanAffineM5
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry

universe v w uC u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Equality of `t`-structures is detected by their aisle and co-aisle
predicates.  Mathlib 4.33.1 does not export an extensionality theorem for
`TStructure`. -/
lemma tStructure_ext {C : Type uC} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {t₁ t₂ : TStructure C}
    (hle : ∀ n X, t₁.le n X ↔ t₂.le n X)
    (hge : ∀ n X, t₁.ge n X ↔ t₂.ge n X) : t₁ = t₂ := by
  have hle' : t₁.le = t₂.le := by
    funext n X
    exact propext (hle n X)
  have hge' : t₁.ge = t₂.ge := by
    funext n X
    exact propext (hge n X)
  cases t₁
  cases t₂
  simpa only [TStructure.mk.injEq] using And.intro hle' hge'

/-- Predicate-level form of `DerivedCategory.isLE_iff`: the latter uses the
one-field class `TStructure.IsLE`, whereas weak approximation uses `t.le`. -/
lemma derivedCategory_standard_le_iff {C : Type uC} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (X : DerivedCategory C) (n : ℤ) :
    DerivedCategory.TStructure.t.le n X ↔
      ∀ i : ℤ, n < i → IsZero ((DerivedCategory.homologyFunctor C i).obj X) := by
  constructor
  · intro h
    exact (DerivedCategory.isLE_iff X n).mp (show X.IsLE n from ⟨h⟩)
  · intro h
    exact ((DerivedCategory.isLE_iff X n).mpr h).le

/-- Predicate-level form of `DerivedCategory.isGE_iff`. -/
lemma derivedCategory_standard_ge_iff {C : Type uC} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (X : DerivedCategory C) (n : ℤ) :
    DerivedCategory.TStructure.t.ge n X ↔
      ∀ i : ℤ, i < n → IsZero ((DerivedCategory.homologyFunctor C i).obj X) := by
  constructor
  · intro h
    exact (DerivedCategory.isGE_iff X n).mp (show X.IsGE n from ⟨h⟩)
  · intro h
    exact ((DerivedCategory.isGE_iff X n).mpr h).ge

/-- On cohomology in degrees at most `n`, the map from the standard `≤ n`
truncation is an isomorphism. -/
lemma isIso_homology_truncLEι {C : Type uC} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (X : DerivedCategory C) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app X)) := by
  let t : TStructure (DerivedCategory C) := DerivedCategory.TStructure.t
  let T := (t.triangleLEGE n (n + 1) (by omega)).obj X
  have hT : T ∈ distTriang (DerivedCategory C) :=
    t.triangleLEGE_distinguished n (n + 1) (by omega) X
  have hz (k : ℤ) (hk : k < n + 1) :
      IsZero ((DerivedCategory.homologyFunctor C k).obj ((t.truncGE (n + 1)).obj X)) :=
    DerivedCategory.isZero_of_isGE _ (n + 1) k hk
  have hepi : Epi ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app X)) := by
    apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mpr
    exact (hz i (by omega)).eq_of_tgt _ _
  have hmono : Mono ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app X)) := by
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hT (i - 1) i (by omega)).mpr
    exact (hz (i - 1) (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- On cohomology in degrees at least `n + 1`, the map to the standard
`≥ n + 1` truncation is an isomorphism. -/
lemma isIso_homology_truncGEπ {C : Type uC} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (X : DerivedCategory C) (n i : ℤ) (hi : n < i) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGEπ (n + 1)).app X)) := by
  let t : TStructure (DerivedCategory C) := DerivedCategory.TStructure.t
  let T := (t.triangleLEGE n (n + 1) (by omega)).obj X
  have hT : T ∈ distTriang (DerivedCategory C) :=
    t.triangleLEGE_distinguished n (n + 1) (by omega) X
  have hz (k : ℤ) (hk : n < k) :
      IsZero ((DerivedCategory.homologyFunctor C k).obj ((t.truncLE n).obj X)) :=
    DerivedCategory.isZero_of_isLE _ n k hk
  have hepi : Epi ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGEπ (n + 1)).app X)) := by
    apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
      T hT i (i + 1) (by omega)).mpr
    exact (hz (i + 1) (by omega)).eq_of_tgt _ _
  have hmono : Mono ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGEπ (n + 1)).app X)) := by
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i).mpr
    exact (hz i hi).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- The standard `≤ n` truncation preserves quasicoherent cohomology. -/
lemma isDQCoh_truncLE (X : Scheme.{u}) (E : Derived X) (hE : IsDQCoh X E) (n : ℤ) :
    IsDQCoh X ((DerivedCategory.TStructure.t.truncLE n).obj E) := by
  intro i
  by_cases hi : n < i
  · exact (quasiCoherent X).prop_of_isZero
      (DerivedCategory.isZero_of_isLE _ n i hi)
  · let _ := isIso_homology_truncLEι E n i (by omega)
    exact (quasiCoherent X).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor X.Modules i).map
        ((DerivedCategory.TStructure.t.truncLEι n).app E))).symm (hE i)

/-- The standard `≥ n + 1` truncation preserves quasicoherent cohomology. -/
lemma isDQCoh_truncGE (X : Scheme.{u}) (E : Derived X) (hE : IsDQCoh X E) (n : ℤ) :
    IsDQCoh X ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj E) := by
  intro i
  by_cases hi : n < i
  · let _ := isIso_homology_truncGEπ E n i hi
    exact (quasiCoherent X).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor X.Modules i).map
        ((DerivedCategory.TStructure.t.truncGEπ (n + 1)).app E))) (hE i)
  · exact (quasiCoherent X).prop_of_isZero
      (DerivedCategory.isZero_of_isGE _ (n + 1) i (by omega))

/-- `D_qc(X)` inherits the standard `t`-structure from `D(X)`. -/
noncomputable instance isDQCoh_hasInducedStandardTStructure (X : Scheme.{u}) :
    (IsDQCoh X).HasInducedTStructure (DerivedCategory.TStructure.t) := by
  apply ObjectProperty.HasInducedTStructure.mk'
  intro E hE n
  constructor
  · exact isDQCoh_truncLE X E hE n
  · change IsDQCoh X ((DerivedCategory.TStructure.t.truncGE n).obj E)
    simpa using isDQCoh_truncGE X E hE (n - 1)

/-- The restricted standard `t`-structure on the repository's cohomological
model `Dqc X`. -/
noncomputable def restrictedStandardTStructure (X : Scheme.{u}) :
    TStructure (Dqc X) :=
  (IsDQCoh X).tStructure DerivedCategory.TStructure.t

@[simp] lemma restrictedStandardTStructure_le (X : Scheme.{u})
    (E : Dqc X) (n : ℤ) :
    (restrictedStandardTStructure X).le n E = DerivedCategory.TStructure.t.le n E.obj :=
  rfl

@[simp] lemma restrictedStandardTStructure_ge (X : Scheme.{u})
    (E : Dqc X) (n : ℤ) :
    (restrictedStandardTStructure X).ge n E = DerivedCategory.TStructure.t.ge n E.obj :=
  rfl

/-- Cohomology after the forward affine comparison is computed by `tilde`. -/
noncomputable def affineDqc_homologyIso (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) (M : AffineD A) (i : ℤ) :
    cohomologySheaf (((affineRingDqcEquivalence A I).functor.obj M).obj) i ≅
      (tilde.functor A).obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M) := by
  letI := I.tildeExact
  exact mapDerivedCategoryHomologyIso (tilde.functor A) M i

/-- Since `tilde` is fully faithful, it both preserves and reflects zero
objects.  Thus vanishing of cohomology is unchanged by the affine comparison. -/
lemma isZero_affineDqc_homology_iff (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) (M : AffineD A) (i : ℤ) :
    IsZero (cohomologySheaf (((affineRingDqcEquivalence A I).functor.obj M).obj) i) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M) := by
  let e := affineDqc_homologyIso A I M i
  constructor
  · intro h
    apply IsZero.of_full_of_faithful_of_isZero (tilde.functor A)
    exact h.of_iso e.symm
  · intro h
    exact ((tilde.functor A).map_isZero h).of_iso e

/-- On an affine scheme the transported standard `t`-structure is literally
the standard `t`-structure restricted from the derived category of all
sheaves.  The proof uses the exact cohomology comparison and does not merely
assert equivalence of the two `t`-structures. -/
theorem transportedStandardTStructure_eq_restricted (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) :
    transportedStandardTStructure A I = restrictedStandardTStructure (Spec A) := by
  let F := (affineRingDqcEquivalence A I).functor
  apply tStructure_ext
  · intro n Y
    change (AffineD.standardTStructure A).le n (F.inv.obj Y) ↔
      DerivedCategory.TStructure.t.le n Y.obj
    constructor
    · intro h
      apply (derivedCategory_standard_le_iff Y.obj n).mpr
      intro i hi
      have hmod : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (F.inv.obj Y)) :=
        (derivedCategory_standard_le_iff (F.inv.obj Y) n).mp h i (by omega)
      have hforward := (isZero_affineDqc_homology_iff A I (F.inv.obj Y) i).mpr hmod
      exact ((DerivedCategory.homologyFunctor (Spec A).Modules i).mapIso
        ((dqcι (Spec A)).mapIso (F.objObjPreimageIso Y))).isZero_iff.mp hforward
    · intro h
      apply (derivedCategory_standard_le_iff (F.inv.obj Y) n).mpr
      intro i hi
      apply (isZero_affineDqc_homology_iff A I (F.inv.obj Y) i).mp
      have hY : IsZero (cohomologySheaf Y.obj i) :=
        (derivedCategory_standard_le_iff Y.obj n).mp h i (by omega)
      exact ((DerivedCategory.homologyFunctor (Spec A).Modules i).mapIso
        ((dqcι (Spec A)).mapIso (F.objObjPreimageIso Y))).isZero_iff.mpr hY
  · intro n Y
    change (AffineD.standardTStructure A).ge n (F.inv.obj Y) ↔
      DerivedCategory.TStructure.t.ge n Y.obj
    constructor
    · intro h
      apply (derivedCategory_standard_ge_iff Y.obj n).mpr
      intro i hi
      have hmod : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (F.inv.obj Y)) :=
        (derivedCategory_standard_ge_iff (F.inv.obj Y) n).mp h i (by omega)
      have hforward := (isZero_affineDqc_homology_iff A I (F.inv.obj Y) i).mpr hmod
      exact ((DerivedCategory.homologyFunctor (Spec A).Modules i).mapIso
        ((dqcι (Spec A)).mapIso (F.objObjPreimageIso Y))).isZero_iff.mp hforward
    · intro h
      apply (derivedCategory_standard_ge_iff (F.inv.obj Y) n).mpr
      intro i hi
      apply (isZero_affineDqc_homology_iff A I (F.inv.obj Y) i).mp
      have hY : IsZero (cohomologySheaf Y.obj i) :=
        (derivedCategory_standard_ge_iff Y.obj n).mp h i (by omega)
      exact ((DerivedCategory.homologyFunctor (Spec A).Modules i).mapIso
        ((dqcι (Spec A)).mapIso (F.objObjPreimageIso Y))).isZero_iff.mpr hY

/-- Bundle the unbundled transported affine package, retaining its exact
regular generator, transported standard `t`-structure, and bound. -/
noncomputable def paperWeakApproximationDataOfTransport
    (A : CommRingCat.{u}) (I : AffineDerivedGammaInput A)
    (h : RegularModuleDqcWeakApproximation A I) :
    PaperM2.PaperWeakApproximationData (Dqc (Spec A)) := by
  let N : ℤ := Classical.choose h
  have hspec := Classical.choose_spec h
  exact
    { G := (affineRingDqcEquivalence A I).functor.obj (ringObject A)
      t := transportedStandardTStructure A I
      A := N
      A_pos := hspec.1
      G_compact := hspec.2.1
      G_paperGenerates := hspec.2.2.1
      G_mem_le := hspec.2.2.2.1
      hom_vanishing := hspec.2.2.2.2.1
      exists_triangle := hspec.2.2.2.2.2 }

/-- The regular-module package with its `t`-structure normalized to the
restricted standard `t`-structure on all sheaves. -/
noncomputable def regularModuleRestrictedStandardPaperData
    (A : CommRingCat.{u}) (I : AffineDerivedGammaInput A)
    (hAc : IsCompactAb (ringObject A)) :
    PaperM2.PaperWeakApproximationData (Dqc (Spec A)) := by
  let W := paperWeakApproximationDataOfTransport A I
    (regularModule_dqcSpec_weakApproximation A I hAc)
  exact
    { G := W.G
      t := restrictedStandardTStructure (Spec A)
      A := W.A
      A_pos := W.A_pos
      G_compact := W.G_compact
      G_paperGenerates := W.G_paperGenerates
      G_mem_le := by
        rw [← transportedStandardTStructure_eq_restricted A I]
        exact W.G_mem_le
      hom_vanishing := by
        intro Y hY f
        apply W.hom_vanishing ?_ f
        change (transportedStandardTStructure A I).le (-W.A) Y
        rw [transportedStandardTStructure_eq_restricted A I]
        exact hY
      exists_triangle := by
        intro Y hY
        have hY' : (transportedStandardTStructure A I).le 0 Y := by
          rw [transportedStandardTStructure_eq_restricted A I]
          exact hY
        obtain ⟨E, D, f, g, h, hT, hE, hD⟩ := W.exists_triangle Y hY'
        refine ⟨E, D, f, g, h, hT, hE, ?_⟩
        rw [← transportedStandardTStructure_eq_restricted A I]
        exact hD }

@[simp] lemma regularModuleRestrictedStandardPaperData_t
    (A : CommRingCat.{u}) (I : AffineDerivedGammaInput A)
    (hAc : IsCompactAb (ringObject A)) :
    (regularModuleRestrictedStandardPaperData A I hAc).t =
      restrictedStandardTStructure (Spec A) :=
  rfl

/-- The affine unsupported base case in precisely the repository's restricted
standard `t`-structure model. -/
theorem regularModuleRestrictedStandardPackage (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) (hAc : IsCompactAb (ringObject A)) :
    ∃ W : PaperM2.PaperWeakApproximationData (Dqc (Spec A)),
      W.t = restrictedStandardTStructure (Spec A) ∧
      W.G = (affineRingDqcEquivalence A I).functor.obj (ringObject A) := by
  refine ⟨regularModuleRestrictedStandardPaperData A I hAc, rfl, ?_⟩
  rfl

/-- Affine `D_qc(Spec A)` satisfies the zero-detection form of weak
approximability, given precisely the inputs of the landed transport theorem. -/
theorem satisfiesPaperWA_dqcSpec (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) (hAc : IsCompactAb (ringObject A)) :
    PaperM2.SatisfiesPaperWA (Dqc (Spec A)) :=
  ⟨paperWeakApproximationDataOfTransport A I
    (regularModule_dqcSpec_weakApproximation A I hAc)⟩

@[simp] lemma paperWeakApproximationDataOfTransport_t
    (A : CommRingCat.{u}) (I : AffineDerivedGammaInput A)
    (h : RegularModuleDqcWeakApproximation A I) :
    (paperWeakApproximationDataOfTransport A I h).t = transportedStandardTStructure A I :=
  rfl

end

end RelativeFM.SchemeNeemanAffineInstanceM2
