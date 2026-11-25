/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.SchemeNeemanTransport
import FourierMukai.Scheme.AffineNeemanEndpointM3
import FourierMukai.Scheme.Inputs
import WeakApprox.PaperGeneratorM2
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
import Mathlib.Topology.Sets.Closeds

/-!
# The scheme statement of Neeman's weak approximability

This file states Neeman, *Bounded t-structures on the category of perfect
complexes*, Acta Math. 233 (2024), Theorem 3.2(iv), in the repository's
all-sheaves model.  The category is `Dqc X`: the full subcategory of
`Derived X` on complexes all of whose cohomology sheaves are quasicoherent.
Its t-structure is induced by the canonical t-structure on `Derived X`, not by
an arbitrary transported t-structure.  Compactness is `IsCompactAb` in this
full subcategory.

The generator condition is Neeman's zero-detection condition
`IsPaperGenerator`, through `PaperWeakApproximationData`.  It is deliberately
**not** `IsGenerator`: `GeneratorCounterexampleM5.lean` proves that the latter
fails for the regular module over the integers.  The legacy template
`Neeman_3_2_iv C = SatisfiesWA C` therefore is not the definition used here.

For a closed `Z`, cohomological support means that every cohomology sheaf
restricts to zero on the open complement `Z.compl`.  Open restriction preserves
finite limits and colimits, so this condition is a Serre class.  Consequently
the supported category is triangulated and inherits the standard t-structure.
-/

@[expose] public section

namespace RelativeFM.SchemeWeakApproxStatementM1

open RelativeWeakApprox
open RelativeWeakApprox.PaperM2
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry
open scoped AlgebraicGeometry ZeroObject

universe v u w
noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-! ## Standard truncations preserve cohomological inverse images -/

/-- In degrees at most `n`, the standard `≤ n` truncation map is an
isomorphism on cohomology.  This is the long-exact-sequence argument, stated
for every abelian category. -/
lemma isIso_homology_truncLEι_general
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app X)) := by
  let t : TStructure (DerivedCategory C) := DerivedCategory.TStructure.t
  let T := (t.triangleLEGE n (n + 1) (by omega)).obj X
  have hT : T ∈ distTriang (DerivedCategory C) :=
    t.triangleLEGE_distinguished n (n + 1) (by omega) X
  have hz (k : ℤ) (hk : k < n + 1) :
      IsZero ((DerivedCategory.homologyFunctor C k).obj
        ((t.truncGE (n + 1)).obj X)) :=
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

/-- In degrees greater than `n`, the standard `≥ n+1` truncation map is an
isomorphism on cohomology. -/
lemma isIso_homology_truncGEπ_general
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) (n i : ℤ) (hi : n < i) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGEπ (n + 1)).app X)) := by
  let t : TStructure (DerivedCategory C) := DerivedCategory.TStructure.t
  let T := (t.triangleLEGE n (n + 1) (by omega)).obj X
  have hT : T ∈ distTriang (DerivedCategory C) :=
    t.triangleLEGE_distinguished n (n + 1) (by omega) X
  have hz (k : ℤ) (hk : n < k) :
      IsZero ((DerivedCategory.homologyFunctor C k).obj
        ((t.truncLE n).obj X)) :=
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

/-- The lower standard truncation preserves any cohomological inverse image
whose defining cohomology property contains a zero object. -/
lemma cohomologyWithin_truncLE
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (X : DerivedCategory C) (hX : cohomologyWithin P X) (n : ℤ) :
    cohomologyWithin P ((DerivedCategory.TStructure.t.truncLE n).obj X) := by
  intro i
  by_cases hi : n < i
  · exact P.prop_of_isZero (DerivedCategory.isZero_of_isLE _ n i hi)
  · have hi' : i ≤ n := by omega
    let _ := isIso_homology_truncLEι_general X n i hi'
    exact P.prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor C i).map
        ((DerivedCategory.TStructure.t.truncLEι n).app X))).symm (hX i)

/-- The upper standard truncation preserves any cohomological inverse image
whose defining cohomology property contains a zero object. -/
lemma cohomologyWithin_truncGE
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (X : DerivedCategory C) (hX : cohomologyWithin P X) (n : ℤ) :
    cohomologyWithin P ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj X) := by
  intro i
  by_cases hi : n < i
  · let _ := isIso_homology_truncGEπ_general X n i hi
    exact P.prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor C i).map
        ((DerivedCategory.TStructure.t.truncGEπ (n + 1)).app X))) (hX i)
  · exact P.prop_of_isZero
      (DerivedCategory.isZero_of_isGE _ (n + 1) i (by omega))

/-- A triangulated cohomological inverse image inherits the canonical
t-structure whenever the defining property contains zero. -/
noncomputable def cohomologyWithin_hasInducedStandardTStructure
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    [(cohomologyWithin P).IsTriangulated] :
    (cohomologyWithin P).HasInducedTStructure DerivedCategory.TStructure.t := by
  apply ObjectProperty.HasInducedTStructure.mk'
  intro X hX n
  constructor
  · exact cohomologyWithin_truncLE P X hX n
  · change cohomologyWithin P ((DerivedCategory.TStructure.t.truncGE n).obj X)
    simpa using cohomologyWithin_truncGE P X hX (n - 1)

/-! ## The restricted standard t-structure on `D_qc(X)` -/

/-- Quasicoherent cohomology is stable under standard truncation, so `Dqc X`
inherits the canonical t-structure on `Derived X`. -/
noncomputable instance isDQCoh_hasInducedStandardTStructure (X : Scheme.{u}) :
    (IsDQCoh X).HasInducedTStructure DerivedCategory.TStructure.t := by
  letI : (cohomologyWithin (quasiCoherent X)).IsTriangulated :=
    SchemeNeemanAffineM5.isDQCohTriangulated01IE X
  exact cohomologyWithin_hasInducedStandardTStructure (quasiCoherent X)

/-- The restricted standard t-structure on the repository's model of
`D_qc(X)`. -/
noncomputable def dqcStandardTStructure (X : Scheme.{u}) : TStructure (Dqc X) :=
  (IsDQCoh X).tStructure DerivedCategory.TStructure.t

@[simp] lemma dqcStandardTStructure_le (X : Scheme.{u})
    (E : Dqc X) (n : ℤ) :
    (dqcStandardTStructure X).le n E = DerivedCategory.TStructure.t.le n E.obj := rfl

@[simp] lemma dqcStandardTStructure_ge (X : Scheme.{u})
    (E : Dqc X) (n : ℤ) :
    (dqcStandardTStructure X).ge n E = DerivedCategory.TStructure.t.ge n E.obj := rfl

/-- Paper-strength weak approximation data on `Dqc X`, restricted to data
whose t-structure is exactly the restricted standard t-structure. -/
def DqcStandardPaperWeakApproximationData (X : Scheme.{u}) : Type (u + 1) :=
  { W : PaperWeakApproximationData (Dqc X) // W.t = dqcStandardTStructure X }

/-- The unsupported scheme-level predicate in Neeman's Theorem 3.2(iv).
This uses zero detection, and compactness is in `Dqc X`, not in `Derived X`. -/
def NeemanWeakApproximability (X : Scheme.{u}) : Prop :=
  Nonempty (DqcStandardPaperWeakApproximationData X)

/-- The bundled data project to ordinary paper-strength weak approximability. -/
theorem satisfiesPaperWA_of_neemanWeakApproximability {X : Scheme.{u}}
    (h : NeemanWeakApproximability X) : SatisfiesPaperWA (Dqc X) := by
  obtain ⟨⟨W, hW⟩⟩ := h
  exact ⟨W⟩

/-! ## Transport and object-property invariance -/

section TransportPaperData

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type w} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Bundle the coproduct-free transport theorem as paper weak approximation
Data.  No global coproduct existence is required on either category. -/
noncomputable def transportPaperWeakApproximationData (F : C ⥤ D)
    [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (W : PaperWeakApproximationData C) : PaperWeakApproximationData D := by
  let h := SchemeNeemanTransportM5.exists_paper_weakApproximation_of_equivalence
    F W.G W.t W.A W.A_pos W.G_compact W.G_paperGenerates W.G_mem_le
    W.hom_vanishing W.exists_triangle
  exact
    { G := F.obj W.G
      t := transportTStructure F W.t
      A := h.choose
      A_pos := h.choose_spec.1
      G_compact := h.choose_spec.2.1
      G_paperGenerates := h.choose_spec.2.2.1
      G_mem_le := h.choose_spec.2.2.2.1
      hom_vanishing := h.choose_spec.2.2.2.2.1
      exists_triangle := h.choose_spec.2.2.2.2.2 }

@[simp] lemma transportPaperWeakApproximationData_G (F : C ⥤ D)
    [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (W : PaperWeakApproximationData C) :
    (transportPaperWeakApproximationData F W).G = F.obj W.G := rfl

@[simp] lemma transportPaperWeakApproximationData_t (F : C ⥤ D)
    [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (W : PaperWeakApproximationData C) :
    (transportPaperWeakApproximationData F W).t = transportTStructure F W.t := rfl

end TransportPaperData

/-- Paper weak approximation with the induced t-structure depends only on the
object property, not on the presentation of its two equality proofs. -/
theorem standardPaperWeakApproximationData_congr
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : TStructure C) {P Q : ObjectProperty C}
    [P.IsTriangulated] [Q.IsTriangulated]
    [P.HasInducedTStructure t] [Q.HasInducedTStructure t] (h : P = Q) :
    Nonempty { W : PaperWeakApproximationData P.FullSubcategory //
      W.t = P.tStructure t } ↔
    Nonempty { W : PaperWeakApproximationData Q.FullSubcategory //
      W.t = Q.tStructure t } := by
  subst Q
  rfl

/-! ## Affine compatibility of transported and restricted standard t-structures -/

/-- On an affine `Dqc` object, module cohomology of the inverse comparison is
zero exactly when the corresponding sheaf cohomology is zero.  The proof uses
the counit's cohomology isomorphism, exactness of `tilde`, and full faithfulness
of `tilde` to reflect zero objects. -/
lemma isZero_affine_inverse_homology_iff (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) (Y : Dqc (Spec A)) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((affineRingDqcEquivalence A I).inverse.obj Y)) ↔
    IsZero (cohomologySheaf Y.obj n) := by
  letI := I.tildeExact
  let M : DerivedCategory (ModuleCat.{u} A) := I.RΓ.obj Y.obj
  change IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj M) ↔ _
  let eTilde :
      (DerivedCategory.homologyFunctor (Spec A).Modules n).obj
        ((affineDerivedTilde A).obj M) ≅
      (tilde.functor A).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj M) :=
    mapDerivedCategoryHomologyIso (tilde.functor A) M n
  letI : IsIso ((DerivedCategory.homologyFunctor (Spec A).Modules n).map
      (I.adjunction.counit.app Y.obj)) :=
    I.counit_cohomology Y.obj Y.property n
  let eCounit :
      (DerivedCategory.homologyFunctor (Spec A).Modules n).obj
        ((affineDerivedTilde A).obj M) ≅ cohomologySheaf Y.obj n :=
    asIso ((DerivedCategory.homologyFunctor (Spec A).Modules n).map
      (I.adjunction.counit.app Y.obj))
  constructor
  · intro h
    have h₁ : IsZero ((DerivedCategory.homologyFunctor (Spec A).Modules n).obj
        ((affineDerivedTilde A).obj M)) :=
      IsZero.of_iso ((tilde.functor A).map_isZero h) eTilde
    exact IsZero.of_iso h₁ eCounit.symm
  · intro h
    apply IsZero.of_full_of_faithful_of_isZero (tilde.functor A)
    have h₁ : IsZero ((DerivedCategory.homologyFunctor (Spec A).Modules n).obj
        ((affineDerivedTilde A).obj M)) := IsZero.of_iso h eCounit
    exact IsZero.of_iso h₁ eTilde.symm

/-- The ring-standard t-structure transported by the affine comparison is the
restricted standard t-structure on the all-sheaves `Dqc` model. -/
theorem transportedStandardTStructure_eq_dqcStandard (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) :
    SchemeNeemanAffineM5.transportedStandardTStructure A I =
      dqcStandardTStructure (Spec A) := by
  let eInv : (affineRingDqcEquivalence A I).functor.inv ≅
      (affineRingDqcEquivalence A I).inverse :=
    Iso.isoInverseOfIsoFunctor
      (G := (affineRingDqcEquivalence A I).functor.asEquivalence)
      (G' := affineRingDqcEquivalence A I) (Iso.refl _)
  apply RelativeWeakApprox.TStructure.ext_le_zero
  ext Y
  unfold SchemeNeemanAffineM5.transportedStandardTStructure dqcStandardTStructure
  rw [transportTStructure_le]
  change (AffineD.standardTStructure A).le 0
      ((affineRingDqcEquivalence A I).functor.inv.obj Y) ↔
    DerivedCategory.TStructure.t.le 0 Y.obj
  rw [TStructure.le_iff_isLE, TStructure.le_iff_isLE]
  change DerivedCategory.IsLE ((affineRingDqcEquivalence A I).functor.inv.obj Y) 0 ↔
    DerivedCategory.IsLE Y.obj 0
  rw [DerivedCategory.isLE_iff, DerivedCategory.isLE_iff]
  have hzero (i : ℤ) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((affineRingDqcEquivalence A I).functor.inv.obj Y)) ↔
      IsZero (cohomologySheaf Y.obj i) :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (eInv.app Y)).isZero_iff.trans (isZero_affine_inverse_homology_iff A I Y i)
  constructor
  · intro h i hi
    exact (hzero i).mp (h i hi)
  · intro h i hi
    exact (hzero i).mpr (h i hi)

/-- The regular-module affine package with its t-structure normalized to the
restricted standard t-structure.  Its arguments are exactly those of the
landed large-Hom affine and comparison packages. -/
noncomputable def regularModuleDqcStandardPaperData (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A)
    (hAc : IsCompactAb (ringObject A)) :
    PaperWeakApproximationData (Dqc (Spec A)) := by
  let W := transportPaperWeakApproximationData
    (affineRingDqcEquivalence A I).functor
    (AffineNeemanEndpointM3.regularModulePaperData A hAc)
  exact
    { G := W.G
      t := dqcStandardTStructure (Spec A)
      A := W.A
      A_pos := W.A_pos
      G_compact := W.G_compact
      G_paperGenerates := W.G_paperGenerates
      G_mem_le := by
        rw [← transportedStandardTStructure_eq_dqcStandard A I]
        exact W.G_mem_le
      hom_vanishing := by
        intro Y hY f
        have hY' := hY
        rw [← transportedStandardTStructure_eq_dqcStandard A I] at hY'
        exact W.hom_vanishing hY' f
      exists_triangle := by
        intro Y hY
        have hY' := hY
        rw [← transportedStandardTStructure_eq_dqcStandard A I] at hY'
        obtain ⟨E, D, f, g, h, hT, hE, hD⟩ := W.exists_triangle Y hY'
        refine ⟨E, D, f, g, h, hT, hE, ?_⟩
        rw [← transportedStandardTStructure_eq_dqcStandard A I]
        exact hD }

@[simp] lemma regularModuleDqcStandardPaperData_t (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) (hAc : IsCompactAb (ringObject A)) :
    (regularModuleDqcStandardPaperData A I hAc).t =
      dqcStandardTStructure (Spec A) := rfl

/-- The affine instance of the scheme-level statement, with no hidden input.
`I` is the existing all-sheaves comparison and `hAc` is large-Hom compactness
of the regular module; this is not asserted to be a ring-alone theorem. -/
theorem regularModule_neemanWeakApproximability (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A)
    (hAc : IsCompactAb (ringObject A)) :
    NeemanWeakApproximability (Spec A) :=
  ⟨⟨regularModuleDqcStandardPaperData A I hAc, rfl⟩⟩

/-! ## Cohomological support on a closed subset -/

/-- Sheaves supported on `Z`: their restriction to the open complement is
zero.  This is the kernel of open restriction. -/
abbrev SheafSupportedOn (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) :
    ObjectProperty X.Modules :=
  Functor.kernel (Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι (X := X) Z.compl))

/-- Objects of the repository's `D_qc,Z(X)` model: quasicoherent cohomology
sheaves, each supported on `Z`. -/
def IsDQCohSupported (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) :
    ObjectProperty (Derived X) :=
  IsDQCoh X ⊓ cohomologyWithin (SheafSupportedOn X Z)

/-- The full subcategory `D_qc,Z(X)` in the all-sheaves model. -/
abbrev DqcSupported (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) : Type (u + 1) :=
  (IsDQCohSupported X Z).FullSubcategory

/-- Membership unfolds to quasicoherence of every cohomology sheaf and
vanishing of all their restrictions to the complement. -/
theorem isDQCohSupported_iff {X : Scheme.{u}} {Z : TopologicalSpace.Closeds X}
    {E : Derived X} : IsDQCohSupported X Z E ↔
      IsDQCoh X E ∧ ∀ n : ℤ,
        IsZero ((Scheme.Modules.restrictFunctor
          (AlgebraicGeometry.Scheme.Opens.ι (X := X) Z.compl)).obj
            (cohomologySheaf E n)) :=
  Iff.rfl

/-- The empty open subscheme has empty underlying type. -/
lemma isEmpty_bot_scheme (X : Scheme.{u}) : IsEmpty (⊥ : X.Opens).toScheme := by
  change IsEmpty (⊥ : X.Opens)
  exact ⟨fun x => by simpa using x.property⟩

/-- Every sheaf of modules on the empty open subscheme is zero.  This follows
from the sheaf condition on the empty cover. -/
lemma isZero_module_on_bot (X : Scheme.{u})
    (M : (⊥ : X.Opens).toScheme.Modules) : IsZero M := by
  letI : IsEmpty (⊥ : X.Opens).toScheme := isEmpty_bot_scheme X
  rw [IsZero.iff_id_eq_zero]
  apply Scheme.Modules.hom_ext
  intro V
  have hV : V = ⊥ := by
    apply bot_unique
    intro x hx
    exact isEmptyElim x
  let F : TopCat.Sheaf AddCommGrpCat (⊥ : X.Opens).toScheme :=
    ⟨M.presheaf, M.isSheaf⟩
  have ht : IsTerminal (M.presheaf.obj (.op V)) := F.isTerminalOfEqEmpty hV
  have hz : IsZero (M.presheaf.obj (.op V)) := ht.isZero
  exact hz.eq_of_src _ _

/-- Restriction of any module to the empty open is zero. -/
lemma isZero_restrict_to_bot (X : Scheme.{u}) (M : X.Modules) :
    IsZero ((Scheme.Modules.restrictFunctor (⊥ : X.Opens).ι).obj M) :=
  isZero_module_on_bot X _

/-- The supported cohomological category is triangulated.  The quasicoherent
part uses the repository's proved 01IE extension theorem; the supported part
is the kernel of an exact open-restriction functor. -/
noncomputable instance isDQCohSupported_isTriangulated
    (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) :
    (IsDQCohSupported X Z).IsTriangulated := by
  letI : (IsDQCoh X).IsTriangulated :=
    SchemeNeemanAffineM5.isDQCohTriangulated01IE X
  unfold IsDQCohSupported
  infer_instance

/-- The supported category inherits the restricted standard t-structure. -/
noncomputable instance isDQCohSupported_hasInducedStandardTStructure
    (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) :
    (IsDQCohSupported X Z).HasInducedTStructure DerivedCategory.TStructure.t := by
  letI : (cohomologyWithin (SheafSupportedOn X Z)).HasInducedTStructure
      DerivedCategory.TStructure.t :=
    cohomologyWithin_hasInducedStandardTStructure (SheafSupportedOn X Z)
  unfold IsDQCohSupported
  infer_instance

/-- The restricted standard t-structure on `D_qc,Z(X)`. -/
noncomputable def dqcSupportedStandardTStructure
    (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) :
    TStructure (DqcSupported X Z) :=
  (IsDQCohSupported X Z).tStructure DerivedCategory.TStructure.t

@[simp] lemma dqcSupportedStandardTStructure_le
    (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X)
    (E : DqcSupported X Z) (n : ℤ) :
    (dqcSupportedStandardTStructure X Z).le n E =
      DerivedCategory.TStructure.t.le n E.obj := rfl

@[simp] lemma dqcSupportedStandardTStructure_ge
    (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X)
    (E : DqcSupported X Z) (n : ℤ) :
    (dqcSupportedStandardTStructure X Z).ge n E =
      DerivedCategory.TStructure.t.ge n E.obj := rfl

/-- Cohomological support on all of `X` is no condition: restriction to the
empty complementary open always vanishes. -/
theorem isDQCohSupported_top (X : Scheme.{u}) :
    IsDQCohSupported X ⊤ = IsDQCoh X := by
  ext E
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, fun n => ?_⟩
    change IsZero ((Scheme.Modules.restrictFunctor
      (AlgebraicGeometry.Scheme.Opens.ι (X := X) (⊤ : TopologicalSpace.Closeds X).compl)).obj
        (cohomologySheaf E n))
    rw [show (⊤ : TopologicalSpace.Closeds X).compl = (⊥ : X.Opens) by
      ext x
      simp]
    exact isZero_restrict_to_bot X (cohomologySheaf E n)

/-- Supported paper-strength weak approximation data with the restricted
standard t-structure. -/
def DqcSupportedStandardPaperWeakApproximationData
    (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) : Type (u + 1) :=
  { W : PaperWeakApproximationData (DqcSupported X Z) //
      W.t = dqcSupportedStandardTStructure X Z }

/-- The supported scheme predicate in Neeman's Theorem 3.2(iv).  In the
theorem, `X` is qcqs and `Z.compl` is quasi-compact; those are hypotheses on
the proof, not extra inputs hidden in this definition. -/
def NeemanSupportedWeakApproximability
    (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) : Prop :=
  Nonempty (DqcSupportedStandardPaperWeakApproximationData X Z)

/-- Supported data project to ordinary paper-strength weak approximability of
the supported category. -/
theorem satisfiesPaperWA_of_neemanSupportedWeakApproximability
    {X : Scheme.{u}} {Z : TopologicalSpace.Closeds X}
    (h : NeemanSupportedWeakApproximability X Z) :
    SatisfiesPaperWA (DqcSupported X Z) := by
  obtain ⟨⟨W, hW⟩⟩ := h
  exact ⟨W⟩

/-- The supported predicate at `Z = X` is exactly the unsupported predicate. -/
theorem neemanSupportedWeakApproximability_top (X : Scheme.{u}) :
    NeemanSupportedWeakApproximability X ⊤ ↔ NeemanWeakApproximability X := by
  unfold NeemanSupportedWeakApproximability NeemanWeakApproximability
    DqcSupportedStandardPaperWeakApproximationData
    DqcStandardPaperWeakApproximationData dqcSupportedStandardTStructure
    dqcStandardTStructure DqcSupported Dqc
  exact standardPaperWeakApproximationData_congr DerivedCategory.TStructure.t
    (isDQCohSupported_top X)

/-! ## Comparison with the legacy proposition template -/

/-- The legacy `Inputs.Neeman_3_2_iv` uses the strictly stronger
`WeakApproximationData`; hence it implies the corrected paper formulation.
There is no converse: zero detection does not imply `IsGenerator`. -/
theorem satisfiesPaperWA_of_legacy_neeman_3_2_iv
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (h : RelativeFM.Neeman_3_2_iv C) : SatisfiesPaperWA C :=
  satisfiesPaperWA_of_satisfiesWA h

end
end RelativeFM.SchemeWeakApproxStatementM1

#print axioms RelativeFM.SchemeWeakApproxStatementM1.cohomologyWithin_hasInducedStandardTStructure
#print axioms RelativeFM.SchemeWeakApproxStatementM1.isDQCoh_hasInducedStandardTStructure
#print axioms RelativeFM.SchemeWeakApproxStatementM1.transportPaperWeakApproximationData
#print axioms RelativeFM.SchemeWeakApproxStatementM1.standardPaperWeakApproximationData_congr
#print axioms RelativeFM.SchemeWeakApproxStatementM1.isZero_affine_inverse_homology_iff
#print axioms RelativeFM.SchemeWeakApproxStatementM1.transportedStandardTStructure_eq_dqcStandard
#print axioms RelativeFM.SchemeWeakApproxStatementM1.regularModuleDqcStandardPaperData
#print axioms RelativeFM.SchemeWeakApproxStatementM1.regularModule_neemanWeakApproximability
#print axioms RelativeFM.SchemeWeakApproxStatementM1.isDQCohSupported_isTriangulated
#print axioms RelativeFM.SchemeWeakApproxStatementM1.isZero_module_on_bot
#print axioms RelativeFM.SchemeWeakApproxStatementM1.isDQCohSupported_top
#print axioms RelativeFM.SchemeWeakApproxStatementM1.neemanSupportedWeakApproximability_top
#print axioms RelativeFM.SchemeWeakApproxStatementM1.isDQCohSupported_hasInducedStandardTStructure
#print axioms RelativeFM.SchemeWeakApproxStatementM1.satisfiesPaperWA_of_legacy_neeman_3_2_iv
