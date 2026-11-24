/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.AffineDictionary
import FourierMukai.Scheme.Derived
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# The two models of `D_qc` for an affine scheme

Stacks 06Z0 identifies complexes of sheaves on `Spec A` with quasicoherent
cohomology with `D(QCoh(Spec A))`, and `AffineDictionary.lean` identifies the
latter with `D(A-Mod)`.  This file *constructs* both comparisons instead of
assuming them as a black-box equivalence.

`AffineDerivedGammaInput A` is the literature input, split into the four facts
with their tags: exactness of affine `tilde` (01HV), unbounded `RΓ` (06Z0), the
derived `tilde ⊣ RΓ` adjunction (079W), and the two cohomology calculations —
unit a quasi-isomorphism everywhere, counit a quasi-isomorphism on complexes
with quasicoherent cohomology (06Z0, via 08D4 and 01XB).  The counit is required
only on `D_qc`, not on all complexes.

From it: `affineRingCohomologyEquivalence A : D(A-Mod) ≌ D_qc(Spec A)`,
`affineQCohCohomologyEquivalence A : D(QCoh(Spec A)) ≌ D_qc(Spec A)`, and
`affineRingDqcEquivalence`; the forward functor is additive, commutes with
shifts, and is triangulated modulo the Serre closure of quasicoherent sheaves.
`quasicoherentCohomology_eq_isDQCoh` identifies the two renderings of `D_qc`.

Supporting results, proved: a general unbounded cohomology comparison for exact
derived functors, additivity of exact derived functors via the localization, and
`preservesFiniteLimits_tilde_of_isClosedUnderSubobjects`, so that subobject
closure of quasicoherent sheaves (AF1) discharges the `tilde` exactness field
through `affineDerivedGammaInputOfSubobjects`.

Found by a member of the Ultramath run `smwv1bkrk` (direction AF2).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe w₁ w₂ v₁ v₂ u₁ u₂ u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-! ## Cohomology of an exact functor on derived categories -/

/-- **Proved.** An exact additive functor commutes with each cohomology
functor, displayed objectwise rather than as a natural isomorphism.

After replacing `X` by `Q.obj K`, all the required comparisons are explicit:
`mapDerivedCategoryFactors`, `homologyFunctorFactors`, and
`ShortComplex.mapHomologyIso`. No boundedness hypothesis is needed. -/
noncomputable def mapDerivedCategoryHomologyIso
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C₁) (n : ℤ) :
    (DerivedCategory.homologyFunctor C₂ n).obj (F.mapDerivedCategory.obj X) ≅
      F.obj ((DerivedCategory.homologyFunctor C₁ n).obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let eK : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  let FK := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let e : F.mapDerivedCategory.obj X ≅ DerivedCategory.Q.obj FK :=
    F.mapDerivedCategory.mapIso eK.symm ≪≫ F.mapDerivedCategoryFactors.app K
  exact (DerivedCategory.homologyFunctor C₂ n).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors C₂ n).app FK ≪≫
    (K.sc n).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C₁ n).app K).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor C₁ n).mapIso eK)

/-- **Proved.** If an exact additive functor takes every object of `C₁` to an
object satisfying `P`, then its derived functor takes every object to
`cohomologyWithin P`.

This is the unbounded, cohomological full-subcategory version of preservation
under an exact functor. -/
theorem mem_cohomologyWithin_mapDerivedCategory
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : ObjectProperty C₂) [P.IsClosedUnderIsomorphisms]
    (hF : ∀ M, P (F.obj M)) (X : DerivedCategory C₁) :
    cohomologyWithin P (F.mapDerivedCategory.obj X) := by
  intro n
  exact P.prop_of_iso (mapDerivedCategoryHomologyIso F X n).symm (hF _)

/-- **Proved instance.** The derived functor of an exact additive functor is
additive.  This instance is not supplied by Mathlib 4.33.1.  The proof uses
that `Qh` is a triangulated localization and that both sides of
`mapDerivedCategoryFactorsh` are additive. -/
noncomputable instance mapDerivedCategory_additive
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.Additive := by
  rw [Localization.functor_additive_iff
    DerivedCategory.Qh (HomotopyCategory.subcategoryAcyclic C₁).trW]
  exact Functor.additive_of_iso F.mapDerivedCategoryFactorsh.symm

/-! ## The derived affine adjunction and its cohomological input -/

/-- **Defined, assuming the supplied exactness instance.** The functor on
unbounded derived categories induced by `M ↦ M^~`. Finite colimits are
preserved because `tilde` is a left adjoint. The remaining exactness instance
is supplied by Stacks Lemma 26.5.4 (Tag 01HV), or proved from quasicoherent
subobject closure by `preservesFiniteLimits_tilde_of_isClosedUnderSubobjects`. -/
noncomputable def affineDerivedTilde (A : CommRingCat.{u})
    [PreservesFiniteLimits (tilde.functor A)] :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (Spec A).Modules :=
  (tilde.functor A).mapDerivedCategory

/-- **Proved instance.** Derived affine `tilde` is additive. -/
noncomputable instance affineDerivedTilde_additive (A : CommRingCat.{u})
    [PreservesFiniteLimits (tilde.functor A)] : (affineDerivedTilde A).Additive := by
  change (tilde.functor A).mapDerivedCategory.Additive
  infer_instance

/-- **Proved instance.** Derived affine `tilde` commutes with integer shifts. -/
noncomputable instance affineDerivedTilde_commShift (A : CommRingCat.{u})
    [PreservesFiniteLimits (tilde.functor A)] : (affineDerivedTilde A).CommShift ℤ := by
  change (tilde.functor A).mapDerivedCategory.CommShift ℤ
  infer_instance

/-- **Proved instance.** Derived affine `tilde` is triangulated. -/
noncomputable instance affineDerivedTilde_isTriangulated (A : CommRingCat.{u})
    [PreservesFiniteLimits (tilde.functor A)] : (affineDerivedTilde A).IsTriangulated := by
  change (tilde.functor A).mapDerivedCategory.IsTriangulated
  infer_instance

/-- **Proved.** If quasicoherent sheaves on `Spec A` are closed under
subobjects, then affine `tilde` preserves finite limits.  Consequently the
Serre-class input of Stacks 01LA also discharges the exactness input 01HV.

The argument is purely categorical.  Subobject closure gives kernel closure;
hence the inclusion of `QCModules A` into all sheaves preserves kernels and
therefore finite limits.  Its precomposition with the equivalence
`tildeEquiv.functor` is `tilde.functor`. -/
theorem preservesFiniteLimits_tilde_of_isClosedUnderSubobjects (A : CommRingCat.{u})
    [(quasiCoherent (Spec A)).IsClosedUnderSubobjects] :
    PreservesFiniteLimits (tilde.functor A) := by
  let _ : (quasiCoherent (Spec A)).IsClosedUnderKernels := inferInstance
  let _ : HasFiniteProducts ((quasiCoherent (Spec A)).FullSubcategory) :=
    qcModulesHasFiniteProducts A
  let _ : HasBinaryBiproducts ((quasiCoherent (Spec A)).FullSubcategory) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  let _ : HasEqualizers ((quasiCoherent (Spec A)).FullSubcategory) :=
    Preadditive.hasEqualizers_of_hasKernels
  let _ : ∀ {X Y : (quasiCoherent (Spec A)).FullSubcategory} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) (quasiCoherent (Spec A)).ι :=
    fun f => (quasiCoherent (Spec A)).preservesKernels_ι f
  change PreservesFiniteLimits
    ((tildeEquiv (R := A)).functor ⋙ (quasiCoherent (Spec A)).ι)
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ (by infer_instance)
    (Functor.preservesFiniteLimits_of_preservesKernels (quasiCoherent (Spec A)).ι)

/-- **Proved.** Derived affine `tilde` lands in complexes with quasicoherent
cohomology. This uses exactness, not derived acyclicity: termwise `tilde`
already produces quasicoherent sheaves, and cohomology commutes with exact
functors by `mapDerivedCategoryHomologyIso`. -/
theorem affineDerivedTilde_mem_quasicoherentCohomology (A : CommRingCat.{u})
    [PreservesFiniteLimits (tilde.functor A)]
    (M : DerivedCategory (ModuleCat.{u} A)) :
    QuasicoherentCohomology A (affineDerivedTilde A |>.obj M) := by
  exact mem_cohomologyWithin_mapDerivedCategory
    (tilde.functor A) (quasiCoherent (Spec A))
    (fun N => by exact inferInstanceAs (tilde N).IsQuasicoherent) M

/-- The published input needed to complete Stacks Lemma 36.3.5 (Tag 06Z0)
from the present Mathlib API. None of these fields asserts the desired
categorical equivalence.

The first field is the exactness of `M ↦ M^~` (Stacks Lemma 26.5.4, Tag 01HV).
The second and third package unbounded derived global sections and the derived
adjunction from `tilde ⊣ Γ` (Cohomology, Lemma 20.28.1, Tag 079W), in the form
used by 06Z0. The last two fields are exactly the cohomology calculations in
the proof of 06Z0. They follow from the truncation/hypercohomology comparison
of Stacks Lemma 36.3.4 (Tag 08D4), applied to `Γ` using Serre vanishing on an
affine scheme, Lemma 30.2.2 (Tag 01XB), together with the underived
`tilde`-global-sections adjunction. The counit condition is imposed only on
`D_QCoh(Spec A)`, as in the published proof. -/
structure AffineDerivedGammaInput (A : CommRingCat.{u}) where
  /-- **Literature input:** exactness of affine `tilde`, Stacks Tag 01HV. -/
  tildeExact : PreservesFiniteLimits (tilde.functor A)
  /-- **Literature input:** unbounded derived global sections on sheaves of
  modules, in the form used by Stacks Tag 06Z0. -/
  RΓ : DerivedCategory (Spec A).Modules ⥤ DerivedCategory (ModuleCat.{u} A)
  /-- **Literature input:** the derived `tilde`-`RΓ` adjunction, Stacks Tag
  079W, specialized as in Stacks Tag 06Z0. -/
  adjunction : letI := tildeExact; affineDerivedTilde A ⊣ RΓ
  /-- **Literature input:** the unit is a quasi-isomorphism for every module
  complex. This is the second cohomology calculation in Stacks 06Z0, using
  Tags 08D4 and 01XB and exactness of `tilde`. -/
  unit_cohomology : letI := tildeExact
    ∀ (M : DerivedCategory (ModuleCat.{u} A)) (n : ℤ),
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        (adjunction.unit.app M))
  /-- **Literature input:** the counit is a quasi-isomorphism on every complex
  with quasicoherent cohomology. This is the first cohomology calculation in
  Stacks 06Z0, using Tags 08D4 and 01XB. No assertion is made for arbitrary
  complexes of sheaves. -/
  counit_cohomology : letI := tildeExact
    ∀ (E : DerivedCategory (Spec A).Modules), QuasicoherentCohomology A E →
      ∀ (n : ℤ), IsIso ((DerivedCategory.homologyFunctor (Spec A).Modules n).map
        (adjunction.counit.app E))

/-- **Proved constructor.** Build the comparison input from subobject closure
of quasicoherent sheaves, without separately supplying exactness of `tilde`.
The remaining arguments retain their Stacks 079W/08D4/01XB meanings. -/
noncomputable def affineDerivedGammaInputOfSubobjects (A : CommRingCat.{u})
    [(quasiCoherent (Spec A)).IsClosedUnderSubobjects]
    (RΓ : DerivedCategory (Spec A).Modules ⥤ DerivedCategory (ModuleCat.{u} A))
    (adjunction : letI := preservesFiniteLimits_tilde_of_isClosedUnderSubobjects A
      affineDerivedTilde A ⊣ RΓ)
    (unit_cohomology : letI := preservesFiniteLimits_tilde_of_isClosedUnderSubobjects A
      ∀ (M : DerivedCategory (ModuleCat.{u} A)) (n : ℤ),
        IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          (adjunction.unit.app M)))
    (counit_cohomology : letI := preservesFiniteLimits_tilde_of_isClosedUnderSubobjects A
      ∀ (E : DerivedCategory (Spec A).Modules), QuasicoherentCohomology A E →
        ∀ (n : ℤ), IsIso ((DerivedCategory.homologyFunctor (Spec A).Modules n).map
          (adjunction.counit.app E))) :
    AffineDerivedGammaInput A where
  tildeExact := preservesFiniteLimits_tilde_of_isClosedUnderSubobjects A
  RΓ := RΓ
  adjunction := adjunction
  unit_cohomology := unit_cohomology
  counit_cohomology := counit_cohomology

/-- **Proved from `AffineDerivedGammaInput`.** The affine equivalence between
`D(A-Mod)` and the full subcategory of the derived category of all sheaves on
objects with quasicoherent cohomology (the ring-side triangle in Stacks 06Z0).

`DerivedCategory.isIso_iff` turns the two cohomological fields into isomorphic
unit and counit components. The adjunction is restricted before forming the
equivalence, so no counit statement on non-quasicoherent complexes is used. -/
noncomputable def affineRingCohomologyEquivalence (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) :
    DerivedCategory (ModuleCat.{u} A) ≌ (QuasicoherentCohomology A).FullSubcategory := by
  letI := I.tildeExact
  haveI (M : DerivedCategory (ModuleCat.{u} A)) : IsIso (I.adjunction.unit.app M) :=
    (DerivedCategory.isIso_iff _ _).mpr (I.unit_cohomology M)
  haveI (E : (QuasicoherentCohomology A).FullSubcategory) :
      IsIso (I.adjunction.counit.app E.obj) :=
    (DerivedCategory.isIso_iff _ _).mpr (I.counit_cohomology E.obj E.property)
  exact
    { functor := ObjectProperty.lift _ (affineDerivedTilde A)
        (affineDerivedTilde_mem_quasicoherentCohomology A)
      inverse := (QuasicoherentCohomology A).ι ⋙ I.RΓ
      unitIso := NatIso.ofComponents
        (fun M => asIso (I.adjunction.unit.app M))
        (fun f => I.adjunction.unit.naturality f)
      counitIso := NatIso.ofComponents
        (fun E => ObjectProperty.isoMk _ (asIso (I.adjunction.counit.app E.obj)))
        (fun f => ObjectProperty.hom_ext _ (I.adjunction.counit.naturality f.hom))
      functor_unitIso_comp := fun M => by
        apply ObjectProperty.hom_ext
        exact I.adjunction.left_triangle_components M }

/-- **Proved from `AffineDerivedGammaInput`.** The comparison from the derived
category of quasicoherent sheaves to the quasicoherent-cohomology model. Its
forward functor is the composite of the existing affine dictionary inverse
with derived `tilde`. -/
noncomputable def affineQCohCohomologyEquivalence (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) :
    DerivedCategory (QCModules A) ≌ (QuasicoherentCohomology A).FullSubcategory :=
  (affineDerivedEquivalence A).symm.trans (affineRingCohomologyEquivalence A I)

/-- **Proved identification.** `QuasicoherentCohomology A` and
`IsDQCoh (Spec A)` are definitionally the same object property: both quantify
over quasicoherence of every derived cohomology sheaf. -/
theorem quasicoherentCohomology_eq_isDQCoh (A : CommRingCat.{u}) :
    QuasicoherentCohomology A = IsDQCoh (Spec A) := rfl

/-- **Proved instance.** The affine quasicoherent-cohomology property is closed
under isomorphisms, by transport of `isDQCoh_isClosedUnderIsomorphisms`. -/
instance quasicoherentCohomology_isClosedUnderIsomorphisms (A : CommRingCat.{u}) :
    (QuasicoherentCohomology A).IsClosedUnderIsomorphisms := by
  rw [quasicoherentCohomology_eq_isDQCoh]
  infer_instance

/-- **Proved instance.** Zero belongs to the affine quasicoherent-cohomology
property. -/
instance quasicoherentCohomology_containsZero (A : CommRingCat.{u}) :
    (QuasicoherentCohomology A).ContainsZero := by
  rw [quasicoherentCohomology_eq_isDQCoh]
  infer_instance

/-- **Proved instance.** The affine quasicoherent-cohomology property is stable
under integer shifts. -/
instance quasicoherentCohomology_isStableUnderShift (A : CommRingCat.{u}) :
    (QuasicoherentCohomology A).IsStableUnderShift ℤ := by
  rw [quasicoherentCohomology_eq_isDQCoh]
  infer_instance

/-- **Proved instance, conditional on AF1's Serre-class fact.** The affine
quasicoherent-cohomology property is triangulated. -/
instance quasicoherentCohomology_isTriangulated (A : CommRingCat.{u})
    [(quasiCoherent (Spec A)).IsSerreClass] :
    (QuasicoherentCohomology A).IsTriangulated := by
  rw [quasicoherentCohomology_eq_isDQCoh]
  infer_instance

/-- **Proved from `AffineDerivedGammaInput`.** The ring comparison written
with the repository's `Dqc (Spec A)` rather than its defining object property. -/
noncomputable def affineRingDqcEquivalence (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) :
    DerivedCategory (ModuleCat.{u} A) ≌ Dqc (Spec A) :=
  affineRingCohomologyEquivalence A I

/-- **Proved instance.** The ring comparison functor is additive. -/
noncomputable instance affineRingCohomologyEquivalence_functor_additive
    (A : CommRingCat.{u}) (I : AffineDerivedGammaInput A) :
    (affineRingCohomologyEquivalence A I).functor.Additive := by
  letI := I.tildeExact
  dsimp only [affineRingCohomologyEquivalence]
  infer_instance

/-- **Proved instance.** The ring comparison functor commutes with integer
shifts. -/
noncomputable instance affineRingCohomologyEquivalence_functor_commShift
    (A : CommRingCat.{u}) (I : AffineDerivedGammaInput A) :
    (affineRingCohomologyEquivalence A I).functor.CommShift ℤ := by
  letI := I.tildeExact
  dsimp only [affineRingCohomologyEquivalence]
  infer_instance

/-- **Proved instance, conditional on AF1's Serre-class fact.** The ring
comparison functor is triangulated. -/
noncomputable instance affineRingCohomologyEquivalence_functor_isTriangulated
    (A : CommRingCat.{u}) (I : AffineDerivedGammaInput A)
    [(quasiCoherent (Spec A)).IsSerreClass] :
    (affineRingCohomologyEquivalence A I).functor.IsTriangulated := by
  letI := I.tildeExact
  dsimp only [affineRingCohomologyEquivalence]
  infer_instance

/-- **Proved from `AffineDerivedGammaInput`.** The quasicoherent-sheaf derived
category compared directly to `Dqc (Spec A)`. -/
noncomputable def affineQCohDqcEquivalence (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) :
    DerivedCategory (QCModules A) ≌ Dqc (Spec A) :=
  affineQCohCohomologyEquivalence A I

/-- **Proved from `AffineDerivedGammaInput`.** Discharges the repository's
provisional `AffineCohomologyComparison` interface. The surviving geometric
input is precisely the named derived-adjunction and cohomology data documented
in `AffineDerivedGammaInput`, sourced to Stacks Tags 01HV, 079W, 08D4 and 01XB;
the equivalence itself is not an input field. -/
noncomputable def affineCohomologyComparisonOfInput (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) : AffineCohomologyComparison A where
  equivalence := affineQCohCohomologyEquivalence A I

/-! ### Axiom audit -/


end
end RelativeFM
