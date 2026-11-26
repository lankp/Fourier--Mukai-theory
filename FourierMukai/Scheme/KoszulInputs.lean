/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.RegularCompactEndpoints
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Inputs of the finite-support affine supported base

Sources: GL26 (affine supported base of Neeman's Thm 3.2, as recorded in
`results/SCHEMES.md`, "Affine supported base"); Neeman, *Acta Math.* 233 (2024),
Lemma 7.6 / Construction 7.3; Stacks 09IR, 0A9A, 09M1.

The finite-list supported base (`IdealNeemanM1.satisfiesPaperWA_idealSupported`,
`AffineSupportedSchemeBaseM1.*`, `RegularCompact.neemanSupported_*`) takes five named
inputs.  This file settles three of them.

* **Refuted:** `StacksInterface.KoszulScalarSupportInput` (tagged 09IR) is *false*
  for every nontrivial ring (`not_koszulScalarSupportInput`).  Its field
  `mem_le_zero` asserts that a cone of `a ^ n • 𝟙 X` is `≤ 0` for *every* perfect
  `X`; for `a = 0`, `n = 1`, `X = A[0]⟦-1⟧`, the object `X` is a retract of the cone,
  so `A[0]` would be `≤ -1`.  Hence every theorem in the tree taking `hS` is vacuous
  outside the zero ring.  The true statements are proved here:
  `scalarConeData_isSupported` (the `support` field, for every perfect `X`) and
  `scalarConeData_le_zero` (the bound, under the hypothesis `X ≤ 0`, which is the
  only case `FiniteKoszulM1.koszulListData` uses).  Replacing the input by these
  two theorems needs a change to the shared file `FiniteKoszulM1.lean` (see the
  report).
* **Proved:** `StacksInterface.IdealSupportedCoproductInput A (functionIdeal A fs)`
  (`idealSupportedCoproductInput`) and
  `StacksInterface.IdealSupportedCompactnessInput A (functionIdeal A fs)`
  (`idealSupportedCompactnessInput`), for every finite list `fs`.  Both follow from
  `isLeftAdjoint_affineDZIdealι`: the inclusion `D_{V(fs)}(A) ⟶ D(A)` has a right
  adjoint, built by induction on `fs` from the principal local-cohomology adjoints
  `AffineLocalCohomology.jShriekAdj` (`V(f :: fs) = V(f) ∩ V(fs)`), using that
  `RΓ_{V(f)}` preserves ideal support (`jStar_supportedIdeal`, from the first gluing
  triangle and the elementwise `idealPowerTorsion_restrictExtend`).  A coreflective,
  retract-closed subcategory is closed under all ambient colimits
  (`isClosedUnderColimitsOfShape_of_adjunction`), and the left adjoint preserves them.

Nothing is assumed in this file: no Stacks field and no named hypothesis.
`KoszulPowerCoprodInput`, `KoszulDetectionInput` (0A9A) and
`AffineSupportedSchemeComparisonInput` are not addressed here, and no strengthened
endpoint is stated, because every endpoint still carries the refuted `hS`.
-/

@[expose] public section

namespace RelativeFM.KoszulInputs

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open RelativeFM.NeemanFiniteSupportM4
open RelativeFM.FiniteKoszulM1

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section Refutation

/-- **Refutation of `KoszulScalarSupportInput`** (tagged Stacks 09IR).  For a
nontrivial ring the input is false: take `a = 0`, `n = 1`, `X = A[0]⟦-1⟧`.  The cone
of `0 • 𝟙 X` has `X` as a retract, so `mem_le_zero` would make `A[0]` lie in degrees
`≤ -1`, forcing `A = 0`. -/
theorem not_koszulScalarSupportInput (A : Type u) [CommRing A] [Nontrivial A] :
    ¬ StacksInterface.KoszulScalarSupportInput A := by
  intro hS
  let X : AffineD A := (ringObject A)⟦(-1 : ℤ)⟧
  have hX : Perf A X := perf_shift A (ringObject_mem_perf A) (-1)
  let C := scalarConeData A ((0 : A) ^ 1) hX
  have hC : (AffineD.standardTStructure A).le 0 C.obj := hS.mem_le_zero (a := 0) 1 hX
  have hCle : C.obj.IsLE 0 := (DerivedCategory.TStructure.t.le_iff_isLE C.obj 0).mp hC
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ C.distinguished (𝟙 X)
    (by change ((0 : A) ^ 1 • 𝟙 X) ≫ 𝟙 X = 0; rw [pow_one, zero_smul]; exact Limits.zero_comp)
  have hXle : X.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
    have hz : IsZero (H.obj C.obj) := DerivedCategory.isZero_of_isLE C.obj 0 i hi
    rw [IsZero.iff_id_eq_zero]
    let g' : C.obj ⟶ X := g
    have hg' : 𝟙 X = C.second ≫ g' := hg
    have h1 : H.map (𝟙 X) = H.map C.second ≫ H.map g' := by
      rw [hg', H.map_comp]
    rw [← H.map_id, h1, hz.eq_of_src (H.map g') 0, comp_zero]
  have hR : (ringObject A).IsLE (-1) := by
    have : DerivedCategory.TStructure.t.IsLE ((ringObject A)⟦(-1 : ℤ)⟧) 0 := hXle
    exact DerivedCategory.TStructure.t.isLE_of_shift (ringObject A) (-1) (-1) 0
  have hz := DerivedCategory.isZero_of_isLE (ringObject A) (-1) 0 (by omega)
  have hA : IsZero (ModuleCat.of A A) :=
    hz.of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} A) 0).app (ModuleCat.of A A)).symm
  have : Subsingleton A := ModuleCat.subsingleton_of_isZero hA
  exact false_of_nontrivial_of_subsingleton A


end Refutation

section Correction

/-- The cohomology functors of `D(A)` commute with scalar multiplication by `A`. -/
lemma homologyFunctor_map_smul_id (A : Type u) [CommRing A] (b : A) (X : AffineD A) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map (b • 𝟙 X) = b • 𝟙 _ := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  have h1 : b • 𝟙 X = e.inv ≫ DerivedCategory.Q.map (b • 𝟙 K) ≫ e.hom := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, e.inv_hom_id]
  have h2 : HomologicalComplex.homologyMap (b • 𝟙 K) n = b • 𝟙 _ := by
    change ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (b • 𝟙 K)) = _
    rw [show (HomologicalComplex.shortComplexFunctor _ _ n).map (b • 𝟙 K) =
        b • 𝟙 ((HomologicalComplex.shortComplexFunctor _ _ n).obj K) by
      ext <;> rfl, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
    rfl
  have h3 := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).hom.naturality
    (b • 𝟙 K)
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, h2] at h3
  have h4 : H.map (DerivedCategory.Q.map (b • 𝟙 K)) = b • 𝟙 _ := by
    rw [← cancel_mono ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).hom.app K)]
    rw [h3, Linear.smul_comp, Category.id_comp]
    erw [Linear.comp_smul, Category.comp_id]
  rw [h1, H.map_comp, H.map_comp, h4, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    ← H.map_comp, e.inv_hom_id, H.map_id]

/-- On a cone of `b • 𝟙 X`, the endomorphism `b² • 𝟙` vanishes. -/
lemma scalarCone_smul_eq_zero (A : Type u) [CommRing A] (b : A) {X : AffineD A}
    (C : AffineD A) (g₂ : X ⟶ C) (g₃ : C ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (b • 𝟙 X) g₂ g₃ ∈ distTriang (AffineD A)) :
    (b * b) • 𝟙 C = 0 := by
  let T := Triangle.mk (b • 𝟙 X) g₂ g₃
  have h12 : g₂ ≫ (b • 𝟙 C) = 0 := by
    rw [Linear.comp_smul, Category.comp_id, ← Category.id_comp g₂, ← Linear.smul_comp]
    exact comp_distTriang_mor_zero₁₂ T hT
  have h31 : (b • 𝟙 C) ≫ g₃ = 0 := by
    have h := comp_distTriang_mor_zero₃₁ T hT
    change g₃ ≫ (shiftFunctor (AffineD A) (1 : ℤ)).map (b • 𝟙 X) = 0 at h
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.comp_smul, Category.comp_id] at h
    rw [Linear.smul_comp, Category.id_comp]
    exact h
  obtain ⟨h, hh⟩ := Triangle.yoneda_exact₃ T hT (b • 𝟙 C) h12
  have hsq : (b * b) • 𝟙 C = (b • 𝟙 C) ≫ (b • 𝟙 C) := by
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, mul_smul]
  rw [hsq]
  nth_rewrite 2 [hh]
  let h' : X⟦(1 : ℤ)⟧ ⟶ C := h
  change (b • 𝟙 C) ≫ g₃ ≫ h' = 0
  rw [← Category.assoc, h31, zero_comp]

/-- **Corrected 09IR, support half** (proved): a cone of `a ^ n • 𝟙 X` is
supported on `V(a)` for *every* perfect `X`; its cohomology is killed by
`a ^ (2n)`.  This is the `support` field of
`StacksInterface.KoszulScalarSupportInput`, which is therefore provable. -/
theorem scalarConeData_isSupported (A : Type u) [CommRing A] (a : A) (n : ℕ)
    {X : AffineD A} (hX : Perf A X) :
    AffineIsSupported A a (scalarConeData A (a ^ n) hX).obj := by
  let C := scalarConeData A (a ^ n) hX
  intro i
  rw [powerTorsion_iff]
  intro x
  refine ⟨n + n, ?_⟩
  have h0 := scalarCone_smul_eq_zero A (a ^ n) C.obj C.second C.third C.distinguished
  have h1 := homologyFunctor_map_smul_id A (a ^ n * a ^ n) C.obj i
  rw [h0, Functor.map_zero] at h1
  have hx := congrArg (fun φ => φ.hom x) h1
  rw [pow_add]
  simpa using hx.symm

/-- **Corrected 09IR, bound half** (proved): a cone of `b • 𝟙 X` lies in the
standard aisle `≤ 0` when `X` does.  The field `mem_le_zero` of
`StacksInterface.KoszulScalarSupportInput` drops the hypothesis on `X` and is
false (`not_koszulScalarSupportInput`); `koszulListData` applies it only to
iterated Koszul objects starting from `A[0]`, which are `≤ 0`. -/
theorem scalarConeData_le_zero (A : Type u) [CommRing A] (b : A)
    {X : AffineD A} (hX : Perf A X) (hle : (AffineD.standardTStructure A).le 0 X) :
    (AffineD.standardTStructure A).le 0 (scalarConeData A b hX).obj := by
  let t := AffineD.standardTStructure A
  letI : (t.le 0).IsTriangulatedClosed₂ := TStructure.le_isTriangulatedClosed₂ t 0
  let C := scalarConeData A b hX
  have hsh : t.le 0 (X⟦(1 : ℤ)⟧) :=
    t.le_monotone (show (-1 : ℤ) ≤ 0 by omega) _ (t.le_shift 0 1 (-1) (by omega) _ hle)
  exact (t.le 0).ext_of_isTriangulatedClosed₂ _ (rot_of_distTriang _ C.distinguished) hle hsh

end Correction

section Localization

/-- Localizing at `f` preserves `V(I)`-power torsion: `M ⊗_A A_f`, viewed as an
`A`-module, is `I`-power torsion when `M` is. -/
lemma idealPowerTorsion_restrictExtend (A : Type u) [CommRing A] (f : A) (I : Ideal A)
    (M : ModuleCat.{u} A) (hM : IdealPowerTorsion A I M) :
    IdealPowerTorsion A I ((ModuleCat.restrictScalars (algebraMap A (Away A f))).obj
      ((ModuleCat.extendScalars (algebraMap A (Away A f))).obj M)) := by
  let R := (ModuleCat.restrictScalars (algebraMap A (Away A f))).obj
    (ModuleCat.of (Away A f) (Away A f))
  let T := (ModuleCat.restrictScalars (algebraMap A (Away A f))).obj
      ((ModuleCat.extendScalars (algebraMap A (Away A f))).obj M)
  have key : ∀ (b : A) (t : TensorProduct A R M),
      @HSMul.hSMul A T T _ b t = (b • t : TensorProduct A R M) := by
    intro b t
    induction t using TensorProduct.induction_on with
    | zero => exact (smul_zero (A := T) b).trans (smul_zero b).symm
    | tmul r m => rfl
    | add x y hx hy => exact (smul_add (M := A) (A := T) b x y).trans (by rw [hx, hy]; exact (smul_add b x y).symm)
  intro x a ha
  change ∃ n : ℕ, @HSMul.hSMul A T T _ (a ^ n) x = 0
  suffices h : ∀ t : TensorProduct A R M, ∃ n : ℕ, a ^ n • t = 0 by
    obtain ⟨n, hn⟩ := h x
    exact ⟨n, (key _ x).trans hn⟩
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, smul_zero _⟩
  | tmul r m =>
      obtain ⟨n, hn⟩ := hM m a ha
      exact ⟨n, by rw [← TensorProduct.tmul_smul, hn, TensorProduct.tmul_zero]⟩
  | add x y hx hy =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨m, hm⟩ := hy
      refine ⟨n + m, ?_⟩
      rw [smul_add, pow_add, mul_smul, smul_comm (a ^ n) (a ^ m) x, hn, mul_smul, hm,
        smul_zero, smul_zero, add_zero]


/-- `Rj_* Lj^*` (localization at `f`) preserves ideal support. -/
lemma affineIsSupportedIdeal_localization (A : Type u) [CommRing A] (f : A) (I : Ideal A)
    {X : AffineD A} (hX : AffineIsSupportedIdeal A I X) :
    AffineIsSupportedIdeal A I
      ((derivedRestrictionScalars A f).obj ((derivedExtensionScalars A f).obj X)) := by
  have hf : (algebraMap A (Away A f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  letI : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap A (Away A f))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Away A f))).left_adjoint_additive
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  intro n
  let E := ModuleCat.extendScalars.{u, u, u} (algebraMap A (Away A f))
  let Rs := ModuleCat.restrictScalars.{u} (algebraMap A (Away A f))
  have e1 := mapDerivedCategoryHomologyIso Rs (E.mapDerivedCategory.obj X) n
  have e2 := mapDerivedCategoryHomologyIso E X n
  letI : (IdealPowerTorsion A I).IsClosedUnderIsomorphisms := inferInstance
  exact (IdealPowerTorsion A I).prop_of_iso (e1 ≪≫ Rs.mapIso e2).symm
    (idealPowerTorsion_restrictExtend A f I _ (hX n))

/-- Local cohomology `RΓ_{V(f)}` preserves `V(I)`-support, by the triangle
`RΓ_{V(f)} X ⟶ X ⟶ Rj_* Lj^* X`. -/
lemma jStar_supportedIdeal (A : Type u) [CommRing A] (f : A) (I : Ideal A)
    {X : AffineD A} (hX : AffineIsSupportedIdeal A I X) :
    AffineIsSupportedIdeal A I ((AffineLocalCohomology.jStar A f).obj X).obj := by
  letI : (AffineIsSupportedIdeal A I).IsClosedUnderIsomorphisms := by
    unfold AffineIsSupportedIdeal
    infer_instance
  have hT := AffineLocalCohomology.supportedFirstTriangle_distinguished A f (AffineLocalCohomology.jStar A f)
    (AffineLocalCohomology.jStarFactors A f) X
  exact (AffineIsSupportedIdeal A I).ext_of_isTriangulatedClosed₂ _
    (inv_rot_of_distTriang _ hT)
    ((AffineIsSupportedIdeal A I).le_shift (-1) _ (affineIsSupportedIdeal_localization A f I hX)) hX


end Localization

section Intersection

universe v w
variable {C : Type w} [Category.{v} C]

/-- The object of `P.FullSubcategory` underlying an object of a smaller subcategory. -/
abbrev restrictObj {S P : ObjectProperty C} (h : ∀ X, S X → P X)
    (Y : S.FullSubcategory) : P.FullSubcategory := ⟨Y.obj, h _ Y.property⟩

/-- If the inclusions of `P` and `Q` are left adjoints and the right adjoint of
`P`'s inclusion preserves `Q`, then the inclusion of `S = P ⊓ Q` is a left
adjoint. -/
theorem isLeftAdjoint_ι_of_inf (P Q S : ObjectProperty C)
    (hS : ∀ X, S X ↔ P X ∧ Q X)
    {RP : C ⥤ P.FullSubcategory} (adjP : P.ι ⊣ RP)
    {RQ : C ⥤ Q.FullSubcategory} (adjQ : Q.ι ⊣ RQ)
    (hPQ : ∀ X, Q X → Q (RP.obj X).obj) : S.ι.IsLeftAdjoint := by
  let hSP : ∀ X, S X → P X := fun X h => ((hS X).1 h).1
  let hSQ : ∀ X, S X → Q X := fun X h => ((hS X).1 h).2
  let G : C → S.FullSubcategory := fun X =>
    ⟨(RP.obj (RQ.obj X).obj).obj,
      (hS _).2 ⟨(RP.obj _).property, hPQ _ (RQ.obj X).property⟩⟩
  let e : ∀ (Y : S.FullSubcategory) (X : C), (S.ι.obj Y ⟶ X) ≃ (Y ⟶ G X) := fun Y X =>
    (adjQ.homEquiv (restrictObj hSQ Y) X).trans
      (Q.fullyFaithfulι.homEquiv.trans
        ((adjP.homEquiv (restrictObj hSP Y) (RQ.obj X).obj).trans
          (P.fullyFaithfulι.homEquiv.trans (S.fullyFaithfulι.homEquiv (X := Y) (Y := G X)).symm)))
  have he : ∀ (Y' Y : S.FullSubcategory) (X : C) (f : Y' ⟶ Y) (g : S.ι.obj Y ⟶ X),
      e Y' X (S.ι.map f ≫ g) = f ≫ e Y X g := by
    intro Y' Y X f g
    have h1 := adjQ.homEquiv_naturality_left
      (ObjectProperty.homMk f.hom : restrictObj hSQ Y' ⟶ restrictObj hSQ Y) g
    have h2 := adjP.homEquiv_naturality_left
      (ObjectProperty.homMk f.hom : restrictObj hSP Y' ⟶ restrictObj hSP Y)
      ((adjQ.homEquiv (restrictObj hSQ Y) X) g).hom
    rw [show S.ι.map f ≫ g = Q.ι.map
      (ObjectProperty.homMk f.hom : restrictObj hSQ Y' ⟶ restrictObj hSQ Y) ≫ g from rfl]
    simp only [e, Equiv.trans_apply]
    rw [h1]
    generalize (adjQ.homEquiv (restrictObj hSQ Y) X) g = φ
    have h2 := adjP.homEquiv_naturality_left
      (ObjectProperty.homMk f.hom : restrictObj hSP Y' ⟶ restrictObj hSP Y)
      (φ.hom : (restrictObj hSP Y).obj ⟶ (RQ.obj X).obj)
    change (S.fullyFaithfulι.homEquiv (X := Y') (Y := G X)).symm (P.fullyFaithfulι.homEquiv
      ((adjP.homEquiv (restrictObj hSP Y') (RQ.obj X).obj)
        (P.ι.map (ObjectProperty.homMk f.hom : restrictObj hSP Y' ⟶ restrictObj hSP Y) ≫
          (φ.hom : (restrictObj hSP Y).obj ⟶ (RQ.obj X).obj)))) = _
    rw [h2]
    rfl
  exact ⟨_, ⟨Adjunction.adjunctionOfEquivRight e he⟩⟩

/-- The inclusion of an object property satisfied by every object is a left
adjoint (its right adjoint is the tautological lift). -/
theorem isLeftAdjoint_ι_of_forall (S : ObjectProperty C) (h : ∀ X, S X) :
    S.ι.IsLeftAdjoint := by
  let G : C → S.FullSubcategory := fun X => ⟨X, h X⟩
  let e : ∀ (Y : S.FullSubcategory) (X : C), (S.ι.obj Y ⟶ X) ≃ (Y ⟶ G X) := fun Y X =>
    (S.fullyFaithfulι.homEquiv (X := Y) (Y := G X)).symm
  exact ⟨_, ⟨Adjunction.adjunctionOfEquivRight e (fun _ _ _ _ _ => rfl)⟩⟩

/-- A coreflective strictly full subcategory which is stable under retracts is
closed under every colimit that exists in the ambient category: the colimit
is a retract of its coreflection. -/
theorem isClosedUnderColimitsOfShape_of_adjunction (S : ObjectProperty C)
    [S.IsStableUnderRetracts] {R : C ⥤ S.FullSubcategory} (adj : S.ι ⊣ R)
    (J : Type*) [Category J] : S.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨c⟩
    let Y : J → S.FullSubcategory := fun j => ⟨c.diag.obj j, c.prop_diag_obj j⟩
    let φ : ∀ j, c.diag.obj j ⟶ (R.obj X).obj := fun j =>
      (adj.homEquiv (Y j) X (c.ι.app j)).hom
    have hφ : ∀ j, φ j ≫ adj.counit.app X = c.ι.app j := by
      intro j
      have h := adj.homEquiv_counit (X := Y j) (Y := X) (adj.homEquiv (Y j) X (c.ι.app j))
      rw [Equiv.symm_apply_apply] at h
      exact h.symm
    have inj : ∀ j (a b : c.diag.obj j ⟶ (R.obj X).obj),
        a ≫ adj.counit.app X = b ≫ adj.counit.app X → a = b := by
      intro j a b hab
      have h' : (adj.homEquiv (Y j) X).symm (ObjectProperty.homMk a) =
          (adj.homEquiv (Y j) X).symm (ObjectProperty.homMk b) := by
        rw [adj.homEquiv_counit, adj.homEquiv_counit]
        exact hab
      exact congrArg InducedCategory.Hom.hom ((adj.homEquiv (Y j) X).symm.injective h')
    let s : X ⟶ (R.obj X).obj := c.isColimit.desc
      { pt := (R.obj X).obj
        ι := { app := φ
               naturality := fun j j' u => by
                 apply inj j
                 simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
                   Category.assoc, hφ]
                 exact (c.ι.naturality u).trans (Category.comp_id _) } }
    have hs : s ≫ adj.counit.app X = 𝟙 X := by
      apply c.isColimit.hom_ext
      intro j
      rw [Category.comp_id, ← Category.assoc]
      erw [c.isColimit.fac]
      exact hφ j
    exact S.prop_of_retract ⟨s, adj.counit.app X, hs⟩ (R.obj X).property

end Intersection

section Inputs

variable (A : Type u) [CommRing A]

/-- The inclusion `D_{V(f₁,…,fₙ)}(A) ⟶ D(A)` is a left adjoint, for every finite
list.  Induction on the list: `V(f :: fs) = V(f) ∩ V(fs)`, local cohomology
`RΓ_{V(f)}` is the right adjoint of the principal inclusion
(`AffineLocalCohomology.jShriekAdj`), and it preserves `V(fs)`-support
(`jStar_supportedIdeal`). -/
theorem isLeftAdjoint_affineDZIdealι :
    ∀ fs : List A, (affineDZIdealι A (functionIdeal A fs)).IsLeftAdjoint
  | [] => isLeftAdjoint_ι_of_forall _ (by
      intro X n x a ha
      have ha0 : a = 0 := by simpa [functionIdeal] using ha
      subst a
      exact ⟨1, by simp⟩)
  | a :: fs => by
      haveI := isLeftAdjoint_affineDZIdealι fs
      exact isLeftAdjoint_ι_of_inf (AffineIsSupported A a)
        (AffineIsSupportedIdeal A (functionIdeal A fs))
        (AffineIsSupportedIdeal A (functionIdeal A (a :: fs)))
        (fun X => by
          change AffineIsSupportedIdeal A (Ideal.span {a} ⊔ functionIdeal A fs) X ↔ _
          rw [affineIsSupportedIdeal_sup, affineIsSupportedIdeal_span_singleton])
        (AffineLocalCohomology.jShriekAdj A a)
        (Adjunction.ofIsLeftAdjoint (affineDZIdealι A (functionIdeal A fs)))
        (fun X hX => jStar_supportedIdeal A a _ hX)

/-- **Supported direct sums, proved** (`IdealSupportedCoproductInput`).  The
supported class `D_{V(f₁,…,fₙ)}` is closed under every coproduct that exists in
`D(A)`. -/
theorem idealSupportedCoproductInput (fs : List A) :
    StacksInterface.IdealSupportedCoproductInput A (functionIdeal A fs) where
  closed J := by
    haveI := isLeftAdjoint_affineDZIdealι A fs
    letI : (AffineIsSupportedIdeal A (functionIdeal A fs)).IsStableUnderRetracts := by
      unfold AffineIsSupportedIdeal
      infer_instance
    exact isClosedUnderColimitsOfShape_of_adjunction _
      (Adjunction.ofIsLeftAdjoint (affineDZIdealι A (functionIdeal A fs))) (Discrete J)

/-- **Supported compactness descent input, proved**
(`IdealSupportedCompactnessInput`): the inclusion preserves coproducts, being a
left adjoint. -/
theorem idealSupportedCompactnessInput (fs : List A) :
    StacksInterface.IdealSupportedCompactnessInput A (functionIdeal A fs) where
  preserves J := by
    haveI := isLeftAdjoint_affineDZIdealι A fs
    exact (Adjunction.ofIsLeftAdjoint
      (affineDZIdealι A (functionIdeal A fs))).leftAdjoint_preservesColimits.preservesColimitsOfShape

end Inputs

end

end RelativeFM.KoszulInputs

#print axioms RelativeFM.KoszulInputs.not_koszulScalarSupportInput
#print axioms RelativeFM.KoszulInputs.scalarConeData_isSupported
#print axioms RelativeFM.KoszulInputs.scalarConeData_le_zero
#print axioms RelativeFM.KoszulInputs.jStar_supportedIdeal
#print axioms RelativeFM.KoszulInputs.isLeftAdjoint_affineDZIdealι
#print axioms RelativeFM.KoszulInputs.idealSupportedCoproductInput
#print axioms RelativeFM.KoszulInputs.idealSupportedCompactnessInput
