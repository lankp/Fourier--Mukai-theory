/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# The affine dictionary: `D(A-Mod) ≃ D(QCoh(Spec A))`

`tildeEquiv` identifies `A`-modules with *quasicoherent* sheaves on `Spec A`, not
with all sheaves of modules — the file's first correction, and it matters.
Around that:

* `derivedEquivalence`: for an additive equivalence `E` of abelian categories, the
  induced equivalence `D(C) ≌ D(D)` of unbounded derived categories, built from
  raw complexes and the localization, together with shifts, the triangulated
  structure, and preservation *and reflection* of the canonical `IsLE`/`IsGE`.
  This is reusable beyond the affine case.
* `affineDerivedEquivalence A : D(A-Mod) ≌ D(QCoh(Spec A))`, with explicit
  `D^-`, `D^+` and `D^b` versions and the compatibility
  `affineDerivedSingleFunctor` on complexes concentrated in one degree.
* `QuasicoherentCohomology` and `AffineCohomologyComparison` (marked PROVISIONAL)
  relate the quasicoherent model to quasicoherent *cohomology* on the all-sheaf
  model; it is the only unproved geometric input here, and it cites Stacks 36.3.5
  and 06Z0.  `affineDerivedCohomologyEquivalence` is the combined dictionary.

Found by a member of the Ultramath run `smwuz1thx` (direction B1).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe w₁ w₂ w₃ v₁ v₂ u₁ u₂ u

/-! ## Derived transport along an equivalence of abelian categories -/

/-- The derived equivalence induced by an additive equivalence of abelian
categories.  This is the transport step in the affine dictionary for GL26
Section 2.2.

The proof uses the induced equivalence on raw cochain complexes and reflects
quasi-isomorphisms along `E.functor`; `LocalizerMorphism` then supplies the
equivalence after localization. -/
noncomputable def derivedEquivalence
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    DerivedCategory C₁ ≌ DerivedCategory C₂ := by
  letI : (E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence :=
    (E.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  let Φ := E.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  have hW : HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ) =
      (HomologicalComplex.quasiIso C₂ (ComplexShape.up ℤ)).inverseImage Φ.functor := by
    ext K L f
    change QuasiIso f ↔ QuasiIso ((E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
    exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f E.functor).symm
  letI : Φ.functor.IsEquivalence :=
    inferInstanceAs (E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence
  letI : Φ.IsLocalizedEquivalence :=
    LocalizerMorphism.IsLocalizedEquivalence.of_equivalence Φ (by
      calc
        HomologicalComplex.quasiIso C₂ (ComplexShape.up ℤ) ≤
            ((HomologicalComplex.quasiIso C₂ (ComplexShape.up ℤ)).inverseImage
              Φ.functor).map Φ.functor :=
          le_of_eq (MorphismProperty.map_inverseImage_eq_of_isEquivalence _ _).symm
        _ = (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)).map Φ.functor :=
          congrArg (fun W => W.map Φ.functor) hW.symm)
  letI : E.functor.mapDerivedCategory.IsEquivalence := by
    change (Φ.localizedFunctor DerivedCategory.Q DerivedCategory.Q).IsEquivalence
    infer_instance
  exact E.functor.mapDerivedCategory.asEquivalence

/-- The underlying derived functor of an additive equivalence is an
equivalence. -/
noncomputable instance mapDerivedCategory_isEquivalence
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    E.functor.mapDerivedCategory.IsEquivalence :=
  (derivedEquivalence E).isEquivalence_functor

/-- Preservation and reflection of the upper cohomological bounds in the
canonical `t`-structure.  Strictly bounded representatives, rather than an
external boundedness theorem, give both directions. -/
theorem isLE_mapDerivedCategory_iff
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] (X : DerivedCategory C₁) (n : ℤ) :
    (E.functor.mapDerivedCategory.obj X).IsLE n ↔ X.IsLE n := by
  constructor
  · rintro ⟨L, e, hL⟩
    let K := (E.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
    let eL : E.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj L :=
      E.functor.mapDerivedCategoryFactors.app K ≪≫
        DerivedCategory.Q.mapIso
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).counitIso.app L)
    exact ⟨K, E.functor.mapDerivedCategory.preimageIso (e ≪≫ eL.symm),
      (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff L E.inverse n).mpr hL⟩
  · rintro ⟨K, e, hK⟩
    exact ⟨(E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
      E.functor.mapDerivedCategory.mapIso e ≪≫
        E.functor.mapDerivedCategoryFactors.app K,
      (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff K E.functor n).mpr hK⟩

/-- Preservation and reflection of the lower cohomological bounds in the
canonical `t`-structure. -/
theorem isGE_mapDerivedCategory_iff
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] (X : DerivedCategory C₁) (n : ℤ) :
    (E.functor.mapDerivedCategory.obj X).IsGE n ↔ X.IsGE n := by
  constructor
  · rintro ⟨L, e, hL⟩
    let K := (E.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
    let eL : E.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj L :=
      E.functor.mapDerivedCategoryFactors.app K ≪≫
        DerivedCategory.Q.mapIso
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).counitIso.app L)
    exact ⟨K, E.functor.mapDerivedCategory.preimageIso (e ≪≫ eL.symm),
      (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff L E.inverse n).mpr hL⟩
  · rintro ⟨K, e, hK⟩
    exact ⟨(E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
      E.functor.mapDerivedCategory.mapIso e ≪≫
        E.functor.mapDerivedCategoryFactors.app K,
      (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff K E.functor n).mpr hK⟩

/-- The equivalence of derived categories preserves and reflects `IsLE`. -/
theorem derivedEquivalence_isLE_iff
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] (X : DerivedCategory C₁) (n : ℤ) :
    ((derivedEquivalence E).functor.obj X).IsLE n ↔ X.IsLE n :=
  isLE_mapDerivedCategory_iff E X n

/-- The equivalence of derived categories preserves and reflects `IsGE`. -/
theorem derivedEquivalence_isGE_iff
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] (X : DerivedCategory C₁) (n : ℤ) :
    ((derivedEquivalence E).functor.obj X).IsGE n ↔ X.IsGE n :=
  isGE_mapDerivedCategory_iff E X n

/-- The restriction of `derivedEquivalence E` to bounded-above objects
(`D^-` in the notation of GL26 Section 2.2). -/
noncomputable def derivedMinusEquivalence
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    DerivedCategory.Minus C₁ ≌ DerivedCategory.Minus C₂ :=
  (derivedEquivalence E).congrFullSubcategory (by
    ext X
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (derivedEquivalence_isLE_iff E X n).mp hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, (derivedEquivalence_isLE_iff E X n).mpr hn⟩)

/-- The restriction of `derivedEquivalence E` to bounded-below objects
(`D^+` in the notation of GL26 Section 2.2). -/
noncomputable def derivedPlusEquivalence
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    DerivedCategory.Plus C₁ ≌ DerivedCategory.Plus C₂ :=
  (derivedEquivalence E).congrFullSubcategory (by
    ext X
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (derivedEquivalence_isGE_iff E X n).mp hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, (derivedEquivalence_isGE_iff E X n).mpr hn⟩)

/-- The restriction of `derivedEquivalence E` to bounded objects (`D^b`). -/
noncomputable def derivedBoundedEquivalence
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    DerivedCategory.Bounded C₁ ≌ DerivedCategory.Bounded C₂ :=
  (derivedEquivalence E).congrFullSubcategory (by
    ext X
    constructor
    · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
      exact ⟨⟨n, (derivedEquivalence_isGE_iff E X n).mp hn⟩,
        ⟨m, (derivedEquivalence_isLE_iff E X m).mp hm⟩⟩
    · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
      exact ⟨⟨n, (derivedEquivalence_isGE_iff E X n).mpr hn⟩,
        ⟨m, (derivedEquivalence_isLE_iff E X m).mpr hm⟩⟩)

/-- The forward derived equivalence commutes with integer shifts. -/
noncomputable instance derivedEquivalence_functor_commShift
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    (derivedEquivalence E).functor.CommShift ℤ := by
  change E.functor.mapDerivedCategory.CommShift ℤ
  infer_instance

/-- The forward derived equivalence is triangulated. -/
noncomputable instance derivedEquivalence_functor_isTriangulated
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    (derivedEquivalence E).functor.IsTriangulated := by
  change E.functor.mapDerivedCategory.IsTriangulated
  infer_instance

/-- The bounded-above restriction commutes with integer shifts. -/
noncomputable instance derivedMinusEquivalence_functor_commShift
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    (derivedMinusEquivalence E).functor.CommShift ℤ := by
  dsimp only [derivedMinusEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- The bounded-below restriction commutes with integer shifts. -/
noncomputable instance derivedPlusEquivalence_functor_commShift
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    (derivedPlusEquivalence E).functor.CommShift ℤ := by
  dsimp only [derivedPlusEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- The bounded restriction commutes with integer shifts. -/
noncomputable instance derivedBoundedEquivalence_functor_commShift
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    (derivedBoundedEquivalence E).functor.CommShift ℤ := by
  dsimp only [derivedBoundedEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- The bounded-above restriction is triangulated for the induced structures. -/
noncomputable instance derivedMinusEquivalence_functor_isTriangulated
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    (derivedMinusEquivalence E).functor.IsTriangulated := by
  dsimp only [derivedMinusEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- The bounded-below restriction is triangulated for the induced structures. -/
noncomputable instance derivedPlusEquivalence_functor_isTriangulated
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    (derivedPlusEquivalence E).functor.IsTriangulated := by
  dsimp only [derivedPlusEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- The bounded restriction is triangulated for the induced structures. -/
noncomputable instance derivedBoundedEquivalence_functor_isTriangulated
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive] :
    (derivedBoundedEquivalence E).functor.IsTriangulated := by
  dsimp only [derivedBoundedEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-! ## The affine dictionary -/

/-- The abelian category of quasi-coherent modules on `Spec A`.  This is the
actual target of Mathlib's `AlgebraicGeometry.tildeEquiv`. -/
abbrev QCModules (A : CommRingCat.{u}) :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory

/-- Finite products on quasi-coherent modules over an affine scheme,
transported from `ModuleCat A` along `tildeEquiv`. -/
noncomputable instance qcModulesHasFiniteProducts (A : CommRingCat.{u}) :
    HasFiniteProducts (QCModules A) := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact E.functor.hasFiniteProducts_of_additive_of_essSurj

/-- The abelian structure on quasi-coherent modules over an affine scheme,
transported along `tildeEquiv`. -/
noncomputable instance qcModulesAbelian (A : CommRingCat.{u}) : Abelian (QCModules A) :=
  abelianOfEquivalence (tildeEquiv (R := A)).inverse

/-- **The affine derived dictionary** for GL26 Section 2.2:
`D(A-Mod) ≃ D(QCoh(Spec A))`.  Its forward functor is induced by the tilde
functor on raw complexes. -/
noncomputable def affineDerivedEquivalence (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    DerivedCategory (ModuleCat.{u} A) ≌ DerivedCategory (QCModules A) := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact derivedEquivalence E

/-- The affine derived dictionary on bounded-above objects. -/
noncomputable def affineDerivedMinusEquivalence (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    DerivedCategory.Minus (ModuleCat.{u} A) ≌ DerivedCategory.Minus (QCModules A) := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact derivedMinusEquivalence E

/-- The affine derived dictionary on bounded-below objects. -/
noncomputable def affineDerivedPlusEquivalence (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    DerivedCategory.Plus (ModuleCat.{u} A) ≌ DerivedCategory.Plus (QCModules A) := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact derivedPlusEquivalence E

/-- The affine derived dictionary on bounded objects. -/
noncomputable def affineDerivedBoundedEquivalence (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    DerivedCategory.Bounded (ModuleCat.{u} A) ≌ DerivedCategory.Bounded (QCModules A) := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact derivedBoundedEquivalence E

/-- The derived affine dictionary extends the underived tilde dictionary on
complexes concentrated in degree `n`. -/
noncomputable def affineDerivedSingleFunctor (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)]
    (n : ℤ) :
    DerivedCategory.singleFunctor (ModuleCat.{u} A) n ⋙
        (affineDerivedEquivalence A).functor ≅
      (tildeEquiv (R := A)).functor ⋙ DerivedCategory.singleFunctor (QCModules A) n := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact E.functor.mapDerivedCategorySingleFunctor n

/-- Shift compatibility of the unbounded affine dictionary. -/
noncomputable instance affineDerivedEquivalence_functor_commShift (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    (affineDerivedEquivalence A).functor.CommShift ℤ := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  change (derivedEquivalence E).functor.CommShift ℤ
  infer_instance

/-- The unbounded affine dictionary is triangulated. -/
noncomputable instance affineDerivedEquivalence_functor_isTriangulated (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    (affineDerivedEquivalence A).functor.IsTriangulated := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  change (derivedEquivalence E).functor.IsTriangulated
  infer_instance

/-- Shift compatibility of the bounded-above affine dictionary. -/
noncomputable instance affineDerivedMinusEquivalence_functor_commShift (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    (affineDerivedMinusEquivalence A).functor.CommShift ℤ := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  change (derivedMinusEquivalence E).functor.CommShift ℤ
  infer_instance

/-- Shift compatibility of the bounded-below affine dictionary. -/
noncomputable instance affineDerivedPlusEquivalence_functor_commShift (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    (affineDerivedPlusEquivalence A).functor.CommShift ℤ := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  change (derivedPlusEquivalence E).functor.CommShift ℤ
  infer_instance

/-- Shift compatibility of the bounded affine dictionary. -/
noncomputable instance affineDerivedBoundedEquivalence_functor_commShift (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    (affineDerivedBoundedEquivalence A).functor.CommShift ℤ := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  change (derivedBoundedEquivalence E).functor.CommShift ℤ
  infer_instance

/-- The bounded-above affine dictionary is triangulated. -/
noncomputable instance affineDerivedMinusEquivalence_functor_isTriangulated
    (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    (affineDerivedMinusEquivalence A).functor.IsTriangulated := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  change (derivedMinusEquivalence E).functor.IsTriangulated
  infer_instance

/-- The bounded-below affine dictionary is triangulated. -/
noncomputable instance affineDerivedPlusEquivalence_functor_isTriangulated
    (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    (affineDerivedPlusEquivalence A).functor.IsTriangulated := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  change (derivedPlusEquivalence E).functor.IsTriangulated
  infer_instance

/-- The bounded affine dictionary is triangulated. -/
noncomputable instance affineDerivedBoundedEquivalence_functor_isTriangulated
    (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)] :
    (affineDerivedBoundedEquivalence A).functor.IsTriangulated := by
  let E := tildeEquiv (R := A)
  let _ : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  change (derivedBoundedEquivalence E).functor.IsTriangulated
  infer_instance

/-! ## The QC-cohomology model and the remaining Stacks 06Z0 input -/

/-- Objects of the derived category of all modules on `Spec A` whose cohomology
sheaves are quasi-coherent.  This is the object predicate underlying Stacks
Project's `D_QCoh(O_{Spec A})`. -/
def QuasicoherentCohomology (A : CommRingCat.{u})
    [HasDerivedCategory.{w₃} (Spec A).Modules] :
    ObjectProperty (DerivedCategory (Spec A).Modules) :=
  fun E => ∀ n : ℤ,
    ((DerivedCategory.homologyFunctor (Spec A).Modules n).obj E).IsQuasicoherent

-- PROVISIONAL: currently only the ordinary categorical comparison is exposed;
-- the canonical triangulated/coherator construction is not yet available in
-- Mathlib and must accompany a full geometric instantiation.
/-- **Remaining input: Stacks Project Lemma 36.3.5 (Tag 06Z0).**  An
instantiation supplies the comparison
`D(QCoh(Spec A)) ≃ D_QCoh(O_{Spec A})`, where the target is the full
subcategory cut out by `QuasicoherentCohomology`.

This field is not used to prove `affineDerivedEquivalence` or any of its
bounded/shift/triangulated compatibilities. -/
structure AffineCohomologyComparison (A : CommRingCat.{u})
    [HasDerivedCategory.{w₂} (QCModules A)]
    [HasDerivedCategory.{w₃} (Spec A).Modules] where
  /-- The comparison in Stacks 06Z0, at the level of ordinary categories. -/
  equivalence : DerivedCategory (QCModules A) ≌
    (QuasicoherentCohomology A).FullSubcategory

/-- The ring dictionary to the QC-cohomology model, after supplying the named
Stacks 06Z0 comparison. -/
noncomputable def affineDerivedCohomologyEquivalence (A : CommRingCat.{u})
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)] [HasDerivedCategory.{w₂} (QCModules A)]
    [HasDerivedCategory.{w₃} (Spec A).Modules]
    (h : AffineCohomologyComparison A) :
    DerivedCategory (ModuleCat.{u} A) ≌
      (QuasicoherentCohomology A).FullSubcategory :=
  (affineDerivedEquivalence A).trans h.equivalence

end RelativeFM
