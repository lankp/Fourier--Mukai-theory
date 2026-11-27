import FourierMukai.Scheme.AffineCoproducts
import Mathlib.CategoryTheory.Localization.LocallySmall
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

@[expose] public section

namespace RelativeFM.UniverseDecision

open CategoryTheory CategoryTheory.Limits
open RelativeFM DerivedCoproducts

universe w v u

noncomputable section

/-- Module coproducts exist at every index universe no larger than the
universe of module carriers. -/
instance moduleCat_hasCoproducts (A : Type u) [CommRing A] [UnivLE.{w, u}] :
    HasCoproducts.{w} (ModuleCat.{u} A) := inferInstance

example (A : Type u) [CommRing A] :
    HasCoproducts.{u} (ModuleCat.{u} A) := inferInstance

example (A : Type u) [CommRing A] :
    HasCoproducts.{0} (ModuleCat.{u} A) := inferInstance

variable {C : Type u} [Category.{v} C] [Abelian C]

attribute [local instance] HasDerivedCategory.standard

/-- K-projective replacements make the standard derived category locally
small at the hom universe of `C`: every derived Hom is equivalent to a
homotopy-category Hom out of a K-projective replacement of the source. -/
noncomputable def locallySmallDerivedCategoryOfKProjectiveReplacementData
    (H : KProjectiveReplacementData C) :
    LocallySmall.{v} (DerivedCategory C) where
  hom_small X Y := by
    let K := (H.resolution X).complex
    let L := DerivedCategory.Q.objPreimage Y
    letI : K.IsKProjective := (H.resolution X).isKProjective
    let eKX : DerivedCategory.Q.obj K ≅ X := (H.resolution X).iso
    let eLY : DerivedCategory.Q.obj L ≅ Y := DerivedCategory.Q.objObjPreimageIso Y
    exact small_map ((derivedHomKProjectiveEquiv K L).trans (Iso.homCongr eKX eLY)).symm

/-- Spaltenstein replacements give a derived category whose morphisms live in
the original hom universe, not in the larger `max (object universe) v`
universe of the standard localization. -/
noncomputable def hasDerivedCategoryOfKProjectiveReplacementData
    (H : KProjectiveReplacementData C) :
    HasDerivedCategory.{v} C := by
  letI : LocallySmall.{v} (DerivedCategory C) :=
    locallySmallDerivedCategoryOfKProjectiveReplacementData H
  exact MorphismProperty.hasLocalizationOfLocallySmall'
    (HomologicalComplex.quasiIso C (.up ℤ)) DerivedCategory.Q

end

end RelativeFM.UniverseDecision

namespace RelativeFM.UniverseDecision

open CategoryTheory CategoryTheory.Limits
open RelativeFM DerivedCoproducts

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Transport Spaltenstein replacement data from the standard localization to
the `v`-small localization constructed above. The comparison map is lifted to
the homotopy category using K-projectivity; it is a quasi-isomorphism because
its image in the standard derived category is an isomorphism. -/
noncomputable def kProjectiveReplacementDataOfHasDerivedCategory
    (H : @KProjectiveReplacementData C _ _ (HasDerivedCategory.standard C)) :
    letI : HasDerivedCategory.{v} C := hasDerivedCategoryOfKProjectiveReplacementData H
    KProjectiveReplacementData C := by
  letI : HasDerivedCategory.{v} C := hasDerivedCategoryOfKProjectiveReplacementData H
  refine ⟨fun X => ?_⟩
  let L : CochainComplex C ℤ := DerivedCategory.Q.objPreimage X
  let R := @KProjectiveReplacementData.resolution C _ _ (HasDerivedCategory.standard C) H
    ((@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C)).obj L)
  let K : CochainComplex C ℤ :=
    @KProjectiveResolution.complex C _ _ (HasDerivedCategory.standard C) _ R
  letI : K.IsKProjective :=
    @KProjectiveResolution.isKProjective C _ _ (HasDerivedCategory.standard C) _ R
  let eR := @KProjectiveResolution.iso C _ _ (HasDerivedCategory.standard C) _ R
  let f : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L :=
    (@derivedHomKProjectiveEquiv C _ _ (HasDerivedCategory.standard C) K L
      (inferInstanceAs K.IsKProjective)).symm eR.hom
  have hf : @derivedHomMap C _ _ (HasDerivedCategory.standard C) K L f = eR.hom := by
    exact (@derivedHomKProjectiveEquiv C _ _ (HasDerivedCategory.standard C) K L
      (inferInstanceAs K.IsKProjective)).apply_symm_apply eR.hom
  have hfIso : IsIso (@derivedHomMap C _ _ (HasDerivedCategory.standard C) K L f) := by
    rw [hf]
    infer_instance
  change IsIso ((@DerivedCategory.quotientCompQhIso C _ _
      (HasDerivedCategory.standard C)).inv.app K ≫
    (@DerivedCategory.Qh C _ _ (HasDerivedCategory.standard C)).map f ≫
    (@DerivedCategory.quotientCompQhIso C _ _
      (HasDerivedCategory.standard C)).hom.app L) at hfIso
  letI : IsIso ((@DerivedCategory.quotientCompQhIso C _ _
      (HasDerivedCategory.standard C)).inv.app K ≫
    (@DerivedCategory.Qh C _ _ (HasDerivedCategory.standard C)).map f ≫
    (@DerivedCategory.quotientCompQhIso C _ _
      (HasDerivedCategory.standard C)).hom.app L) := hfIso
  have hfstab : IsIso ((@DerivedCategory.quotientCompQhIso C _ _
      (HasDerivedCategory.standard C)).inv.app K ≫
    (@DerivedCategory.Qh C _ _ (HasDerivedCategory.standard C)).map f) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _
      ((@DerivedCategory.quotientCompQhIso C _ _
        (HasDerivedCategory.standard C)).hom.app L) (by infer_instance)
      (by simpa only [Category.assoc] using hfIso)
  letI : IsIso ((@DerivedCategory.quotientCompQhIso C _ _
      (HasDerivedCategory.standard C)).inv.app K ≫
    (@DerivedCategory.Qh C _ _ (HasDerivedCategory.standard C)).map f) := hfstab
  have hfb : IsIso ((@DerivedCategory.Qh C _ _ (HasDerivedCategory.standard C)).map f) :=
    IsIso.of_isIso_comp_left ((@DerivedCategory.quotientCompQhIso C _ _
      (HasDerivedCategory.standard C)).inv.app K) _
  letI : IsIso ((@DerivedCategory.Qh C _ _ (HasDerivedCategory.standard C)).map f) := hfb
  have hq : QuasiIso f.out := by
    change HomologicalComplex.quasiIso C (.up ℤ) f.out
    apply (HomotopyCategory.quotient_map_mem_quasiIso_iff f.out).1
    rw [HomotopyCategory.quotient_map_out]
    exact (@DerivedCategory.isIso_Qh_map_iff C _ _ (HasDerivedCategory.standard C) _ _ f).1 hfb
  exact
    { complex := K
      isKProjective := inferInstance
      iso := Localization.isoOfHom DerivedCategory.Q
        (HomologicalComplex.quasiIso C (.up ℤ)) f.out hq ≪≫
        DerivedCategory.Q.objObjPreimageIso X }

end

end RelativeFM.UniverseDecision

namespace RelativeFM.UniverseDecision

open CategoryTheory CategoryTheory.Limits
open RelativeFM DerivedCoproducts

universe w v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In the small localization, replacement data and `w`-small coproducts in
`C` give `w`-small derived coproducts. This is the existing derived-coproduct
theorem, now with the localization at hom universe `v`. -/
noncomputable def hasCoproductsOfKProjectiveReplacementDataSmall
    (H : @KProjectiveReplacementData C _ _ (HasDerivedCategory.standard C))
    [HasCoproducts.{w} C] :
    letI : HasDerivedCategory.{v} C := hasDerivedCategoryOfKProjectiveReplacementData H
    HasCoproducts.{w} (DerivedCategory C) := by
  letI : HasDerivedCategory.{v} C := hasDerivedCategoryOfKProjectiveReplacementData H
  exact DerivedCoproducts.hasCoproductsOfKProjectiveReplacementData
    (kProjectiveReplacementDataOfHasDerivedCategory H)

end

end RelativeFM.UniverseDecision

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits
open RelativeWeakApprox
open UniverseDecision DerivedCoproducts

universe u uZ uU

noncomputable section

/-- The affine derived category with `u`-small morphisms, constructed from
Spaltenstein replacement data. Unlike the standard `AffineD`, its category
instance has hom universe `u`, not `u+1`. -/
abbrev SmallAffineD (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    Type (u + 1) :=
  @DerivedCategory (ModuleCat.{u} A) _ _
    (hasDerivedCategoryOfKProjectiveReplacementData H)

example (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    Category.{u} (SmallAffineD A H) := inferInstance

/-- The required middle coproduct instance at the same universe used by the
LP layer. -/
noncomputable def smallAffineHasCoproducts
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    HasCoproducts.{u} (SmallAffineD A H) :=
  hasCoproductsOfKProjectiveReplacementDataSmall H

section Categories

variable (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
  (DZ : Type uZ) (DU : Type uU)
  [Category.{u} DZ] [Category.{u} DU]
  [Preadditive DZ] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DU]

/-- Universe-correct replacement for `AffineDerivedCoproducts` when the small
localization is used. -/
structure SmallAffineDerivedCoproducts where
  hasCoproductsZ : HasCoproducts.{u} DZ
  hasCoproductsA : HasCoproducts.{u} (SmallAffineD A H)
  hasCoproductsU : HasCoproducts.{u} DU

/-- Only the two end coproduct instances remain inputs: Spaltenstein supplies
the middle one. -/
noncomputable def smallAffineDerivedCoproductsOfSpaltenstein
    [HasCoproducts.{u} DZ] [HasCoproducts.{u} DU] :
    SmallAffineDerivedCoproducts A H DZ DU where
  hasCoproductsZ := inferInstance
  hasCoproductsA := smallAffineHasCoproducts A H
  hasCoproductsU := inferInstance

end Categories

end

end RelativeFM

#print axioms RelativeFM.UniverseDecision.locallySmallDerivedCategoryOfKProjectiveReplacementData
#print axioms RelativeFM.UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData
#print axioms RelativeFM.UniverseDecision.kProjectiveReplacementDataOfHasDerivedCategory
#print axioms RelativeFM.UniverseDecision.hasCoproductsOfKProjectiveReplacementDataSmall
#print axioms RelativeFM.smallAffineHasCoproducts

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits
open RelativeWeakApprox
open UniverseDecision DerivedCoproducts

universe w u

noncomputable section

/-- At every index universe admitted by the module-carrier universe, the
standard (large-Hom) affine derived category has coproducts. -/
noncomputable def affineHasCoproductsOfUnivLE
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) [UnivLE.{w, u}] :
    HasCoproducts.{w} (AffineD A) :=
  affine_hasCoproducts_of_spaltenstein A H

/-- The same size-polymorphic statement for the `u`-small-Hom affine model. -/
noncomputable def smallAffineHasCoproductsOfUnivLE
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) [UnivLE.{w, u}] :
    HasCoproducts.{w} (SmallAffineD A H) :=
  hasCoproductsOfKProjectiveReplacementDataSmall H

/-- The small-Hom and standard derived categories are equivalent by uniqueness
of localization. Their `Q` functors are the ones used in the comparison. -/
noncomputable def affineDEquivSmallAffineD
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    AffineD A ≌ SmallAffineD A H := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    hasDerivedCategoryOfKProjectiveReplacementData H
  exact Localization.uniq
    (@DerivedCategory.Q (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
    (@DerivedCategory.Q (ModuleCat.{u} A) _ _
      (hasDerivedCategoryOfKProjectiveReplacementData H))
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ))

end

end RelativeFM

#print axioms RelativeFM.affineHasCoproductsOfUnivLE
#print axioms RelativeFM.smallAffineHasCoproductsOfUnivLE
#print axioms RelativeFM.affineDEquivSmallAffineD
