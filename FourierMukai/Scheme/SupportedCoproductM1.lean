import FourierMukai.Scheme.AffineSupportedBaseM1

/-!
# Supported coproducts without a global large-coproduct instance

The proofs use only a presented ambient colimit.  A coreflective full
subcategory has the corresponding colimit, and its left-adjoint inclusion
preserves it; no global coproduct-existence hypothesis is needed.
-/

@[expose] public section

namespace RelativeFM.SupportedCoproductM1

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe w v u

noncomputable section

/-- A coreflective full subcategory is closed under every ambient colimit
which is actually presented. -/
def isClosedUnderColimitsOfShape_coreflective
    {C : Type u} [Category.{v} C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] [Coreflective P.ι]
    (J : Type w) [Category.{w} J] :
    P.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    let D := P.lift p.diag p.prop_diag_obj
    letI : HasColimit (D ⋙ P.ι) := p.hasColimit
    letI : HasColimit D := hasColimit_of_coreflective D P.ι
    exact P.prop_of_iso (IsColimit.coconePointUniqueUpToIso
      (isColimitOfPreserves P.ι (colimit.isColimit D)) p.isColimit)
      (colimit D).property

/-- Ambient coproduct-and-extension closure of the shifts of a supported
object stays supported.  Unlike the earlier version, this uses no global
coproduct existence. -/
lemma affineIsSupported_of_ambient_coprod (A : Type u) [CommRing A] (f : A)
    (GU : AffineDZ A f) {X : AffineD A}
    (hX : Coprod (shiftTail GU.obj 0) X) : AffineIsSupported A f X := by
  let P := AffineIsSupported A f
  letI : P.IsClosedUnderIsomorphisms := by
    dsimp [P]
    unfold AffineIsSupported
    infer_instance
  letI (J : Type (u + 1)) : P.IsClosedUnderColimitsOfShape (Discrete J) :=
    isClosedUnderColimitsOfShape_coreflective P (Discrete J)
  refine Coprod.le (Q := P) ?_ X hX
  rintro Y ⟨n, hn, ⟨e⟩⟩
  exact P.prop_of_iso e.symm (P.le_shift n GU.obj GU.property)

/-- Lift an ambient `Coprod` presentation to the principal supported
subcategory, using only the colimits occurring in that presentation. -/
lemma supported_coprod_of_ambient (A : Type u) [CommRing A] (f : A)
    (GU : AffineDZ A f) {X : AffineDZ A f}
    (hX : Coprod (shiftTail GU.obj 0) X.obj) : Coprod (shiftTail GU 0) X := by
  let P := AffineIsSupported A f
  have hP : ∀ {Y : AffineD A}, Coprod (shiftTail GU.obj 0) Y → P Y :=
    fun {Y} hY => affineIsSupported_of_ambient_coprod A f GU hY
  let rep : ∀ {Y : AffineD A}, Coprod (shiftTail GU.obj 0) Y → AffineDZ A f :=
    fun {Y} hY => ⟨Y, hP hY⟩
  have main : ∀ {Y : AffineD A} (hY : Coprod (shiftTail GU.obj 0) Y),
      Coprod (shiftTail GU 0) (rep hY) := by
    intro Y hY
    induction hY with
    | of_mem Y hY =>
        obtain ⟨n, hn, ⟨e⟩⟩ := hY
        let e' : rep (Coprod.of_mem Y ⟨n, hn, ⟨e⟩⟩) ≅ GU⟦n⟧ :=
          P.fullyFaithfulι.preimageIso
            (e ≪≫ ((affineDZι A f).commShiftIso n).symm.app GU)
        exact Coprod.of_isoClosure e'.symm (Coprod.of_mem _ ⟨n, hn, ⟨Iso.refl _⟩⟩)
    | of_isoClosure e hY ih =>
        let e' : rep hY ≅ rep (Coprod.of_isoClosure e hY) :=
          P.fullyFaithfulι.preimageIso e
        exact Coprod.of_isoClosure e' ih
    | @of_colimitPresentation Y J pres hmem ih =>
        let D : Discrete J ⥤ AffineDZ A f :=
          P.lift pres.diag (fun j => hP (hmem j))
        letI : HasColimit (D ⋙ affineDZι A f) := pres.hasColimit
        letI : HasColimit D := hasColimit_of_coreflective D (affineDZι A f)
        let e : colimit D ≅ rep (Coprod.of_colimitPresentation pres hmem) :=
          P.fullyFaithfulι.preimageIso
            ((isColimitOfPreserves (affineDZι A f)
              (colimit.isColimit D)).coconePointUniqueUpToIso pres.isColimit)
        apply Coprod.of_isoClosure e
        apply Coprod.of_colimitPresentation (ColimitPresentation.colimit D)
        intro j
        exact ih j
    | of_extension T hT h₁ h₃ ih₁ ih₃ =>
        let f₁ : rep h₁ ⟶ rep (Coprod.of_extension T hT h₁ h₃) :=
          P.fullyFaithfulι.preimage T.mor₁
        let f₂ : rep (Coprod.of_extension T hT h₁ h₃) ⟶ rep h₃ :=
          P.fullyFaithfulι.preimage T.mor₂
        let f₃ : rep h₃ ⟶ (rep h₁)⟦(1 : ℤ)⟧ :=
          P.fullyFaithfulι.preimage
            (T.mor₃ ≫ ((affineDZι A f).commShiftIso (1 : ℤ)).inv.app (rep h₁))
        let T' : Triangle (AffineDZ A f) := Triangle.mk f₁ f₂ f₃
        have hT' : T' ∈ distTriang (AffineDZ A f) := by
          change (affineDZι A f).mapTriangle.obj T' ∈ distTriang (AffineD A)
          dsimp [T', f₁, f₂, f₃, Functor.mapTriangle]
          with_unfolding_all
            change Triangle.mk T.mor₁ T.mor₂
              ((T.mor₃ ≫ ((affineDZι A f).commShiftIso (1 : ℤ)).inv.app (rep h₁)) ≫
                ((affineDZι A f).commShiftIso (1 : ℤ)).hom.app (rep h₁)) ∈
              distTriang (AffineD A)
          rw [Category.assoc, Iso.inv_hom_id_app]
          convert hT using 1
          cases T
          rename_i X₁ X₂ X₃ m₁ m₂ m₃
          change Triangle.mk m₁ m₂ (m₃ ≫ 𝟙 ((shiftFunctor (AffineD A) 1).obj X₁)) = _
          rw [Category.comp_id]
          rfl
        exact Coprod.of_extension T' hT' ih₁ ih₃
  let e : rep hX ≅ X := P.fullyFaithfulι.preimageIso (Iso.refl X.obj)
  exact Coprod.of_isoClosure e (main hX)

/-- Supported and ambient `Coprod` constructions agree, without any global
coproduct-existence assumption. -/
lemma supported_coprod_iff_ambient (A : Type u) [CommRing A] (f : A)
    (GU : AffineDZ A f) (X : AffineDZ A f) :
    Coprod (shiftTail GU 0) X ↔ Coprod (shiftTail GU.obj 0) X.obj :=
  ⟨SupportedAisleM6.map_supported_coprod GU,
    supported_coprod_of_ambient A f GU⟩


/-- The unshifted-interval version of support closure under ambient coproduct
and extension. -/
lemma affineIsSupported_of_ambient_coprod_interval (A : Type u) [CommRing A]
    (f : A) (GU : AffineDZ A f) (a b : ℤ) {X : AffineD A}
    (hX : Coprod (shiftInterval GU.obj a b) X) : AffineIsSupported A f X := by
  let P := AffineIsSupported A f
  letI : P.IsClosedUnderIsomorphisms := by
    dsimp [P]
    unfold AffineIsSupported
    infer_instance
  letI (J : Type (u + 1)) : P.IsClosedUnderColimitsOfShape (Discrete J) :=
    isClosedUnderColimitsOfShape_coreflective P (Discrete J)
  refine Coprod.le (Q := P) ?_ X hX
  rintro Y ⟨n, hn₀, hn₁, ⟨e⟩⟩
  exact P.prop_of_iso e.symm (P.le_shift (-n) GU.obj GU.property)

/-- Lift the coproduct closure of any ambient object property to its inverse
image in the supported category. -/
lemma supported_coprod_preimage_of_ambient (A : Type u) [CommRing A] (f : A)
    (P : ObjectProperty (AffineD A))
    (hPS : ∀ {Y : AffineD A}, Coprod P Y → AffineIsSupported A f Y)
    {X : AffineDZ A f} (hX : Coprod P X.obj) :
    Coprod (P.inverseImage (affineDZι A f)) X := by
  let S := AffineIsSupported A f
  let rep : ∀ {Y : AffineD A}, Coprod P Y → AffineDZ A f :=
    fun {Y} hY => ⟨Y, hPS hY⟩
  have main : ∀ {Y : AffineD A} (hY : Coprod P Y),
      Coprod (P.inverseImage (affineDZι A f)) (rep hY) := by
    intro Y hY
    induction hY with
    | of_mem Y hY =>
        exact Coprod.of_mem _ hY
    | of_isoClosure e hY ih =>
        let e' : rep hY ≅ rep (Coprod.of_isoClosure e hY) :=
          S.fullyFaithfulι.preimageIso e
        exact Coprod.of_isoClosure e' ih
    | @of_colimitPresentation Y J pres hmem ih =>
        let D : Discrete J ⥤ AffineDZ A f :=
          S.lift pres.diag (fun j => (rep (hmem j)).property)
        letI : HasColimit (D ⋙ affineDZι A f) := pres.hasColimit
        letI : HasColimit D := hasColimit_of_coreflective D (affineDZι A f)
        let e : colimit D ≅ rep (Coprod.of_colimitPresentation pres hmem) :=
          S.fullyFaithfulι.preimageIso
            ((isColimitOfPreserves (affineDZι A f)
              (colimit.isColimit D)).coconePointUniqueUpToIso pres.isColimit)
        apply Coprod.of_isoClosure e
        apply Coprod.of_colimitPresentation (ColimitPresentation.colimit D)
        intro j
        exact ih j
    | of_extension T hT h₁ h₃ ih₁ ih₃ =>
        let f₁ : rep h₁ ⟶ rep (Coprod.of_extension T hT h₁ h₃) :=
          S.fullyFaithfulι.preimage T.mor₁
        let f₂ : rep (Coprod.of_extension T hT h₁ h₃) ⟶ rep h₃ :=
          S.fullyFaithfulι.preimage T.mor₂
        let f₃ : rep h₃ ⟶ (rep h₁)⟦(1 : ℤ)⟧ :=
          S.fullyFaithfulι.preimage
            (T.mor₃ ≫ ((affineDZι A f).commShiftIso (1 : ℤ)).inv.app (rep h₁))
        let T' : Triangle (AffineDZ A f) := Triangle.mk f₁ f₂ f₃
        have hT' : T' ∈ distTriang (AffineDZ A f) := by
          change (affineDZι A f).mapTriangle.obj T' ∈ distTriang (AffineD A)
          dsimp [T', f₁, f₂, f₃, Functor.mapTriangle]
          with_unfolding_all
            change Triangle.mk T.mor₁ T.mor₂
              ((T.mor₃ ≫ ((affineDZι A f).commShiftIso (1 : ℤ)).inv.app (rep h₁)) ≫
                ((affineDZι A f).commShiftIso (1 : ℤ)).hom.app (rep h₁)) ∈
              distTriang (AffineD A)
          rw [Category.assoc, Iso.inv_hom_id_app]
          convert hT using 1
          cases T
          rename_i X₁ X₂ X₃ m₁ m₂ m₃
          change Triangle.mk m₁ m₂ (m₃ ≫ 𝟙 ((shiftFunctor (AffineD A) 1).obj X₁)) = _
          rw [Category.comp_id]
          rfl
        exact Coprod.of_extension T' hT' ih₁ ih₃
  let e : rep hX ≅ X := S.fullyFaithfulι.preimageIso (Iso.refl X.obj)
  exact Coprod.of_isoClosure e (main hX)

/-- Shift intervals are computed identically in the supported category and in
its ambient derived category. -/
lemma shiftInterval_inverseImage (A : Type u) [CommRing A] (f : A)
    (G : AffineDZ A f) (a b : ℤ) :
    (shiftInterval G.obj a b).inverseImage (affineDZι A f) = shiftInterval G a b := by
  ext X
  constructor
  · rintro ⟨k, hk₀, hk₁, ⟨e⟩⟩
    exact ⟨k, hk₀, hk₁, ⟨(AffineIsSupported A f).fullyFaithfulι.preimageIso
      (e ≪≫ ((affineDZι A f).commShiftIso (-k)).symm.app G)⟩⟩
  · rintro ⟨k, hk₀, hk₁, ⟨e⟩⟩
    exact ⟨k, hk₀, hk₁, ⟨(affineDZι A f).mapIso e ≪≫
      ((affineDZι A f).commShiftIso (-k)).app G⟩⟩

end

end RelativeFM.SupportedCoproductM1

#print axioms RelativeFM.SupportedCoproductM1.isClosedUnderColimitsOfShape_coreflective
#print axioms RelativeFM.SupportedCoproductM1.affineIsSupported_of_ambient_coprod
#print axioms RelativeFM.SupportedCoproductM1.supported_coprod_of_ambient
#print axioms RelativeFM.SupportedCoproductM1.supported_coprod_preimage_of_ambient
#print axioms RelativeFM.SupportedCoproductM1.shiftInterval_inverseImage
#print axioms RelativeFM.SupportedCoproductM1.supported_coprod_iff_ambient
