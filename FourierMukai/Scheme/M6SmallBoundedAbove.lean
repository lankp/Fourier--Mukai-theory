/-
Bounded-above compact objects in the small-Hom affine derived category.

The AB4 coproduct transport and truncation arguments are in `BoundedAbove`.
This file adapts their short affine wrapper to the `u`-small localization,
using coproduct indices `ULift.{u} ℕ` instead of `ULift.{u+1} ℕ`.
-/
import FourierMukai.Scheme.CompactBoundedAbove
import FourierMukai.Scheme.AffineUniverse

@[expose] public section

namespace RelativeFM.CapstoneM6Small

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeFM RelativeFM.DerivedCoproducts RelativeWeakApprox
open CochainComplex
open RelativeFM.Stacks07LT.BoundedAboveM1

universe u

noncomputable section

/-- The localization functor for the explicit small-Hom model. -/
noncomputable abbrev smallDerivedQ (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ SmallAffineD A H :=
  @DerivedCategory.Q (ModuleCat.{u} A) _ _
    (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)

/-- The derived coproduct cocone at the small instance. -/
noncomputable abbrev smallQCoproductCofan (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (F : ℕ → CochainComplex (ModuleCat.{u} A) ℤ) :
    Cofan (fun i => (smallDerivedQ A H).obj (F i)) :=
  @RelativeFM.Stacks07LT.BoundedAboveM1.qCoproductCofan
    (ModuleCat.{u} A) _ _
    (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H) ℕ _ F

/-- Spaltenstein resolution at the small derived-category instance. -/
noncomputable def smallSpaltensteinResolution (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    QuasiIsoKProjectiveResolution K := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  letI : AB5OfSize.{0, 0} (ModuleCat.{u} A) :=
    AB5OfSize_of_univLE (ModuleCat.{u} A)
  exact spaltensteinResolution
    (RelativeFM.Spaltenstein.theoremCInput (C := ModuleCat.{u} A)) K

/-- The canonical truncations have a derived coproduct in the small model. -/
noncomputable def smallAffineTruncationCoproductIsColimit
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsColimit (smallQCoproductCofan A H (truncGEFamily K)) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  let R := fun n => (smallSpaltensteinResolution A H (truncGEFamily K n)).complex
  let f := fun n => (smallSpaltensteinResolution A H (truncGEFamily K n)).π
  letI (n : ℕ) : (R n).IsKProjective := by
    dsimp [R]
    exact (smallSpaltensteinResolution A H (truncGEFamily K n)).isKProjective
  letI (n : ℕ) : QuasiIso (f n) := by
    dsimp [f]
    exact (smallSpaltensteinResolution A H (truncGEFamily K n)).quasiIso
  exact qCoproductCofanIsColimit_of_quasiIso R (truncGEFamily K) f

/-- Compactness makes a canonical lower-truncation map zero in the small
localization. -/
theorem small_exists_piTruncGE_eq_zero_of_isCompactAb
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : IsCompactAb ((smallDerivedQ A H).obj K)) :
    ∃ n : ℕ, (smallDerivedQ A H).map (K.πTruncGE (n : ℤ)) = 0 := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  let S := coproductComplexCocone (truncGEFamily K)
  let pres : ColimitPresentation (Discrete ℕ) (DerivedCategory.Q.obj S.pt) :=
    { diag := Discrete.functor (fun n => DerivedCategory.Q.obj (truncGEFamily K n))
      ι := (qCoproductCofan (truncGEFamily K)).ι
      isColimit := smallAffineTruncationCoproductIsColimit A H K }
  let presU : ColimitPresentation (Discrete (ULift.{u} ℕ))
      (DerivedCategory.Q.obj S.pt) :=
    pres.reindex (Discrete.equivalence Equiv.ulift).functor
  let g : ∀ n : ULift.{u} ℕ,
      DerivedCategory.Q.obj (truncGEFamily K n.down) ⟶ DerivedCategory.Q.obj S.pt :=
    fun n => DerivedCategory.Q.map (S.ι.app ⟨n.down⟩)
  have hg : IsColimit (Cofan.mk (DerivedCategory.Q.obj S.pt) g) := presU.isColimit
  obtain ⟨n, hn⟩ := RelativeFM.Stacks07LT.exists_comp_coproductProjection_eq_zero
    (J := ULift.{u} ℕ) hK
    (fun n : ULift.{u} ℕ => DerivedCategory.Q.obj (truncGEFamily K n.down))
    g hg (DerivedCategory.Q.map (truncationDiagonal K))
  have hp : RelativeWeakApprox.coproductProjection g hg n =
      DerivedCategory.Q.map (natCoproductProjection (truncGEFamily K) n.down) := by
    apply hg.hom_ext
    intro j
    change g j.as ≫ RelativeWeakApprox.coproductProjection g hg n =
      g j.as ≫ DerivedCategory.Q.map (natCoproductProjection (truncGEFamily K) n.down)
    rw [RelativeWeakApprox.coproductProjection_comp]
    dsimp [g]
    rw [← DerivedCategory.Q.map_comp, natCoproductProjection_inj]
    by_cases h : j.as = n
    · subst n
      simp
    · have hd : j.as.down ≠ n.down := by
        intro hd
        exact h (ULift.ext _ _ hd)
      simp [h, hd]
  rw [hp] at hn
  refine ⟨n.down, ?_⟩
  rw [← DerivedCategory.Q.map_comp, truncationDiagonal_comp_projection] at hn
  exact hn

/-- A compact `Q`-image is bounded above in the small model. -/
theorem small_exists_isLE_Q_obj_of_isCompactAb
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : IsCompactAb ((smallDerivedQ A H).obj K)) :
    ∃ n : ℤ, @DerivedCategory.IsLE (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)
      ((smallDerivedQ A H).obj K) n := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  obtain ⟨n, hn⟩ := small_exists_piTruncGE_eq_zero_of_isCompactAb A H K hK
  exact exists_isLE_Q_obj_of_piTruncGE_eq_zero K (n : ℤ) hn

/-- Every compact object of the small-Hom affine derived category is bounded
above for its standard `t`-structure. -/
theorem small_exists_isLE_of_isCompactAb
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (X : SmallAffineD A H) (hX : IsCompactAb X) :
    ∃ n : ℤ, (@DerivedCategory.TStructure.t (ModuleCat.{u} A) _ _
      (UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H)).IsLE X n := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hpre : IsCompactAb (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X)) :=
    isCompactAb_of_iso e.symm hX
  obtain ⟨n, hn⟩ := small_exists_isLE_Q_obj_of_isCompactAb A H
    (DerivedCategory.Q.objPreimage X) hpre
  letI : DerivedCategory.IsLE (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X)) n := hn
  exact ⟨n, DerivedCategory.TStructure.t.isLE_of_iso e n⟩

end

end RelativeFM.CapstoneM6Small

#print axioms RelativeFM.CapstoneM6Small.smallSpaltensteinResolution
#print axioms RelativeFM.CapstoneM6Small.smallAffineTruncationCoproductIsColimit
#print axioms RelativeFM.CapstoneM6Small.small_exists_piTruncGE_eq_zero_of_isCompactAb
#print axioms RelativeFM.CapstoneM6Small.small_exists_isLE_Q_obj_of_isCompactAb
#print axioms RelativeFM.CapstoneM6Small.small_exists_isLE_of_isCompactAb
