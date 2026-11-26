import FourierMukai.Scheme.FiniteKoszulM1
import FourierMukai.Scheme.PrincipalH0CoverM1
import FourierMukai.Scheme.KoszulSupportAdjoint
import FourierMukai.Scheme.KoszulFiniteInputs

/-!
# Finite ideal-supported weak approximation

LP26 Corollary 1.2 (`cor:weak_approx_spaces`), affine base case = Neeman, *Acta
Math.* 233 (2024), Theorem 3.2(iv) for `Spec A`, `Z = V(f₁,…,fₙ)`, in the module
model `AffineD A = D(A-Mod)` with the ideal-supported subcategory
`AffineDZIdeal A (functionIdeal A fs)`.

The four inputs the finite-list argument used to carry are now theorems:

* `IdealSupportedCoproductInput`, `IdealSupportedCompactnessInput` (supported direct
  sums; the inclusion is a left adjoint, `KoszulInputs.isLeftAdjoint_affineDZIdealι`):
  `KoszulInputs.idealSupportedCoproductInput`, `KoszulInputs.idealSupportedCompactnessInput`;
* `KoszulPowerCoprodInput` (Neeman, Construction 7.3):
  `FiniteKoszulM1.koszulPowerCoprodInput`, from `KoszulFiniteInputs.koszulList_power_coprod`;
* `KoszulDetectionInput` (finite Koszul zero detection; formerly labelled Stacks
  0A9A, which it is not): `StacksInterface.koszulDetectionInput`, from
  `KoszulFiniteInputs.koszulList_detects_zero`.

The refuted `KoszulScalarSupportInput` is no longer an argument of anything.
`satisfiesPaperWA_idealSupported` keeps only the ambient regular compactness
`hAc : IsCompactAb (ringObject A)` (as the pinned principal theorem does); it is
discharged in `NeemanAffineSupport.lean`, which states the result with no
hypothesis.  The approximation is proved by the free cover and finite simultaneous
Koszul factorization.
-/

@[expose] public section

namespace RelativeFM.FiniteKoszulM1

open RelativeFM RelativeWeakApprox

universe u

/-- **Neeman Construction 7.3.** The finite-power coproduct envelope, with no
approximation or weak-approximability assertion built into the statement.
(Formerly it also took the refuted `hS : KoszulScalarSupportInput A`.) -/
structure KoszulPowerCoprodInput (A : Type u) [CommRing A] (fs : List A) : Prop where
  power : ∀ ns : List ℕ, ns.length = fs.length →
    Coprod (shiftInterval (koszulListData A (unitExponents A fs)).obj 0 0)
      (koszulListData A (fs.zip ns)).obj

/-- **Neeman Construction 7.3, proved** for every finite list
(`KoszulFiniteInputs.koszulList_power_coprod`). -/
theorem koszulPowerCoprodInput (A : Type u) [CommRing A] (fs : List A) :
    KoszulPowerCoprodInput A fs :=
  ⟨fun ns h => KoszulFiniteInputs.koszulList_power_coprod fs ns h⟩

end RelativeFM.FiniteKoszulM1

namespace RelativeFM.StacksInterface

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open RelativeFM.NeemanFiniteSupportM4

universe w u

/-- **Stacks, supported direct sums.** The power-torsion supported class is
closed under presented coproducts. -/
structure IdealSupportedCoproductInput (A : Type u) [CommRing A] (I : Ideal A) : Prop where
  closed : ∀ (J : Type (u + 1)),
    (AffineIsSupportedIdeal A I).IsClosedUnderColimitsOfShape (Discrete J)

/-- **Stacks 09M1, supported-direct-sum form.** Compactness descends to the
ideal-supported full subcategory because its inclusion preserves coproducts. -/
structure IdealSupportedCompactnessInput (A : Type u) [CommRing A] (I : Ideal A) : Prop where
  preserves : ∀ (J : Type (u + 1)),
    PreservesColimitsOfShape (Discrete J) (affineDZIdealι A I)

/-- **Finite Koszul zero detection.** The degree-one finite Koszul object detects
zero on its supported derived category.  (Formerly labelled Stacks 0A9A, but 0A9A
is the existence of a perfect generator of `D_{QCoh,T}`, a different statement;
formerly it also took the refuted `hS : KoszulScalarSupportInput A`.) -/
structure KoszulDetectionInput (A : Type u) [CommRing A] (fs : List A) : Prop where
  detect : ∀ F : AffineD A, AffineIsSupportedIdeal A (FiniteKoszulM1.functionIdeal A fs) F →
    (∀ k : ℤ, ∀ g : (FiniteKoszulM1.koszulListData A
      (FiniteKoszulM1.unitExponents A fs)).obj⟦k⟧ ⟶ F, g = 0) → IsZero F

/-- **Finite Koszul zero detection, proved** for every finite list
(`KoszulFiniteInputs.koszulList_detects_zero`). -/
theorem koszulDetectionInput (A : Type u) [CommRing A] (fs : List A) :
    KoszulDetectionInput A fs :=
  ⟨KoszulFiniteInputs.koszulList_detects_zero fs⟩

end RelativeFM.StacksInterface

namespace RelativeFM.KoszulInputs

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open RelativeFM.NeemanFiniteSupportM4
open RelativeFM.FiniteKoszulM1

universe u

variable (A : Type u) [CommRing A]

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

end RelativeFM.KoszulInputs

namespace RelativeFM.StacksInterface

end RelativeFM.StacksInterface

namespace RelativeFM.IdealNeemanM1

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open RelativeFM.SupportedAisleM6.Koszul
open RelativeFM.NeemanFiniteSupportM4
open RelativeFM.FiniteKoszulM1
open RelativeFM.StacksInterface

universe w u

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HasDerivedCategory.standard

/-- Ideal-support closure for an ambient coproduct-and-extension closure. -/
lemma affineIsSupportedIdeal_of_ambient_coprod_interval
    (A : Type u) [CommRing A] (I : Ideal A)
    (hD : IdealSupportedCoproductInput A I)
    (G : AffineDZIdeal A I) (a b : ℤ) {X : AffineD A}
    (hX : Coprod (shiftInterval G.obj a b) X) : AffineIsSupportedIdeal A I X := by
  let P := AffineIsSupportedIdeal A I
  letI : P.IsClosedUnderIsomorphisms := by
    dsimp [P]
    unfold AffineIsSupportedIdeal
    infer_instance
  letI (J : Type (u + 1)) : P.IsClosedUnderColimitsOfShape (Discrete J) := hD.closed J
  refine Coprod.le (Q := P) ?_ X hX
  rintro Y ⟨n, hn₀, hn₁, ⟨e⟩⟩
  exact P.prop_of_iso e.symm (P.le_shift (-n) G.obj G.property)

/-- Lift an ambient coproduct closure to an ideal-supported category using its
explicit direct-sum closure input. -/
lemma supported_coprod_preimage_of_ambient_ideal
    (A : Type u) [CommRing A] (I : Ideal A)
    (hD : IdealSupportedCoproductInput A I)
    (P : ObjectProperty (AffineD A))
    (hPS : ∀ {Y : AffineD A}, Coprod P Y → AffineIsSupportedIdeal A I Y)
    {X : AffineDZIdeal A I} (hX : Coprod P X.obj) :
    Coprod (P.inverseImage (affineDZIdealι A I)) X := by
  let S := AffineIsSupportedIdeal A I
  let rep : ∀ {Y : AffineD A}, Coprod P Y → AffineDZIdeal A I :=
    fun {Y} hY => ⟨Y, hPS hY⟩
  have main : ∀ {Y : AffineD A} (hY : Coprod P Y),
      Coprod (P.inverseImage (affineDZIdealι A I)) (rep hY) := by
    intro Y hY
    induction hY with
    | of_mem Y hY => exact Coprod.of_mem _ hY
    | of_isoClosure e hY ih =>
        let e' : rep hY ≅ rep (Coprod.of_isoClosure e hY) :=
          S.fullyFaithfulι.preimageIso e
        exact Coprod.of_isoClosure e' ih
    | @of_colimitPresentation Y J pres hmem ih =>
        let D : Discrete J ⥤ AffineDZIdeal A I :=
          S.lift pres.diag (fun j => (rep (hmem j)).property)
        letI : HasColimit (D ⋙ affineDZIdealι A I) := pres.hasColimit
        letI : (AffineIsSupportedIdeal A I).IsClosedUnderColimitsOfShape (Discrete J) :=
          hD.closed J
        letI : HasColimit D :=
          hasColimit_of_closedUnderColimits (Discrete J) (AffineIsSupportedIdeal A I) D
        letI : CreatesColimit D (affineDZIdealι A I) :=
          createsColimitFullSubcategoryInclusionOfClosed (Discrete J) (AffineIsSupportedIdeal A I) D
        let e : colimit D ≅ rep (Coprod.of_colimitPresentation pres hmem) :=
          S.fullyFaithfulι.preimageIso
            ((isColimitOfPreserves (affineDZIdealι A I)
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
            (T.mor₃ ≫ ((affineDZIdealι A I).commShiftIso (1 : ℤ)).inv.app (rep h₁))
        let T' : Triangle (AffineDZIdeal A I) := Triangle.mk f₁ f₂ f₃
        have hT' : T' ∈ distTriang (AffineDZIdeal A I) := by
          change (affineDZIdealι A I).mapTriangle.obj T' ∈ distTriang (AffineD A)
          dsimp [T', f₁, f₂, f₃, Functor.mapTriangle]
          with_unfolding_all
            change Triangle.mk T.mor₁ T.mor₂
              ((T.mor₃ ≫ ((affineDZIdealι A I).commShiftIso (1 : ℤ)).inv.app (rep h₁)) ≫
                ((affineDZIdealι A I).commShiftIso (1 : ℤ)).hom.app (rep h₁)) ∈
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

/-- Shift intervals in an ideal-supported category agree with their ambient
presentation. -/
lemma shiftInterval_inverseImage_ideal (A : Type u) [CommRing A] (I : Ideal A)
    (G : AffineDZIdeal A I) (a b : ℤ) :
    (shiftInterval G.obj a b).inverseImage (affineDZIdealι A I) = shiftInterval G a b := by
  ext X
  constructor
  · rintro ⟨k, hk₀, hk₁, ⟨e⟩⟩
    exact ⟨k, hk₀, hk₁, ⟨(AffineIsSupportedIdeal A I).fullyFaithfulι.preimageIso
      (e ≪≫ ((affineDZIdealι A I).commShiftIso (-k)).symm.app G)⟩⟩
  · rintro ⟨k, hk₀, hk₁, ⟨e⟩⟩
    exact ⟨k, hk₀, hk₁, ⟨(affineDZIdealι A I).mapIso e ≪≫
      ((affineDZIdealι A I).commShiftIso (-k)).app G⟩⟩

/-- The free-cover construction of Neeman's Lemma 7.6, specialized to a finite
list.  The approximation map and all of its bounds are proved, not assumed. -/
theorem idealSupportedH0Cover (A : Type u) [CommRing A] (fs : List A)
    (N : ℤ) (hN : 0 < N) :
    ClosedSupportNeemanM4.IdealSupportedH0Cover A (functionIdeal A fs)
      ⟨(koszulListData A (unitExponents A fs)).obj, by
      rw [← listIdeal_unitExponents]
      exact (koszulListData A (unitExponents A fs)).supported⟩ N := by
  let G : AffineDZIdeal A (functionIdeal A fs) :=
    ⟨(koszulListData A (unitExponents A fs)).obj, by
      rw [← listIdeal_unitExponents]
      exact (koszulListData A (unitExponents A fs)).supported⟩
  have hD := KoszulInputs.idealSupportedCoproductInput A fs
  have hP := koszulPowerCoprodInput A fs
  intro F hF
  let H0 := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let M : Type u := H0.obj F.obj
  letI : F.obj.IsLE 0 := (DerivedCategory.TStructure.t.le_iff_isLE F.obj 0).mp hF
  obtain ⟨K, hK, ⟨eFK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE F.obj 0
  letI : K.IsStrictlyLE 0 := hK
  let ρ : (ModuleCat.free A).obj M ⟶ H0.obj F.obj :=
    PrincipalH0CoverM1.freeLinearCombination A (H0.obj F.obj)
  letI : Epi ρ := by
    dsimp [ρ]
    infer_instance
  letI : Projective ((ModuleCat.free A).obj M) := inferInstance
  obtain ⟨ψ, hψ⟩ := FreeDerivedCoverM1.exists_derived_from_single_projective K eFK.symm ρ
  have hψepi : Epi (H0.map ψ) := by
    rw [← hψ]
    infer_instance
  let basis : ∀ i : M, ringObject A ⟶
      DerivedCategory.Q.obj ((HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) 0).obj ((ModuleCat.free A).obj M)) := fun i =>
    DerivedCategory.Q.map ((HomologicalComplex.single (ModuleCat.{u} A)
      (ComplexShape.up ℤ) 0).map (PrincipalH0CoverM1.freeBasisMap A i))
  choose ns hlen hpos β hβ using fun i : M =>
    exists_koszulList_factorization A fs F.property (basis i ≫ ψ)
  let S := Spaltenstein.affineSpaltensteinInput A
  let R := fun i : M => S.resolution ((koszulListData A (fs.zip (ns i))).obj)
  let K' : M → CochainComplex (ModuleCat.{u} A) ℤ := fun i => (R i).complex
  have hK' : ∀ i : M, (K' i).IsKProjective := fun i => (R i).isKProjective
  letI := hK'
  let t : Cofan (fun i : M => DerivedCategory.Q.obj (K' i)) :=
    Cofan.mk F.obj (fun i => (R i).iso.hom ≫ β i)
  let α : (RelativeFM.DerivedCoproducts.derivedCoproductCofan K').pt ⟶ F.obj :=
    RelativeFM.DerivedCoproducts.derivedCoproductDesc K' t
  let Kreg : M → CochainComplex (ModuleCat.{u} A) ℤ := fun _ =>
    (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A)
  have hKreg : ∀ i : M, (Kreg i).IsKProjective := by
    intro i
    dsimp [Kreg]
    exact CochainComplex.isKProjective_of_projective _ 0
  let tq : Cofan (fun i : M => DerivedCategory.Q.obj (Kreg i)) :=
    Cofan.mk (RelativeFM.DerivedCoproducts.derivedCoproductCofan K').pt (fun i =>
      (koszulListData A (fs.zip (ns i))).second ≫ (R i).iso.inv ≫
        (RelativeFM.DerivedCoproducts.derivedCoproductCofan K').inj i)
  let q0 := @RelativeFM.DerivedCoproducts.derivedCoproductDesc
    (ModuleCat.{u} A) _ _ M Kreg _ _ hKreg tq
  let eL := PrincipalH0CoverM1.derivedCoproductSingleFreeIso A M
  let qfree : DerivedCategory.Q.obj ((HomologicalComplex.single (ModuleCat.{u} A)
      (ComplexShape.up ℤ) 0).obj ((ModuleCat.free A).obj M)) ⟶
      (RelativeFM.DerivedCoproducts.derivedCoproductCofan K').pt := eL.inv ≫ q0
  have hfactor : ψ = qfree ≫ α := by
    apply (cancel_epi eL.hom).mp
    apply (@RelativeFM.DerivedCoproducts.derivedCoproductCofanIsColimit
      (ModuleCat.{u} A) _ _ M Kreg _ _ hKreg).hom_ext
    rintro ⟨i⟩
    calc
      (RelativeFM.DerivedCoproducts.derivedCoproductCofan Kreg).inj i ≫ eL.hom ≫ ψ =
          basis i ≫ ψ := by
        rw [← Category.assoc, PrincipalH0CoverM1.derivedCoproductSingleFreeIso_injection]
      _ = (koszulListData A (fs.zip (ns i))).second ≫ β i := (hβ i).symm
      _ = (RelativeFM.DerivedCoproducts.derivedCoproductCofan Kreg).inj i ≫
          eL.hom ≫ eL.inv ≫ q0 ≫ α := by
        rw [Iso.hom_inv_id_assoc]
        rw [← Category.assoc, RelativeFM.DerivedCoproducts.derivedCoproductDesc_fac]
        dsimp [tq, α, Kreg]
        rw [show DerivedCategory.Q.map
            ((RelativeFM.DerivedCoproducts.coproductComplexCocone K').ι.app { as := i }) =
          (RelativeFM.DerivedCoproducts.derivedCoproductCofan K').inj i from rfl]
        rw [Category.assoc, Category.assoc,
          RelativeFM.DerivedCoproducts.derivedCoproductDesc_fac]
        simp [t, Category.assoc]
    simp [qfree]
  let P₀ : ObjectProperty (AffineD A) := shiftInterval G.obj 0 0
  have hmem (i : M) : Coprod P₀ (DerivedCategory.Q.obj (K' i)) := by
    apply Coprod.of_isoClosure (R i).iso.symm
    exact hP.power (ns i) (hlen i)
  have hEamb : Coprod P₀ (RelativeFM.DerivedCoproducts.derivedCoproductCofan K').pt := by
    exact RelativeFM.AisleGeneration.DerivedCoproduct.coprod_Q_coproductComplex P₀ K' hmem
  have hsupp : AffineIsSupportedIdeal A (functionIdeal A fs)
      (RelativeFM.DerivedCoproducts.derivedCoproductCofan K').pt :=
    affineIsSupportedIdeal_of_ambient_coprod_interval A (functionIdeal A fs) hD G 0 0 hEamb
  let E : AffineDZIdeal A (functionIdeal A fs) :=
    ⟨(RelativeFM.DerivedCoproducts.derivedCoproductCofan K').pt, hsupp⟩
  have hEpre : Coprod (P₀.inverseImage (affineDZIdealι A (functionIdeal A fs))) E := by
    apply supported_coprod_preimage_of_ambient_ideal A (functionIdeal A fs) hD P₀ _ hEamb
    intro Y hY
    exact affineIsSupportedIdeal_of_ambient_coprod_interval
      A (functionIdeal A fs) hD G 0 0 hY
  have hEcop : Coprod (shiftInterval G 0 0) E := by
    rw [← shiftInterval_inverseImage_ideal A (functionIdeal A fs) G 0 0]
    exact hEpre
  have hEnv : envelope G (-N) N E := by
    apply lemma31_2_mono G (a := 0) (b := 0) (a' := -N) (b' := N) (by omega) (by omega)
    exact ObjectProperty.le_retractClosure _ E hEcop
  have hEb : (affineDZIdealStandardTStructure A (functionIdeal A fs)).le 0 E := by
    let t₀ := affineDZIdealStandardTStructure A (functionIdeal A fs)
    letI (J : Type (u + 1)) : (t₀.le 0).IsClosedUnderColimitsOfShape (Discrete J) :=
      TStructure.le_isClosedUnderColimitsOfShape t₀ 0 (Discrete J)
    letI : (t₀.le 0).IsTriangulatedClosed₂ := TStructure.le_isTriangulatedClosed₂ t₀ 0
    refine Coprod.le (Q := t₀.le 0) ?_ E hEcop
    rintro Y ⟨k, hk₀, hk₁, ⟨e⟩⟩
    have hk : k = 0 := by omega
    subst k
    apply (t₀.le 0).prop_of_iso e.symm
    have hG0 : (affineDZIdealStandardTStructure A (functionIdeal A fs)).le 0 G :=
      (koszulListData A (unitExponents A fs)).mem_le_zero
    exact (t₀.le 0).prop_of_iso ((shiftFunctorZero (AffineDZIdeal A (functionIdeal A fs)) ℤ).symm.app _) hG0
  let qfree' : E ⟶ F := (affineDZIdealι A (functionIdeal A fs)).preimage α
  refine ⟨E, qfree', hEnv, hEb, ?_⟩
  have hαepi : Epi (H0.map α) := by
    letI : Epi (H0.map ψ) := hψepi
    exact epi_of_epi_fac (f := H0.map qfree) (g := H0.map α) (h := H0.map ψ)
      (by rw [← Functor.map_comp, ← hfactor])
  change Epi (H0.map ((affineDZIdealι A (functionIdeal A fs)).map qfree'))
  have hq : (affineDZIdealι A (functionIdeal A fs)).map qfree' = α := by
    simpa [qfree'] using (affineDZIdealι A (functionIdeal A fs)).map_preimage
      (X := E) (Y := F) α
  rw [hq]
  exact hαepi


/-- Supported zero detection descends from the ambient finite Koszul
zero-detection input along the full inclusion. -/
lemma isZero_idealSupported_of_ambient_detection
    (A : Type u) [CommRing A] (fs : List A)
    {F : AffineDZIdeal A (functionIdeal A fs)}
    (h : ∀ k : ℤ, ∀ g :
      (⟨(koszulListData A (unitExponents A fs)).obj, by
        rw [← listIdeal_unitExponents]
        exact (koszulListData A (unitExponents A fs)).supported⟩ :
        AffineDZIdeal A (functionIdeal A fs))⟦k⟧ ⟶ F, g = 0) : IsZero F := by
  let G : AffineDZIdeal A (functionIdeal A fs) :=
    ⟨(koszulListData A (unitExponents A fs)).obj, by
      rw [← listIdeal_unitExponents]
      exact (koszulListData A (unitExponents A fs)).supported⟩
  have hz : IsZero F.obj := (koszulDetectionInput A fs).detect F.obj F.property (fun k g => by
    let e := ((affineDZIdealι A (functionIdeal A fs)).commShiftIso k).app G
    let q : G⟦k⟧ ⟶ F := (affineDZIdealι A (functionIdeal A fs)).preimage (e.hom ≫ g)
    have hq : q = 0 := h k q
    have heq : e.hom ≫ g = 0 := by
      have hm := congrArg (affineDZIdealι A (functionIdeal A fs)).map hq
      rw [Functor.map_zero, (affineDZIdealι A (functionIdeal A fs)).map_preimage] at hm
      exact hm
    rw [← cancel_epi e.hom]
    simpa only [comp_zero] using heq)
  rw [IsZero.iff_id_eq_zero] at hz ⊢
  apply (affineDZIdealι A (functionIdeal A fs)).map_injective
  simpa using hz

/-- Compactness of the degree-one finite Koszul object follows from its
perfectness and the supported-direct-sum inclusion. -/
lemma isCompactAb_koszulListData_unitExponents
    (A : Type u) [CommRing A] (fs : List A)
    (hAc : IsCompactAb (ringObject A)) :
    IsCompactAb (show AffineDZIdeal A (functionIdeal A fs) from
      ⟨(koszulListData A (unitExponents A fs)).obj, by
        rw [← listIdeal_unitExponents]
        exact (koszulListData A (unitExponents A fs)).supported⟩) := by
  let G : AffineDZIdeal A (functionIdeal A fs) :=
    ⟨(koszulListData A (unitExponents A fs)).obj, by
      rw [← listIdeal_unitExponents]
      exact (koszulListData A (unitExponents A fs)).supported⟩
  apply AffineSupportedBaseM1.isCompactAb_of_fullyFaithful
    (affineDZIdealι A (functionIdeal A fs)) G
  · exact RelativeFM.isCompactAb_of_perf A hAc
      (koszulListData A (unitExponents A fs)).perfect
  · intro J
    exact (KoszulInputs.idealSupportedCompactnessInput A fs).preserves J

/-- **LP26 Corollary 1.2, affine base case** (`cor:weak_approx_spaces`), with the
ambient regular compactness `hAc` as its only argument: `D_{V(f₁,…,fₙ)}(A-Mod)`
satisfies the paper's weak approximability (LP26 Definition 2.1, `def:weak_approx`).
Restated in wave 5: the refuted `hS` and the four inputs `hD`, `hP`, `hC`, `hDet`
(all now theorems) were deleted.  `hAc` is discharged in
`NeemanAffineSupport.satisfiesPaperWA_idealSupported`. -/
theorem satisfiesPaperWA_idealSupported
    (A : Type u) [CommRing A] (fs : List A)
    (hAc : IsCompactAb (ringObject A)) :
    PaperM2.SatisfiesPaperWA (AffineDZIdeal A (functionIdeal A fs)) := by
  let G : AffineDZIdeal A (functionIdeal A fs) :=
    ⟨(koszulListData A (unitExponents A fs)).obj, by
      rw [← listIdeal_unitExponents]
      exact (koszulListData A (unitExponents A fs)).supported⟩
  have hGc : IsCompactAb G := isCompactAb_koszulListData_unitExponents A fs hAc
  have hGg : IsPaperGenerator G := by
    intro F hF
    exact isZero_idealSupported_of_ambient_detection A fs hF
  obtain ⟨N, hN, hGle, hvan⟩ :=
    ClosedSupportNeemanM4.exists_idealSupported_perfect_standard_bounds
      A (functionIdeal A fs) G (koszulListData A (unitExponents A fs)).perfect
  exact ⟨ClosedSupportNeemanM4.idealSupportedPaperDataOfH0Cover
    A (functionIdeal A fs) G N hN hGc hGg hGle hvan
      (idealSupportedH0Cover A fs N hN)⟩

end

end RelativeFM.IdealNeemanM1

#print axioms RelativeFM.IdealNeemanM1.idealSupportedH0Cover
#print axioms RelativeFM.IdealNeemanM1.isZero_idealSupported_of_ambient_detection
#print axioms RelativeFM.IdealNeemanM1.isCompactAb_koszulListData_unitExponents
#print axioms RelativeFM.IdealNeemanM1.satisfiesPaperWA_idealSupported
