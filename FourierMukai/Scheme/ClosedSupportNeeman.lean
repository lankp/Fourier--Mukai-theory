import FourierMukai.Scheme.IdealKoszulM4
import FourierMukai.Scheme.AffineNeemanEndpointM3
import WeakApprox.CompactVanishing

/-!
# Closed-support reductions for Neeman weak approximability

This module proves the parts of Neeman's Construction 7.3 and Lemma 7.6 that
follow from the repository's affine closed-support infrastructure, in the
zero-detection formulation.  It does not assert the missing compact-generator
or supported-cover theorem.

The main results are:

* the Koszul cone of `f` has standard cohomological amplitude `[-1, 0]`;
* every perfect object of an ideal-supported derived category has a bound `N`
  for which the standard-t fields `G_mem_le` and `hom_vanishing` of
  `PaperWeakApproximationData` hold;
* an `H⁰`-epimorphism cover with envelope control completes all the remaining
  approximation-triangle fields;
* the family of all positive-power Koszul cones detects zero on the
  `f`-supported derived category.  Consequently a single object whose thick
  envelope contains all these cones is a zero-detecting generator.

The last implication isolates the Koszul-telescope input, rather than assuming
zero detection itself.  Compactness in the supported category and construction
of the supported `H⁰` cover remain separate inputs.
-/

@[expose] public section

namespace RelativeFM.ClosedSupportNeemanM4

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open RelativeFM.SupportedAisleM6.Koszul

universe v u

noncomputable section

section ThickOrthogonality

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If every map from `G` to `F` vanishes, then so does every map from an
object of the finite thick envelope of `G` to `F`; the same holds after an
integer shift.  This is the zero-detection form of thickness, with no
morphism-separation hypothesis. -/
lemma eq_zero_shift_of_mem_triangEnvelope {G K F : C}
    (hG : ∀ k : ℤ, ∀ f : G⟦k⟧ ⟶ F, f = 0)
    (hK : (ObjectProperty.singleton G).triangEnvelope K)
    (k : ℤ) (f : K⟦k⟧ ⟶ F) : f = 0 := by
  let Q : ObjectProperty C := ((ObjectProperty.singleton F).shiftClosure ℤ).leftOrthogonal
  letI : Q.IsStableUnderRetracts := {
    of_retract := by
      intro X Y r hY Z g hZ
      rw [← cancel_epi r.r]
      simpa only [comp_zero] using hY (r.r ≫ g) hZ }
  letI : Q.IsTriangulated := {}
  have hsub : ObjectProperty.singleton G ≤ Q := by
    intro X hX
    obtain rfl : G = X := (ObjectProperty.singleton_iff _ _).mp hX
    intro Y g hY
    obtain ⟨F₀, m, e, hF₀⟩ := hY
    obtain rfl : F = F₀ := (ObjectProperty.singleton_iff _ _).mp hF₀
    rw [← cancel_mono e.hom]
    obtain ⟨q, hq⟩ := ((shiftEquiv C m).symm.toAdjunction.homEquiv _ _).surjective
      (g ≫ e.hom)
    letI : (shiftEquiv C m).symm.functor.Additive := by
      change (shiftFunctor C (-m)).Additive
      infer_instance
    have hq0 : ((shiftEquiv C m).symm.toAdjunction.homEquiv G F) q = 0 := by
      calc
        ((shiftEquiv C m).symm.toAdjunction.homEquiv G F) q =
            ((shiftEquiv C m).symm.toAdjunction.homEquiv G F) 0 :=
          congrArg _ (hG (-m) q)
        _ = 0 := ((shiftEquiv C m).symm.toAdjunction).homAddEquiv_zero G F
    rw [zero_comp]
    exact hq.symm.trans hq0
  have hcl : (ObjectProperty.singleton G).triangEnvelope ≤ Q :=
    (ObjectProperty.triangEnvelope_le_iff (ObjectProperty.singleton G)).mpr hsub
  exact hcl _ ((ObjectProperty.singleton G).triangEnvelope.le_shift k K hK) f
    ⟨F, 0, (shiftFunctorZero C ℤ).symm.app F, (ObjectProperty.singleton_iff _ _).mpr rfl⟩

end ThickOrthogonality

section NegativeAisleBounds

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A uniform negative-aisle Hom-vanishing bound for maps out of `G`. -/
def HasNegativeAisleHomBound (t : TStructure C) : ObjectProperty C :=
  fun G => ∃ N : ℤ, ∀ {Y : C}, t.le (-N) Y → ∀ f : G ⟶ Y, f = 0

instance (t : TStructure C) : (HasNegativeAisleHomBound t).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, 0, by
    intro Y hY f
    exact (isZero_zero C).eq_of_src f 0⟩

instance (t : TStructure C) (a : ℤ) :
    (HasNegativeAisleHomBound t).IsStableUnderShiftBy a where
  le_shift X hX := by
    obtain ⟨N, hN⟩ := hX
    refine ⟨N + a, ?_⟩
    intro Y hY f
    let f' : X ⟶ Y⟦-a⟧ := (shiftShiftNeg X a).inv ≫
      (shiftFunctor C (-a)).map f
    have hY' : t.le (-N) (Y⟦-a⟧) :=
      t.le_shift (-(N + a)) (-a) (-N) (by omega) Y hY
    have hf' : f' = 0 := hN hY' f'
    apply (shiftFunctor C (-a)).map_injective
    rw [Functor.map_zero]
    rw [← cancel_epi (shiftShiftNeg X a).inv]
    simpa only [f', comp_zero] using hf'

instance (t : TStructure C) : (HasNegativeAisleHomBound t).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    obtain ⟨N, hN⟩ := hX
    refine ⟨N, ?_⟩
    intro Y hY f
    rw [← cancel_epi e.hom]
    simpa only [comp_zero] using hN hY (e.hom ≫ f)

instance (t : TStructure C) :
    (HasNegativeAisleHomBound t).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ => by
    obtain ⟨N₁, hN₁⟩ := h₁
    obtain ⟨N₃, hN₃⟩ := h₃
    refine ⟨max N₁ N₃, ?_⟩
    intro Y hY
    exact (homZeroLeft Y).ext_of_isTriangulatedClosed₂ T hT
      (fun f => hN₁ (t.le_monotone (by omega) Y hY) f)
      (fun f => hN₃ (t.le_monotone (by omega) Y hY) f))

instance (t : TStructure C) : (HasNegativeAisleHomBound t).IsStableUnderRetracts where
  of_retract r hY := by
    obtain ⟨N, hN⟩ := hY
    refine ⟨N, ?_⟩
    intro Y hY f
    rw [← cancel_epi r.r]
    simpa only [comp_zero] using hN hY (r.r ≫ f)

instance (t : TStructure C) : (HasNegativeAisleHomBound t).IsTriangulated where

lemma hasNegativeAisleHomBound_of_mem_triangEnvelope (t : TStructure C)
    {G X : C} (hG : HasNegativeAisleHomBound t G)
    (hX : (ObjectProperty.singleton G).triangEnvelope X) :
    HasNegativeAisleHomBound t X := by
  apply (ObjectProperty.triangEnvelope_le_iff (ObjectProperty.singleton G)).mpr _ X hX
  intro Y hY
  obtain rfl : G = Y := (ObjectProperty.singleton_iff _ _).mp hY
  exact hG

end NegativeAisleBounds

section KoszulBounds

attribute [local instance] HasDerivedCategory.standard

/-- The chosen Koszul cone lies in `D^{≥ -1}` as well as `D^{≤ 0}`. -/
lemma coneData_obj_mem_ge_neg_one (A : Type u) [CommRing A] (f : A) :
    (AffineD.standardTStructure A).ge (-1) (coneData A f).obj := by
  let t := AffineD.standardTStructure A
  let T := Triangle.mk (derivedMultiplication A f)
    (coneData A f).second (coneData A f).third
  have hA : t.ge (-1) (ringObject A) :=
    t.ge_antitone (show (-1 : ℤ) ≤ 0 by omega) _
      (RelativeFM.ringObject_mem_standard_ge_zero A)
  have hAshift : t.ge (-1) ((ringObject A)⟦(1 : ℤ)⟧) :=
    t.ge_shift 0 1 (-1) (by omega) _
      (RelativeFM.ringObject_mem_standard_ge_zero A)
  exact (t.isGE₂ T.rotate (rot_of_distTriang _ (coneData A f).distinguished)
    (-1) ⟨hA⟩ ⟨hAshift⟩).ge

/-- Perfect complexes inherit negative-aisle Hom bounds from the regular
projective module. -/
lemma perfect_hasNegativeAisleHomBound (A : Type u) [CommRing A]
    {X : AffineD A} (hX : Perf A X) :
    HasNegativeAisleHomBound (AffineD.standardTStructure A) X := by
  change (ObjectProperty.singleton (ringObject A)).triangEnvelope X at hX
  apply hasNegativeAisleHomBound_of_mem_triangEnvelope _ _ hX
  exact ⟨1, fun hY f => RelativeFM.ringObject_hom_zero_of_standard_le_neg_one A hY f⟩

/-- Maps out of the Koszul cone vanish below the explicit bound two. -/
lemma coneData_obj_hom_zero_of_standard_le_neg_two
    (A : Type u) [CommRing A] (f : A) {Y : AffineD A}
    (hY : (AffineD.standardTStructure A).le (-2) Y)
    (g : (coneData A f).obj ⟶ Y) : g = 0 := by
  let t := AffineD.standardTStructure A
  let T := Triangle.mk (derivedMultiplication A f)
    (coneData A f).second (coneData A f).third
  have hA : homZeroLeft Y (ringObject A) := by
    intro q
    exact RelativeFM.ringObject_hom_zero_of_standard_le_neg_one A
      (t.le_monotone (show (-2 : ℤ) ≤ -1 by omega) Y hY) q
  have hAshift : homZeroLeft Y ((ringObject A)⟦(1 : ℤ)⟧) := by
    intro q
    apply (shiftFunctor (AffineD A) (-1)).map_injective
    rw [Functor.map_zero]
    rw [← cancel_epi (shiftShiftNeg (ringObject A) 1).inv]
    simpa only [comp_zero] using RelativeFM.ringObject_hom_zero_of_standard_le_neg_one A
      (t.le_shift (-2) (-1) (-1) (by omega) Y hY)
      ((shiftShiftNeg (ringObject A) 1).inv ≫ (shiftFunctor (AffineD A) (-1)).map q)
  exact (homZeroLeft Y).ext_of_isTriangulatedClosed₂ T.rotate
    (rot_of_distTriang _ (coneData A f).distinguished) hA hAshift g

/-- The principal supported Koszul generator has the standard bound two. -/
lemma supportedGenerator_standard_bounds_at_two (A : Type u) [CommRing A] (f : A) :
    (Recollement.AssemblyM6.affineDZStandardTStructure A f).le 2
        (supportedGenerator A f) ∧
      ∀ {Y : AffineDZ A f},
        (Recollement.AssemblyM6.affineDZStandardTStructure A f).le (-2) Y →
        ∀ g : supportedGenerator A f ⟶ Y, g = 0 := by
  let t := Recollement.AssemblyM6.affineDZStandardTStructure A f
  refine ⟨t.le_monotone (show (0 : ℤ) ≤ 2 by omega) _
    (supportedGenerator_mem_le_zero A f), ?_⟩
  intro Y hY g
  apply (affineDZι A f).map_injective
  rw [Functor.map_zero]
  apply coneData_obj_hom_zero_of_standard_le_neg_two A f
  exact hY

end KoszulBounds

section IdealBounds

attribute [local instance] HasDerivedCategory.standard

open NeemanFiniteSupportM4

/-- Every perfect supported object has a positive standard bound giving both
non-triangular generator fields of paper-style weak approximability. -/
theorem exists_idealSupported_perfect_standard_bounds
    (A : Type u) [CommRing A] (I : Ideal A) (G : AffineDZIdeal A I)
    (hG : Perf A G.obj) :
    ∃ N : ℤ, 0 < N ∧
      (affineDZIdealStandardTStructure A I).le N G ∧
      ∀ {Y : AffineDZIdeal A I},
        (affineDZIdealStandardTStructure A I).le (-N) Y →
        ∀ f : G ⟶ Y, f = 0 := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := perf_le_db A G.obj hG
  obtain ⟨N₀, hN₀⟩ := perfect_hasNegativeAisleHomBound A hG
  let N := max 1 (max b N₀)
  have hN : 0 < N := by dsimp [N]; omega
  have hbN : b ≤ N := by dsimp [N]; omega
  have hN₀N : N₀ ≤ N := by dsimp [N]; omega
  refine ⟨N, hN, ?_, ?_⟩
  · rw [affineDZIdealStandardTStructure_le]
    exact (AffineD.standardTStructure A).le_monotone hbN _ hb.le
  · intro Y hY f
    rw [affineDZIdealStandardTStructure_le] at hY
    have hY' : (AffineD.standardTStructure A).le (-N₀) Y.obj :=
      (AffineD.standardTStructure A).le_monotone (by omega) Y.obj hY
    have hz := hN₀ hY' ((affineDZIdealι A I).map f)
    apply (affineDZIdealι A I).map_injective
    simpa only [Functor.map_zero] using hz

end IdealBounds

section SupportedCovers

attribute [local instance] HasDerivedCategory.standard

open NeemanFiniteSupportM4

/-- The geometric input to Neeman's supported approximation triangle: an
`H⁰`-epimorphism from an object in the fixed finite generator envelope.
Unlike the approximation-triangle conclusion, this asserts no cone and no
negative-aisle bound; both are proved from it below. -/
def IdealSupportedH0Cover (A : Type u) [CommRing A] (I : Ideal A)
    (G : AffineDZIdeal A I) (N : ℤ) : Prop :=
  ∀ F : AffineDZIdeal A I, (affineDZIdealStandardTStructure A I).le 0 F →
    ∃ (E : AffineDZIdeal A I) (f : E ⟶ F),
      envelope G (-N) N E ∧
      (affineDZIdealStandardTStructure A I).le 0 E ∧
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((affineDZIdealι A I).map f))

/-- Assemble paper-style supported weak approximation from a compact
zero-detecting generator, its two standard bounds, and an `H⁰` cover.
The approximation cone and its `≤ -1` bound are proved, not assumed. -/
noncomputable def idealSupportedPaperDataOfH0Cover
    (A : Type u) [CommRing A] (I : Ideal A) (G : AffineDZIdeal A I) (N : ℤ)
    (hN : 0 < N) (hGc : IsCompactAb G) (hGg : IsPaperGenerator G)
    (hGle : (affineDZIdealStandardTStructure A I).le N G)
    (hvan : ∀ {Y : AffineDZIdeal A I},
      (affineDZIdealStandardTStructure A I).le (-N) Y → ∀ f : G ⟶ Y, f = 0)
    (hcover : IdealSupportedH0Cover A I G N) :
    PaperM2.PaperWeakApproximationData (AffineDZIdeal A I) where
  G := G
  t := affineDZIdealStandardTStructure A I
  A := N
  A_pos := hN
  G_compact := hGc
  G_paperGenerates := hGg
  G_mem_le := hGle
  hom_vanishing := hvan
  exists_triangle := by
    intro F hF
    obtain ⟨E, f, hE, hEb, hEpi⟩ := hcover F hF
    letI := hEpi
    obtain ⟨D, g, h, hT, hD⟩ :=
      exists_supported_triangle_of_h0_epi I f hEb hF
    exact ⟨E, D, f, g, h, hT, hE, hD⟩

/-- In particular a perfect supported generator needs only its supported
compactness, zero detection, and the `H⁰` cover at a valid bound; the standard
bounds are supplied by `exists_idealSupported_perfect_standard_bounds`. -/
theorem exists_idealSupportedPaperData_of_perfect
    (A : Type u) [CommRing A] (I : Ideal A) (G : AffineDZIdeal A I)
    (hGperf : Perf A G.obj) (hGc : IsCompactAb G) (hGg : IsPaperGenerator G)
    (hcover : ∀ N : ℤ, 0 < N →
      (affineDZIdealStandardTStructure A I).le N G →
      (∀ {Y : AffineDZIdeal A I},
        (affineDZIdealStandardTStructure A I).le (-N) Y →
        ∀ f : G ⟶ Y, f = 0) → IdealSupportedH0Cover A I G N) :
    PaperM2.SatisfiesPaperWA (AffineDZIdeal A I) := by
  obtain ⟨N, hN, hGle, hvan⟩ :=
    exists_idealSupported_perfect_standard_bounds A I G hGperf
  exact ⟨idealSupportedPaperDataOfH0Cover A I G N hN hGc hGg hGle hvan
    (hcover N hN hGle hvan)⟩

end SupportedCovers

section PrincipalSupportedPackage

attribute [local instance] HasDerivedCategory.standard

/-- Principal form of the supported triangle-completion lemma. -/
theorem exists_principal_supported_triangle_of_h0_epi
    (A : Type u) [CommRing A] (f : A) {E F : AffineDZ A f} (q : E ⟶ F)
    (hE : (Recollement.AssemblyM6.affineDZStandardTStructure A f).le 0 E)
    (hF : (Recollement.AssemblyM6.affineDZStandardTStructure A f).le 0 F)
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((affineDZι A f).map q))] :
    ∃ (D : AffineDZ A f) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk q g h ∈ distTriang (AffineDZ A f) ∧
        (Recollement.AssemblyM6.affineDZStandardTStructure A f).le (-1) D := by
  obtain ⟨D, g, h, hT⟩ := distinguished_cocone_triangle q
  refine ⟨D, g, h, hT, ?_⟩
  change (AffineD.standardTStructure A).le (-1) D.obj
  let _ : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (((affineDZι A f).mapTriangle.obj (Triangle.mk q g h)).mor₁)) := by
    change Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((affineDZι A f).map q))
    infer_instance
  exact NeemanFiniteSupportM4.cone_mem_standard_le_neg_one_of_epi
    ((affineDZι A f).mapTriangle.obj (Triangle.mk q g h)) hT hE hF

/-- `H⁰`-cover input in the principal supported model. -/
def PrincipalSupportedH0Cover (A : Type u) [CommRing A] (f : A)
    (G : AffineDZ A f) (N : ℤ) : Prop :=
  ∀ F : AffineDZ A f,
    (Recollement.AssemblyM6.affineDZStandardTStructure A f).le 0 F →
    ∃ (E : AffineDZ A f) (q : E ⟶ F),
      envelope G (-N) N E ∧
      (Recollement.AssemblyM6.affineDZStandardTStructure A f).le 0 E ∧
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((affineDZι A f).map q))

/-- Assemble principal supported paper weak approximation from an `H⁰` cover. -/
noncomputable def principalSupportedPaperDataOfH0Cover
    (A : Type u) [CommRing A] (f : A) (G : AffineDZ A f) (N : ℤ)
    (hN : 0 < N) (hGc : IsCompactAb G) (hGg : IsPaperGenerator G)
    (hGle : (Recollement.AssemblyM6.affineDZStandardTStructure A f).le N G)
    (hvan : ∀ {Y : AffineDZ A f},
      (Recollement.AssemblyM6.affineDZStandardTStructure A f).le (-N) Y →
      ∀ q : G ⟶ Y, q = 0)
    (hcover : PrincipalSupportedH0Cover A f G N) :
    PaperM2.PaperWeakApproximationData (AffineDZ A f) where
  G := G
  t := Recollement.AssemblyM6.affineDZStandardTStructure A f
  A := N
  A_pos := hN
  G_compact := hGc
  G_paperGenerates := hGg
  G_mem_le := hGle
  hom_vanishing := hvan
  exists_triangle := by
    intro F hF
    obtain ⟨E, q, hE, hEb, hEpi⟩ := hcover F hF
    letI := hEpi
    obtain ⟨D, g, h, hT, hD⟩ :=
      exists_principal_supported_triangle_of_h0_epi A f q hEb hF
    exact ⟨E, D, q, g, h, hT, hE, hD⟩

/-- The concrete principal Koszul package.  Only supported compactness,
single-generator zero detection, and the `H⁰` cover are arguments; the bound
`N = 2` and both non-triangular standard-t fields are proved. -/
noncomputable def koszulSupportedPaperDataOfH0Cover
    (A : Type u) [CommRing A] (f : A)
    (hGc : IsCompactAb (supportedGenerator A f))
    (hGg : IsPaperGenerator (supportedGenerator A f))
    (hcover : PrincipalSupportedH0Cover A f (supportedGenerator A f) 2) :
    PaperM2.PaperWeakApproximationData (AffineDZ A f) :=
  principalSupportedPaperDataOfH0Cover A f (supportedGenerator A f) 2 (by omega)
    hGc hGg (supportedGenerator_standard_bounds_at_two A f).1
      (supportedGenerator_standard_bounds_at_two A f).2 hcover

@[simp] theorem koszulSupportedPaperDataOfH0Cover_G
    (A : Type u) [CommRing A] (f : A)
    (hGc : IsCompactAb (supportedGenerator A f))
    (hGg : IsPaperGenerator (supportedGenerator A f))
    (hcover : PrincipalSupportedH0Cover A f (supportedGenerator A f) 2) :
    (koszulSupportedPaperDataOfH0Cover A f hGc hGg hcover).G =
      supportedGenerator A f := rfl

@[simp] theorem koszulSupportedPaperDataOfH0Cover_t
    (A : Type u) [CommRing A] (f : A)
    (hGc : IsCompactAb (supportedGenerator A f))
    (hGg : IsPaperGenerator (supportedGenerator A f))
    (hcover : PrincipalSupportedH0Cover A f (supportedGenerator A f) 2) :
    (koszulSupportedPaperDataOfH0Cover A f hGc hGg hcover).t =
      Recollement.AssemblyM6.affineDZStandardTStructure A f := rfl

@[simp] theorem koszulSupportedPaperDataOfH0Cover_A
    (A : Type u) [CommRing A] (f : A)
    (hGc : IsCompactAb (supportedGenerator A f))
    (hGg : IsPaperGenerator (supportedGenerator A f))
    (hcover : PrincipalSupportedH0Cover A f (supportedGenerator A f) 2) :
    (koszulSupportedPaperDataOfH0Cover A f hGc hGg hcover).A = 2 := rfl

/-- Existence form of the principal supported reduction to the three named
remaining inputs. -/
theorem koszulSupported_satisfiesPaperWA_of_h0Cover
    (A : Type u) [CommRing A] (f : A)
    (hGc : IsCompactAb (supportedGenerator A f))
    (hGg : IsPaperGenerator (supportedGenerator A f))
    (hcover : PrincipalSupportedH0Cover A f (supportedGenerator A f) 2) :
    PaperM2.SatisfiesPaperWA (AffineDZ A f) :=
  ⟨koszulSupportedPaperDataOfH0Cover A f hGc hGg hcover⟩

end PrincipalSupportedPackage

section KoszulPowerDetection

attribute [local instance] HasDerivedCategory.standard

/-- Orthogonality to all shifts of all positive-power principal Koszul cones. -/
def KoszulPowerOrthogonal (A : Type u) [CommRing A] (f : A)
    (F : AffineD A) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ k : ℤ,
    ∀ g : (coneData A (f ^ n)).obj⟦k⟧ ⟶ F, g = 0

/-- The positive-power Koszul family detects zero on `f`-supported objects.
The proof shifts a map from the regular module, applies the landed principal
Koszul factorization, and shifts back. -/
theorem isZero_of_koszulPowerOrthogonal
    (A : Type u) [CommRing A] (f : A) {F : AffineD A}
    (hF : AffineIsSupported A f F) (h : KoszulPowerOrthogonal A f F) :
    IsZero F := by
  apply NeemanGeneratorM5.Paper.Modules.ringObject_isPaperGenerator A
  intro k α
  let α' : ringObject A ⟶ F⟦-k⟧ :=
    (shiftShiftNeg (ringObject A) k).inv ≫ (shiftFunctor (AffineD A) (-k)).map α
  have hFshift : AffineIsSupported A f (F⟦-k⟧) :=
    (AffineIsSupported A f).le_shift (-k) F hF
  obtain ⟨n, hn, β, hβ⟩ :=
    NeemanFiniteSupportM4.exists_principal_koszul_factorization A f hFshift α'
  have hβk : (shiftFunctor (AffineD A) k).map β ≫ (shiftNegShift F k).hom = 0 :=
    h n hn k ((shiftFunctor (AffineD A) k).map β ≫ (shiftNegShift F k).hom)
  have hβk0 : (shiftFunctor (AffineD A) k).map β = 0 := by
    rw [← cancel_mono (shiftNegShift F k).hom]
    simpa only [zero_comp] using hβk
  have hβ0 : β = 0 := by
    apply (shiftFunctor (AffineD A) k).map_injective
    simpa using hβk0
  have hα' : α' = 0 := by
    rw [← hβ, hβ0, comp_zero]
  have hmap : (shiftFunctor (AffineD A) (-k)).map α = 0 := by
    rw [← cancel_epi (shiftShiftNeg (ringObject A) k).inv]
    simpa only [comp_zero] using hα'
  apply (shiftFunctor (AffineD A) (-k)).map_injective
  simpa using hmap

/-- Zero detection on a supported full-subcategory object follows from the
ambient form. -/
theorem isZero_supportedGenerator_orthogonal
    (A : Type u) [CommRing A] (f : A) {F : AffineDZ A f}
    (h : ∀ k : ℤ, ∀ g : (supportedGenerator A f)⟦k⟧ ⟶ F, g = 0)
    (hpowers : ∀ n : ℕ, 0 < n →
      (ObjectProperty.singleton (supportedGenerator A f).obj).triangEnvelope
        (coneData A (f ^ n)).obj) : IsZero F := by
  have hambient : KoszulPowerOrthogonal A f F.obj := by
    intro n hn k g
    apply eq_zero_shift_of_mem_triangEnvelope
      (G := (supportedGenerator A f).obj) (K := (coneData A (f ^ n)).obj)
      (F := F.obj) _ (hpowers n hn) k g
    intro m q
    let e := ((affineDZι A f).commShiftIso m).app (supportedGenerator A f)
    let q' : (supportedGenerator A f)⟦m⟧ ⟶ F :=
      (affineDZι A f).preimage (e.hom ≫ q)
    have hq' : q' = 0 := h m q'
    have hq : e.hom ≫ q = 0 := by
      have hq'' := congrArg (affineDZι A f).map hq'
      change ((affineDZι A f).preimage (e.hom ≫ q)).hom = 0 at hq''
      exact ((affineDZι A f).map_preimage (e.hom ≫ q)).symm.trans hq''
    rw [← cancel_epi e.hom]
    simpa only [comp_zero] using hq
  have hz : IsZero F.obj := isZero_of_koszulPowerOrthogonal A f F.property hambient
  rw [IsZero.iff_id_eq_zero] at hz ⊢
  apply (affineDZι A f).map_injective
  simpa using hz

/-- The exact Koszul-telescope reduction of single-generator zero detection.
The hypothesis is finite thick generation of each positive-power cone, not the
zero-detection conclusion and not classical morphism separation. -/
theorem supportedGenerator_isPaperGenerator_of_koszulPower_thick
    (A : Type u) [CommRing A] (f : A)
    (hpowers : ∀ n : ℕ, 0 < n →
      (ObjectProperty.singleton (supportedGenerator A f).obj).triangEnvelope
        (coneData A (f ^ n)).obj) :
    IsPaperGenerator (supportedGenerator A f) := by
  intro F h
  exact isZero_supportedGenerator_orthogonal A f h hpowers

end KoszulPowerDetection

end

end RelativeFM.ClosedSupportNeemanM4
