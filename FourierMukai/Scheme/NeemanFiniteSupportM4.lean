/-
Closed support on a general ideal, and its finite-generator presentation.

This is the affine support model needed for Neeman's Construction 7.3: if the
complement of Z is covered by the principal opens defined by `f i`, then
`Z = V(Ideal.span (Set.range f))`.  We prove that cohomology supported on this
closed set is exactly the intersection of the principal supported classes.

No Noetherian hypothesis is needed for the Serre-class and t-structure results.
-/
import FourierMukai.Scheme.AffineSupportedTStructure
import Mathlib.RingTheory.Support

@[expose] public section

namespace RelativeFM.NeemanFiniteSupportM4

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe u v

noncomputable section

attribute [local instance] HasDerivedCategory.standard

open RelativeFM

/-- Modules supported on `V(I)`: every element of `I` is locally nilpotent on
every element of the module.  The exponent may depend on both elements. -/
def IdealPowerTorsion (A : Type u) [CommRing A] (I : Ideal A) :
    ObjectProperty (ModuleCat.{u} A) :=
  fun M => ∀ (x : M) (a : A), a ∈ I → ∃ n : ℕ, a ^ n • x = 0

/-- Radical-of-annihilator formulation of support in `V(I)`. -/
lemma idealPowerTorsion_iff_radical {A : Type u} [CommRing A] {I : Ideal A}
    {M : ModuleCat.{u} A} :
    IdealPowerTorsion A I M ↔
      ∀ x : M, I ≤ (Ideal.torsionOf A M x).radical := by
  constructor
  · intro h x a ha
    obtain ⟨n, hn⟩ := h x a ha
    exact ⟨n, (Ideal.mem_torsionOf_iff x (a ^ n)).mpr hn⟩
  · intro h x a ha
    obtain ⟨n, hn⟩ := h x ha
    exact ⟨n, (Ideal.mem_torsionOf_iff x (a ^ n)).mp hn⟩

/-- The predicate is exactly containment of the module-theoretic support in
`V(I)`.  In particular it describes closed support, rather than merely an
intersection of localization-vanishing conditions. -/
lemma idealPowerTorsion_iff_support_subset_zeroLocus
    {A : Type u} [CommRing A] {I : Ideal A} {M : ModuleCat.{u} A} :
    IdealPowerTorsion A I M ↔
      Module.support A M ⊆ PrimeSpectrum.zeroLocus (I : Set A) := by
  constructor
  · intro h p hp
    rw [PrimeSpectrum.mem_zeroLocus]
    obtain ⟨x, hx⟩ := Module.mem_support_iff_exists_annihilator.mp hp
    have hx' : Ideal.torsionOf A M x ≤ p.asIdeal := by
      rwa [Ideal.annihilator_span_singleton_eq_torsionOf] at hx
    have hr : (Ideal.torsionOf A M x).radical ≤ p.asIdeal :=
      (inferInstance : p.asIdeal.IsPrime).radical_le_iff.mpr hx'
    intro a ha
    exact hr ((idealPowerTorsion_iff_radical.mp h x) ha)
  · intro h
    rw [idealPowerTorsion_iff_radical]
    intro x a ha
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro p ⟨hp, hprime⟩
    let q : PrimeSpectrum A := ⟨p, hprime⟩
    have hq : q ∈ Module.support A M :=
      Module.mem_support_iff_exists_annihilator.mpr ⟨x, by
        rwa [Ideal.annihilator_span_singleton_eq_torsionOf]⟩
    exact (PrimeSpectrum.mem_zeroLocus q (I : Set A)).mp (h hq) ha

/-- Support on `V(f)` is the existing principal power-torsion predicate. -/
lemma idealPowerTorsion_span_singleton {A : Type u} [CommRing A] (f : A)
    {M : ModuleCat.{u} A} :
    IdealPowerTorsion A (Ideal.span {f}) M ↔ PowerTorsion A f M := by
  rw [powerTorsion_iff]
  constructor
  · intro h x
    exact h x f (Ideal.subset_span (Set.mem_singleton f))
  · intro h
    rw [idealPowerTorsion_iff_radical]
    intro x
    apply Ideal.span_le.mpr
    intro a ha
    rw [Set.mem_singleton_iff.mp ha]
    obtain ⟨n, hn⟩ := h x
    exact ⟨n, (Ideal.mem_torsionOf_iff x (f ^ n)).mpr hn⟩

/-- Support on the closed set cut out by a family is the intersection of the
principal supports.  Finiteness is not needed for this set-theoretic fact. -/
lemma idealPowerTorsion_span_range {A : Type u} [CommRing A] {ι : Type v}
    (f : ι → A) {M : ModuleCat.{u} A} :
    IdealPowerTorsion A (Ideal.span (Set.range f)) M ↔
      ∀ i, PowerTorsion A (f i) M := by
  constructor
  · intro h i
    rw [powerTorsion_iff]
    intro x
    exact h x (f i) (Ideal.subset_span ⟨i, rfl⟩)
  · intro h
    rw [idealPowerTorsion_iff_radical]
    intro x
    apply Ideal.span_le.mpr
    rintro a ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := powerTorsion_iff.mp (h i) x
    exact ⟨n, (Ideal.mem_torsionOf_iff x ((f i) ^ n)).mpr hn⟩

/-- Ideal-supported modules contain a zero object. -/
instance idealPowerTorsion_containsZero (A : Type u) [CommRing A] (I : Ideal A) :
    (IdealPowerTorsion A I).ContainsZero where
  exists_zero :=
    let Z : ModuleCat.{u} A := ModuleCat.of A PUnit
    ⟨Z, ModuleCat.isZero_of_subsingleton _,
      fun x _ _ => ⟨0, by simpa using Subsingleton.elim x 0⟩⟩

/-- Ideal-supported modules are closed under subobjects. -/
instance idealPowerTorsion_isClosedUnderSubobjects
    (A : Type u) [CommRing A] (I : Ideal A) :
    (IdealPowerTorsion A I).IsClosedUnderSubobjects where
  prop_of_mono {M N} g _ hN := by
    intro x a ha
    obtain ⟨n, hn⟩ := hN (g x) a ha
    refine ⟨n, (ModuleCat.mono_iff_injective g).mp inferInstance ?_⟩
    simpa using hn

/-- Ideal-supported modules are closed under quotients. -/
instance idealPowerTorsion_isClosedUnderQuotients
    (A : Type u) [CommRing A] (I : Ideal A) :
    (IdealPowerTorsion A I).IsClosedUnderQuotients where
  prop_of_epi {M N} g _ hM := by
    intro y a ha
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective g).mp inferInstance y
    obtain ⟨n, hn⟩ := hM x a ha
    exact ⟨n, by simpa using congrArg g hn⟩

/-- Ideal-supported modules are closed under extensions. -/
instance idealPowerTorsion_isClosedUnderExtensions
    (A : Type u) [CommRing A] (I : Ideal A) :
    (IdealPowerTorsion A I).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    intro x a ha
    obtain ⟨n, hn⟩ := h₃ (S.g x) a ha
    have hg : S.g (a ^ n • x) = 0 := by simpa using hn
    obtain ⟨y, hy⟩ := (S.moduleCat_exact_iff).mp hS.exact _ hg
    obtain ⟨m, hm⟩ := h₁ y a ha
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_smul, ← hy, ← map_smul, hm, map_zero]

/-- Ideal-supported modules form a Serre class, without finiteness or
Noetherian hypotheses. -/
instance idealPowerTorsion_isSerreClass (A : Type u) [CommRing A] (I : Ideal A) :
    (IdealPowerTorsion A I).IsSerreClass where

/-- Complexes all of whose cohomology modules are supported on `V(I)`. -/
def AffineIsSupportedIdeal (A : Type u) [CommRing A] (I : Ideal A) :
    ObjectProperty (AffineD A) :=
  cohomologyWithin (IdealPowerTorsion A I)

/-- The derived category of `A`-modules with cohomology supported on `V(I)`. -/
abbrev AffineDZIdeal (A : Type u) [CommRing A] (I : Ideal A) : Type (u + 1) :=
  (AffineIsSupportedIdeal A I).FullSubcategory

/-- Its fully faithful inclusion into the ambient derived category. -/
abbrev affineDZIdealι (A : Type u) [CommRing A] (I : Ideal A) :
    AffineDZIdeal A I ⥤ AffineD A :=
  (AffineIsSupportedIdeal A I).ι

instance affineIsSupportedIdeal_isTriangulated
    (A : Type u) [CommRing A] (I : Ideal A) :
    (AffineIsSupportedIdeal A I).IsTriangulated := by
  unfold AffineIsSupportedIdeal
  infer_instance

/-- The principal supported category is recovered exactly. -/
lemma affineIsSupportedIdeal_span_singleton (A : Type u) [CommRing A] (f : A) :
    AffineIsSupportedIdeal A (Ideal.span {f}) = AffineIsSupported A f := by
  ext X
  exact forall_congr' (fun _ => idealPowerTorsion_span_singleton f)

/-- The support predicate for Neeman's finite family `f₁,…,fᵣ` is the
intersection of the principal support predicates. -/
lemma affineIsSupportedIdeal_span_range (A : Type u) [CommRing A]
    {ι : Type v} (f : ι → A) (X : AffineD A) :
    AffineIsSupportedIdeal A (Ideal.span (Set.range f)) X ↔
      ∀ i, AffineIsSupported A (f i) X := by
  constructor
  · intro h i n
    exact (idealPowerTorsion_span_range f).mp (h n) i
  · intro h n
    exact (idealPowerTorsion_span_range f).mpr (fun i => h i n)

/-- Standard truncations preserve ideal-supported cohomology. -/
lemma affineIsSupportedIdeal_truncLE {A : Type u} [CommRing A] (I : Ideal A)
    (X : AffineD A) (hX : AffineIsSupportedIdeal A I X) (n : ℤ) :
    AffineIsSupportedIdeal A I ((DerivedCategory.TStructure.t.truncLE n).obj X) := by
  intro i
  by_cases hi : n < i
  · exact (IdealPowerTorsion A I).prop_of_isZero
      (DerivedCategory.isZero_of_isLE _ n i hi)
  · have hi' : i ≤ n := by omega
    let _ := Recollement.AssemblyM6.isIso_homology_truncLEι X n i hi'
    exact (IdealPowerTorsion A I).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((DerivedCategory.TStructure.t.truncLEι n).app X))).symm (hX i)

/-- The upper truncation also preserves ideal-supported cohomology. -/
lemma affineIsSupportedIdeal_truncGE {A : Type u} [CommRing A] (I : Ideal A)
    (X : AffineD A) (hX : AffineIsSupportedIdeal A I X) (n : ℤ) :
    AffineIsSupportedIdeal A I ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj X) := by
  intro i
  by_cases hi : n < i
  · let _ := Recollement.AssemblyM6.isIso_homology_truncGEπ X n i hi
    exact (IdealPowerTorsion A I).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((DerivedCategory.TStructure.t.truncGEπ (n + 1)).app X))) (hX i)
  · exact (IdealPowerTorsion A I).prop_of_isZero
      (DerivedCategory.isZero_of_isGE _ (n + 1) i (by omega))

/-- The ideal-supported derived category inherits the standard t-structure. -/
noncomputable instance affineIsSupportedIdeal_hasInducedTStructure
    (A : Type u) [CommRing A] (I : Ideal A) :
    (AffineIsSupportedIdeal A I).HasInducedTStructure (AffineD.standardTStructure A) := by
  apply ObjectProperty.HasInducedTStructure.mk'
  intro X hX n
  constructor
  · exact affineIsSupportedIdeal_truncLE I X hX n
  · change AffineIsSupportedIdeal A I ((DerivedCategory.TStructure.t.truncGE n).obj X)
    simpa using affineIsSupportedIdeal_truncGE I X hX (n - 1)

/-- The standard t-structure on `D_{V(I)}(A)`. -/
noncomputable def affineDZIdealStandardTStructure
    (A : Type u) [CommRing A] (I : Ideal A) : TStructure (AffineDZIdeal A I) :=
  (AffineIsSupportedIdeal A I).tStructure (AffineD.standardTStructure A)

@[simp] lemma affineDZIdealStandardTStructure_le
    (A : Type u) [CommRing A] (I : Ideal A) (X : AffineDZIdeal A I) (n : ℤ) :
    (affineDZIdealStandardTStructure A I).le n X =
      (AffineD.standardTStructure A).le n X.obj := rfl

@[simp] lemma affineDZIdealStandardTStructure_ge
    (A : Type u) [CommRing A] (I : Ideal A) (X : AffineDZIdeal A I) (n : ℤ) :
    (affineDZIdealStandardTStructure A I).ge n X =
      (AffineD.standardTStructure A).ge n X.obj := rfl

end
end RelativeFM.NeemanFiniteSupportM4

#print axioms RelativeFM.NeemanFiniteSupportM4.idealPowerTorsion_iff_radical
#print axioms RelativeFM.NeemanFiniteSupportM4.idealPowerTorsion_iff_support_subset_zeroLocus
#print axioms RelativeFM.NeemanFiniteSupportM4.idealPowerTorsion_span_singleton
#print axioms RelativeFM.NeemanFiniteSupportM4.idealPowerTorsion_span_range
#print axioms RelativeFM.NeemanFiniteSupportM4.affineIsSupportedIdeal_span_singleton
#print axioms RelativeFM.NeemanFiniteSupportM4.affineIsSupportedIdeal_span_range
#print axioms RelativeFM.NeemanFiniteSupportM4.affineIsSupportedIdeal_truncLE
#print axioms RelativeFM.NeemanFiniteSupportM4.affineIsSupportedIdeal_truncGE
#print axioms RelativeFM.NeemanFiniteSupportM4.affineIsSupportedIdeal_hasInducedTStructure
#print axioms RelativeFM.NeemanFiniteSupportM4.affineDZIdealStandardTStructure

namespace RelativeFM.NeemanFiniteSupportM4

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

open RelativeFM

set_option maxHeartbeats 1000000

/-- The cohomological part of Neeman's Lemma 7.6.  If `E` and `F` are bounded
above by zero and `H⁰(E) → H⁰(F)` is epi, then every cone of the map is
bounded above by `-1`. -/
lemma cone_mem_standard_le_neg_one_of_epi {A : Type u} [CommRing A]
    (T : Triangle (AffineD A)) (hT : T ∈ distTriang (AffineD A))
    (hE : (AffineD.standardTStructure A).le 0 T.obj₁)
    (hF : (AffineD.standardTStructure A).le 0 T.obj₂)
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map T.mor₁)] :
    (AffineD.standardTStructure A).le (-1) T.obj₃ := by
  change DerivedCategory.TStructure.t.le (-1) T.obj₃
  let _ : T.obj₁.IsLE 0 :=
    (DerivedCategory.TStructure.t.le_iff_isLE T.obj₁ 0).mp hE
  let _ : T.obj₂.IsLE 0 :=
    (DerivedCategory.TStructure.t.le_iff_isLE T.obj₂ 0).mp hF
  rw [DerivedCategory.TStructure.t.le_iff_isLE]
  let _ : T.obj₃.IsLE (-1) := (DerivedCategory.isLE_iff T.obj₃ (-1)).mpr (by
    intro i hi
    have hi0 : 0 ≤ i := by omega
    have hg : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map T.mor₂ = 0 := by
      by_cases hi' : i = 0
      · subst i
        exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT 0).mp
          inferInstance
      · exact (DerivedCategory.isZero_of_isLE T.obj₂ 0 i (by omega)).eq_of_src _ _
    have hd : DerivedCategory.HomologySequence.δ T i (i + 1) (by omega) = 0 :=
      (DerivedCategory.isZero_of_isLE T.obj₁ 0 (i + 1) (by omega)).eq_of_tgt _ _
    let _ : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map T.mor₂) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1)
        (by omega)).mpr hd
    let _ : Epi (0 : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T.obj₂ ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T.obj₃) := hg ▸ inferInstance
    exact IsZero.of_epi_zero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T.obj₂)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T.obj₃))
  infer_instance

/-- Complete a supported `H⁰`-cover to an approximation triangle.  This is the
triangle-completion half of affine Neeman Lemma 7.6; the remaining geometric
input is construction of the cover by finite Koszul objects. -/
theorem exists_supported_triangle_of_h0_epi {A : Type u} [CommRing A] (I : Ideal A)
    {E F : AffineDZIdeal A I} (f : E ⟶ F)
    (hE : (affineDZIdealStandardTStructure A I).le 0 E)
    (hF : (affineDZIdealStandardTStructure A I).le 0 F)
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((affineDZIdealι A I).map f))] :
    ∃ (D : AffineDZIdeal A I) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (AffineDZIdeal A I) ∧
        (affineDZIdealStandardTStructure A I).le (-1) D := by
  obtain ⟨D, g, h, hT⟩ := distinguished_cocone_triangle f
  refine ⟨D, g, h, hT, ?_⟩
  change (AffineD.standardTStructure A).le (-1) D.obj
  let _ : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (((affineDZIdealι A I).mapTriangle.obj (Triangle.mk f g h)).mor₁)) := by
    change Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((affineDZIdealι A I).map f))
    infer_instance
  exact cone_mem_standard_le_neg_one_of_epi
    ((affineDZIdealι A I).mapTriangle.obj (Triangle.mk f g h)) hT hE hF

/-- A supported approximation triangle with envelope control, assuming only a
supported `H⁰`-cover by an object in the prescribed envelope. -/
theorem exists_supported_approximation_triangle_of_h0_epi
    {A : Type u} [CommRing A] (I : Ideal A) (G : AffineDZIdeal A I) (N : ℤ)
    {E F : AffineDZIdeal A I} (f : E ⟶ F)
    (hE : envelope G (-N) N E)
    (hEb : (affineDZIdealStandardTStructure A I).le 0 E)
    (hF : (affineDZIdealStandardTStructure A I).le 0 F)
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((affineDZIdealι A I).map f))] :
    ∃ (D : AffineDZIdeal A I) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (AffineDZIdeal A I) ∧
        envelope G (-N) N E ∧
        (affineDZIdealStandardTStructure A I).le (-1) D := by
  obtain ⟨D, g, h, hT, hD⟩ := exists_supported_triangle_of_h0_epi I f hEb hF
  exact ⟨D, g, h, hT, hE, hD⟩

/-- Factor a map through the third term of a distinguished triangle when its
composite with the first map vanishes.  For the Koszul triangle
`A --f^n→ A → B_n`, this is precisely the principal Koszul factorization step. -/
lemma exists_factor_through_triangle_obj₃ {C : Type u} [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {W : C} (α : T.obj₂ ⟶ W)
    (hα : T.mor₁ ≫ α = 0) :
    ∃ β : T.obj₃ ⟶ W, T.mor₂ ≫ β = α := by
  obtain ⟨β, hβ⟩ := Triangle.yoneda_exact₂ T hT α hα
  exact ⟨β, hβ.symm⟩

end
end RelativeFM.NeemanFiniteSupportM4

#print axioms RelativeFM.NeemanFiniteSupportM4.cone_mem_standard_le_neg_one_of_epi
#print axioms RelativeFM.NeemanFiniteSupportM4.exists_supported_triangle_of_h0_epi
#print axioms RelativeFM.NeemanFiniteSupportM4.exists_supported_approximation_triangle_of_h0_epi
#print axioms RelativeFM.NeemanFiniteSupportM4.exists_factor_through_triangle_obj₃

namespace RelativeFM.NeemanFiniteSupportM4

open CategoryTheory CategoryTheory.Limits
open RelativeFM

universe u

/-- Closed support depends only on the radical of the defining ideal. -/
lemma idealPowerTorsion_radical {A : Type u} [CommRing A] (I : Ideal A)
    {M : ModuleCat.{u} A} :
    IdealPowerTorsion A I.radical M ↔ IdealPowerTorsion A I M := by
  rw [idealPowerTorsion_iff_radical, idealPowerTorsion_iff_radical]
  constructor
  · intro h x
    exact Ideal.le_radical.trans (h x)
  · intro h x
    exact Ideal.radical_le_radical_iff.mpr (h x)

/-- Support for a sum of ideals is the intersection of the two support classes. -/
lemma idealPowerTorsion_sup {A : Type u} [CommRing A] (I J : Ideal A)
    {M : ModuleCat.{u} A} :
    IdealPowerTorsion A (I ⊔ J) M ↔
      IdealPowerTorsion A I M ∧ IdealPowerTorsion A J M := by
  simp only [idealPowerTorsion_iff_radical]
  constructor
  · intro h
    exact ⟨fun x => le_sup_left.trans (h x), fun x => le_sup_right.trans (h x)⟩
  · intro h x
    exact sup_le (h.1 x) (h.2 x)

/-- The derived support predicates for `I ⊔ J` likewise intersect. -/
lemma affineIsSupportedIdeal_sup {A : Type u} [CommRing A] (I J : Ideal A)
    (X : AffineD A) :
    AffineIsSupportedIdeal A (I ⊔ J) X ↔
      AffineIsSupportedIdeal A I X ∧ AffineIsSupportedIdeal A J X := by
  constructor
  · intro h
    exact ⟨fun n => (idealPowerTorsion_sup I J).mp (h n) |>.1,
      fun n => (idealPowerTorsion_sup I J).mp (h n) |>.2⟩
  · intro h n
    exact (idealPowerTorsion_sup I J).mpr ⟨h.1 n, h.2 n⟩

/-- At the level of object properties, replacing an ideal by its radical does
not change the supported derived category. -/
lemma affineIsSupportedIdeal_radical {A : Type u} [CommRing A] (I : Ideal A) :
    AffineIsSupportedIdeal A I.radical = AffineIsSupportedIdeal A I := by
  ext X
  exact forall_congr' (fun _ => idealPowerTorsion_radical I)

end RelativeFM.NeemanFiniteSupportM4

#print axioms RelativeFM.NeemanFiniteSupportM4.idealPowerTorsion_radical
#print axioms RelativeFM.NeemanFiniteSupportM4.idealPowerTorsion_sup
#print axioms RelativeFM.NeemanFiniteSupportM4.affineIsSupportedIdeal_sup
#print axioms RelativeFM.NeemanFiniteSupportM4.affineIsSupportedIdeal_radical
