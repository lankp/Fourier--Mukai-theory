/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.FiniteKoszulM1
import FourierMukai.Scheme.AffineLocalCohomology

/-!
# The ideal-supported inclusion is a left adjoint

Used for LP26 Corollary 1.2 (`cor:weak_approx_spaces`), affine base case
(Neeman, *Acta Math.* 233 (2024), Thm 3.2(iv) for `Spec A`, `Z = V(f₁,…,fₙ)`).

`isLeftAdjoint_affineDZIdealι`: for every finite list `fs`, the inclusion
`D_{V(fs)}(A-Mod) ⟶ D(A-Mod)` has a right adjoint, built by induction on `fs` from
the principal local-cohomology adjoints `AffineLocalCohomology.jShriekAdj`
(`V(f :: fs) = V(f) ∩ V(fs)`), using that `RΓ_{V(f)}` preserves ideal support
(`jStar_supportedIdeal`).  Consequently the supported class is closed under all
ambient colimits and its inclusion preserves them
(`isClosedUnderColimitsOfShape_of_adjunction`).

These declarations were proved in wave 3 in `KoszulInputs.lean` and are moved
here unchanged so that `IdealNeemanM1.lean` can use them.  Nothing is assumed.
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

end Inputs

end

end RelativeFM.KoszulInputs

#print axioms RelativeFM.KoszulInputs.jStar_supportedIdeal
#print axioms RelativeFM.KoszulInputs.isLeftAdjoint_affineDZIdealι
