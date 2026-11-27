/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Affine.Inputs
import FourierMukai.Scheme.NeemanFiniteSupportM4

/-!
# Supports on the affine algebraic space `Spec R` and supports of `R`-modules

LP26 Corollary 1.2 (`cor:weak_approx_spaces`), affine base case: the support matching.  Let
`U` be an object of the big fppf site with affine underlying scheme `X_U`, `R = Γ(X_U, 𝒪)`,
`h_U` the algebraic space it represents, and `Φ = (M ↦ M^~)` the associated-module functor
(`RelativeFM.Spaces.Affine.associated`).

* `mem_supportOfSheaf_associated_iff`: a point `p` of `h_U` lies in the support (Stacks 04KA)
  of the `𝒪_{h_U}`-module `N^~` exactly when its image in `Spec R` lies in the support of the
  `R`-module `N`.
* `cohomologySupportedOn_iff`: for `M ∈ D(R)`, `Φ(M) ∈ D(𝒪_{h_U})` is supported on
  `|V(I)|` (Stacks 08GF, AxiomMath's `CohomologySupportedOn`) exactly when every `Hⁿ(M)` is
  `I`-power torsion, that is, exactly when `M ∈ D_{V(I)}(R)` in the sense of the module model of
  the tree (`NeemanFiniteSupportM4.AffineIsSupportedIdeal`).  No finiteness of `I` is needed.
* `dqc_map`: `Φ(M)` lies in `D_qc(h_U)`.

Assumed: the tagged inputs `Tag06Z0ExactInput` (to form `Φ` on derived categories),
`Tag06Z0QcohInput` and `Tag07TYInput` of `Spaces/Affine/Inputs.lean`.  The rest is Mathlib
(the stalks of `M^~` are the localizations of `M`; restriction along an open immersion is the
pullback and commutes with stalks), AxiomMath's Stacks 04KB (`supportOfSheaf_subset_of_mono`,
in the import closure), the cohomology of `Φ(M)` (AxiomMath's `mapDerivedCategoryHomologyIso`,
a definition module added to the import list) and the tree's
`idealPowerTorsion_iff_support_subset_zeroLocus`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Affine

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Stalks of `M^~` pulled back along `X ≅ Spec R` -/

section Stalk

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) [IsOpenImmersion f]

/-- The stalk at `x` of the pullback of `N^~` along an open immersion `f : X ⟶ Spec R`
vanishes exactly when `f(x)` is outside the support of the `R`-module `N`. -/
theorem isZero_stalk_pullback_tilde_iff (N : ModuleCat.{u} R) (x : X) :
    IsZero (TopCat.Presheaf.stalk ((Scheme.Modules.pullback f).obj (tilde N)).val.presheaf x) ↔
      f x ∉ Module.support R N := by
  let e₁ : TopCat.Presheaf.stalk ((Scheme.Modules.pullback f).obj (tilde N)).val.presheaf x ≅
      TopCat.Presheaf.stalk (tilde N).val.presheaf (f x) :=
    ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor _ x).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback f).app (tilde N))).symm ≪≫
      (Scheme.Modules.restrictStalkNatIso f x).app (tilde N)
  rw [Iso.isZero_iff e₁, AddCommGrpCat.isZero_iff_subsingleton]
  let y : PrimeSpectrum R := f x
  have hy : f x ∈ Module.support R N ↔ Nontrivial (LocalizedModule y.asIdeal.primeCompl N) :=
    Module.mem_support_iff
  rw [hy, not_nontrivial_iff_subsingleton]
  have e : LocalizedModule y.asIdeal.primeCompl N ≃ₗ[R] (tilde N).presheaf.stalk y :=
    IsLocalizedModule.linearEquiv y.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap y.asIdeal.primeCompl N) (tilde.toStalk N y).hom
  exact (Equiv.subsingleton_congr e.toEquiv).symm

end Stalk

/-! ### Supports of associated modules -/

variable (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- The pullback of `N^~` along `X_U ≅ Spec R` is quasi-coherent. -/
instance isQuasicoherent_pullback_tilde (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).obj
      (tilde N)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent _).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback _).app (tilde N))
    (inferInstanceAs ((Scheme.Modules.restrictFunctor _).obj (tilde N)).IsQuasicoherent)

/-- **The support of `N^~` on `h_U` is the support of `N`** (Stacks 04KA, 07TY): a point `p`
of `h_U` is in the support of the associated module exactly when its image in `Spec R` is in
`Module.support R N`.  From `Tag07TYInput`. -/
theorem mem_supportOfSheaf_associated_iff (h07TY : Tag07TYInput B S hS)
    (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (p : points B S hS (yoneda.obj U)) :
    p ∈ supportOfSheaf B S hS (yoneda.obj U)
        ((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O)).obj ((associated U).obj N)) ↔
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom (schemePointsHomeomorph B S hS U p) ∈
        Module.support Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) N := by
  have h := h07TY U ((Scheme.Modules.pullback
    ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).obj (tilde N)) inferInstance p
  rw [isZero_stalk_pullback_tilde_iff, not_not] at h
  exact h

/-! ### The derived associated-module functor -/

section Derived

variable [PreservesFiniteLimits (associated U)]

/-- **`Φ : D(R) ⥤ D(𝒪_{h_U})`**, the functor induced on derived categories by the exact functor
`M ↦ M^~` (AxiomMath's `representedAffineDerivedAssociated`, by its body). -/
abbrev derivedAssociated :
    DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
      D B S hS (space U) :=
  (associated U).mapDerivedCategory

/-- `Φ` commutes with shifts (Mathlib's instance for `mapDerivedCategory`, read in the spelling
`D B S hS (space U)` of the target). -/
noncomputable instance commShift_derivedAssociated : (derivedAssociated U).CommShift ℤ :=
  inferInstanceAs ((associated U).mapDerivedCategory.CommShift ℤ)

/-- `Φ` is triangulated (Mathlib's instance for `mapDerivedCategory`). -/
instance isTriangulated_derivedAssociated : (derivedAssociated U).IsTriangulated :=
  inferInstanceAs (associated U).mapDerivedCategory.IsTriangulated

/-- `Hⁿ(Φ(M)) ≅ Hⁿ(M)^~` (AxiomMath's `mapDerivedCategoryHomologyIso`). -/
def homologyIso (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (n : ℤ) :
    (DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) n).obj
        ((derivedAssociated U).obj M) ≅
      (associated U).obj ((DerivedCategory.homologyFunctor _ n).obj M) :=
  ((associated U).mapDerivedCategoryHomologyIso n).app M

/-- **`Φ` lands in `D_qc(h_U)`**, from `Tag06Z0QcohInput`. -/
theorem dqc_derivedAssociated (hq : Tag06Z0QcohInput B S hS)
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    Dqc (space U) ((derivedAssociated U).obj M) := fun n =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso (homologyIso U M n).symm (hq U _)

end Derived

variable {U} in
/-- Isomorphic `𝒪_X`-modules have the same support (Stacks 04KB, both ways). -/
theorem supportOfSheaf_eq_of_iso {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (e : M ≅ N) :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M) =
      supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj N) :=
  let e' : ((SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M :
          Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) ≅
      (SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj N :=
    (SheafOfModules.toSheaf _).mapIso e
  have h₁ : Mono e'.hom := @IsIso.mono_of_iso _ _ _ _ e'.hom (Iso.isIso_hom e')
  have h₂ : Mono e'.inv := @IsIso.mono_of_iso _ _ _ _ e'.inv (Iso.isIso_inv e')
  le_antisymm (@supportOfSheaf_subset_of_mono B S hS X.1 X.2 _ _ e'.hom h₁)
    (@supportOfSheaf_subset_of_mono B S hS X.1 X.2 _ _ e'.inv h₂)

section Derived

variable [PreservesFiniteLimits (associated U)]

/-- **Support matching**: `Φ(M)` is supported on `|V(I)| ⊆ |h_U|` (Stacks 08GF) exactly when
every cohomology module of `M` is `I`-power torsion, i.e. `M ∈ D_{V(I)}(R)`.  From
`Tag07TYInput`; no finiteness of `I` is used. -/
theorem cohomologySupportedOn_iff (h07TY : Tag07TYInput B S hS)
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    Space.CohomologySupportedOn.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        (zeroLocusPoints U I) ((derivedAssociated U).obj M) ↔
      NeemanFiniteSupportM4.AffineIsSupportedIdeal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) I M := by
  have key : ∀ (n : ℤ) (p : points B S hS (yoneda.obj U)),
      p ∈ supportOfSheaf B S hS (yoneda.obj U)
          ((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O)).obj
            ((DerivedCategory.homologyFunctor
              (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) n).obj
                ((derivedAssociated U).obj M))) ↔
        ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom (schemePointsHomeomorph B S hS U p) ∈
          Module.support Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
            ((DerivedCategory.homologyFunctor
              (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) n).obj M) := fun n p => by
    rw [supportOfSheaf_eq_of_iso (X := space U) (homologyIso U M n)]
    exact mem_supportOfSheaf_associated_iff U h07TY _ p
  refine forall_congr' fun n => ?_
  rw [NeemanFiniteSupportM4.idealPowerTorsion_iff_support_subset_zeroLocus]
  constructor
  · intro h q hq
    obtain ⟨x, rfl⟩ :=
      (Scheme.homeoOfIso ((BigFppfOver.toScheme B S hS).obj U).isoSpec).surjective q
    obtain ⟨p, rfl⟩ := (schemePointsHomeomorph B S hS U).surjective x
    exact h ((key n p).2 hq)
  · intro h p hp
    exact h ((key n p).1 hp)

end Derived

end RelativeFM.Spaces.Affine
