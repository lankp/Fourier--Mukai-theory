/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.QCohSerre
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

@[expose] public section

/-!
# Extension closure of quasicoherent sheaves: the exact affine reduction

This file discharges all categorical steps in Stacks Tag 01IE for the extension
case. The sole geometric hypothesis is isolated in
`AffineExtensionSurjectivityInput`: global sections on an affine scheme are
surjective on the right map of a short exact sequence whose *outer* terms are
quasicoherent. In particular, the middle term is not assumed quasicoherent.
That statement is precisely the nontrivial local patching assertion in the
second half of the proof of Stacks Tag 01IE.

Given this input, we prove extension closure on every scheme. The proof applies
`tilde` to global sections, uses the two four lemmas for the middle vertical
morphism, and then invokes the affine-local criterion. No derived-category or
cohomology machinery is needed.
-/

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped ZeroObject

universe u

noncomputable section

attribute [local instance] moduleSpecΓFunctor_preservesZeroMorphisms
  moduleSpecΓFunctor_preservesFiniteLimits moduleSpecΓFunctor_isRightAdjoint

/-- The left-exact global-sections sequence, followed by `tilde`, maps to the
original short complex by the counit `tildeΓ ⟶ 𝟙`. -/
noncomputable def tildeGammaHom {R : CommRingCat.{u}}
    [(moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms]
    (S : ShortComplex (Spec R).Modules) :
    (S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R) ⟶ S :=
  ShortComplex.homMk S.X₁.fromTildeΓ S.X₂.fromTildeΓ S.X₃.fromTildeΓ
    ((tilde.adjunction (R := R)).counit.naturality S.f).symm
    ((tilde.adjunction (R := R)).counit.naturality S.g).symm

@[simp] lemma tildeGammaHom_τ₁ {R : CommRingCat.{u}}
    [(moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms]
    (S : ShortComplex (Spec R).Modules) :
    (tildeGammaHom S).τ₁ = S.X₁.fromTildeΓ := rfl

@[simp] lemma tildeGammaHom_τ₂ {R : CommRingCat.{u}}
    [(moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms]
    (S : ShortComplex (Spec R).Modules) :
    (tildeGammaHom S).τ₂ = S.X₂.fromTildeΓ := rfl

@[simp] lemma tildeGammaHom_τ₃ {R : CommRingCat.{u}}
    [(moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms]
    (S : ShortComplex (Spec R).Modules) :
    (tildeGammaHom S).τ₃ = S.X₃.fromTildeΓ := rfl

/-- **Categorical part of Stacks Tag 01IE.** On `Spec R`, a short exact
sequence with quasicoherent outer terms has quasicoherent middle term as soon
as its right map is surjective on global sections. -/
theorem isQuasicoherent_X₂_spec_of_shortExact_of_surjective
    {R : CommRingCat.{u}} {S : ShortComplex (Spec R).Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hg : Function.Surjective ((moduleSpecΓFunctor (R := R)).map S.g)) :
    S.X₂.IsQuasicoherent := by
  letI : IsIso S.X₁.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁
  letI : IsIso S.X₃.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃
  letI : (moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms :=
    moduleSpecΓFunctor_preservesZeroMorphisms R
  letI : PreservesFiniteLimits (moduleSpecΓFunctor (R := R)) :=
    moduleSpecΓFunctor_preservesFiniteLimits R
  letI : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
    moduleSpecΓFunctor_isRightAdjoint R
  letI : (moduleSpecΓFunctor (R := R)).Additive :=
    (moduleSpecΓFunctor (R := R)).additive_of_preserves_binary_products
  have hΓ : (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
    have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (moduleSpecΓFunctor (R := R))).mp inferInstance S hS
    refine ShortComplex.ShortExact.mk' h.1 h.2 ?_
    exact (ModuleCat.epi_iff_surjective _).mpr hg
  have hT : ((S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R)).ShortExact :=
    hΓ.map_of_exact (tilde.functor R)
  let φ := tildeGammaHom S
  have hφmono : Mono φ.τ₂ := by
    apply ShortComplex.mono_of_mono_of_mono_of_mono φ hT.exact hS.mono_f
    · dsimp [φ]
      exact @CategoryTheory.IsIso.mono_of_iso _ _ _ _
        S.X₁.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁)
    · dsimp [φ]
      exact @CategoryTheory.IsIso.mono_of_iso _ _ _ _
        S.X₃.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃)
  have hφepi : Epi φ.τ₂ := by
    apply ShortComplex.epi_of_epi_of_epi_of_epi φ hS.exact hT.epi_g
    · dsimp [φ]
      exact @CategoryTheory.IsIso.epi_of_iso _ _ _ _
        S.X₁.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁)
    · dsimp [φ]
      exact @CategoryTheory.IsIso.epi_of_iso _ _ _ _
        S.X₃.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃)
  have : IsIso φ.τ₂ := isIso_of_mono_of_epi _
  apply (quasiCoherent (Spec R)).prop_of_iso (asIso φ.τ₂)
  change (tilde ((moduleSpecΓFunctor (R := R)).obj S.X₂)).IsQuasicoherent
  infer_instance

/-- The unique geometric input left by the categorical proof of the extension
case of Stacks Tags 01IE and 01LA(6). This is *not* the stronger assertion
that global sections preserve every epimorphism: only sequences with
quasicoherent outer terms occur, and the middle sheaf is arbitrary. -/
structure AffineExtensionSurjectivityInput : Prop where
  /-- Stacks Tag 01IE (the quasi-compact `D(f)`/`D(g)` patching argument):
  `Γ(Spec R)` is surjective on the right map after restriction to a short exact
  sequence with quasicoherent outer terms. -/
  surjective {R : CommRingCat.{u}} (S : ShortComplex (Spec R).Modules)
    (hS : S.ShortExact) (h₁ : S.X₁.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    Function.Surjective ((moduleSpecΓFunctor (R := R)).map S.g)

/-- Extension closure on `Spec R`, modulo exactly the Stacks 01IE global-section
patching statement. -/
theorem isQuasicoherent_X₂_spec_of_shortExact
    (H : AffineExtensionSurjectivityInput.{u}) {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    S.X₂.IsQuasicoherent := by
  letI : S.X₁.IsQuasicoherent := h₁
  letI : S.X₃.IsQuasicoherent := h₃
  exact isQuasicoherent_X₂_spec_of_shortExact_of_surjective
    (R := R) (S := S) hS (H.surjective (R := R) S hS h₁ h₃)

/-- Extension closure on an arbitrary affine scheme. Transport to `Spec Γ(X)`
is along the isomorphism `X.isoSpec`; no affine description of the middle sheaf
is assumed. -/
theorem isQuasicoherent_X₂_affine_of_shortExact
    (H : AffineExtensionSurjectivityInput.{u}) {X : Scheme.{u}} [IsAffine X]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    S.X₂.IsQuasicoherent := by
  letI : S.X₁.IsQuasicoherent := h₁
  letI : S.X₃.IsQuasicoherent := h₃
  let F := Scheme.Modules.restrictFunctor X.isoSpec.inv
  have hSF : (S.map F).ShortExact := hS.map_of_exact F
  have h₁F : (S.map F).X₁.IsQuasicoherent := by
    change (F.obj S.X₁).IsQuasicoherent
    infer_instance
  have h₃F : (S.map F).X₃.IsQuasicoherent := by
    change (F.obj S.X₃).IsQuasicoherent
    infer_instance
  have h₂F : (S.map F).X₂.IsQuasicoherent :=
    isQuasicoherent_X₂_spec_of_shortExact H hSF h₁F h₃F
  exact (isQuasicoherent_restrict_iff_of_isIso S.X₂ X.isoSpec.inv).1 h₂F

/-- **Extension closure of quasicoherent sheaves (Stacks Tag 01LA(6))**, with
all formal arguments proved and the unique affine patching fact supplied by
`AffineExtensionSurjectivityInput`. -/
theorem quasiCoherent_isClosedUnderExtensions
    (H : AffineExtensionSurjectivityInput.{u}) (X : Scheme.{u}) :
    (quasiCoherent X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    refine (isQuasicoherent_iff_forall_affineOpens S.X₂).2 fun U ↦ ?_
    letI : S.X₁.IsQuasicoherent := h₁
    letI : S.X₃.IsQuasicoherent := h₃
    let F := Scheme.Modules.restrictFunctor U.val.ι
    have hSF : (S.map F).ShortExact := hS.map_of_exact F
    have h₁F : (S.map F).X₁.IsQuasicoherent := by
      change (F.obj S.X₁).IsQuasicoherent
      infer_instance
    have h₃F : (S.map F).X₃.IsQuasicoherent := by
      change (F.obj S.X₃).IsQuasicoherent
      infer_instance
    exact isQuasicoherent_X₂_affine_of_shortExact H hSF h₁F h₃F

/-- Structure-valued form matching the repository's scoreboard row 3. -/
theorem quasicoherentExtensionInput
    (H : AffineExtensionSurjectivityInput.{u}) (X : Scheme.{u}) :
    QuasicoherentExtensionInput X where
  extensionClosed := quasiCoherent_isClosedUnderExtensions H X

/-- The triangulated `D_qc` consequence consumed by the rest of the scheme
layer, again with Stacks 01IE as its only residual geometric input. -/
theorem isDQCohTriangulatedOfAffineExtensionSurjectivityInput
    (H : AffineExtensionSurjectivityInput.{u}) (X : Scheme.{u}) :
    (IsDQCoh X).IsTriangulated :=
  isDQCohTriangulatedOfExtensionInput X (quasicoherentExtensionInput H X)

/-- Conversely, affine extension closure supplies the global-section
surjectivity used above.  Hence the remaining input is not an artificial
strengthening: it is exactly the affine extension theorem in a form which
mentions no quasicoherence of the middle term. -/
theorem affineExtensionSurjectivityInput_of_extensionClosure
    (H : ∀ (R : CommRingCat.{u}), (quasiCoherent (Spec R)).IsClosedUnderExtensions) :
    AffineExtensionSurjectivityInput.{u} where
  surjective S hS h₁ h₃ := by
    letI : S.X₃.IsQuasicoherent := h₃
    letI : S.X₂.IsQuasicoherent := (H _).prop_X₂_of_shortExact hS h₁ h₃
    have hΓ := shortExact_map_moduleSpecΓFunctor_of_isQuasicoherent hS
    exact (ModuleCat.epi_iff_surjective _).mp hΓ.epi_g

/-- Precise equivalence isolating the outstanding geometric content of Stacks
Tags 01IE and 01LA(6). -/
theorem affineExtensionSurjectivityInput_iff :
    AffineExtensionSurjectivityInput.{u} ↔
      ∀ (R : CommRingCat.{u}), (quasiCoherent (Spec R)).IsClosedUnderExtensions :=
  ⟨fun H R ↦ quasiCoherent_isClosedUnderExtensions H (Spec R),
    affineExtensionSurjectivityInput_of_extensionClosure⟩

/-! ## Unconditional coproduct and split-extension cases -/

/-- On an affine scheme, small coproducts of quasicoherent sheaves in the
ambient category are quasicoherent.  Restrict to `Spec Γ(X)` and use the
proved essential-image coproduct closure of `tilde`. -/
theorem quasiCoherent_affine_isClosedUnderCoproducts
    (X : Scheme.{u}) [IsAffine X] (ι : Type u) :
    (quasiCoherent X).IsClosedUnderColimitsOfShape (Discrete ι) where
  colimitsOfShape_le := by
    rintro M ⟨c⟩
    let F := Scheme.Modules.restrictFunctor X.isoSpec.inv
    apply (isQuasicoherent_restrict_iff_of_isIso M X.isoSpec.inv).1
    letI : (quasiCoherent (Spec Γ(X, ⊤))).IsClosedUnderColimitsOfShape
        (Discrete ι) := quasiCoherent_spec_isClosedUnderCoproducts Γ(X, ⊤) ι
    apply (quasiCoherent (Spec Γ(X, ⊤))).prop_of_isColimit
      (isColimitOfPreserves F c.isColimit)
    intro j
    change (F.obj (c.diag.obj j)).IsQuasicoherent
    have := c.prop_diag_obj j
    infer_instance

/-- Small coproducts of quasicoherent sheaves are quasicoherent on every
scheme.  This is the ambient-category form of Stacks Tag 01LA(3), proved here
without any extension or global-section hypothesis. -/
theorem quasiCoherent_isClosedUnderCoproducts
    (X : Scheme.{u}) (ι : Type u) :
    (quasiCoherent X).IsClosedUnderColimitsOfShape (Discrete ι) where
  colimitsOfShape_le := by
    rintro M ⟨c⟩
    refine (isQuasicoherent_iff_forall_affineOpens M).2 fun U ↦ ?_
    let F := Scheme.Modules.restrictFunctor U.val.ι
    letI := quasiCoherent_affine_isClosedUnderCoproducts U.val.toScheme ι
    apply (quasiCoherent U.val.toScheme).prop_of_isColimit
      (isColimitOfPreserves F c.isColimit)
    intro j
    change (F.obj (c.diag.obj j)).IsQuasicoherent
    have := c.prop_diag_obj j
    infer_instance

/-- Binary biproducts of quasicoherent sheaves are quasicoherent on every
scheme, unconditionally. -/
theorem isQuasicoherent_biprod {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [HasBinaryBiproduct M N] :
    (M ⊞ N).IsQuasicoherent := by
  letI : (quasiCoherent X).IsClosedUnderColimitsOfShape
      (Discrete WalkingPair) :=
    ((quasiCoherent X).isClosedUnderColimitsOfShape_iff_of_equivalence
      (Discrete.equivalence Equiv.ulift.{u, 0}.symm)).2
      (quasiCoherent_isClosedUnderCoproducts X (ULift.{u} WalkingPair))
  apply (quasiCoherent X).prop_of_isColimit (BinaryBiproduct.isColimit M N)
  rintro ⟨j⟩
  cases j <;> assumption

/-- Every split short exact sequence with quasicoherent outer terms has a
quasicoherent middle term.  Unlike the general extension theorem above, this
case uses no input at all. -/
theorem isQuasicoherent_X₂_of_splitting {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (σ : S.Splitting)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.IsQuasicoherent :=
  (quasiCoherent X).prop_of_iso σ.isoBinaryBiproduct.symm
    (isQuasicoherent_biprod S.X₁ S.X₃)

#print axioms RelativeFM.isQuasicoherent_X₂_spec_of_shortExact_of_surjective
#print axioms RelativeFM.isQuasicoherent_X₂_affine_of_shortExact
#print axioms RelativeFM.quasiCoherent_isClosedUnderExtensions
#print axioms RelativeFM.quasicoherentExtensionInput
#print axioms RelativeFM.isDQCohTriangulatedOfAffineExtensionSurjectivityInput
#print axioms RelativeFM.affineExtensionSurjectivityInput_of_extensionClosure
#print axioms RelativeFM.affineExtensionSurjectivityInput_iff
#print axioms RelativeFM.quasiCoherent_affine_isClosedUnderCoproducts
#print axioms RelativeFM.quasiCoherent_isClosedUnderCoproducts
#print axioms RelativeFM.isQuasicoherent_biprod
#print axioms RelativeFM.isQuasicoherent_X₂_of_splitting

end

end RelativeFM
