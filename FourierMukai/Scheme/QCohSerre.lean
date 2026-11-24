/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.Derived
import FourierMukai.Scheme.OpenImmersion
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.ObjectProperty.Kernels

@[expose] public section

/-!
# Quasicoherence: locality, exactness, and what `D_qc` really needs

Stacks 01LA says quasicoherent sheaves are closed under extensions.  This file
does not prove that, but it reduces what the derived layer actually needs to a
much smaller input.

Proved unconditionally: quasicoherence is affine-local (including reflection
along isomorphisms of schemes); `tilde` is exact on `Spec R`; quasicoherent
sheaves are closed under kernels and cokernels *inside the ambient category*;
affine global sections are exact when the outer two terms are quasicoherent; and
a five-term weak-Serre lemma.  Consequently `QuasicoherentExtensionInput` **alone**
makes `IsDQCoh X` triangulated (`isDQCohTriangulatedOfExtensionInput`) with direct
mapping-cone closure — the strong subobject and quotient hypotheses used earlier
are not needed for that consequence.  `quasicoherentSerreInputOfStrongClosure`
assembles the strong interface from three explicitly named 01LA fields, so a
future proof of extension closure plugs in without touching `Derived.lean`.

Not proved: extension closure itself, and arbitrary subobject or quotient
closure.  No claim of full 01LA is made.

Found by a member of the Ultramath run `smwv1bkrk` (direction AF1).
-/

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry
open scoped ZeroObject

universe u v w

noncomputable section

/-! ## Affine-local quasicoherence -/

/-- Restriction along an isomorphism of schemes preserves and reflects
quasicoherence.  This is the isomorphism case of the affine-local criterion for
Stacks Tag **01BD**. -/
theorem isQuasicoherent_restrict_iff_of_isIso {X Y : Scheme.{u}}
    (M : X.Modules) (f : Y ⟶ X) [IsIso f] :
    (M.restrict f).IsQuasicoherent ↔ M.IsQuasicoherent := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  have h' := Scheme.Modules.isQuasicoherent_restrictFunctor (inv f) (M.restrict f)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.restrictFunctorComp (inv f) f).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (IsIso.inv_hom_id f)).app M ≪≫
      (Scheme.Modules.restrictFunctorId).app M) h'

/-- The open-subscheme equivalence sends quasicoherent modules on the slice
site to quasicoherent modules on the open subscheme. -/
instance isQuasicoherent_overEquiv_functor {X : Scheme.{u}} (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) [hM : M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv U).functor.obj M).IsQuasicoherent := by
  let G := U.overEquivalence.inverse
  have hcont (V : TopologicalSpace.Opens {x : X // x ∈ U}) :
      (Over.post (X := V) G).IsContinuous
        ((Opens.grothendieckTopology {x : X // x ∈ U}).over V)
        (((Opens.grothendieckTopology X).over U).over (G.obj V)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous G _ _).overPost V)
  let ψ := (U.overPullbackSheafEquivOver.app X.ringCatSheaf).inv
  have hψ : IsIso ψ := by dsimp [ψ]; infer_instance
  exact @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ ψ
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) _ hψ hcont _ _ M hM

/-- The inverse open-subscheme equivalence preserves quasicoherence. -/
instance isQuasicoherent_overEquiv_inverse {X : Scheme.{u}} (U : X.Opens)
    (M : U.toScheme.Modules) [hM : M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsQuasicoherent := by
  let G := U.overEquivalence.functor
  have hcont (V : Over U) : (Over.post (X := V) G).IsContinuous
      (((Opens.grothendieckTopology X).over U).over V)
      ((Opens.grothendieckTopology {x : X // x ∈ U}).over (G.obj V)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous G _ _).overPost V)
  let ψ := (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
  have hψ : IsIso ψ := by dsimp [ψ]; infer_instance
  exact @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ ψ
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) _ hψ hcont _ _ M hM

/-- Quasicoherence on the slice site agrees with quasicoherence after
restriction to the corresponding open subscheme. -/
theorem isQuasicoherent_over_iff {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) :
    (M.over U).IsQuasicoherent ↔ (M.restrict U.ι).IsQuasicoherent := by
  let e := (Scheme.Modules.overFunctorEquiv U).app M
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso e
      (isQuasicoherent_overEquiv_functor U (M.over U))
  · exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
      ((Scheme.Modules.overEquiv U).unitIso.app (M.over U) ≪≫
        (Scheme.Modules.overEquiv U).inverse.mapIso e).symm
      (isQuasicoherent_overEquiv_inverse U (M.restrict U.ι))

/-- **Affine-local criterion for quasicoherence, cover form** (Stacks Tag
**01BD**).  No exactness or cohomology hypothesis is needed. -/
theorem isQuasicoherent_iff_of_iSup_eq_top {X : Scheme.{u}} {ι : Sort*}
    (M : X.Modules) (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    M.IsQuasicoherent ↔ ∀ i, (M.restrict (U i).ι).IsQuasicoherent := by
  refine ⟨fun _ _ ↦ inferInstance, fun h ↦ ?_⟩
  have (V : Set.range U) : (M.over V.val).IsQuasicoherent := by
    obtain ⟨_, i, rfl⟩ := V
    exact (isQuasicoherent_over_iff M (U i)).2 (h i)
  exact SheafOfModules.IsQuasicoherent.of_coversTop M
    (Subtype.val : Set.range U → X.Opens)
    (by rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover, ← hU]
        exact iSup_range' id U)

/-- **Affine-local criterion for quasicoherence** (Stacks Tag **01BD**). -/
theorem isQuasicoherent_iff_forall_affineOpens {X : Scheme.{u}} (M : X.Modules) :
    M.IsQuasicoherent ↔ ∀ U : X.affineOpens, (M.restrict U.val.ι).IsQuasicoherent :=
  isQuasicoherent_iff_of_iSup_eq_top M (fun U : X.affineOpens ↦ U.val)
    (iSup_affineOpens_eq_top X)

/-! ## Exactness of the associated-sheaf functor -/

/-- An injective linear map induces injective section maps for the associated
sheaf.  The pointwise statement follows from exactness of localization. -/
theorem tilde_map_app_injective {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (hf : Function.Injective f.hom) (U : (Spec R).Opensᵒᵖ) :
    Function.Injective ((tilde.map f).val.app U) := by
  have hloc (p : PrimeSpectrum R) :
      Function.Injective (StructureSheaf.Localizations.comapFun f.hom p) := by
    simp only [PrimeSpectrum.comap_id]
    change Function.Injective (IsLocalizedModule.map p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) f.hom)
    exact IsLocalizedModule.map_injective _ _ _ _ hf
  intro s t hst
  exact Subtype.ext (funext fun p ↦ hloc p.val (congr_arg (fun x ↦ x.val p) hst))

/-- The associated-sheaf functor preserves monomorphisms. -/
instance mono_tilde_map {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Mono f] : Mono (tilde.map f) :=
  (SheafOfModules.forget _).mono_of_mono_map <| PresheafOfModules.mono_of_injective
    fun U ↦ tilde_map_app_injective f ((ModuleCat.mono_iff_injective f).mp ‹_›) U

/-- The associated-sheaf functor is exact (Stacks Tag **00NX**).  Its right
exactness comes from the adjunction with global sections; left exactness is
`tilde_map_app_injective`. -/
noncomputable instance preservesFiniteLimits_tildeFunctor (R : CommRingCat.{u}) :
    PreservesFiniteLimits (tilde.functor R) := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have := hS.mono_f
  exact ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mp
    inferInstance S hS).1, inferInstanceAs (Mono (tilde.map S.f))⟩

/-! ## Affine global sections -/

/-- Global sections on `Spec R` are right adjoint to the associated-sheaf
functor. -/
instance moduleSpecΓFunctor_isRightAdjoint (R : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
  (tilde.adjunction (R := R)).isRightAdjoint

/-- Global sections preserve finite limits, hence zero morphisms. -/
noncomputable instance moduleSpecΓFunctor_preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (moduleSpecΓFunctor (R := R)) := by
  let _ : PreservesLimitsOfSize.{u, u} (moduleSpecΓFunctor (R := R)) :=
    (tilde.adjunction (R := R)).rightAdjoint_preservesLimits
  infer_instance

/-- Global sections preserve zero morphisms. -/
noncomputable instance moduleSpecΓFunctor_preservesZeroMorphisms (R : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_preserves_terminal_object

/-- An epimorphism between quasicoherent sheaves on an affine scheme is
surjective on global sections.  The proof uses only `tildeEquiv`, not an
unformalized affine-cohomology vanishing theorem. -/
theorem moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (f : M ⟶ N) [Epi f] [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective ((moduleSpecΓFunctor (R := R)).map f) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let F : P.FullSubcategory := ⟨M, inferInstance⟩
  let G : P.FullSubcategory := ⟨N, inferInstance⟩
  let g : F ⟶ G := ObjectProperty.homMk f
  have hg : Epi g := by
    have hg_hom : g.hom = f := ObjectProperty.homMk_hom (X := F) (Y := G) f
    apply P.ι.epi_of_epi_map
    rw [ObjectProperty.ι_map, hg_hom]
    exact (inferInstance : Epi f)
  have hΓ : Epi ((tildeEquiv (R := R)).inverse.map g) := Functor.map_epi _ g
  have hmap : (tildeEquiv (R := R)).inverse.map g =
      (moduleSpecΓFunctor (R := R)).map f := by
    exact congrArg (moduleSpecΓFunctor (R := R)).map
      (ObjectProperty.homMk_hom (X := F) (Y := G) f)
  rw [hmap] at hΓ
  exact (ModuleCat.epi_iff_surjective _).mp hΓ

attribute [local instance] moduleSpecΓFunctor_preservesZeroMorphisms
  moduleSpecΓFunctor_preservesFiniteLimits moduleSpecΓFunctor_isRightAdjoint

/-- Global sections preserve a short exact sequence whose middle and right
terms are quasicoherent on `Spec R`. -/
theorem shortExact_map_moduleSpecΓFunctor_of_isQuasicoherent
    {R : CommRingCat.{u}} {S : ShortComplex (Spec R).Modules}
    (hS : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    [(moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms] :
    (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
  have : (moduleSpecΓFunctor (R := R)).Additive :=
    (moduleSpecΓFunctor (R := R)).additive_of_preserves_binary_products
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (moduleSpecΓFunctor (R := R))).mp inferInstance S hS
  have : Epi S.g := hS.epi_g
  have hΓ : Epi ((moduleSpecΓFunctor (R := R)).map S.g) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent S.g)
  exact { exact := h.1, mono_f := h.2, epi_g := hΓ }

/-! ## Kernels and cokernels -/

/-- On `Spec R`, the ambient kernel of a map between quasicoherent sheaves is
the associated sheaf of the kernel on global sections. -/
noncomputable def tildeKernelIso {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    tilde (kernel ((moduleSpecΓFunctor (R := R)).map f)) ≅ kernel f :=
  PreservesKernel.iso (tilde.functor R) _ ≪≫
    kernel.mapIso _ _
      (@asIso _ _ _ _ M.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M))
      (@asIso _ _ _ _ N.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) N))
      ((tilde.adjunction (R := R)).counit.naturality f)

/-- Affine kernel closure for quasicoherent sheaves. -/
theorem isQuasicoherent_kernel_spec {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel f).IsQuasicoherent :=
  (quasiCoherent (Spec R)).prop_of_iso (tildeKernelIso f) inferInstance

/-- Kernel closure on an arbitrary affine scheme. -/
theorem isQuasicoherent_kernel_affine {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel f).IsQuasicoherent := by
  let F := Scheme.Modules.restrictFunctor X.isoSpec.inv
  have : (F.obj (kernel f)).IsQuasicoherent :=
    (quasiCoherent (Spec Γ(X, ⊤))).prop_of_iso
      (PreservesKernel.iso F f).symm (isQuasicoherent_kernel_spec (F.map f))
  exact (isQuasicoherent_restrict_iff_of_isIso _ X.isoSpec.inv).1 this

/-- Kernels of morphisms between quasicoherent sheaves are quasicoherent
(Hartshorne II.5.7; Stacks Tag **01LA**). -/
instance isQuasicoherent_kernel {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel f).IsQuasicoherent := by
  refine (isQuasicoherent_iff_forall_affineOpens (kernel f)).2 fun U ↦ ?_
  let F := Scheme.Modules.restrictFunctor U.val.ι
  exact (quasiCoherent U.val.toScheme).prop_of_iso
    (PreservesKernel.iso F f).symm (isQuasicoherent_kernel_affine (F.map f))

/-- On `Spec R`, the ambient cokernel of a map between quasicoherent sheaves is
the associated sheaf of the cokernel on global sections. -/
noncomputable def tildeCokernelIso {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    tilde (cokernel ((moduleSpecΓFunctor (R := R)).map f)) ≅ cokernel f :=
  PreservesCokernel.iso (tilde.functor R) _ ≪≫
    cokernel.mapIso _ _
      (@asIso _ _ _ _ M.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M))
      (@asIso _ _ _ _ N.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) N))
      ((tilde.adjunction (R := R)).counit.naturality f)

/-- Affine cokernel closure for quasicoherent sheaves. -/
theorem isQuasicoherent_cokernel_spec {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel f).IsQuasicoherent :=
  (quasiCoherent (Spec R)).prop_of_iso (tildeCokernelIso f) inferInstance

/-- Cokernel closure on an arbitrary affine scheme. -/
theorem isQuasicoherent_cokernel_affine {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel f).IsQuasicoherent := by
  let F := Scheme.Modules.restrictFunctor X.isoSpec.inv
  have : (F.obj (cokernel f)).IsQuasicoherent :=
    (quasiCoherent (Spec Γ(X, ⊤))).prop_of_iso
      (PreservesCokernel.iso F f).symm (isQuasicoherent_cokernel_spec (F.map f))
  exact (isQuasicoherent_restrict_iff_of_isIso _ X.isoSpec.inv).1 this

/-- Cokernels of morphisms between quasicoherent sheaves are quasicoherent
(Hartshorne II.5.7; Stacks Tag **01LA**). -/
instance isQuasicoherent_cokernel {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel f).IsQuasicoherent := by
  refine (isQuasicoherent_iff_forall_affineOpens (cokernel f)).2 fun U ↦ ?_
  let F := Scheme.Modules.restrictFunctor U.val.ι
  exact (quasiCoherent U.val.toScheme).prop_of_iso
    (PreservesCokernel.iso F f).symm (isQuasicoherent_cokernel_affine (F.map f))

/-- Package ambient kernel closure as an object-property instance. -/
instance quasiCoherent_isClosedUnderKernels (X : Scheme.{u}) :
    (quasiCoherent X).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    have := hM
    have := hN
    exact (quasiCoherent X).prop_of_iso
      (limit.isoLimitCone ⟨k, hk⟩) (isQuasicoherent_kernel f)

/-- Package ambient cokernel closure as an object-property instance. -/
instance quasiCoherent_isClosedUnderCokernels (X : Scheme.{u}) :
    (quasiCoherent X).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    have := hM
    have := hN
    exact (quasiCoherent X).prop_of_iso
      (colimit.isoColimitCocone ⟨k, hk⟩) (isQuasicoherent_cokernel f)

/-! ## Weak Serre classes and triangulated cohomological subcategories -/

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)
  [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]

/-- **Five-term lemma for a weak Serre class.** If the four outer objects of
an exact five-term sequence satisfy `P`, then so does its middle object. -/
theorem prop_X₂_of_exact_of_exact_of_exact {S : ShortComplex C} (hS : S.Exact)
    {A E : C} {a : A ⟶ S.X₁} {e : S.X₃ ⟶ E}
    (wa : a ≫ S.f = 0) (we : S.g ≫ e = 0)
    (ha : (ShortComplex.mk a S.f wa).Exact)
    (he : (ShortComplex.mk S.g e we).Exact)
    (hA : P A) (h₁ : P S.X₁) (h₃ : P S.X₃) (hE : P E) : P S.X₂ := by
  let T := ShortComplex.mk (cokernel.desc a S.f wa) (kernel.lift e S.g we) (by ext; simp)
  have : Mono T.f := ha.mono_cokernelDesc
  have : Epi T.g := he.epi_kernelLift
  let T' := ShortComplex.mk (cokernel.desc a S.f wa) S.g (by ext; simp)
  let φ : S ⟶ T' := ShortComplex.homMk (cokernel.π a) (𝟙 _) (𝟙 _)
    (by simp [T']) (by simp [T'])
  have : Epi φ.τ₁ := inferInstanceAs (Epi (cokernel.π a))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 S.X₂))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 S.X₃))
  let ψ : T ⟶ T' := ShortComplex.homMk (𝟙 _) (𝟙 _) (kernel.ι e)
    (by simp [T, T']) (by simp [T, T'])
  have : Epi ψ.τ₁ := inferInstanceAs (Epi (𝟙 (cokernel a)))
  have : IsIso ψ.τ₂ := inferInstanceAs (IsIso (𝟙 S.X₂))
  have : Mono ψ.τ₃ := inferInstanceAs (Mono (kernel.ι e))
  have hT : T.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS)
  exact P.prop_X₂_of_shortExact (S := T) ⟨hT⟩
    (P.prop_cokernel a hA h₁) (P.prop_kernel e h₃ hE)

end ObjectProperty

section WeakCohomologyWithin

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]

/-- Cohomological inverse images of weak Serre classes are closed in the middle
position of distinguished triangles. -/
instance (priority := 90) cohomologyWithin_isTriangulatedClosed₂_of_weakSerre :
    (cohomologyWithin P).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ n ↦
    RelativeFM.ObjectProperty.prop_X₂_of_exact_of_exact_of_exact P
      (DerivedCategory.HomologySequence.exact₂ T hT n) _ _
      (DerivedCategory.HomologySequence.exact₁ T hT (n - 1) n)
      (DerivedCategory.HomologySequence.exact₃ T hT n (n + 1))
      (h₃ (n - 1)) (h₁ n) (h₃ n) (h₁ (n + 1)))

/-- Cohomological inverse images of weak Serre classes are triangulated. -/
instance (priority := 90) cohomologyWithin_isTriangulated_of_weakSerre :
    (cohomologyWithin P).IsTriangulated where

end WeakCohomologyWithin

/-- The only geometric input still needed for the triangulated structure on
`D_qc(X)`: extension closure of quasicoherent sheaves, Stacks Tag **01LA(6)**.
Unlike `QuasicoherentSerreInput`, this does not ask for the stronger,
unnecessary subobject and quotient fields. -/
structure QuasicoherentExtensionInput (X : Scheme.{u}) : Prop where
  extensionClosed : (quasiCoherent X).IsClosedUnderExtensions

/-- `D_qc(X)` is triangulated from extension closure alone.  Kernels and
cokernels are proved above; the five-term long exact cohomology argument does
not need arbitrary subobjects or quotients. -/
instance isDQCoh_isTriangulatedOfExtension (X : Scheme.{u})
    [(quasiCoherent X).IsClosedUnderExtensions] : (IsDQCoh X).IsTriangulated :=
  cohomologyWithin_isTriangulated_of_weakSerre (quasiCoherent X)

/-- Structure-valued form of `isDQCoh_isTriangulatedOfExtension`. -/
theorem isDQCohTriangulatedOfExtensionInput (X : Scheme.{u})
    (h : QuasicoherentExtensionInput X) : (IsDQCoh X).IsTriangulated := by
  let _ := h.extensionClosed
  infer_instance

/-- Direct mapping-cone form of `isDQCohTriangulatedOfExtensionInput`.
Given a morphism between objects with quasicoherent cohomology, there is a
distinguished cocone whose cone again has quasicoherent cohomology. -/
theorem isDQCoh_exists_coneOfExtensionInput (X : Scheme.{u})
    (h : QuasicoherentExtensionInput X) {E F : Derived X} (f : E ⟶ F)
    (hE : IsDQCoh X E) (hF : IsDQCoh X F) :
    ∃ (Z : Derived X) (b : F ⟶ Z) (c : Z ⟶ E⟦(1 : ℤ)⟧),
      IsDQCoh X Z ∧ Triangle.mk f b c ∈ distTriang (Derived X) := by
  let _ := h.extensionClosed
  obtain ⟨Z, hZ, b, c, hT⟩ :=
    (IsDQCoh X).distinguished_cocone_triangle f hE hF
  exact ⟨Z, b, c, hZ, hT⟩

/-- The three strong closure facts used only to build the pre-existing
`QuasicoherentSerreInput`.  All are standard parts of Stacks Tag **01LA**;
the first two are not needed for triangulatedness of `D_qc(X)`. -/
structure QuasicoherentStrongClosureInput (X : Scheme.{u}) : Prop where
  subobjects : (quasiCoherent X).IsClosedUnderSubobjects
  quotients : (quasiCoherent X).IsClosedUnderQuotients
  extensions : (quasiCoherent X).IsClosedUnderExtensions

/-- Assemble the original strong Serre input from its three non-zero fields. -/
theorem quasicoherentSerreInputOfStrongClosure (X : Scheme.{u})
    (h : QuasicoherentStrongClosureInput X) : QuasicoherentSerreInput X where
  serreClass :=
    { exists_zero := (quasiCoherent_containsZero X).exists_zero
      prop_of_mono := h.subobjects.prop_of_mono
      prop_of_epi := h.quotients.prop_of_epi
      prop_X₂_of_shortExact := h.extensions.prop_X₂_of_shortExact }

/-! ### Axiom audit -/


end

end RelativeFM
