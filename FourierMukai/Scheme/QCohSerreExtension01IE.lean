/-
Stacks 01IE: affine surjectivity for extensions with quasicoherent kernel.
This development is intended for FourierMukai/Scheme/QCohSerreExtension.lean.
-/
import FourierMukai.Scheme.QCohSerreExtension
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.CategoryTheory.Preadditive.LeftExact

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace Opposite
open scoped ZeroObject AlgebraicGeometry

universe u v v' u'

noncomputable section

namespace AffineExtension

open PrimeSpectrum

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

set_option backward.isDefEq.respectTransparency.types false in
/-- The two elementary localization consequences needed in the proof of Stacks 01IE.
This is a public, small version of the auxiliary predicate used privately in
`AlgebraicGeometry.Modules.Tilde`. -/
structure BasicOpenAux (V : (Spec R).Opens) where
  existence (f : R) (hf : basicOpen f ≤ V) (s : Γ(M, basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)), M.presheaf.map (homOfLE hf).op t = f ^ n • s
  uniqueness (f : R) (hf : basicOpen f ≤ V) (t : Γ(M, V)) :
    M.presheaf.map (.op <| homOfLE hf) t = (0 : Γ(M, basicOpen f)) →
    ∃ (n : ℕ), f ^ n • t = 0

set_option backward.isDefEq.respectTransparency false in
/-- A sheaf whose basic-open restriction maps are localizations satisfies
`BasicOpenAux` on the whole space. -/
theorem basicOpenAuxTopOfIsLocalizing {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (h : IsLocalizing (modulesSpecToSheaf.obj M)) : BasicOpenAux M ⊤ where
  existence f _ s := by
    let φ := ((modulesSpecToSheaf.obj M).obj.map (basicOpen f).leTop.op).hom
    have hf : IsLocalizedModule.Away f φ := h f
    obtain ⟨n, y, hy⟩ := hf.surj _ _ s
    exact ⟨n, y, hy.symm⟩
  uniqueness f _ t ht := by
    let φ := ((modulesSpecToSheaf.obj M).obj.map (basicOpen f).leTop.op).hom
    have hf : IsLocalizedModule.Away f φ := h f
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) φ).mp ht
    exact ⟨n, hn⟩

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of `BasicOpenAux` from an open to a basic open contained in it. -/
theorem BasicOpenAux.of_le {R : CommRingCat.{u}} {M : (Spec R).Modules}
    {V : (Spec R).Opens} (g : R) (hg : basicOpen g ≤ V)
    (hV : BasicOpenAux M V) : BasicOpenAux M (basicOpen g) where
  existence f hfg s := by
    obtain ⟨n, t, ht⟩ := hV.existence f (le_trans hfg hg) s
    use n, M.presheaf.map (homOfLE hg).op t
    simp [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, ht]
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
    obtain ⟨m, hm⟩ := hV.uniqueness _ (le_trans hfg hg) t' <| by
      rw [← homOfLE_comp hfg hg, op_comp, M.presheaf.map_comp_apply, ht',
        M.map_smul_Spec, ht]
      simp
    refine ⟨m, ((M.isSMulRegular_of_le_basicOpen le_rfl).pow n).right_eq_zero_of_smul ?_⟩
    simp [smul_comm, ← ht', ← M.map_smul_Spec, hm]

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (𝓡 : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

set_option backward.isDefEq.respectTransparency false in
/-- The forgetful functor from module sheaves to abelian-group sheaves preserves
finite colimits.  The proof uses that module sheafification is a left adjoint
with isomorphic counit, and that its composite with the forgetful functor is
ordinary abelian-group sheafification. -/
lemma preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{v} 𝓡) := by
  let L := PresheafOfModules.sheafification (J := J) (𝟙 𝓡.obj)
  let T := SheafOfModules.toSheaf.{v} 𝓡
  letI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  letI : T.Additive := T.additive_of_preserves_binary_products
  letI : PreservesFiniteColimits (L ⋙ T) :=
    preservesFiniteColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (J := J) (𝟙 𝓡.obj)).symm
  rw [((Functor.preservesFiniteColimits_tfae T).out 4 3 :)]
  intro X Y f
  let ε := (PresheafOfModules.sheafificationAdjunction (J := J) (𝟙 𝓡.obj)).counit
  have hdiag : parallelPair (L.map f.val) 0 ≅ parallelPair f 0 :=
    parallelPair.ext (asIso (ε.app X)) (asIso (ε.app Y)) (ε.naturality f) (by simp)
  have : PreservesColimit (parallelPair (L.map f.val) 0) T :=
    preservesColimit_of_preserves_colimit_cocone
      (CokernelCofork.isColimitMapCoconeEquiv _ _
        (isColimitOfPreserves L (cokernelIsCokernel f.val)))
      ((CokernelCofork.isColimitMapCoconeEquiv _ T).symm
        (CokernelCofork.isColimitMapCoconeEquiv _ (L ⋙ T)
          (isColimitOfPreserves (L ⋙ T) (cokernelIsCokernel f.val))))
  exact preservesColimit_of_iso_diagram T hdiag


set_option backward.isDefEq.respectTransparency false in
lemma epi_toSheaf {M N : SheafOfModules.{v} 𝓡} (f : M ⟶ N) (hf : Epi f) :
    Epi ((SheafOfModules.toSheaf 𝓡).map f) := by
  letI := hf
  let T := SheafOfModules.toSheaf.{v} 𝓡
  letI : PreservesFiniteColimits T := preservesFiniteColimits_toSheaf 𝓡
  letI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  letI : T.PreservesEpimorphisms := by infer_instance
  exact Functor.map_epi T f



end

lemma f_app_injective {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact) (U : (Spec R).Opens) :
    Function.Injective (S.f.app U) := by
  let F := SheafOfModules.evaluation (Spec R).ringCatSheaf (.op U)
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  letI : F.Additive := F.additive_of_preserves_binary_products
  have hmono := ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).mp
    inferInstance S hS).2
  exact (ModuleCat.mono_iff_injective _).mp hmono

/-- Left exactness of a short exact sequence, on sections over an arbitrary open. -/
lemma exists_preimage_f_app_of_g_app_eq_zero {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact) {U : (Spec R).Opens}
    (s : Γ(S.X₂, U)) (hs : S.g.app U s = 0) :
    ∃ t : Γ(S.X₁, U), S.f.app U t = s := by
  haveI : (SheafOfModules.evaluation (Spec R).ringCatSheaf (.op U)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  haveI : (SheafOfModules.evaluation (Spec R).ringCatSheaf (.op U)).Additive :=
    (SheafOfModules.evaluation (Spec R).ringCatSheaf (.op U)).additive_of_preserves_binary_products
  have hmap := ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (SheafOfModules.evaluation (Spec R).ringCatSheaf (.op U))).mp inferInstance S hS).1
  exact (ShortComplex.moduleCat_exact_iff _).mp hmap s hs

set_option backward.isDefEq.respectTransparency false in
lemma Hom_app_map {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (φ : M ⟶ N) {U V : (Spec R).Opens} (i : V ≤ U) (s : Γ(M, U)) :
    φ.app V (M.presheaf.map (homOfLE i).op s) =
      N.presheaf.map (homOfLE i).op (φ.app U s) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE i).op) s

set_option backward.isDefEq.respectTransparency false in
lemma map_top_restrict_eq {R : CommRingCat.{u}} (M : (Spec R).Modules)
    {U V W : (Spec R).Opens} (iU : U ≤ ⊤) (iV : V ≤ ⊤)
    (iW : W ≤ U) (jW : W ≤ V) (m : Γ(M, ⊤)) :
    M.presheaf.map (homOfLE iW).op (M.presheaf.map (homOfLE iU).op m) =
      M.presheaf.map (homOfLE jW).op (M.presheaf.map (homOfLE iV).op m) := by
  rw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply]
  exact congrArg (fun q => M.presheaf.map q m) (Subsingleton.elim _ _)

lemma Hom_app_smul_Spec {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (φ : M ⟶ N) (U : (Spec R).Opens) (r : R) (x : Γ(M, U)) :
    φ.app U (r • x) = r • φ.app U x := by
  rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.smul_Spec_def,
    Scheme.Modules.Hom.app_smul]

lemma Hom_app_smul_Spec' {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (φ : M ⟶ N) (U : (Spec R).Opens) (r : R) (x : Γ(M, U)) :
    @SMul.smul R Γ(N, U) inferInstance r (φ.app U x) =
      φ.app U (@SMul.smul R Γ(M, U) inferInstance r x) :=
  (Hom_app_smul_Spec φ U r x).symm

lemma g_f_app {R : CommRingCat.{u}} (S : ShortComplex (Spec R).Modules)
    (U : (Spec R).Opens) (x : Γ(S.X₁, U)) : S.g.app U (S.f.app U x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, S.zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Local lifting on a basic open for an epimorphism of sheaves of modules. -/
lemma exists_basicOpen_lift {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (φ : M ⟶ N) [Epi φ] (m : Γ(N, ⊤)) (p : Spec R) :
    ∃ (g : R) (_ : p ∈ basicOpen g) (s : Γ(M, basicOpen g)),
      φ.app (basicOpen g) s = N.presheaf.map (homOfLE le_top).op m := by
  let T := SheafOfModules.toSheaf (Spec R).ringCatSheaf
  let ψ := T.map φ
  have hφ : @Epi (SheafOfModules (Spec R).ringCatSheaf) _ M N φ := by
    change Epi φ
    infer_instance
  have hψ : @Epi (TopCat.Sheaf AddCommGrpCat (Spec R)) _ _ _ ψ := by
    change Epi ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map φ)
    exact epi_toSheaf _ φ hφ
  have hloc : TopCat.Presheaf.IsLocallySurjective ψ.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi ψ).mpr hψ
  obtain ⟨V, hV, ⟨t, ht⟩, hpV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff ψ.hom).mp hloc ⊤ m p (by simp)
  change ψ.hom.app (.op V) t = N.presheaf.map (homOfLE hV).op m at ht
  obtain ⟨a, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hgV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpV V.2
  refine ⟨g, hpg, M.presheaf.map (homOfLE hgV).op t, ?_⟩
  change ψ.hom.app _ (M.presheaf.map (homOfLE hgV).op t) = _
  have hn : ψ.hom.app _ (M.presheaf.map (homOfLE hgV).op t) =
      N.presheaf.map (homOfLE hgV).op (ψ.hom.app _ t) :=
    ConcreteCategory.congr_hom (ψ.hom.naturality (homOfLE hgV).op) t
  rw [hn]
  rw [ht]
  rw [← N.presheaf.map_comp_apply]
  exact congrArg (fun q => N.presheaf.map q m) (Subsingleton.elim _ _)

/-- Quasicoherent sheaves have the two power-clearing properties on every basic open. -/
theorem basicOpenAuxOfIsQuasicoherent {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (g : R) : BasicOpenAux M (basicOpen g) :=
  BasicOpenAux.of_le g (by exact le_top : basicOpen g ≤ (⊤ : (Spec R).Opens)) <|
    basicOpenAuxTopOfIsLocalizing M <|
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Correct one local lift by a section of the quasicoherent kernel. -/
lemma exists_corrected_lift {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent]
    (m : Γ(S.X₃, ⊤)) (f g : R)
    {s : Γ(S.X₂, basicOpen f)}
    (hs : S.g.app (basicOpen f) s = S.X₃.presheaf.map (homOfLE le_top).op m)
    {t : Γ(S.X₂, basicOpen g)}
    (ht : S.g.app (basicOpen g) t = S.X₃.presheaf.map (homOfLE le_top).op m) :
    ∃ (n : ℕ) (u : Γ(S.X₂, basicOpen g)),
      S.g.app (basicOpen g) u = f ^ n • S.X₃.presheaf.map (homOfLE le_top).op m ∧
      S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_right f g)).op u =
        S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_left f g)).op (f ^ n • s) := by
  let d := S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_left f g)).op s -
    S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_right f g)).op t
  have hd : S.g.app (basicOpen (f * g)) d = 0 := by
    dsimp [d]
    rw [map_sub, Hom_app_map, Hom_app_map, hs, ht,
      map_top_restrict_eq S.X₃ (U := basicOpen f) (V := basicOpen g)
        (W := basicOpen (f * g)) le_top le_top
        (basicOpen_mul_le_left f g) (basicOpen_mul_le_right f g) m]
    simp
  obtain ⟨a, ha⟩ := exists_preimage_f_app_of_g_app_eq_zero hS d hd
  obtain ⟨n, b, hb⟩ : ∃ (n : ℕ) (b : Γ(S.X₁, basicOpen g)),
      S.X₁.presheaf.map (homOfLE (basicOpen_mul_le_right f g)).op b = f ^ n • a := by
    obtain ⟨n, b, hb⟩ := (basicOpenAuxOfIsQuasicoherent S.X₁ g).existence
      (f * g) (basicOpen_mul_le_right f g) a
    rw [mul_pow, mul_smul, smul_comm] at hb
    have hug : IsUnit (algebraMap R (Module.End R Γ(S.X₁, basicOpen g)) (g ^ n)) := by
      rw [map_pow]
      exact (S.X₁.isUnit_algebraMap_end_of_le_basicOpen g le_rfl).pow n
    obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv hug
    refine ⟨n, ψ b, ?_⟩
    apply (S.X₁.isSMulRegular_of_le_basicOpen (basicOpen_mul_le_right f g)).pow n
    dsimp
    rw [← hb, ← Scheme.Modules.map_smul_Spec]
    congr 1
    exact congr($hψ b)
  refine ⟨n, f ^ n • t + S.f.app (basicOpen g) b, ?_, ?_⟩
  · simp only [map_add, Hom_app_smul_Spec, ht, g_f_app, add_zero]
  · rw [S.X₂.map_smul_Spec, map_add, S.X₂.map_smul_Spec, ← Hom_app_map, hb,
      Hom_app_smul_Spec, ha]
    dsimp [d]
    rw [smul_sub]
    abel

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Two corrected local lifts become compatible after a further power of `f`. -/
lemma exists_power_eq_on_intersection {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent]
    (m : Γ(S.X₃, ⊤)) (f g₁ g₂ : R) (n : ℕ)
    {s : Γ(S.X₂, basicOpen f)}
    {u₁ : Γ(S.X₂, basicOpen g₁)} {u₂ : Γ(S.X₂, basicOpen g₂)}
    (hu₁ : S.g.app (basicOpen g₁) u₁ = f ^ n • S.X₃.presheaf.map (homOfLE le_top).op m)
    (hu₂ : S.g.app (basicOpen g₂) u₂ = f ^ n • S.X₃.presheaf.map (homOfLE le_top).op m)
    (hs₁ : S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_right f g₁)).op u₁ =
      S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_left f g₁)).op (f ^ n • s))
    (hs₂ : S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_right f g₂)).op u₂ =
      S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_left f g₂)).op (f ^ n • s)) :
    ∃ k : ℕ,
      S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_left g₁ g₂)).op (f ^ k • u₁) =
        S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_right g₁ g₂)).op (f ^ k • u₂) := by
  let d := S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_left g₁ g₂)).op u₁ -
    S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_right g₁ g₂)).op u₂
  have hd : S.g.app (basicOpen (g₁ * g₂)) d = 0 := by
    dsimp [d]
    rw [map_sub, Hom_app_map, Hom_app_map, hu₁, hu₂,
      S.X₃.map_smul_Spec, S.X₃.map_smul_Spec,
      map_top_restrict_eq S.X₃ (U := basicOpen g₁) (V := basicOpen g₂)
        (W := basicOpen (g₁ * g₂)) le_top le_top
        (basicOpen_mul_le_left g₁ g₂) (basicOpen_mul_le_right g₁ g₂) m]
    simp
  obtain ⟨a, ha⟩ := exists_preimage_f_app_of_g_app_eq_zero hS d hd
  have ha0 : S.X₁.presheaf.map
      (homOfLE (basicOpen_mul_le_right f (g₁ * g₂))).op a = 0 := by
    apply f_app_injective hS
    rw [map_zero, Hom_app_map, ha]
    have hfg₁ : basicOpen (f * g₁) ≤ basicOpen g₁ := basicOpen_mul_le_right f g₁
    have hfg₂ : basicOpen (f * g₂) ≤ basicOpen g₂ := basicOpen_mul_le_right f g₂
    have hfgig₁ : basicOpen (f * (g₁ * g₂)) ≤ basicOpen (f * g₁) := by
      rw [← mul_assoc]
      exact basicOpen_mul_le_left _ _
    have hfgig₂ : basicOpen (f * (g₁ * g₂)) ≤ basicOpen (f * g₂) := by
      rw [mul_comm g₁ g₂, ← mul_assoc]
      exact basicOpen_mul_le_left _ _
    dsimp [d]
    rw [map_sub, ← S.X₂.presheaf.map_comp_apply, ← op_comp,
      ← S.X₂.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, homOfLE_comp,
      ← homOfLE_comp hfgig₁ hfg₁, ← homOfLE_comp hfgig₂ hfg₂,
      op_comp, S.X₂.presheaf.map_comp_apply, hs₁, S.X₂.map_smul_Spec, S.X₂.map_smul_Spec,
      ← S.X₂.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
      op_comp, S.X₂.presheaf.map_comp_apply, hs₂, S.X₂.map_smul_Spec, S.X₂.map_smul_Spec,
      ← S.X₂.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]
    simp
  obtain ⟨k, hk⟩ := (basicOpenAuxOfIsQuasicoherent S.X₁ (g₁ * g₂)).uniqueness
    (f * (g₁ * g₂)) (basicOpen_mul_le_right f (g₁ * g₂)) a ha0
  refine ⟨k, ?_⟩
  apply (S.X₂.isSMulRegular_of_le_basicOpen le_rfl).pow k
  simp only [S.X₂.map_smul_Spec _ (f ^ k), ← mul_smul, ← mul_pow, ← mul_comm f]
  rw [← sub_eq_zero, ← smul_sub]
  have h := congrArg (fun x : Γ(S.X₁, basicOpen (g₁ * g₂)) =>
    S.f.app (basicOpen (g₁ * g₂)) x) hk
  rw [Hom_app_smul_Spec, ha, map_zero] at h
  exact h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Stacks 01IE's finite patching step. -/
lemma exists_global_lift_of_finite_cover {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent]
    (m : Γ(S.X₃, ⊤)) (f : R)
    {s : Γ(S.X₂, basicOpen f)}
    (hs : S.g.app (basicOpen f) s = S.X₃.presheaf.map (homOfLE le_top).op m)
    {ι : Type*} [Finite ι] (g : ι → R) (t : ∀ i, Γ(S.X₂, basicOpen (g i)))
    (ht : ∀ i, S.g.app (basicOpen (g i)) (t i) =
      S.X₃.presheaf.map (homOfLE le_top).op m)
    (hcover : ⊤ ≤ basicOpen f ⊔ ⨆ i, basicOpen (g i)) :
    ∃ (N : ℕ) (a : Γ(S.X₂, ⊤)), S.g.app ⊤ a = f ^ N • m := by
  choose n u hu hus using fun i => exists_corrected_lift hS m f (g i) hs (ht i)
  let N := ⨆ i, n i
  have hn (i : ι) : n i ≤ N := le_ciSup (Finite.bddAbove_range _) _
  let v (i : ι) := f ^ (N - n i) • u i
  have hv (i : ι) : S.g.app (basicOpen (g i)) (v i) =
      f ^ N • S.X₃.presheaf.map (homOfLE le_top).op m := by
    dsimp [v]
    rw [Hom_app_smul_Spec, hu, ← mul_smul, ← pow_add, Nat.sub_add_cancel (hn i)]
  have hvs (i : ι) : S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_right f (g i))).op (v i) =
      S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_left f (g i))).op (f ^ N • s) := by
    dsimp [v]
    simp only [S.X₂.map_smul_Spec, hus, ← mul_smul, ← pow_add,
      Nat.sub_add_cancel (hn i)]
  choose k hk using fun i j => exists_power_eq_on_intersection hS m f (g i) (g j) N
    (hv i) (hv j) (hvs i) (hvs j)
  let K := ⨆ i, ⨆ j, k i j
  have hkle (i j : ι) : k i j ≤ K :=
    le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) _)
  let w (i : ι) := f ^ K • v i
  have hw (i : ι) : S.g.app (basicOpen (g i)) (w i) =
      f ^ (K + N) • S.X₃.presheaf.map (homOfLE le_top).op m := by
    dsimp [w]
    rw [Hom_app_smul_Spec, hv, ← mul_smul, ← pow_add]
  have hww (i j : ι) :
      S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (w i) =
        S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (w j) := by
    dsimp [w]
    have hKK : K = (K - k i j) + k i j :=
      (Nat.sub_add_cancel (hkle i j)).symm
    rw [hKK, pow_add, mul_smul, mul_smul]
    simpa only [S.X₂.map_smul_Spec] using
      congrArg (fun z : Γ(S.X₂, basicOpen (g i * g j)) =>
        f ^ (K - k i j) • z) (hk i j)
  have hsw (i : ι) :
      S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_right f (g i))).op (w i) =
        S.X₂.presheaf.map (homOfLE (basicOpen_mul_le_left f (g i))).op (f ^ (K + N) • s) := by
    dsimp [w]
    simp only [S.X₂.map_smul_Spec, hvs, pow_add, mul_smul]
  let U : Option ι → (Spec R).Opens
    | none => basicOpen f
    | some i => basicOpen (g i)
  let sf : ∀ j, Γ(S.X₂, U j)
    | none => f ^ (K + N) • s
    | some i => w i
  have hU : (⊤ : (Spec R).Opens) ≤ ⨆ j, U j := by
    simpa [U, iSup_option] using hcover
  have hnone (j : ι) :
      S.X₂.presheaf.map (Opens.infLELeft (U none) (U (some j))).op (sf none) =
        S.X₂.presheaf.map (Opens.infLERight (U none) (U (some j))).op (sf (some j)) := by
    have hinj : Function.Injective
        (S.X₂.presheaf.map (eqToHom (basicOpen_mul f (g j))).op) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback _
    apply hinj
    dsimp [Opens.infLELeft, Opens.infLERight, U, sf]
    simp_rw [← S.X₂.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
    exact (hsw j).symm
  have hcompat : TopCat.Presheaf.IsCompatible S.X₂.presheaf U sf := by
    intro a b
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j => exact hnone j
    | some i =>
      cases b with
      | none =>
        have h := congrArg (fun x : Γ(S.X₂, U none ⊓ U (some i)) =>
          S.X₂.presheaf.map (eqToHom (inf_comm (U (some i)) (U none))).op x)
          (hnone i).symm
        dsimp [Opens.infLELeft, Opens.infLERight, U, sf] at h ⊢
        simp_rw [← S.X₂.presheaf.map_comp_apply, ← op_comp,
          eqToHom_comp_homOfLE] at h
        exact h
      | some j =>
        have hinj : Function.Injective
            (S.X₂.presheaf.map (eqToHom (basicOpen_mul (g i) (g j))).op) :=
          ConcreteCategory.injective_of_mono_of_preservesPullback _
        apply hinj
        dsimp [Opens.infLELeft, Opens.infLERight, U, sf]
        simp_rw [← S.X₂.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
        exact hww i j
  obtain ⟨a, ha, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨_, S.X₂.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) hU sf hcompat
  have ha' (j : Option ι) : S.X₂.presheaf.map
      (homOfLE (show U j ≤ ⊤ from le_top)).op a = sf j := ha j
  refine ⟨K + N, a, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, S.X₃.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) hU
  intro j
  rw [← Hom_app_map, S.X₃.map_smul_Spec]
  cases j with
  | none =>
    change S.g.app (basicOpen f) (S.X₂.presheaf.map (homOfLE le_top).op a) = _
    rw [ha' none, Hom_app_smul_Spec, hs]
  | some i =>
    change S.g.app (basicOpen (g i)) (S.X₂.presheaf.map (homOfLE le_top).op a) = _
    rw [ha' (some i), hw]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Stacks 01IE.** Global sections are surjective on the right map of a short
exact sequence on `Spec R` with quasicoherent kernel. -/
theorem surjective_appTop {R : CommRingCat.{u}}
    (S : ShortComplex (Spec R).Modules) (hS : S.ShortExact)
    (h₁ : S.X₁.IsQuasicoherent) : Function.Surjective (S.g.app ⊤) := by
  classical
  letI : S.X₁.IsQuasicoherent := h₁
  letI : Epi S.g := hS.epi_g
  intro m
  choose g hg t ht using fun p => exists_basicOpen_lift S.g m p
  have hAll : (⨆ p : Spec R, basicOpen (g p)) = ⊤ := by
    apply top_unique
    intro p _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hg p⟩
  obtain ⟨s, hs⟩ := (TopologicalSpace.IsOpenCover.mk hAll).exists_finite_of_compactSpace
  let I : Ideal R :=
    { carrier := {r | ∃ a : Γ(S.X₂, ⊤), S.g.app ⊤ a = r • m}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro r₁ r₂ ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩
        exact ⟨a₁ + a₂, by simp only [map_add, ha₁, ha₂, add_smul]⟩
      smul_mem' := by
        rintro c r ⟨a, ha⟩
        exact ⟨c • a, by rw [Hom_app_smul_Spec, ha, smul_eq_mul, mul_smul]⟩ }
  have hlocal : ∀ p : Spec R, ∃ r ∈ I, r ∉ p.asIdeal := by
    intro p
    let s' : Finset (Spec R) := insert p s
    have hcover : (⊤ : (Spec R).Opens) ≤ basicOpen (g p) ⊔
        ⨆ q : s', basicOpen (g q.1) := by
      rw [← hs.iSup_eq_top]
      refine (iSup_le fun q => ?_).trans le_sup_right
      exact le_iSup_of_le ⟨q.1, Finset.mem_insert_of_mem q.2⟩ le_rfl
    obtain ⟨N, a, ha⟩ := exists_global_lift_of_finite_cover hS m (g p) (ht p)
      (fun q : s' => g q.1) (fun q => t q.1) (fun q => ht q.1) hcover
    have hrmem : g p ^ N ∈ I := ⟨a, ha⟩
    have hrnot : g p ^ N ∉ p.asIdeal := fun hmem =>
      hg p (p.isPrime.mem_of_pow_mem N hmem)
    exact ⟨g p ^ N, hrmem, hrnot⟩
  have hItop : I = ⊤ := by
    by_contra hI
    obtain ⟨M, hM, hIM⟩ := Ideal.ne_top_iff_exists_maximal.mp hI
    obtain ⟨r, hrI, hrM⟩ := hlocal ⟨M, hM.isPrime⟩
    exact hrM (hIM hrI)
  obtain ⟨a, ha⟩ := (Ideal.eq_top_iff_one I).mp hItop
  exact ⟨a, by simpa using ha⟩

/-- The concrete Stacks 01IE input used by `QCohSerreExtension.lean`. -/
theorem affineExtensionSurjectivityInput : AffineExtensionSurjectivityInput.{u} where
  surjective S hS h₁ _ := by
    change Function.Surjective (S.g.app ⊤)
    exact surjective_appTop S hS h₁

/-- Affine 01IE, and hence extension closure on every scheme by the categorical
reduction already in `QCohSerreExtension.lean`. -/
theorem quasicoherent_isClosedUnderExtensions_01IE (X : Scheme.{u}) :
    (quasiCoherent X).IsClosedUnderExtensions :=
  RelativeFM.quasiCoherent_isClosedUnderExtensions affineExtensionSurjectivityInput X

/-- The triangulated consequence for quasicoherent cohomology, using the same
input through the existing reduction. -/
theorem isDQCohTriangulated_01IE (X : Scheme.{u}) :
    (IsDQCoh X).IsTriangulated :=
  RelativeFM.isDQCohTriangulatedOfAffineExtensionSurjectivityInput
    affineExtensionSurjectivityInput X

#print axioms RelativeFM.AffineExtension.surjective_appTop
#print axioms RelativeFM.AffineExtension.affineExtensionSurjectivityInput
#print axioms RelativeFM.AffineExtension.quasicoherent_isClosedUnderExtensions_01IE
#print axioms RelativeFM.AffineExtension.isDQCohTriangulated_01IE

end AffineExtension
end
end RelativeFM
