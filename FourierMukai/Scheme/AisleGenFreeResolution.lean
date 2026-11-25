/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.KProjectiveResolution
import Mathlib.Algebra.Category.ModuleCat.LeftResolution

/-! # The explicit free resolution of a module -/

@[expose] public section

namespace RelativeFM.AisleGeneration.FreeResolution

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The chain complex of the functorial free resolution, transported out of
the full subcategory of projective modules. -/
noncomputable def complex (A : Type u) [CommRing A] (M : ModuleCat.{u} A) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  ((ObjectProperty.ι (isProjective (ModuleCat.{u} A))).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj ((ModuleCat.projectiveResolution A).chainComplex M)

/-- The augmentation of the explicit free resolution. -/
noncomputable def π (A : Type u) [CommRing A] (M : ModuleCat.{u} A) :
    complex A M ⟶ (ChainComplex.single₀ (ModuleCat.{u} A)).obj M :=
  let Λ := ModuleCat.projectiveResolution A
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(ObjectProperty.ι _).map (Λ.chainComplexXZeroIso M).hom ≫ Λ.π.app M, by
      change (ObjectProperty.ι _).map ((Λ.chainComplex M).d 1 0) ≫
        (ObjectProperty.ι _).map (Λ.chainComplexXZeroIso M).hom ≫ Λ.π.app M = 0
      rw [Λ.map_chainComplex_d_1_0]
      simp [Category.assoc]⟩

/-- Exactness of the first augmentation step of a left resolution. -/
lemma exact_π_kernel (A : Type u) [CommRing A] (M : ModuleCat.{u} A) :
    (ShortComplex.mk
      ((ModuleCat.projectiveResolution A).π.app
        (kernel ((ModuleCat.projectiveResolution A).π.app M)) ≫ kernel.ι _)
      ((ModuleCat.projectiveResolution A).π.app M) (by simp)).Exact := by
  let Λ := ModuleCat.projectiveResolution A
  let α : ShortComplex.mk (Λ.π.app (kernel (Λ.π.app M)) ≫ kernel.ι _)
      (Λ.π.app M) (by simp) ⟶
      ShortComplex.mk (kernel.ι (Λ.π.app M)) (Λ.π.app M) (by simp) :=
    { τ₁ := Λ.π.app _, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

/-- The explicit free resolution, with its quasi-isomorphism proved from the
left-resolution exactness lemmas. -/
noncomputable def resolution (A : Type u) [CommRing A] (M : ModuleCat.{u} A) :
    ProjectiveResolution M := by
  let Λ := ModuleCat.projectiveResolution A
  exact
    { complex := complex A M
      projective := fun n => ((Λ.chainComplex M).X n).property
      π := π A M
      quasiIso := ⟨fun n => by
        cases n with
        | zero =>
          rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
          · dsimp [π]
            refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
              ⟨exact_π_kernel A M, by dsimp; infer_instance⟩
            exact ShortComplex.isoMk
              ((ObjectProperty.ι _).mapIso (Λ.chainComplexXOneIso M))
              ((ObjectProperty.ι _).mapIso (Λ.chainComplexXZeroIso M))
              (Iso.refl _)
              (by
                change _ = (ObjectProperty.ι _).map ((Λ.chainComplex M).d 1 0) ≫ _
                rw [Λ.map_chainComplex_d_1_0]
                simp [Category.assoc]
                rfl)
              rfl
          all_goals dsimp [HomologicalComplex.shortComplexFunctor']
          apply HomologicalComplex.shape
          simp
        | succ n =>
          rw [quasiIsoAt_iff_exactAt']
          · apply Λ.exactAt_map_chainComplex_succ
          · apply ChainComplex.exactAt_succ_single_obj⟩ }

/-- Every term of the explicit free resolution is literally isomorphic to a
free module. -/
lemma exists_termFreeIso (A : Type u) [CommRing A] (M : ModuleCat.{u} A) (n : ℕ) :
    ∃ I : ModuleCat.{u} A, Nonempty ((complex A M).X n ≅ (ModuleCat.free A).obj I) := by
  let Λ := ModuleCat.projectiveResolution A
  obtain _ | _ | n := n
  · exact ⟨M, ⟨(ObjectProperty.ι _).mapIso (Λ.chainComplexXZeroIso M)⟩⟩
  · exact ⟨kernel (Λ.π.app M), ⟨(ObjectProperty.ι _).mapIso (Λ.chainComplexXOneIso M)⟩⟩
  · exact ⟨_, ⟨(ObjectProperty.ι _).mapIso (Λ.chainComplexXIso M n)⟩⟩

end

end RelativeFM.AisleGeneration.FreeResolution

#print axioms RelativeFM.AisleGeneration.FreeResolution.complex
#print axioms RelativeFM.AisleGeneration.FreeResolution.π
#print axioms RelativeFM.AisleGeneration.FreeResolution.resolution
#print axioms RelativeFM.AisleGeneration.FreeResolution.exists_termFreeIso
