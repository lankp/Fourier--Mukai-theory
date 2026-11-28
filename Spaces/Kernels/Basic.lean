/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.BaseChange.Cube
import Spaces.InternalHom.TensorHom
import Spaces.Statements.Notions
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource

/-!
# Kernels over algebraic spaces: the common ingredients of GL26 Lemmas 2.25 and 2.26

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), §2.3,
`sec:funct_on_kernel`.  The two lemmas there (Lemma 2.25, `lem:funct_on_kernel`, and Lemma 2.26,
`lem:convolution`; `Spaces/Kernels/Diagonal.lean`, `Spaces/Kernels/Convolution.lean`) use:

* **the structure sheaf** `𝒪_X ∈ D(𝒪_X)` in degree zero (`structureObj`), its quasi-coherence
  (`Dqc_structureObj`), and the left unit law `𝒪_X ⊗^L - ≅ -` (`tensorLeftUnitor`, AxiomMath's
  `DerivedTensorProduct.leftUnitor`, the unit of the monoidal structure of Stacks 0FPT re-seated on
  `⊗^L`);
* **the projection map natural in the pulled-back variable** (`projNatRight`): for fixed
  `E ∈ D(X)`, the maps `Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` of Stacks 08IN (AxiomMath's
  `smallEtaleProjectionFormulaMap`, written by its body `projectionFormulaMap`) form a natural
  transformation in `K` (`projectionFormulaMap_naturality_right`);
* **permanence of morphism properties**: a proper morphism is quasi-compact and quasi-separated,
  and flatness, quasi-compactness and quasi-separatedness are stable under base change in
  `AlgebraicSpaces B S hS` (`isQuasiCompact_of_isProper`, `isQuasiSeparated_of_isProper`,
  `isFlat_of_isPullback'`, `isQuasiCompact_of_isPullback'`, `isQuasiSeparated_of_isPullback'`);
* **the triple fibre product** `Y₁ ×_S Y₂ ×_S Y₃`, modelled as `(Y₁ ×_S Y₂) ×_{Y₂} (Y₂ ×_S Y₃)`,
  and the cartesian square exhibiting its projection to `Y₁ ×_S Y₃` as a base change of
  `Y₂ ⟶ S` (`isPullback_triple`).

## What is used from AxiomMath

No tagged input.  Every AxiomMath theorem used here is in modules that the `Spaces` library
imports (`scripts/axiommath/spaces-imports.txt`): `isQuasiCompact_of_isClosedImmersion'`
(Stacks 04CG, `Spaces/ClosedImmersionQC.lean`), `IsQuasiCompact.of_isPullback`
(`Spaces/SeparatedTfae.lean`), `isQuasiSeparated_of_isPullback` (Stacks 03HF,
`Spaces/QuasiSeparatedCriteria.lean`), `isFlat_isStableUnderBaseChange` (Stacks 03MO,
`Descent/EtaleLocal/FlatLocalAtSource.lean`), `isQuasiSeparated_of_mono`
(`Stacks/QuasiSeparatedDiagonal.lean`), `SheafOfModules.isQuasicoherentOnSite_unit` (Stacks 03DL(6)
for the structure sheaf, `Spaces/QuasicoherentStructureSheaf.lean`), `AlgebraicSpaces.isPullback_hom`
(Stacks 02X2), `DerivedTensorProduct.leftUnitor` (Stacks 0FPT) and the bodies of 08IN of
`Spaces/BaseChange/Inputs.lean`.  The modules of the first four were already in the import closure
of `Spaces`; the last two lists add three modules to it.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space
open scoped CategoryTheory.Prod

namespace RelativeFM.Spaces.Kernels

open RelativeFM.Spaces RelativeFM.Spaces.BaseChange RelativeFM.Spaces.Statements

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The structure sheaf -/

section Structure

/-- In `D(C)`, the homology in a nonzero degree of an object placed in degree zero vanishes. -/
theorem isZero_homology_singleFunctor_obj {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (M : C) {i : ℤ} (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj
      ((DerivedCategory.singleFunctor C 0).obj M)) := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact DerivedCategory.isZero_of_isGE _ 0 i hi
  · exact DerivedCategory.isZero_of_isLE _ 0 i hi

variable (X : AlgebraicSpaces B S hS)

/-- **`𝒪_X ∈ D(𝒪_X)`**: the structure sheaf of the small étale site of `X`, in degree zero. -/
abbrev structureObj : D B S hS X :=
  (DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS X.1 X.2) 0).obj (SheafOfModules.unit _)

/-- **The left unit law of `⊗^L`**: `𝒪_X ⊗^L - ≅ 𝟭`, AxiomMath's `DerivedTensorProduct.leftUnitor`
for the derived tensor product of the small étale site of `X` (Stacks 0FPT, re-seated on `⊗^L`). -/
def tensorLeftUnitor : (tensor X).obj (structureObj X) ≅ 𝟭 (D B S hS X) :=
  (smallEtaleDerivedTensorProduct B S hS X).leftUnitor

/-- **`𝒪_X ∈ D_qc(X)`**: its only nonzero cohomology sheaf is `𝒪_X`, which is quasi-coherent
(Stacks 03DL(6), AxiomMath's instance `SheafOfModules.isQuasicoherentOnSite_unit`). -/
theorem Dqc_structureObj : Dqc X (structureObj X) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
      (SheafOfModules.isQuasicoherentOnSite_unit _)
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (isZero_homology_singleFunctor_obj _ hi)

/-- `D_qc(X)` is closed under isomorphisms (as AxiomMath's instance for `QcohDerived`). -/
theorem Dqc_of_iso {X : AlgebraicSpaces B S hS} {E E' : D B S hS X} (e : E ≅ E')
    (h : Dqc X E) : Dqc X E' := fun n =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e)
    (h n)

end Structure

/-! ### Permanence of properties of morphisms -/

section Morphisms

variable {X Y : AlgebraicSpaces B S hS}

/-- A proper morphism is quasi-compact (finite type includes quasi-compact, Stacks 03XF). -/
theorem isQuasiCompact_of_isProper {f : X ⟶ Y} (hf : IsProperHom f) :
    IsQuasiCompact B S hS f.hom :=
  hf.2.1.2

/-- A proper morphism is quasi-separated: its diagonal is a closed immersion (separated), hence
quasi-compact (Stacks 04CG, AxiomMath's `isQuasiCompact_of_isClosedImmersion'`). -/
theorem isQuasiSeparated_of_isProper {f : X ⟶ Y} (hf : IsProperHom f) :
    IsQuasiSeparated B S hS f.hom :=
  isQuasiCompact_of_isClosedImmersion' B S hS hf.1

variable {P X' Y' Z' : AlgebraicSpaces B S hS} {fst : P ⟶ X'} {snd : P ⟶ Y'} {a : X' ⟶ Z'}
  {b : Y' ⟶ Z'}

/-- Quasi-compactness is stable under base change in `AlgebraicSpaces B S hS`: in a cartesian
square, `snd` is quasi-compact if `a` is (AxiomMath's `IsQuasiCompact.of_isPullback`, with
`AlgebraicSpaces.isPullback_hom`, Stacks 02X2). -/
theorem isQuasiCompact_of_isPullback' (sq : IsPullback fst snd a b)
    (ha : IsQuasiCompact B S hS a.hom) : IsQuasiCompact B S hS snd.hom :=
  IsQuasiCompact.of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) ha

/-- Quasi-separatedness is stable under base change (Stacks 03HF, AxiomMath's
`isQuasiSeparated_of_isPullback`). -/
theorem isQuasiSeparated_of_isPullback' (sq : IsPullback fst snd a b)
    (ha : IsQuasiSeparated B S hS a.hom) : IsQuasiSeparated B S hS snd.hom :=
  isQuasiSeparated_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) ha

/-- Flatness is stable under base change (Stacks 03MO, AxiomMath's
`isFlat_isStableUnderBaseChange`). -/
theorem isFlat_of_isPullback' (sq : IsPullback fst snd a b) (ha : IsFlatHom a) :
    IsFlatHom snd :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq ha

end Morphisms

/-! ### The projection map, natural in the pulled-back variable -/

section Projection

/-- `(uncurry F).map (c, 𝟙) = (F.map c).app _`. -/
lemma uncurry_map_prod_id {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (F : C₁ ⥤ C₂ ⥤ C₃) {Z Z' : C₁} (c : Z ⟶ Z') (W : C₂) :
    (Functor.uncurry.obj F).map (c ×ₘ 𝟙 W) = (F.map c).app W := by
  simp

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The projection map `Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` (`projectionFormulaMap`, the body of
AxiomMath's `smallEtaleProjectionFormulaMap`) is natural in `K`. -/
theorem projectionFormulaMap_naturality_right (E : D B S hS X) {K K' : D B S hS Y}
    (k : K ⟶ K') :
    ((tensor Y).obj ((push f).obj E)).map k ≫ projectionFormulaMap f E K' =
      projectionFormulaMap f E K ≫ (push f).map (((tensor X).obj E).map ((pull f).map k)) := by
  simp only [projectionFormulaMap]
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  have h := ((pullTensor (B := B) (S := S) (hS := hS) f).app ((push f).obj E)).hom.naturality k
  change (pull f).map (((tensor Y).obj ((push f).obj E)).map k) ≫
      (smallEtaleDerivedPullbackTensorIso f).hom.app ((push f).obj E, K') =
    (smallEtaleDerivedPullbackTensorIso f).hom.app ((push f).obj E, K) ≫
      ((tensor X).obj ((pull f).obj ((push f).obj E))).map ((pull f).map k) at h
  rw [reassoc_of% h, Category.assoc]
  congr 1
  rw [uncurry_map_prod_id, uncurry_map_prod_id]
  exact ((tensor X).map ((pullPushAdj f).counit.app E)).naturality ((pull f).map k)

/-- **The projection map as a natural transformation in the pulled-back variable**: for fixed
`E ∈ D(X)`, `K ↦ (Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K))` (Stacks 08IN). -/
def projNatRight (E : D B S hS X) :
    (tensor Y).obj ((push f).obj E) ⟶ pull f ⋙ (tensor X).obj E ⋙ push f where
  app K := projectionFormulaMap f E K
  naturality _ _ k := projectionFormulaMap_naturality_right f E k

@[simp] lemma projNatRight_app (E : D B S hS X) (K : D B S hS Y) :
    (projNatRight f E).app K = projectionFormulaMap f E K := rfl

/-- The projection map of `tensorPullPushData` (natural in the pushed-forward variable) is
invertible at `E ∈ D_qc(X)`, `K ∈ D_qc(Y)` for `f` quasi-compact and quasi-separated
(Stacks 08IN, `Tag08INInput`). -/
theorem isIso_projMap_app (hIN : Tag08INInput B S hS) (hqc : IsQuasiCompact B S hS f.hom)
    (hqs : IsQuasiSeparated B S hS f.hom) {K : D B S hS Y} (hK : Dqc Y K) {E : D B S hS X}
    (hE : Dqc X E) : IsIso (((tensorPullPushData B S hS).projMap f K).app E) :=
  (congrArg IsIso (projMap_app_eq f K E)).mpr (hIN f hqc hqs E hE K hK)

end Projection

/-! ### The triple fibre product -/

section Triple

-- Stated in `AlgebraicSpaces B S hS` (not in a general category with pullbacks) so that every
-- `pullback` carries AxiomMath's instance `AlgebraicSpaces.hasPullback`, as in the rest of
-- `Spaces`: two instance paths inside `D(…)` make the kernel unfold derived categories.
variable {S' Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S') (f₃ : Y₃ ⟶ S')

/-- `Y₁ ×_S Y₂ ×_S Y₃`, modelled as `(Y₁ ×_S Y₂) ×_{Y₂} (Y₂ ×_S Y₃)`. -/
abbrev triple : AlgebraicSpaces B S hS := pullback (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)

/-- `p₁₂ : Y₁ ×_S Y₂ ×_S Y₃ ⟶ Y₁ ×_S Y₂`. -/
abbrev p₁₂ : triple f₁ f₂ f₃ ⟶ pullback f₁ f₂ := pullback.fst _ _

/-- `p₂₃ : Y₁ ×_S Y₂ ×_S Y₃ ⟶ Y₂ ×_S Y₃`. -/
abbrev p₂₃ : triple f₁ f₂ f₃ ⟶ pullback f₂ f₃ := pullback.snd _ _

lemma triple_w :
    (p₁₂ f₁ f₂ f₃ ≫ pullback.fst f₁ f₂) ≫ f₁ = (p₂₃ f₁ f₂ f₃ ≫ pullback.snd f₂ f₃) ≫ f₃ := by
  simp only [Category.assoc, pullback.condition]
  rw [← Category.assoc, pullback.condition, Category.assoc, pullback.condition]

/-- `p₁₃ : Y₁ ×_S Y₂ ×_S Y₃ ⟶ Y₁ ×_S Y₃`. -/
abbrev p₁₃ : triple f₁ f₂ f₃ ⟶ pullback f₁ f₃ :=
  pullback.lift (p₁₂ f₁ f₂ f₃ ≫ pullback.fst f₁ f₂) (p₂₃ f₁ f₂ f₃ ≫ pullback.snd f₂ f₃)
    (triple_w f₁ f₂ f₃)

@[reassoc (attr := simp)] lemma p₁₃_fst :
    p₁₃ f₁ f₂ f₃ ≫ pullback.fst f₁ f₃ = p₁₂ f₁ f₂ f₃ ≫ pullback.fst f₁ f₂ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] lemma p₁₃_snd :
    p₁₃ f₁ f₂ f₃ ≫ pullback.snd f₁ f₃ = p₂₃ f₁ f₂ f₃ ≫ pullback.snd f₂ f₃ :=
  pullback.lift_snd _ _ _

/-- The defining cartesian square of the triple product: `p₂₃` is the base change of
`Y₁ ×_S Y₂ ⟶ Y₂` along `Y₂ ×_S Y₃ ⟶ Y₂`. -/
lemma isPullback_triple₁ :
    IsPullback (p₁₂ f₁ f₂ f₃) (p₂₃ f₁ f₂ f₃) (pullback.snd f₁ f₂) (pullback.fst f₂ f₃) :=
  IsPullback.of_hasPullback _ _

/-- **`p₁₃` is a base change of `f₂`**: the square with sides `p₁₃`, `Y₁₂₃ ⟶ Y₂`, `f₂` and
`Y₁ ×_S Y₃ ⟶ S` is cartesian, i.e. `Y₁ ×_S Y₂ ×_S Y₃ ≅ Y₂ ×_S (Y₁ ×_S Y₃)`. -/
lemma isPullback_triple :
    IsPullback (p₁₂ f₁ f₂ f₃ ≫ pullback.snd f₁ f₂) (p₁₃ f₁ f₂ f₃) f₂
      (pullback.fst f₁ f₃ ≫ f₁) := by
  refine IsPullback.of_isLimit' ⟨by simp [← pullback.condition]⟩ ?_
  refine PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (pullback.lift (s.snd ≫ pullback.fst f₁ f₃) s.fst (by
        rw [Category.assoc]; exact s.condition.symm))
      (pullback.lift s.fst (s.snd ≫ pullback.snd f₁ f₃) (by
        rw [s.condition, Category.assoc]; exact s.snd ≫= pullback.condition))
      (by simp))
    (fun s => by simp) (fun s => by apply pullback.hom_ext <;> simp) ?_
  intro s m h₁ h₂
  have h₁' : m ≫ p₁₂ f₁ f₂ f₃ ≫ pullback.snd f₁ f₂ = s.fst := by simpa using h₁
  have e₁ : m ≫ p₁₂ f₁ f₂ f₃ ≫ pullback.fst f₁ f₂ = s.snd ≫ pullback.fst f₁ f₃ := by
    rw [← h₂]; simp
  have e₂ : m ≫ p₂₃ f₁ f₂ f₃ ≫ pullback.snd f₂ f₃ = s.snd ≫ pullback.snd f₁ f₃ := by
    rw [← h₂]; simp
  have e₃ : m ≫ p₂₃ f₁ f₂ f₃ ≫ pullback.fst f₂ f₃ = s.fst := by
    rw [← h₁', ← pullback.condition]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa using e₁
    · simpa using h₁'
  · apply pullback.hom_ext
    · simpa using e₃
    · simpa using e₂

end Triple

end RelativeFM.Spaces.Kernels
