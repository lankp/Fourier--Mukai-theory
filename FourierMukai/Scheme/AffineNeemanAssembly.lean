import FourierMukai.Scheme.AffineMain
import FourierMukai.Scheme.AisleGenRingGeneration
import WeakApprox.GeneratorBridge
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Affine Neeman assembly, and an obstruction in the generation predicate

The exact approximation-data assembly is provided by
`RegularModuleApproximationInput.toWeakApproximationData`: its only residual
inputs are a positive bound, compactness of the regular module, the repository's
`IsGenerator` field, and approximation triangles. The standard-t-structure
bound and negative-aisle Hom vanishing are filled from `AffineMain`.

The literal regular-generator target is nevertheless false for arbitrary rings.
`IsGenerator` means separation of morphisms by the whole shift class, whereas
Neeman and Lank--Pauwels use zero detection (`IsPaperGenerator`). Any nonzero
class in `Ext^1(M,N)` gives a nonzero ghost for the regular module. For the
integers, an explicit two-term projective resolution of `ZMod 2` produces such a
class. Consequently `not_isGenerator_ringObject_int`,
`no_weakApproximationData_ringObject_int`, and
`not_regularGeneratorNeemanTarget_int` hold. This is not a counterexample to
Neeman's theorem; it is a counterexample to the stronger repository rendering
with the regular module as the separating generator.
-/

@[expose] public section

namespace RelativeFM.NeemanAssemblyM4

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The nonzeroth object in the length-two resolution is the zero module. -/
def zmodTwoResolutionX : ℕ → ModuleCat.{0} ℤ
  | 0 | 1 => ModuleCat.of ℤ ℤ
  | _ => 0

/-- Multiplication by two on the integers. -/
def intMulTwo : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
  ModuleCat.ofHom (LinearMap.mulLeft ℤ (2 : ℤ))

/-- Reduction of an integer modulo two. -/
def intModTwo : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ (ZMod 2) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (ZMod 2) 1)

lemma linearMulTwo_eval (x : ℤ) : (LinearMap.mulLeft ℤ (2 : ℤ)) x = 2 * x :=
  LinearMap.mulLeft_apply ..

lemma linearModTwo_eval (x : ℤ) :
    (LinearMap.toSpanSingleton ℤ (ZMod 2) 1) x = (x : ZMod 2) := by
  simp [LinearMap.toSpanSingleton_apply]

/-- The differential in the complex `... → 0 → ℤ --2→ ℤ`. -/
def zmodTwoResolutionD : ∀ n : ℕ, zmodTwoResolutionX (n + 1) ⟶ zmodTwoResolutionX n
  | 0 => intMulTwo
  | _ => 0

/-- The length-two chain complex resolving `ZMod 2`. -/
def zmodTwoResolutionComplex : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ChainComplex.of zmodTwoResolutionX zmodTwoResolutionD (fun n => by
    rw [show zmodTwoResolutionD (n + 1) = 0 from rfl, Limits.zero_comp])

@[simp] lemma zmodTwoResolutionComplex_d_one_zero :
    zmodTwoResolutionComplex.d 1 0 = intMulTwo := by
  exact ChainComplex.of_d zmodTwoResolutionX zmodTwoResolutionD 0

@[simp] lemma zmodTwoResolutionComplex_d_succ_succ (n : ℕ) :
    zmodTwoResolutionComplex.d (n + 2) (n + 1) = 0 := by
  exact ChainComplex.of_d zmodTwoResolutionX zmodTwoResolutionD (n + 1)

/-- The augmentation `ℤ --2→ ℤ → ZMod 2`. -/
def zmodTwoResolutionπ : zmodTwoResolutionComplex ⟶
    (ChainComplex.single₀ (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ (ZMod 2)) := by
  refine (ChainComplex.toSingle₀Equiv _ _).symm ⟨?_, ?_⟩
  · dsimp [zmodTwoResolutionComplex, zmodTwoResolutionX]
    exact intModTwo
  · change intMulTwo ≫ intModTwo = 0
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, intMulTwo, intModTwo,
      ModuleCat.hom_ofHom]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply,
      LinearMap.mulLeft_apply, LinearMap.toSpanSingleton_apply,
      Int.cast_smul_eq_zsmul, zsmul_one]
    norm_num
    exact Or.inl (by decide)

@[simp] lemma zmodTwoResolutionπ_f_zero : zmodTwoResolutionπ.f 0 = intModTwo := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

/-- The short complex `ℤ --2→ ℤ → ZMod 2`. -/
def zmodTwoShortComplex : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk intMulTwo intModTwo (by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, intMulTwo, intModTwo,
      ModuleCat.hom_ofHom]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply,
      LinearMap.mulLeft_apply, LinearMap.toSpanSingleton_apply, zsmul_one]
    norm_num
    exact Or.inl (by decide))

lemma zmodTwoShortComplex_exact : zmodTwoShortComplex.Exact := by
  dsimp [zmodTwoShortComplex, intMulTwo, intModTwo]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, hy⟩
    dsimp only at hy ⊢
    rw [ModuleCat.hom_ofHom] at hy ⊢
    rw [linearMulTwo_eval] at hy
    rw [← hy, linearModTwo_eval]
    norm_num
    exact Or.inl (by decide)
  · intro hx
    dsimp only at hx ⊢
    rw [ModuleCat.hom_ofHom] at hx ⊢
    rw [linearModTwo_eval, ZMod.intCast_eq_zero_iff_even] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    rw [linearMulTwo_eval]
    omega

lemma zmodTwoShortComplex_epi : Epi intModTwo := by
  refine (ModuleCat.epi_iff_surjective intModTwo).2 ?_
  intro x
  change ZMod 2 at x
  refine ⟨(x.val : ℤ), ?_⟩
  simpa [intModTwo, LinearMap.toSpanSingleton_apply,
    Int.cast_smul_eq_zsmul, zsmul_one] using (ZMod.natCast_val (R := ZMod 2) x)

/-- The short complex `0 → ℤ --2→ ℤ`. -/
def zmodTwoKernelShortComplex : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk (X₁ := (0 : ModuleCat.{0} ℤ)) 0 intMulTwo (by simp)

lemma zmodTwoKernelShortComplex_exact : zmodTwoKernelShortComplex.Exact := by
  dsimp [zmodTwoKernelShortComplex, intMulTwo]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, hy⟩
    change 0 = x at hy
    subst x
    rfl
  · intro hx
    change 2 * x = 0 at hx
    refine ⟨0, ?_⟩
    change 0 = x
    omega

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma zmodTwoResolutionπ_quasiIso : QuasiIso zmodTwoResolutionπ where
  quasiIsoAt n := by
    induction n with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff]
        refine (ShortComplex.quasiIso_iff_of_zeros' _ ?_ ?_ ?_).2 ?_
        · simp only [HomologicalComplex.shortComplexFunctor'_obj_g]
          exact ChainComplex.of_d_ne zmodTwoResolutionX zmodTwoResolutionD (by omega)
        · simp only [HomologicalComplex.shortComplexFunctor'_obj_f]
          apply HomologicalComplex.single_obj_d
        · simp only [HomologicalComplex.shortComplexFunctor'_obj_g]
          apply HomologicalComplex.single_obj_d
        · dsimp [HomologicalComplex.shortComplexFunctor', zmodTwoResolutionComplex,
            zmodTwoResolutionX, zmodTwoResolutionD, ChainComplex.of.d,
            ChainComplex.single₀, HomologicalComplex.single]
          exact ⟨by simpa [zmodTwoShortComplex] using zmodTwoShortComplex_exact,
            zmodTwoShortComplex_epi⟩
    | succ n _ =>
        rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
          HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
        cases n with
        | zero =>
            dsimp [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
              zmodTwoResolutionComplex, zmodTwoResolutionX, zmodTwoResolutionD,
              ChainComplex.of.d]
            simpa [zmodTwoKernelShortComplex] using zmodTwoKernelShortComplex_exact
        | succ n =>
            apply ShortComplex.exact_of_isZero_X₂
            change IsZero (0 : ModuleCat.{0} ℤ)
            exact isZero_zero _

/-- The explicit projective resolution `... → 0 → ℤ --2→ ℤ → ZMod 2`. -/
def zmodTwoProjectiveResolution : ProjectiveResolution (ModuleCat.of ℤ (ZMod 2)) where
  complex := zmodTwoResolutionComplex
  projective n := by
    cases n with
    | zero => exact inferInstanceAs (Projective (ModuleCat.of ℤ ℤ))
    | succ n =>
        cases n with
        | zero => exact inferInstanceAs (Projective (ModuleCat.of ℤ ℤ))
        | succ n => exact IsZero.projective (isZero_zero _)
  π := zmodTwoResolutionπ
  quasiIso := zmodTwoResolutionπ_quasiIso

local instance hasExtZmodTwo : HasExt.{1} (ModuleCat.{0} ℤ) := HasExt.standard _

/-- The extension class represented by reduction modulo two in degree one. -/
noncomputable def zmodTwoExtOne :
    Abelian.Ext.{1} (ModuleCat.of ℤ (ZMod 2)) (ModuleCat.of ℤ (ZMod 2)) 1 := by
  exact zmodTwoProjectiveResolution.extMk (n := 1) intModTwo 2 rfl (by
    change zmodTwoResolutionComplex.d 2 1 ≫ intModTwo = 0
    rw [show zmodTwoResolutionComplex.d 2 1 = 0 from
      zmodTwoResolutionComplex_d_succ_succ 0]
    exact Limits.zero_comp)

lemma zmodTwoExtOne_ne_zero : zmodTwoExtOne ≠ 0 := by
  intro h
  have hz := (zmodTwoProjectiveResolution.extMk_eq_zero_iff (n := 1)
    intModTwo 2 rfl (by
      change zmodTwoResolutionComplex.d 2 1 ≫ intModTwo = 0
      rw [show zmodTwoResolutionComplex.d 2 1 = 0 from
        zmodTwoResolutionComplex_d_succ_succ 0]
      exact Limits.zero_comp) 0 rfl).mp h
  obtain ⟨g, hg⟩ := hz
  change intMulTwo ≫ g = intModTwo at hg
  have happ := congrArg (fun k : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ (ZMod 2) =>
    k.hom (1 : ℤ)) hg
  simp only [ModuleCat.hom_comp, intMulTwo, intModTwo, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.toSpanSingleton_apply,
    zsmul_one] at happ
  have hg2 : g.hom (2 : ℤ) = 0 := by
    calc
      g.hom (2 : ℤ) = (2 : ℕ) • g.hom (1 : ℤ) := by
        exact map_nsmul g.hom (2 : ℕ) (1 : ℤ)
      _ = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
        norm_num
        exact Or.inl (by decide)
  have hone : (1 : ZMod 2) = 0 := happ.symm.trans hg2
  exact one_ne_zero hone

section Ghost

universe u

variable (A : Type u) [CommRing A]

local instance hasExtModule (A : Type u) [CommRing A] : HasExt.{u + 1} (ModuleCat.{u} A) :=
  HasExt.standard _

/-- A nonzero extension between single modules is a ghost for the regular module.
Maps from positive shifts vanish by strict degree bounds; the other composites
vanish by projectivity of the regular module. -/
lemma isGhostFromShifts_ringObject_of_ext_ne_zero
    {M N : ModuleCat.{u} A} (e : Abelian.Ext.{u + 1} M N 1) (he : e ≠ 0) :
    IsGhostFromShifts (ringObject A) e.hom := by
  let sA (n : ℤ) : (ringObject A)⟦n⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-n)).obj (ModuleCat.of A A) :=
    ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
      n (-n) 0 (by omega)).app (ModuleCat.of A A)
  let sN : ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).obj N :=
    ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
      (1 : ℤ) (-1) 0 (by omega)).app N
  constructor
  · intro hf
    apply he
    apply Abelian.Ext.ext
    simpa only [Abelian.Ext.zero_hom] using hf
  · intro n a
    by_cases hn : 0 < n
    · have ha : a = 0 := by
        have hna : (sA n).inv ≫ a = 0 := by
          apply (DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) (-n)).obj (ModuleCat.of A A))
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M) (-n) 0
            (by omega)).elim
        calc
          a = (sA n).hom ≫ ((sA n).inv ≫ a) := by simp
          _ = 0 := by rw [hna, Limits.comp_zero]
      rw [ha]
      exact Limits.zero_comp
    · have hn' : n ≤ 0 := le_of_not_gt hn
      have hcomp : (sA n).inv ≫ a ≫ e.hom ≫ sN.hom = 0 := by
        apply DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
          (P := ModuleCat.of A A)
          (L := (CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).obj N)
          (i := -n) _ (-1) (by omega)
      calc
        a ≫ e.hom = (sA n).hom ≫
            (((sA n).inv ≫ a ≫ e.hom) ≫ sN.hom) ≫ sN.inv := by
          simp [Category.assoc]
        _ = 0 := by
          rw [show ((sA n).inv ≫ a ≫ e.hom) ≫ sN.hom = 0 from by
            simpa only [Category.assoc] using hcomp]
          simp

lemma zmodTwo_isGhostFromShifts_ringObject :
    IsGhostFromShifts (ringObject ℤ) zmodTwoExtOne.hom :=
  isGhostFromShifts_ringObject_of_ext_ne_zero ℤ zmodTwoExtOne zmodTwoExtOne_ne_zero

lemma not_isGenerator_ringObject_int : ¬ IsGenerator (ringObject ℤ) := by
  intro h
  exact not_isGenerator_of_isGhostFromShifts zmodTwo_isGhostFromShifts_ringObject h

lemma no_weakApproximationData_ringObject_int
    (W : WeakApproximationData (AffineD ℤ)) (hG : W.G = ringObject ℤ) : False :=
  not_isGenerator_ringObject_int (hG ▸ W.G_generates)

end Ghost

section Assembly

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The exact regular-generator affine Neeman target using this repository's
`WeakApproximationData`: standard `t`, preferred aisle, compact/perfect, and
`G = A[0]`. -/
def RegularGeneratorNeemanTarget (A : Type u) [CommRing A] : Prop :=
  ∃ W : WeakApproximationData (AffineD A),
    W.t = AffineD.standardTStructure A ∧ W.G = ringObject A ∧
    (∀ X : AffineD A, IsCompactAb X ↔ Perf A X) ∧
    (AffineD.standardTStructure A).le 0 = Coprod (shiftTail (ringObject A) 0)

/-- This full target is false for the integers. The obstruction is exclusively
the repository's morphism-separating generation field, not the preferred aisle
identity or the mathematical compact-generation theorem. -/
lemma not_regularGeneratorNeemanTarget_int : ¬ RegularGeneratorNeemanTarget ℤ := by
  rintro ⟨W, -, hG, -, -⟩
  exact no_weakApproximationData_ringObject_int W hG

/-- The remaining inputs for assembling regular-module approximation data.
The final field is precisely the approximation-triangle obligation; the other
`WeakApproximationData` fields are discharged below by existing affine lemmas.
No inhabitance of the strong `generates` field is claimed. -/
structure RegularModuleApproximationInput (A : Type u) [CommRing A] where
  bound : ℤ
  bound_pos : 0 < bound
  compact : IsCompactAb (ringObject A)
  generates : IsGenerator (ringObject A)
  approximates : ∀ F : AffineD A, (AffineD.standardTStructure A).le 0 F →
    ∃ (E D : AffineD A) (f : E ⟶ F) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (AffineD A) ∧
      envelope (ringObject A) (-bound) bound E ∧
      (AffineD.standardTStructure A).le (-1) D

/-- Assemble regular-module approximation data. Only the four mathematical
inputs above remain: a positive bound, compactness, the strong separation field,
and approximation triangles. -/
def RegularModuleApproximationInput.toWeakApproximationData
    {A : Type u} [CommRing A] (I : RegularModuleApproximationInput A) :
    WeakApproximationData (AffineD A) where
  G := ringObject A
  t := AffineD.standardTStructure A
  A := I.bound
  A_pos := I.bound_pos
  G_compact := I.compact
  G_generates := I.generates
  G_mem_le := by
    have hB := I.bound_pos
    exact (AffineD.standardTStructure A).le_monotone (by omega) _
      (ringObject_mem_standard_le_zero A)
  hom_vanishing := by
    have hB := I.bound_pos
    intro Y hY f
    exact ringObject_hom_zero_of_standard_le_neg_one A
      ((AffineD.standardTStructure A).le_monotone (show -I.bound ≤ -1 by omega) _ hY) f
  exists_triangle := I.approximates

/-- Weak approximability from the exact residual regular-module inputs. -/
theorem RegularModuleApproximationInput.satisfiesWA
    {A : Type u} [CommRing A] (I : RegularModuleApproximationInput A) :
    SatisfiesWA (AffineD A) := ⟨I.toWeakApproximationData⟩

/-- The assembled data use the standard `t`-structure and regular generator. -/
theorem RegularModuleApproximationInput.satisfiesStandardWA
    {A : Type u} [CommRing A] (I : RegularModuleApproximationInput A) :
    SatisfiesStandardWA (AffineD A) (AffineD.standardTStructure A) :=
  ⟨I.toWeakApproximationData, rfl⟩

end

end Assembly

#print axioms zmodTwoProjectiveResolution
#print axioms zmodTwoExtOne
#print axioms zmodTwoExtOne_ne_zero
#print axioms isGhostFromShifts_ringObject_of_ext_ne_zero
#print axioms not_isGenerator_ringObject_int
#print axioms no_weakApproximationData_ringObject_int
#print axioms not_regularGeneratorNeemanTarget_int
#print axioms RegularModuleApproximationInput.toWeakApproximationData
#print axioms RegularModuleApproximationInput.satisfiesWA
#print axioms RegularModuleApproximationInput.satisfiesStandardWA

end

end RelativeFM.NeemanAssemblyM4
