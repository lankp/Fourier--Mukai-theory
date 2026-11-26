/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.PerfectPowerTorsionM1
import FourierMukai.Scheme.ColimitHomologyM4
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Finite Koszul objects and simultaneous factorization

Neeman, *Acta Math.* 233 (2024), §7 (finite Koszul objects), used for LP26
Corollary 1.2 (`cor:weak_approx_spaces`), affine base case.

`koszulListData` builds the iterated scalar cone `K(a₁^{n₁},…,a_k^{n_k})` from
`A[0]`; its support on `V(a₁,…,a_k)` and its bound `≤ 0` are proved here
(`KoszulInputs.scalarConeData_isSupported`, `KoszulInputs.scalarConeData_le_zero`,
moved to this file from `KoszulInputs.lean`).  Nothing is assumed: the earlier
argument `hS : KoszulScalarSupportInput A` was false for every nonzero ring
(`KoszulInputs.not_koszulScalarSupportInput`) and has been removed.
-/

@[expose] public section

namespace RelativeFM.FiniteKoszulM1

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open RelativeFM.SupportedAisleM6.Koszul
open RelativeFM.NeemanFiniteSupportM4
open RelativeFM.PerfectPowerTorsionM1

universe u

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HasDerivedCategory.standard

/-- A chosen cone of scalar multiplication on an arbitrary derived object. -/
structure ScalarConeData (A : Type u) [CommRing A] (a : A) (X : AffineD A) where
  obj : AffineD A
  perfect : Perf A obj
  second : X ⟶ obj
  third : obj ⟶ X⟦(1 : ℤ)⟧
  distinguished : Triangle.mk (a • 𝟙 X) second third ∈ distTriang (AffineD A)

/-- The perfect scalar cone exists by triangulated closure of perfect objects. -/
noncomputable def scalarConeData (A : Type u) [CommRing A] (a : A)
    {X : AffineD A} (hX : Perf A X) : ScalarConeData A a X := by
  let h := perf_exists_cone (A := A) (a • 𝟙 X) hX hX
  exact
    { obj := h.choose
      perfect := h.choose_spec.choose
      second := h.choose_spec.choose_spec.choose
      third := h.choose_spec.choose_spec.choose_spec.choose
      distinguished := h.choose_spec.choose_spec.choose_spec.choose_spec }

end

end RelativeFM.FiniteKoszulM1

namespace RelativeFM.KoszulInputs

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeFM.NeemanFiniteSupportM4
open RelativeFM.FiniteKoszulM1

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The cohomology functors of `D(A)` commute with scalar multiplication by `A`. -/
lemma homologyFunctor_map_smul_id (A : Type u) [CommRing A] (b : A) (X : AffineD A) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map (b • 𝟙 X) = b • 𝟙 _ := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  have h1 : b • 𝟙 X = e.inv ≫ DerivedCategory.Q.map (b • 𝟙 K) ≫ e.hom := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, e.inv_hom_id]
  have h2 : HomologicalComplex.homologyMap (b • 𝟙 K) n = b • 𝟙 _ := by
    change ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (b • 𝟙 K)) = _
    rw [show (HomologicalComplex.shortComplexFunctor _ _ n).map (b • 𝟙 K) =
        b • 𝟙 ((HomologicalComplex.shortComplexFunctor _ _ n).obj K) by
      ext <;> rfl, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
    rfl
  have h3 := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).hom.naturality
    (b • 𝟙 K)
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, h2] at h3
  have h4 : H.map (DerivedCategory.Q.map (b • 𝟙 K)) = b • 𝟙 _ := by
    rw [← cancel_mono ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).hom.app K)]
    rw [h3, Linear.smul_comp, Category.id_comp]
    erw [Linear.comp_smul, Category.comp_id]
  rw [h1, H.map_comp, H.map_comp, h4, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    ← H.map_comp, e.inv_hom_id, H.map_id]

/-- On a cone of `b • 𝟙 X`, the endomorphism `b² • 𝟙` vanishes. -/
lemma scalarCone_smul_eq_zero (A : Type u) [CommRing A] (b : A) {X : AffineD A}
    (C : AffineD A) (g₂ : X ⟶ C) (g₃ : C ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (b • 𝟙 X) g₂ g₃ ∈ distTriang (AffineD A)) :
    (b * b) • 𝟙 C = 0 := by
  let T := Triangle.mk (b • 𝟙 X) g₂ g₃
  have h12 : g₂ ≫ (b • 𝟙 C) = 0 := by
    rw [Linear.comp_smul, Category.comp_id, ← Category.id_comp g₂, ← Linear.smul_comp]
    exact comp_distTriang_mor_zero₁₂ T hT
  have h31 : (b • 𝟙 C) ≫ g₃ = 0 := by
    have h := comp_distTriang_mor_zero₃₁ T hT
    change g₃ ≫ (shiftFunctor (AffineD A) (1 : ℤ)).map (b • 𝟙 X) = 0 at h
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.comp_smul, Category.comp_id] at h
    rw [Linear.smul_comp, Category.id_comp]
    exact h
  obtain ⟨h, hh⟩ := Triangle.yoneda_exact₃ T hT (b • 𝟙 C) h12
  have hsq : (b * b) • 𝟙 C = (b • 𝟙 C) ≫ (b • 𝟙 C) := by
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, mul_smul]
  rw [hsq]
  nth_rewrite 2 [hh]
  let h' : X⟦(1 : ℤ)⟧ ⟶ C := h
  change (b • 𝟙 C) ≫ g₃ ≫ h' = 0
  rw [← Category.assoc, h31, zero_comp]

/-- **Corrected 09IR, support half** (proved): a cone of `a ^ n • 𝟙 X` is
supported on `V(a)` for *every* perfect `X`; its cohomology is killed by
`a ^ (2n)`.  This is the `support` field of
`StacksInterface.KoszulScalarSupportInput`, which is therefore provable. -/
theorem scalarConeData_isSupported (A : Type u) [CommRing A] (a : A) (n : ℕ)
    {X : AffineD A} (hX : Perf A X) :
    AffineIsSupported A a (scalarConeData A (a ^ n) hX).obj := by
  let C := scalarConeData A (a ^ n) hX
  intro i
  rw [powerTorsion_iff]
  intro x
  refine ⟨n + n, ?_⟩
  have h0 := scalarCone_smul_eq_zero A (a ^ n) C.obj C.second C.third C.distinguished
  have h1 := homologyFunctor_map_smul_id A (a ^ n * a ^ n) C.obj i
  rw [h0, Functor.map_zero] at h1
  have hx := congrArg (fun φ => φ.hom x) h1
  rw [pow_add]
  simpa using hx.symm

/-- **Corrected 09IR, bound half** (proved): a cone of `b • 𝟙 X` lies in the
standard aisle `≤ 0` when `X` does.  The field `mem_le_zero` of
`StacksInterface.KoszulScalarSupportInput` drops the hypothesis on `X` and is
false (`not_koszulScalarSupportInput`); `koszulListData` applies it only to
iterated Koszul objects starting from `A[0]`, which are `≤ 0`. -/
theorem scalarConeData_le_zero (A : Type u) [CommRing A] (b : A)
    {X : AffineD A} (hX : Perf A X) (hle : (AffineD.standardTStructure A).le 0 X) :
    (AffineD.standardTStructure A).le 0 (scalarConeData A b hX).obj := by
  let t := AffineD.standardTStructure A
  letI : (t.le 0).IsTriangulatedClosed₂ := TStructure.le_isTriangulatedClosed₂ t 0
  let C := scalarConeData A b hX
  have hsh : t.le 0 (X⟦(1 : ℤ)⟧) :=
    t.le_monotone (show (-1 : ℤ) ≤ 0 by omega) _ (t.le_shift 0 1 (-1) (by omega) _ hle)
  exact (t.le 0).ext_of_isTriangulatedClosed₂ _ (rot_of_distTriang _ C.distinguished) hle hsh

end

end RelativeFM.KoszulInputs

namespace RelativeFM.FiniteKoszulM1

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open RelativeFM.SupportedAisleM6.Koszul
open RelativeFM.NeemanFiniteSupportM4
open RelativeFM.PerfectPowerTorsionM1

universe u

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HasDerivedCategory.standard

/-- The cone also inherits every ideal-support property of its source. -/
lemma scalarConeData_obj_supportedIdeal (A : Type u) [CommRing A] (a : A)
    {X : AffineD A} (hX : Perf A X) {I : Ideal A}
    (hsupp : AffineIsSupportedIdeal A I X) :
    AffineIsSupportedIdeal A I (scalarConeData A a hX).obj := by
  letI : (AffineIsSupportedIdeal A I).IsClosedUnderIsomorphisms := by
    unfold AffineIsSupportedIdeal
    infer_instance
  let C := scalarConeData A a hX
  let T := Triangle.mk (a • 𝟙 X) C.second C.third
  exact (AffineIsSupportedIdeal A I).ext_of_isTriangulatedClosed₂ T.rotate
    (rot_of_distTriang _ C.distinguished) hsupp
    ((AffineIsSupportedIdeal A I).le_shift 1 X hsupp)

/-- The ideal generated by the coefficients of a finite list. -/
def listIdeal (A : Type u) [CommRing A] : List (A × ℕ) → Ideal A
  | [] => ⊥
  | (a, _) :: ps => Ideal.span {a} ⊔ listIdeal A ps

/-- Data for the iterated Koszul cone of a finite list of scalar powers. -/
structure KoszulListData (A : Type u) [CommRing A] (ps : List (A × ℕ)) where
  obj : AffineD A
  perfect : Perf A obj
  second : ringObject A ⟶ obj
  supported : AffineIsSupportedIdeal A (listIdeal A ps) obj
  mem_le_zero : (AffineD.standardTStructure A).le 0 obj

/-- Iterated scalar cones give the finite Koszul object.  The support and the
bound `≤ 0` of each cone are the proved lemmas
`KoszulInputs.scalarConeData_isSupported` and `KoszulInputs.scalarConeData_le_zero`
(no input). -/
noncomputable def koszulListData (A : Type u) [CommRing A] :
    ∀ ps : List (A × ℕ), KoszulListData A ps
  | [] =>
    { obj := ringObject A
      perfect := ringObject_mem_perf A
      second := 𝟙 _
      supported := by
        intro n x a ha
        have ha0 : a = 0 := by simpa [listIdeal] using ha
        subst a
        exact ⟨1, by simp⟩
      mem_le_zero := ringObject_mem_standard_le_zero A }
  | (a, n) :: ps =>
    let tail := koszulListData A ps
    let C := scalarConeData A (a ^ n) tail.perfect
    { obj := C.obj
      perfect := C.perfect
      second := tail.second ≫ C.second
      supported := by
        change AffineIsSupportedIdeal A (Ideal.span {a} ⊔ listIdeal A ps) C.obj
        rw [affineIsSupportedIdeal_sup]
        refine ⟨?_, scalarConeData_obj_supportedIdeal A (a ^ n) tail.perfect tail.supported⟩
        rw [affineIsSupportedIdeal_span_singleton]
        exact KoszulInputs.scalarConeData_isSupported A a n tail.perfect
      mem_le_zero := KoszulInputs.scalarConeData_le_zero A (a ^ n) tail.perfect tail.mem_le_zero }

/-- The ideal generated by a list of scalars. -/
def functionIdeal (A : Type u) [CommRing A] : List A → Ideal A
  | [] => ⊥
  | a :: fs => Ideal.span {a} ⊔ functionIdeal A fs

/-- Exponents in a zip do not affect the ideal generated by the coefficients. -/
lemma listIdeal_zip_eq_functionIdeal (A : Type u) [CommRing A]
    (fs : List A) (ns : List ℕ) (h : ns.length = fs.length) :
    listIdeal A (fs.zip ns) = functionIdeal A fs := by
  induction fs generalizing ns with
  | nil =>
      cases ns with
      | nil => rfl
      | cons n ns => simp at h
  | cons a fs ih =>
      cases ns with
      | nil => simp at h
      | cons n ns =>
          simp only [List.zip_cons_cons, listIdeal, functionIdeal, List.map_cons]
          rw [ih ns (by simpa using h)]

/-- All exponents one. -/
def unitExponents (A : Type u) [CommRing A] (fs : List A) : List (A × ℕ) :=
  fs.map (fun a => (a, 1))

/-- The coefficient ideal is unchanged by replacing every exponent by one. -/
lemma listIdeal_unitExponents (A : Type u) [CommRing A] (fs : List A) :
    listIdeal A (unitExponents A fs) = functionIdeal A fs := by
  induction fs with
  | nil => rfl
  | cons a fs ih =>
      change Ideal.span {a} ⊔ listIdeal A (unitExponents A fs) =
        Ideal.span {a} ⊔ functionIdeal A fs
      rw [ih]

/-- Neeman's simultaneous finite Koszul factorization: every map from the
regular module to a complex supported on the common zero locus factors through
an iterated Koszul cone with strictly positive exponents. -/
theorem exists_koszulList_factorization (A : Type u) [CommRing A]
    (fs : List A) {F : AffineD A}
    (hF : AffineIsSupportedIdeal A (functionIdeal A fs) F) :
    ∀ α : ringObject A ⟶ F,
      ∃ ns : List ℕ, ns.length = fs.length ∧ (∀ n ∈ ns, 0 < n) ∧
        ∃ β : (koszulListData A (fs.zip ns)).obj ⟶ F,
          (koszulListData A (fs.zip ns)).second ≫ β = α := by
  intro α
  induction fs generalizing F with
  | nil =>
      refine ⟨[], rfl, by simp, α, ?_⟩
      simp [koszulListData]
  | cons a fs ih =>
      rw [functionIdeal, affineIsSupportedIdeal_sup] at hF
      obtain ⟨hFa, hFs⟩ := hF
      obtain ⟨ns, hlen, hpos, γ, hγ⟩ := ih hFs α
      have hFa' : AffineIsSupported A a F := by
        rw [← affineIsSupportedIdeal_span_singleton]
        exact hFa
      obtain ⟨k, hk, hk0⟩ := perf_sourcePowerTorsion A a
        (koszulListData A (fs.zip ns)).perfect F hFa' γ
      let C := scalarConeData A (a ^ k) (koszulListData A (fs.zip ns)).perfect
      obtain ⟨β, hβ⟩ := exists_factor_through_triangle_obj₃
        (Triangle.mk (a ^ k • 𝟙 (koszulListData A (fs.zip ns)).obj) C.second C.third)
        C.distinguished γ hk0
      refine ⟨k :: ns, by simp [hlen], ?_, β, ?_⟩
      · intro m hm
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · exact hk
        · exact hpos m hm
      · change (koszulListData A ((a, k) :: fs.zip ns)).second ≫ β = α
        change ((koszulListData A (fs.zip ns)).second ≫ C.second) ≫ β = α
        rw [Category.assoc, show C.second ≫ β = γ from hβ, hγ]

end

end RelativeFM.FiniteKoszulM1

#print axioms RelativeFM.FiniteKoszulM1.scalarConeData_obj_supportedIdeal
#print axioms RelativeFM.FiniteKoszulM1.koszulListData
#print axioms RelativeFM.FiniteKoszulM1.exists_koszulList_factorization
