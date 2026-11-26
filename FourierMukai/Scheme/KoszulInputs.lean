/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.RegularCompactEndpoints
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Inputs of the finite-support affine supported base: the refuted one

Sources: LP26 Corollary 1.2 (`cor:weak_approx_spaces`), affine base case = Neeman,
*Acta Math.* 233 (2024), Thm 3.2(iv) for `Spec A`, `Z = V(f₁,…,fₙ)`.

**Refuted:** `StacksInterface.KoszulScalarSupportInput` (formerly tagged Stacks 09IR,
whose content it is not) is *false* for every nontrivial ring
(`not_koszulScalarSupportInput`).  Its field `mem_le_zero` asserts that a cone of
`a ^ n • 𝟙 X` is `≤ 0` for *every* perfect `X`; for `a = 0`, `n = 1`,
`X = A[0]⟦-1⟧`, the object `X` is a retract of the cone, so `A[0]` would be `≤ -1`.
The structure is kept here only as the refuted notion: since wave 5 no theorem of
the tree takes it.

History (wave 5).  The true replacements `scalarConeData_isSupported` and
`scalarConeData_le_zero` now live in `FiniteKoszulM1.lean`, where
`koszulListData` uses them; the adjoint argument (`isLeftAdjoint_affineDZIdealι`)
lives in `KoszulSupportAdjoint.lean`; the proofs `idealSupportedCoproductInput`,
`idealSupportedCompactnessInput` are in `IdealNeemanM1.lean`.  The remaining inputs
`KoszulPowerCoprodInput` and `KoszulDetectionInput` are proved in
`KoszulFiniteInputs.lean`.  The declaration names are unchanged.

Nothing is assumed in this file.
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

section Refutation

/-- **Refuted notion** (formerly tagged Stacks 09IR; not the content of 09IR).
Kept only to record its refutation `not_koszulScalarSupportInput`: no theorem of
the tree takes it as an argument any more.  Its `support` field is true
(`scalarConeData_isSupported`); its `mem_le_zero` field drops the hypothesis
`X ≤ 0` of the true `scalarConeData_le_zero` and is false for every nonzero ring. -/
structure _root_.RelativeFM.StacksInterface.KoszulScalarSupportInput (A : Type u) [CommRing A] : Prop where
  support : ∀ {a : A} (n : ℕ) {X : AffineD A} (hX : Perf A X),
    AffineIsSupported A a (scalarConeData A (a ^ n) hX).obj
  mem_le_zero : ∀ {a : A} (n : ℕ) {X : AffineD A} (hX : Perf A X),
    (AffineD.standardTStructure A).le 0 (scalarConeData A (a ^ n) hX).obj

/-- **Refutation of `KoszulScalarSupportInput`** (tagged Stacks 09IR).  For a
nontrivial ring the input is false: take `a = 0`, `n = 1`, `X = A[0]⟦-1⟧`.  The cone
of `0 • 𝟙 X` has `X` as a retract, so `mem_le_zero` would make `A[0]` lie in degrees
`≤ -1`, forcing `A = 0`. -/
theorem not_koszulScalarSupportInput (A : Type u) [CommRing A] [Nontrivial A] :
    ¬ StacksInterface.KoszulScalarSupportInput A := by
  intro hS
  let X : AffineD A := (ringObject A)⟦(-1 : ℤ)⟧
  have hX : Perf A X := perf_shift A (ringObject_mem_perf A) (-1)
  let C := scalarConeData A ((0 : A) ^ 1) hX
  have hC : (AffineD.standardTStructure A).le 0 C.obj := hS.mem_le_zero (a := 0) 1 hX
  have hCle : C.obj.IsLE 0 := (DerivedCategory.TStructure.t.le_iff_isLE C.obj 0).mp hC
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ C.distinguished (𝟙 X)
    (by change ((0 : A) ^ 1 • 𝟙 X) ≫ 𝟙 X = 0; rw [pow_one, zero_smul]; exact Limits.zero_comp)
  have hXle : X.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
    have hz : IsZero (H.obj C.obj) := DerivedCategory.isZero_of_isLE C.obj 0 i hi
    rw [IsZero.iff_id_eq_zero]
    let g' : C.obj ⟶ X := g
    have hg' : 𝟙 X = C.second ≫ g' := hg
    have h1 : H.map (𝟙 X) = H.map C.second ≫ H.map g' := by
      rw [hg', H.map_comp]
    rw [← H.map_id, h1, hz.eq_of_src (H.map g') 0, comp_zero]
  have hR : (ringObject A).IsLE (-1) := by
    have : DerivedCategory.TStructure.t.IsLE ((ringObject A)⟦(-1 : ℤ)⟧) 0 := hXle
    exact DerivedCategory.TStructure.t.isLE_of_shift (ringObject A) (-1) (-1) 0
  have hz := DerivedCategory.isZero_of_isLE (ringObject A) (-1) 0 (by omega)
  have hA : IsZero (ModuleCat.of A A) :=
    hz.of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} A) 0).app (ModuleCat.of A A)).symm
  have : Subsingleton A := ModuleCat.subsingleton_of_isZero hA
  exact false_of_nontrivial_of_subsingleton A


end Refutation



end

end RelativeFM.KoszulInputs

#print axioms RelativeFM.KoszulInputs.not_koszulScalarSupportInput
#print axioms RelativeFM.KoszulInputs.scalarConeData_isSupported
#print axioms RelativeFM.KoszulInputs.scalarConeData_le_zero
#print axioms RelativeFM.KoszulInputs.jStar_supportedIdeal
#print axioms RelativeFM.KoszulInputs.isLeftAdjoint_affineDZIdealι
#print axioms RelativeFM.KoszulInputs.idealSupportedCoproductInput
#print axioms RelativeFM.KoszulInputs.idealSupportedCompactnessInput
