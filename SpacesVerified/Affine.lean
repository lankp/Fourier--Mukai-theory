/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces
import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleSupport
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# Discharge of the tagged inputs of the affine base case; LP26 Corollary 1.2, affine base

The five tagged AxiomMath inputs of `Spaces/Affine/Inputs.lean` are proved here by the
AxiomMath/Stacks declarations they name (commit `f56a316`), so that **LP26 Corollary 1.2,
affine base case** (`cor:weak_approx_spaces`; `Spaces.Affine.lp26_cor_1_2_affine`) and its
non-vacuity witness hold with nothing assumed.

| input | Stacks | proved by |
|---|---|---|
| `Tag06Z0ExactInput` | 06Z0 | `AlgebraicGeometry.Space.preservesFiniteLimits_representedAffineAssociated` |
| `Tag06Z0QcohInput` | 06Z0, 03DX (2) | `AlgebraicGeometry.Space.isQuasicoherentOnSite_representedAffineAssociated_obj` |
| `Tag06Z0Input` | 06Z0 | `AlgebraicGeometry.Space.isEquivalence_representedAffineDerivedAssociatedQcoh` |
| `Tag07TYInput` | 04KA, 07TY | `AlgebraicGeometry.Space.mem_supportOfSheaf_representedAssociatedModule_iff` |
| `Tag021RInput` | 021R, 000J | `AlgebraicGeometry.BigFppfSite.exists_contains` |

Each discharge is the AxiomMath declaration applied to the input's binders; that it
typechecks is the check that the input's statement is AxiomMath's (up to unfolding the
AxiomMath abbreviations written out by their bodies in `Spaces/Affine/Inputs.lean`).
The instance context is that of `Spaces/Affine/Inputs.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space
open RelativeWeakApprox

namespace RelativeFM.SpacesVerified

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

open RelativeFM.Spaces.Affine

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06Z0**, exactness, proved: `M ↦ M^~` preserves finite limits. -/
theorem tag06Z0Exact : Tag06Z0ExactInput B S hS := fun U _ =>
  preservesFiniteLimits_representedAffineAssociated B S hS U

/-- **Stacks 06Z0 / 03DX (2)**, proved: `M^~` is quasi-coherent. -/
theorem tag06Z0Qcoh : Tag06Z0QcohInput B S hS := fun U _ M =>
  isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U M

/-- **Stacks 06Z0**, proved: `D(R) ⥤ D_QCoh(𝒪_{Spec R})` is an equivalence. -/
theorem tag06Z0 : Tag06Z0Input B S hS := fun U _ _ _ =>
  isEquivalence_representedAffineDerivedAssociatedQcoh B S hS U

/-- **Stacks 04KA, 07TY**, proved: the support of an associated module is read off its stalks. -/
theorem tag07TY : Tag07TYInput B S hS := fun U G₀ hG₀ p =>
  mem_supportOfSheaf_representedAssociatedModule_iff B S hS U G₀ hG₀ p

/-- **Stacks 021R (000J)**, proved: every scheme lies in some big fppf site. -/
theorem tag021R : Tag021RInput.{u} := fun X => BigFppfSite.exists_contains X

variable {B S hS}

/-- **LP26 Corollary 1.2, affine base case** (`cor:weak_approx_spaces`), unconditional: for `U` an
object of the big fppf site with affine underlying scheme, `R = Γ(U, 𝒪)` and `I ⊆ R` finitely
generated, `D_{qc,V(I)}(Spec R)` is a triangulated subcategory of `D(𝒪_{h_U})` and is weakly
approximable (LP26 Definition 2.1, `def:weak_approx`).  `Spaces.Affine.lp26_cor_1_2_affine` with
its four tagged inputs proved; the differences from the paper's statement are those recorded
there (the affine base `Spec R` only). -/
theorem lp26_cor_1_2_affine_unconditional
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) (hI : I.FG) :
    ∃ h : (Spaces.DqcSupported (space U) (zeroLocusPoints U I)).IsTriangulated,
      letI := h
      PaperM2.SatisfiesPaperWA
        (Spaces.DqcSupported (space U) (zeroLocusPoints U I)).FullSubcategory :=
  lp26_cor_1_2_affine (tag06Z0Exact B S hS) (tag06Z0Qcoh B S hS) (tag06Z0 B S hS)
    (tag07TY B S hS) U I hI

/-- **Non-vacuity of LP26 Corollary 1.2, affine base case**, unconditional: `A = ℤ`, `I = (p)`,
over a big fppf site containing `Spec ℤ` (`Spaces.Affine.lp26_cor_1_2_affine_int` with its five
tagged inputs proved). -/
theorem lp26_cor_1_2_affine_int_unconditional (p : ℕ) :
    ∃ (B : BigFppfSite.{0}) (hS : B.Contains (Spec (.of ℤ))),
      ∃ h : (Spaces.DqcSupported (space (intObject B hS)) (zeroLocusPoints (intObject B hS)
          (Ideal.span {(p : Γ((BigFppfOver.toScheme B _ hS).obj (intObject B hS), ⊤))}))).IsTriangulated,
        letI := h
        PaperM2.SatisfiesPaperWA (Spaces.DqcSupported (space (intObject B hS)) (zeroLocusPoints
          (intObject B hS) (Ideal.span
            {(p : Γ((BigFppfOver.toScheme B _ hS).obj (intObject B hS), ⊤))}))).FullSubcategory := by
  obtain ⟨B, hS, h⟩ := lp26_cor_1_2_affine_int tag021R.{0} p
  exact ⟨B, hS, h (tag06Z0Exact B _ hS) (tag06Z0Qcoh B _ hS) (tag06Z0 B _ hS) (tag07TY B _ hS)⟩

end RelativeFM.SpacesVerified

#print axioms RelativeFM.SpacesVerified.tag06Z0Exact
#print axioms RelativeFM.SpacesVerified.tag06Z0Qcoh
#print axioms RelativeFM.SpacesVerified.tag06Z0
#print axioms RelativeFM.SpacesVerified.tag07TY
#print axioms RelativeFM.SpacesVerified.tag021R
#print axioms RelativeFM.SpacesVerified.lp26_cor_1_2_affine_unconditional
#print axioms RelativeFM.SpacesVerified.lp26_cor_1_2_affine_int_unconditional
