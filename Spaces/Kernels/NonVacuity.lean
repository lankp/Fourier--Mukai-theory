/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Kernels.Diagonal
import Spaces.Kernels.Convolution
import Spaces.Statements.NonVacuity

/-!
# Non-vacuity of GL26 Lemmas 2.25 and 2.26 over algebraic spaces

CLAUDE.md, verification step 5.  The hypotheses of `lemma_2_25` (`lem:funct_on_kernel`) and
`lemma_2_26` (`lem:convolution`) — Noetherian spaces, proper flat morphisms, kernels in `D_qc` —
are met by the identity of the base space `S` (an affine locally Noetherian scheme, e.g. `Spec k`)
with zero kernels, by `setup_hypotheses_satisfiable` (`Spaces/Statements/NonVacuity.lean`, from the
tagged inputs of `Spaces/Statements/Inputs.lean`) and `Dqc_of_isZero`; the objects of `D_qc` at
which the isomorphisms are evaluated include the zero object and `𝒪_Y` (`Dqc_structureObj`).  So
both lemmas apply (`lemma_2_25_nonVacuity`, `lemma_2_26_nonVacuity`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Kernels

open RelativeFM.Spaces RelativeFM.Spaces.BaseChange RelativeFM.Spaces.Statements

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Lemma 2.25 applies**: for the identity of the base space (Noetherian, proper, flat, from the
inputs of `Spaces/Statements/Inputs.lean`), `Φ_{RΔ_*𝒪} ≅ id` on `D_qc`. -/
theorem lemma_2_25_nonVacuity (h06LT : Tag06LTInput B S hS)
    (hqc : IsQuasiCompactOfIsIsoInput B S hS) (huc : UniversallyClosedOfIsIsoInput B S hS)
    (hfl : IsFlatIdInput B S hS) (hqs : AffineQuasiSeparatedInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [IsAffine S] [IsLocallyNoetherian S]
    (h4 : Tag08F4Input B S hS) (hIN : Tag08INInput B S hS) :
    Nonempty ((Dqc (baseSpace B S hS)).ι ⋙
        transformOver (𝟙 (baseSpace B S hS)) (𝟙 _) (diagKernel (𝟙 (baseSpace B S hS))) ≅
      (Dqc (baseSpace B S hS)).ι) :=
  let h := setup_hypotheses_satisfiable B S hS h06LT hqc huc hfl hqs hZ
  lemma_2_25 (𝟙 _) h4 hIN hZ h.1 h.1 h.2.1 h.2.2.1

/-- **Lemma 2.26 applies**: for `f₁ = f₂ = f₃ = 𝟙` on the base space and zero kernels. -/
theorem lemma_2_26_nonVacuity (h06LT : Tag06LTInput B S hS)
    (hqc : IsQuasiCompactOfIsIsoInput B S hS) (huc : UniversallyClosedOfIsIsoInput B S hS)
    (hfl : IsFlatIdInput B S hS) (hqs : AffineQuasiSeparatedInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [IsAffine S] [IsLocallyNoetherian S]
    (hF : FlatBaseChangeInput B S hS) (hA : CompIsoAgreeInput B S hS) (hIN : Tag08INInput B S hS)
    (h4 : Tag08F4Input B S hS) (h5 : Tag08F5Input B S hS) :
    let X := baseSpace B S hS
    Nonempty ((Dqc X).ι ⋙ transformOver (𝟙 X) (𝟙 X) (zeroObj (pullback (𝟙 X) (𝟙 X))) ⋙
        transformOver (𝟙 X) (𝟙 X) (zeroObj (pullback (𝟙 X) (𝟙 X))) ≅
      (Dqc X).ι ⋙ transformOver (𝟙 X) (𝟙 X) (convolution (𝟙 X) (𝟙 X) (𝟙 X)
        (zeroObj (pullback (𝟙 X) (𝟙 X))) (zeroObj (pullback (𝟙 X) (𝟙 X))))) :=
  let h := setup_hypotheses_satisfiable B S hS h06LT hqc huc hfl hqs hZ
  lemma_2_26 (f₁ := 𝟙 _) (f₂ := 𝟙 _) (f₃ := 𝟙 _) hF hA hIN h4 h5 hZ h.1 h.1 h.1 h.1 h.2.1
    h.2.2.1 h.2.1 h.2.2.1 h.2.1 h.2.2.1 (Dqc_of_isZero (isZero_zeroObj _))
    (Dqc_of_isZero (isZero_zeroObj _))

end RelativeFM.Spaces.Kernels
