/-
Cross-check of the final scheme statement against the affine construction and
against the categorical consumer interface.  This is an audit module, not the
preferred integration location for the underlying statement or affine proof.
-/
import FourierMukai.Scheme.SchemeWeakApproxStatement
import FourierMukai.Scheme.SchemeNeemanAffineInstance
import FourierMukai.Scheme.PaperTwoOpenGluing
import FourierMukai.Scheme.SchemeNeemanConsumerAudit

@[expose] public section

namespace RelativeFM.SchemeNeemanFinalAuditSmww16bpbM6

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry
open RelativeWeakApprox
open RelativeWeakApprox.PaperM2

universe u
noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The two independently constructed restricted standard `t`-structures have
identical aisles and co-aisles, hence are equal. -/
theorem restrictedStandardTStructure_eq_dqcStandardTStructure
    (X : Scheme.{u}) :
    SchemeNeemanAffineInstanceM2.restrictedStandardTStructure X =
      SchemeWeakApproxStatementM1.dqcStandardTStructure X := by
  apply SchemeNeemanAffineInstanceM2.tStructure_ext <;> intros <;> rfl

/-- The final statement is inhabited on an affine scheme with precisely the
inputs of the existing all-sheaves transport theorem.  No stronger generator
field and no extra `t`-structure transport is left implicit. -/
theorem neemanWeakApproximability_spec (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) (hAc : IsCompactAb (ringObject A)) :
    SchemeWeakApproxStatementM1.NeemanWeakApproximability (Spec A) := by
  refine ⟨⟨SchemeNeemanAffineInstanceM2.regularModuleRestrictedStandardPaperData A I hAc, ?_⟩⟩
  exact restrictedStandardTStructure_eq_dqcStandardTStructure (Spec A)

/-- The fixed-standard scheme statement is exactly the prescribed-`t`
interface consumed by the zero-detection gluing development. -/
theorem neemanWeakApproximability_iff_satisfiesPaperWAAt (X : Scheme.{u}) :
    SchemeWeakApproxStatementM1.NeemanWeakApproximability X ↔
      SchemeTwoOpenM3.SatisfiesPaperWAAt (Dqc X)
        (SchemeWeakApproxStatementM1.dqcStandardTStructure X) := by
  constructor
  · rintro ⟨⟨W, hW⟩⟩
    exact ⟨W, hW⟩
  · rintro ⟨W, hW⟩
    exact ⟨⟨W, hW⟩⟩

/-- The same interoperability check for the supported statement. -/
theorem neemanSupportedWeakApproximability_iff_satisfiesPaperWAAt
    (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) :
    SchemeWeakApproxStatementM1.NeemanSupportedWeakApproximability X Z ↔
      SchemeTwoOpenM3.SatisfiesPaperWAAt
        (SchemeWeakApproxStatementM1.DqcSupported X Z)
        (SchemeWeakApproxStatementM1.dqcSupportedStandardTStructure X Z) := by
  constructor
  · rintro ⟨⟨W, hW⟩⟩
    exact ⟨W, hW⟩
  · rintro ⟨W, hW⟩
    exact ⟨⟨W, hW⟩⟩

/-- The scheme-level statement is sufficient for the compact Hom-vanishing
consumer as soon as 09SR is supplied in the same zero-detection formulation. -/
theorem compactHomZeroAtTop_of_neemanWeakApproximability
    (X : Scheme.{u})
    (h : SchemeWeakApproxStatementM1.NeemanWeakApproximability X)
    (h09SR : ∀ G : Dqc X, IsPaperGenerator G → IsCompactAb G →
      IsClassicalGeneratorOnCompacts G) :
    RelativeFM.CompactHomZeroAtTop (Dqc X) :=
  SchemeNeemanConsumerAuditSmww16bpbM6.schemeCompactHomZeroAtTop_of_paperWA_of_paper09SR
    (Dqc X) (SchemeWeakApproxStatementM1.satisfiesPaperWA_of_neemanWeakApproximability h)
    h09SR

end
end RelativeFM.SchemeNeemanFinalAuditSmww16bpbM6

#print axioms RelativeFM.SchemeNeemanFinalAuditSmww16bpbM6.restrictedStandardTStructure_eq_dqcStandardTStructure
#print axioms RelativeFM.SchemeNeemanFinalAuditSmww16bpbM6.neemanWeakApproximability_spec
#print axioms RelativeFM.SchemeNeemanFinalAuditSmww16bpbM6.compactHomZeroAtTop_of_neemanWeakApproximability
#print axioms RelativeFM.SchemeNeemanFinalAuditSmww16bpbM6.neemanWeakApproximability_iff_satisfiesPaperWAAt
#print axioms RelativeFM.SchemeNeemanFinalAuditSmww16bpbM6.neemanSupportedWeakApproximability_iff_satisfiesPaperWAAt
