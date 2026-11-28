/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.QuasiPerfect.Bounded
import Spaces.InternalHom.NonVacuity
import Spaces.Duality.NonVacuity

/-!
# Non-vacuity of the hypotheses of `Spaces/QuasiPerfect/`

CLAUDE.md, verification step 5: the hypothesis-carrying notions of GL26 Lemmas 5.3 and 5.9 as
rendered in `Spaces/QuasiPerfect/` are satisfiable.  On the affine (quasi-compact,
quasi-separated) space `X = h_{T₀}` of an affine object `T₀` of the site:

* the identity `𝟙 X` satisfies the hypotheses of Stacks 0E55 (`IsQcqsHom`, `isQcqsHom_id`);
* `X` has a coherator (`coheratorAdj`, Stacks 0CR4);
* `E = 0` is `𝟙`-quasi-perfect (`isQuasiPerfect_of_isZero`), pseudo-coherent and in `D_qc`;
* `𝒪_X[0]` is bounded (degree `0`).

So **Lemma 5.9** (`lemma_5_9`) and **Lemma 5.3** (`lemma_5_3_tensor`, `lemma_5_3_bounded`) apply
(`lemma_5_9_nonVacuity`, `lemma_5_3_nonVacuity`).  Inputs used beyond those of the statements:
`Supported.AffineQuasiSeparatedInput` (affine schemes are quasi-separated),
`Statements.IsQuasiCompactOfIsIsoInput` (isomorphisms are quasi-compact), `Tag0CR4Input`; all
AxiomMath theorems.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space ZeroObject

namespace RelativeFM.Spaces.QuasiPerfect

open RelativeFM.Spaces RelativeFM.Spaces.Duality RelativeFM.Spaces.LP26 RelativeFM.Spaces.Statements

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The identity of a quasi-compact quasi-separated algebraic space satisfies the hypotheses of
Stacks 0E55. -/
theorem isQcqsHom_id (hZ : B.Contains (⊤_ Scheme.{u})) (hqcI : IsQuasiCompactOfIsIsoInput B S hS)
    {X : AlgebraicSpaces B S hS} (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) : IsQcqsHom hZ (𝟙 X) := by
  refine ⟨hqc, hqs, hqs, ?_, ?_⟩
  · change IsQuasiCompact B S hS (𝟙 X.1)
    exact hqcI _
  · change IsQuasiSeparated B S hS (𝟙 X.1)
    exact isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isIso B S hS _)

variable (h08IN : BaseChange.Tag08INInput B S hS) (h08F4 : Tag08F4Input B S hS)
  (h08F5 : Tag08F5Input B S hS) (h08FA : Tag08FAInput B S hS) (h0E55 : Tag0E55Input B S hS)
  (h0CR4 : Tag0CR4Input B S hS) (hqsA : Supported.AffineQuasiSeparatedInput B S hS)
  (hqcI : IsQuasiCompactOfIsIsoInput B S hS)

include h08IN h08F4 h08F5 h0CR4 hqsA hqcI in
/-- **Non-vacuity of Lemma 5.9** (`lem:neeman23lem5_3`): on the affine space `X = h_{T₀}`, with
`f = 𝟙`, the coherator of `X` and `E = 0`, every hypothesis of `lemma_5_9` holds. -/
theorem lemma_5_9_nonVacuity (hZ : B.Contains (⊤_ Scheme.{u})) (T₀ : BigFppfOver B S hS)
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ∃ (hqc : IsQuasiCompactSpace B S hS (Supported.representedSpace T₀).1)
      (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (Supported.representedSpace T₀).1),
      Nonempty (upperTimes h08FA h0E55 _ (isQcqsHom_id hZ hqcI hqc hqs) ⋙
          qcHom (coheratorAdj h0CR4 hZ _ hqc hqs) (zeroQc _) ⋙
            pushQc h08FA _ (isQcqsHom_id hZ hqcI hqc hqs).qc (isQcqsHom_id hZ hqcI hqc hqs).qs ≅
        qcHom (coheratorAdj h0CR4 hZ _ hqc hqs)
          ((pushQc h08FA _ (isQcqsHom_id hZ hqcI hqc hqs).qc
            (isQcqsHom_id hZ hqcI hqc hqs).qs).obj (zeroQc _))) := by
  obtain ⟨hqc, hqs, -, -⟩ := Supported.nonVacuity_affine_univ hqsA hZ T₀ hT₀
  exact ⟨hqc, hqs, ⟨lemma_5_9 h08IN h08F4 h08F5 h08FA h0E55 _ (isQcqsHom_id hZ hqcI hqc hqs)
    (coheratorAdj h0CR4 hZ _ hqc hqs) (coheratorAdj h0CR4 hZ _ hqc hqs) (zeroQc _)⟩⟩

variable (h0A8A : Tag0A8AInput B S hS) (h08FAb : Tag08FABoundInput B S hS)
  (htr : QcohTruncLEInput B S hS) (hPq : PerfectQcohInput B S hS) (h09M8 : Tag09M8Input B S hS)
  (h09MB : Tag09MBInput B S hS) (hbd : PerfectBoundedAboveInput B S hS)
  (h0GFH : Tag0GFHInput B S hS) (h0GFI : Tag0GFIInput B S hS) (hO : StructureSheafQcohInput B S hS)
  (h09JB : Tag09JBInput B S hS)

include h08F5 h0A8A h08FAb htr hPq h09M8 h09MB hbd h0GFH h0GFI hqsA hqcI h09JB in
/-- **Non-vacuity of Lemma 5.3** (`lem:quasi-perfect_bounded`), first two claims: on the affine
space `X = h_{T₀}`, with `f = 𝟙` and `E = Q = 0`, `E` is `𝟙`-quasi-perfect and pseudo-coherent,
`Q` is perfect, and the conclusions of `lemma_5_3_tensor` and `lemma_5_3_bounded` hold. -/
theorem lemma_5_3_nonVacuity (hZ : B.Contains (⊤_ Scheme.{u})) (T₀ : BigFppfOver B S hS)
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ∃ (hqc : IsQuasiCompactSpace B S hS (Supported.representedSpace T₀).1)
      (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (Supported.representedSpace T₀).1),
      IsQuasiPerfect (𝟙 (Supported.representedSpace T₀)) 0 ∧
        IsPseudoCoherent (Supported.representedSpace T₀) 0 ∧
        Perf (Supported.representedSpace T₀) 0 ∧
        IsQuasiPerfect (𝟙 (Supported.representedSpace T₀)) (tensorObj 0 0) ∧
        Dbqc (Supported.representedSpace T₀)
          (sheafHomObj 0 ((upperTimes h08FA h0E55 _ (isQcqsHom_id hZ hqcI hqc hqs)).obj
            (structureSheafQc hO _)).obj) := by
  obtain ⟨hqc, hqs, -, -⟩ := Supported.nonVacuity_affine_univ hqsA hZ T₀ hT₀
  have hE := isQuasiPerfect_of_isZero (𝟙 (Supported.representedSpace T₀)) (isZero_zero _)
  have hpc := IsPseudoCoherent_of_isZero (X := Supported.representedSpace T₀) (isZero_zero _)
  exact ⟨hqc, hqs, hE, hpc, Perf_of_isZero (isZero_zero _),
    lemma_5_3_tensor h08F5 hPq h09JB _ hE (Perf_of_isZero (isZero_zero _)),
    lemma_5_3_bounded h08FA h0E55 h08F5 h0A8A h08FAb htr hPq h09M8 h09MB hbd h0GFH h0GFI hO _
      (isQcqsHom_id hZ hqcI hqc hqs) hqc hE hpc⟩

end RelativeFM.Spaces.QuasiPerfect
