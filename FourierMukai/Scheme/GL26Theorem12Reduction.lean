/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.Statements
import FourierMukai.Scheme.SchemeWeakApproxStatement

/-!
# GL26 Theorem 1.2 over Noetherian schemes: named residues and reductions

This module checks the existing scheme rendering of GL26 Theorem 1.2 and proves
its two logical assembly steps.  It does **not** claim the geometric residues.

The weak-approximability input below is `SatisfiesPaperWA`, hence uses Neeman's
zero-detection condition `IsPaperGenerator`, not the unusable legacy
`IsGenerator`.  In a geometric instantiation it is supplied by Neeman, Acta
Math. 233 (2024), Theorem 3.2(iv), using
`SchemeWeakApproxStatementM1.satisfiesPaperWA_of_neemanWeakApproximability`
and equivalence transport when the Fourier--Mukai category is not definitionally
`Dqc Y`.  No AxiomMath/Stacks statement is consumed in this module.

Two independent inputs remain visible in `CHNS_B_OnDcohAndPerf`: coherence (Neeman,
arXiv:1806.06471v2, Example 5.4) and the intrinsic-subcategory restriction
(Canonaco--Haesemeyer--Neeman--Stellari, arXiv:2402.04605v1, Theorem B).
The repository has no definition of coherent triangulated categories, so the
two coherence assertions are explicit proposition parameters, as in
`Scheme/Inputs.lean`; neither is asserted here.

The proof of Theorem 1.2 needs more than Neeman and CHNS.  The residues are
kept separate:

* `TransformPreservationForcesRelativePerfect`: the preservation part of GL26
  Remark 2.7;
* `CanonicalRelativePerfectReflection`: passage from an arbitrary field
  representative to the canonical residue-field representative;
* openness of `CanonicalRelativePerfectLocus` (Proposition 12.8);
* on that open locus, Theorem 12.3 and pseudofunctoriality (for part (1));
* comparison of the relatively perfect loci under base change (Corollary 6.18
  plus faithfully flat field reflection) and Corollary 12.4 plus
  pseudofunctoriality (for part (2)).

The last two theorems prove the existing
`Noetherian.theorem_1_2_openStatement` and
`Noetherian.theorem_1_2_baseChangeStatement` from those smaller statements.
None of their parameters is either target itself.
-/

@[expose] public section

namespace RelativeFM.GL26Theorem12Smww27cujM5

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry
open RelativeWeakApprox RelativeWeakApprox.PaperM2

universe w u v

open RelativeFM.Noetherian

/-!
## The checked statement

The existing rendering has the correct bounded-pseudocoherent hypothesis
`SP.Dcoh K`, proper flat families, and no flatness restriction on base change.
The following definition merely packages its two clauses.
-/

/-- GL26 Theorem 1.2(1)--(2), bundled from the repository's checked rendering. -/
def theorem_1_2_Statement (X : Noetherian.FMSetup.{w, u, v}) (hX : X.ctx.IsProperFlat)
    {K : X.DP} (hK : X.ctx.SP.Dcoh K) : Prop :=
  theorem_1_2_openStatement X hX hK ∧
    ∀ t : Noetherian.BaseChange X, theorem_1_2_baseChangeStatement X hX hK t

/-!
## Remark 2.6 and the preservation part of Remark 2.7

The following proposition is the precise implication from CHNS Theorem B used
here.  It is not a global axiom: it is a `Prop`-valued specification which a
consumer must supply.  Its hypotheses make the two Neeman 3.2(iv) inputs and
the two independent coherence inputs visible in every use.
-/

section CHNS

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The consequence of CHNS Theorem B needed by GL26 Remark 2.6: for an exact,
shift-compatible integral transform, global equivalence restricts to
equivalences on bounded coherent objects and on perfect objects.  `CoherentC` and `CoherentD` stand for
Neeman Example 5.4's coherence assertions; weak approximability is separately
quantified in zero-detection form.

CHNS is cited for equivalence of all four intrinsic decorated categories in
Remark 2.6.  The assembly uses the `D_qc ⇒ D^b_coh` implication for relative
perfectness over the first factor and `D_qc ⇒ Perf` for the second.  The
unneeded assertion about `D^-_coh` is deliberately omitted. -/
def CHNS_B_OnDcohAndPerf (SC : Subcats C) (SD : Subcats D)
    (CoherentC CoherentD : Prop) (F : C ⥤ D)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] : Prop :=
  SatisfiesPaperWA C → SatisfiesPaperWA D → CoherentC → CoherentD →
    F.IsEquivalence →
      EquivalenceOn SC.Dcoh SD.Dcoh F ∧ EquivalenceOn SC.Perf SD.Perf F

/-- Apply the CHNS bridge with its four categorical hypotheses exposed. -/
theorem equivalenceOnDcohAndPerf_of_neeman_coherent_CHNS
    {SC : Subcats C} {SD : Subcats D} {CoherentC CoherentD : Prop}
    {F : C ⥤ D} [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (H : CHNS_B_OnDcohAndPerf SC SD CoherentC CoherentD F)
    (hN₁ : SatisfiesPaperWA C) (hN₂ : SatisfiesPaperWA D)
    (hCoh₁ : CoherentC) (hCoh₂ : CoherentD) (hF : F.IsEquivalence) :
    EquivalenceOn SC.Dcoh SD.Dcoh F ∧ EquivalenceOn SC.Perf SD.Perf F :=
  H hN₁ hN₂ hCoh₁ hCoh₂ hF

end CHNS

/-- The preservation consequence in GL26 Remark 2.7.  This is deliberately
separate from CHNS: bounded-coherent and perfect preservation by the transform
is combined with the relative-perfect preservation theory to obtain relative
perfectness over both factors. -/
def TransformPreservationForcesRelativePerfect {D1 D2 DP : Type u}
    [Category.{v} D1] [Category.{v} D2] [Category.{v} DP]
    (C : Noetherian.FMContext D1 D2 DP) (K : DP) : Prop :=
  C.SP.IsPseudocoherent K → AlgebraicGeometry.IsProper C.f1 →
    AlgebraicGeometry.IsProper C.f2 →
    Noetherian.MapsTo C.S1.Dcoh C.S2.Dcoh (C.transform K) →
    Noetherian.MapsTo C.S1.Perf C.S2.Perf (C.transform K) →
    C.IsRelativelyPerfectOverOne K ∧ C.IsRelativelyPerfectOverTwo K

/-- GL26 Remark 2.7, decomposed into Neeman 3.2(iv), coherence, CHNS B, and the
relative-perfect preservation theory.  Applying this theorem to the context of
each fibre supplies `FibreRelativePerfectFromEquivalence` below. -/
theorem relativelyPerfect_of_neeman_coherent_CHNS
    {D1 D2 DP : Type u} [Category.{v} D1] [Category.{v} D2] [Category.{v} DP]
    [Preadditive D1] [HasZeroObject D1] [HasShift D1 ℤ]
    [∀ n : ℤ, (shiftFunctor D1 n).Additive] [Pretriangulated D1]
    [Preadditive D2] [HasZeroObject D2] [HasShift D2 ℤ]
    [∀ n : ℤ, (shiftFunctor D2 n).Additive] [Pretriangulated D2]
    (C : Noetherian.FMContext D1 D2 DP) (K : DP)
    {Coherent₁ Coherent₂ : Prop}
    [(C.transform K).Additive] [(C.transform K).CommShift ℤ]
    [(C.transform K).IsTriangulated]
    (H : CHNS_B_OnDcohAndPerf C.S1 C.S2 Coherent₁ Coherent₂ (C.transform K))
    (hN₁ : SatisfiesPaperWA D1) (hN₂ : SatisfiesPaperWA D2)
    (hCoh₁ : Coherent₁) (hCoh₂ : Coherent₂)
    (P : TransformPreservationForcesRelativePerfect C K)
    (hK : C.SP.IsPseudocoherent K)
    (hproper₁ : AlgebraicGeometry.IsProper C.f1)
    (hproper₂ : AlgebraicGeometry.IsProper C.f2)
    (hΦ : C.IsEquivalence K) :
    C.IsRelativelyPerfectOverOne K ∧ C.IsRelativelyPerfectOverTwo K := by
  have H' := equivalenceOnDcohAndPerf_of_neeman_coherent_CHNS
    H hN₁ hN₂ hCoh₁ hCoh₂ hΦ
  exact P hK hproper₁ hproper₂ H'.1.1 H'.2.1

/-!
## Field representatives and the relatively perfect locus

The paper defines Proposition 12.8's locus using canonical residue fields,
whereas `FM` is an existential over all field representatives.  Keeping this
reflection step explicit avoids silently identifying those two definitions.
-/

/-- Relative perfectness of the pulled-back kernel over both factors at one
chosen field representative. -/
def RelativelyPerfectAt (X : Noetherian.FMSetup.{w, u, v}) (K : X.DP)
    {p : X.ctx.Base} (t : Noetherian.PointRepresentative p) : Prop :=
  (X.fibre t).ctx.IsRelativelyPerfectOverOne ((X.fibre t).pullKernel.obj K) ∧
    (X.fibre t).ctx.IsRelativelyPerfectOverTwo ((X.fibre t).pullKernel.obj K)

/-- The locus occurring in GL26 Proposition 12.8, using the canonical
residue-field representative at each point. -/
def CanonicalRelativePerfectLocus (X : Noetherian.FMSetup.{w, u, v}) (K : X.DP) :
    Set X.ctx.Base :=
  {p | RelativelyPerfectAt X K (Noetherian.PointRepresentative.canonical p)}

/-- Exactly the representative-comparison input needed to pass from the
existential definition of `FM` to the canonical relatively perfect locus.
Geometrically this is the common-field-extension and faithfully flat
ascent/descent part of GL26's relative-perfect machinery. -/
def CanonicalRelativePerfectReflection (X : Noetherian.FMSetup.{w, u, v}) (K : X.DP) : Prop :=
  ∀ {p : X.ctx.Base} (t : Noetherian.PointRepresentative p),
    RelativelyPerfectAt X K t →
      RelativelyPerfectAt X K (Noetherian.PointRepresentative.canonical p)

/-- The fibrewise consequence of Remark 2.7, without yet changing the chosen
field representative to the canonical one. -/
def FibreRelativePerfectFromEquivalence (X : Noetherian.FMSetup.{w, u, v}) (K : X.DP) : Prop :=
  ∀ {p : X.ctx.Base} (t : Noetherian.PointRepresentative p),
    X.EquivalenceAt K t → RelativelyPerfectAt X K t

/-- Remark 2.7 plus representative reflection puts `FM(K)` inside the canonical
relatively perfect locus. -/
theorem fm_subset_canonicalRelativePerfectLocus
    (X : Noetherian.FMSetup.{w, u, v}) (K : X.DP)
    (h₂₇ : FibreRelativePerfectFromEquivalence X K)
    (hreflect : CanonicalRelativePerfectReflection X K) :
    X.FM K ⊆ CanonicalRelativePerfectLocus X K := by
  rintro p ⟨t, ht⟩
  exact hreflect t (h₂₇ t ht)

/-- Proposition 12.8 in the exact form consumed by Theorem 1.2(1). -/
def RelativePerfectLocusOpenInput (X : Noetherian.FMSetup.{w, u, v}) (K : X.DP) : Prop :=
  IsOpen (CanonicalRelativePerfectLocus X K)

/-- On the relatively perfect open subscheme, this is the identification of the
original equivalence locus with the equivalence locus of the restricted setup.
The subtype is the relatively perfect locus; the displayed set `V` is the open
set supplied there by Theorem 12.3.  Pseudofunctoriality of derived pullback is
part of this comparison input, not something asserted by `Noetherian.FMSetup`. -/
def OpenRestrictionComparison (X : Noetherian.FMSetup.{w, u, v}) (K : X.DP)
    (V : Set (CanonicalRelativePerfectLocus X K)) : Prop :=
  ∀ q : CanonicalRelativePerfectLocus X K,
    q ∈ V ↔ (q : X.ctx.Base) ∈ X.FM K

/-!
## Theorem 1.2(1): the open-restriction assembly

`hU` is Proposition 12.8; `hV` is Theorem 12.3 after restricting to the
relatively perfect open locus; `hcompare` is pseudofunctoriality and the local
identification of the two loci.  Remark 2.7 and representative reflection
supply the only global subset relation needed in the proof.
-/

/-- Reduction of GL26 Theorem 1.2(1) to the named geometric residues above. -/
theorem theorem_1_2_open_of_relative_perfect_localization
    (X : Noetherian.FMSetup.{w, u, v}) (hX : X.ctx.IsProperFlat) {K : X.DP}
    (hK : X.ctx.SP.Dcoh K)
    (h₂₇ : FibreRelativePerfectFromEquivalence X K)
    (hreflect : CanonicalRelativePerfectReflection X K)
    (hU : RelativePerfectLocusOpenInput X K)
    (V : Set (CanonicalRelativePerfectLocus X K)) (hV : IsOpen V)
    (hcompare : OpenRestrictionComparison X K V) :
    theorem_1_2_openStatement X hX hK := by
  have hsub : X.FM K ⊆ CanonicalRelativePerfectLocus X K :=
    fm_subset_canonicalRelativePerfectLocus X K h₂₇ hreflect
  have hEq : X.FM K = Subtype.val '' V := by
    ext p
    constructor
    · intro hp
      let q : CanonicalRelativePerfectLocus X K := ⟨p, hsub hp⟩
      have hq : q ∈ V := (hcompare q).2 hp
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact (hcompare q).1 hq
  change IsOpen (X.FM K)
  rw [hEq]
  exact hU.isOpenMap_subtype_val V hV

/-!
## Theorem 1.2(2): the relatively perfect base-change assembly

The local comparison below is only quantified on the base-changed relatively
perfect locus.  It is therefore strictly weaker than assuming the target set
equality.  It is supplied by Corollary 12.4 on that locus and by
pseudofunctoriality.  The equality `hUV` records Corollary 6.18 in one
_direction and faithfully flat reflection for residue-field extensions in the
other.  Outside these loci, Remark 2.7 rules out both equivalence loci.
-/

/-- Generic pointwise assembly of arbitrary base change from comparison on the
relatively perfect loci. -/
theorem theorem_1_2_baseChange_of_relative_perfect_localization
    (X : Noetherian.FMSetup.{w, u, v}) (hX : X.ctx.IsProperFlat) {K : X.DP}
    (hK : X.ctx.SP.Dcoh K) (t : Noetherian.BaseChange X)
    {U : Set X.ctx.Base} {V : Set t.over.ctx.Base}
    (hsub : X.FM K ⊆ U)
    (hsubT : t.over.FM (t.pullKernel.obj K) ⊆ V)
    (hUV : t.mapBase ⁻¹' U = V)
    (hlocal : ∀ q : t.over.ctx.Base, q ∈ V →
      (q ∈ t.over.FM (t.pullKernel.obj K) ↔ t.mapBase q ∈ X.FM K)) :
    theorem_1_2_baseChangeStatement X hX hK t := by
  ext q
  change (t.mapBase q ∈ X.FM K ↔ q ∈ t.over.FM (t.pullKernel.obj K))
  by_cases hq : q ∈ V
  · exact (hlocal q hq).symm
  · apply iff_of_false
    · intro hp
      have hpU : t.mapBase q ∈ U := hsub hp
      have hqV : q ∈ V := by
        rw [← hUV]
        exact hpU
      exact hq hqV
    · intro hqFM
      exact hq (hsubT hqFM)

/-- Theorem 1.2(2), with both subset inclusions derived from fibrewise Remark
2.7 and canonical-representative reflection. -/
theorem theorem_1_2_baseChange_of_neeman_relative_perfect_localization
    (X : Noetherian.FMSetup.{w, u, v}) (hX : X.ctx.IsProperFlat) {K : X.DP}
    (hK : X.ctx.SP.Dcoh K) (t : Noetherian.BaseChange X)
    (h₂₇ : FibreRelativePerfectFromEquivalence X K)
    (hreflect : CanonicalRelativePerfectReflection X K)
    (h₂₇T : FibreRelativePerfectFromEquivalence t.over (t.pullKernel.obj K))
    (hreflectT : CanonicalRelativePerfectReflection t.over (t.pullKernel.obj K))
    (hUV : t.mapBase ⁻¹' CanonicalRelativePerfectLocus X K =
      CanonicalRelativePerfectLocus t.over (t.pullKernel.obj K))
    (hlocal : ∀ q : t.over.ctx.Base,
      q ∈ CanonicalRelativePerfectLocus t.over (t.pullKernel.obj K) →
        (q ∈ t.over.FM (t.pullKernel.obj K) ↔ t.mapBase q ∈ X.FM K)) :
    theorem_1_2_baseChangeStatement X hX hK t :=
  theorem_1_2_baseChange_of_relative_perfect_localization X hX hK t
    (fm_subset_canonicalRelativePerfectLocus X K h₂₇ hreflect)
    (fm_subset_canonicalRelativePerfectLocus t.over (t.pullKernel.obj K)
      h₂₇T hreflectT) hUV hlocal

end RelativeFM.GL26Theorem12Smww27cujM5

#print axioms RelativeFM.GL26Theorem12Smww27cujM5.equivalenceOnDcohAndPerf_of_neeman_coherent_CHNS
#print axioms RelativeFM.GL26Theorem12Smww27cujM5.relativelyPerfect_of_neeman_coherent_CHNS
#print axioms RelativeFM.GL26Theorem12Smww27cujM5.fm_subset_canonicalRelativePerfectLocus
#print axioms RelativeFM.GL26Theorem12Smww27cujM5.theorem_1_2_open_of_relative_perfect_localization
#print axioms RelativeFM.GL26Theorem12Smww27cujM5.theorem_1_2_baseChange_of_relative_perfect_localization
#print axioms RelativeFM.GL26Theorem12Smww27cujM5.theorem_1_2_baseChange_of_neeman_relative_perfect_localization
