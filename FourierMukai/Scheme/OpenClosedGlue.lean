import FourierMukai.Scheme.SchemeNeemanFiniteCoverAssembly
import FourierMukai.Scheme.SchemeSupportedTwoOpen

/-!
# Preferred-normalized supported open/closed gluing

This module weakens the generator-normalization hypotheses of LP gluing from
object equalities to isomorphisms, and the three `t`-structure equalities to
bounded equivalences. It uses only zero-detection generation
(`IsPaperGenerator`), never the stronger `IsGenerator` field.

Both the repository's original universal fourth field and a compact-glue
variant sufficient for the qcqs induction are populated. No scheme-level
recollement, compact/perfect comparison, or preferredness theorem is asserted
globally: the geometric theorem takes a completion of the two supplied endpoint
approximation packages as an explicit hypothesis.
-/

@[expose] public section

namespace RelativeFM.SchemeOpenClosedGlueM3Smww27cuj

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry TopologicalSpace
open RelativeFM RelativeWeakApprox RelativeWeakApprox.PaperM2
open RelativeFM.SchemeWeakApproxStatementM1
open RelativeFM.NeemanPreferredM6
open RelativeFM.SchemeSupportedTwoOpenM3
open RelativeWeakApprox.SchemeTwoOpenM3

universe v u uZ uD uU

section Rebase

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Finite bounded envelopes only depend on the isomorphism class of their
generator. -/
lemma envelope_le_of_generatorIso {G H : C} (e : G ≅ H) (a b : ℤ) :
    envelope G a b ≤ envelope H a b := by
  unfold envelope
  apply ObjectProperty.monotone_retractClosure
  apply Coprod_mono
  rintro X ⟨k, hak, hkb, ⟨eX⟩⟩
  exact ⟨k, hak, hkb, ⟨eX ≪≫ (shiftFunctor C (-k)).mapIso e⟩⟩

/-- Weak approximation data can be rebased along an isomorphism of its
compact zero-detecting generator, without changing its `t`-structure or
bound. -/
def rebasePaperWeakApproximationData (W : PaperWeakApproximationData C)
    {H : C} (e : W.G ≅ H) : PaperWeakApproximationData C where
  G := H
  t := W.t
  A := W.A
  A_pos := W.A_pos
  G_compact := isCompactAb_of_iso e W.G_compact
  G_paperGenerates := by
    intro E hE
    apply W.G_paperGenerates
    intro n f
    have hh : ((shiftFunctor C n).mapIso e).inv ≫ f =
        ((shiftFunctor C n).mapIso e).inv ≫ (0 : W.G⟦n⟧ ⟶ E) := by
      rw [comp_zero]
      exact hE n ((shiftFunctor C n).map e.inv ≫ f)
    exact (cancel_epi ((shiftFunctor C n).mapIso e).inv).mp hh
  G_mem_le := (W.t.le W.A).prop_of_iso e W.G_mem_le
  hom_vanishing := by
    intro Y hY f
    rw [← cancel_epi e.hom, comp_zero]
    exact W.hom_vanishing hY (e.hom ≫ f)
  exists_triangle := by
    intro F hF
    obtain ⟨E, D, f, g, h, hT, hE, hD⟩ := W.exists_triangle F hF
    exact ⟨E, D, f, g, h, hT, envelope_le_of_generatorIso e _ _ E hE, hD⟩

@[simp] lemma rebasePaperWeakApproximationData_G
    (W : PaperWeakApproximationData C) {H : C} (e : W.G ≅ H) :
    (rebasePaperWeakApproximationData W e).G = H := rfl

@[simp] lemma rebasePaperWeakApproximationData_t
    (W : PaperWeakApproximationData C) {H : C} (e : W.G ≅ H) :
    (rebasePaperWeakApproximationData W e).t = W.t := rfl

@[simp] lemma rebasePaperWeakApproximationData_A
    (W : PaperWeakApproximationData C) {H : C} (e : W.G ≅ H) :
    (rebasePaperWeakApproximationData W e).A = W.A := rfl

end Rebase

section TStructureChange

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [CategoryTheory.IsTriangulated C]

/-- Weak approximation data at `t` induce weak approximation data at any
boundedly equivalent `t'`.  The generator is unchanged and the approximation
bound increases by the interposition bound. -/
def rebasePaperWeakApproximationDataTStructure
    (W : PaperWeakApproximationData C) (t' : TStructure C)
    (h : TStructureEquivalent W.t t') : PaperWeakApproximationData C := by
  let N := h.choose
  have hN : 0 < N := h.choose_spec.1
  have h₁ : W.t.le (-N) ≤ t'.le 0 := h.choose_spec.2.1
  have h₂ : t'.le 0 ≤ W.t.le N := h.choose_spec.2.2
  exact
    { G := W.G
      t := t'
      A := W.A + N
      A_pos := add_pos W.A_pos hN
      G_compact := W.G_compact
      G_paperGenerates := W.G_paperGenerates
      G_mem_le := by
        have hle := shift_aisle_inclusion h₁ (-(W.A + N))
        rw [show -N - -(W.A + N) = W.A by ring,
          show 0 - -(W.A + N) = W.A + N by ring] at hle
        exact hle W.G W.G_mem_le
      hom_vanishing := by
        intro Y hY f
        have hle := shift_aisle_inclusion h₂ (W.A + N)
        rw [show 0 - (W.A + N) = -(W.A + N) by ring,
          show N - (W.A + N) = -W.A by ring] at hle
        exact W.hom_vanishing (hle Y hY) f
      exists_triangle := by
        intro F hF
        have hFN : W.t.le N F := h₂ F hF
        have hF0 : W.t.le 0 (F⟦N⟧) :=
          W.t.le_shift N N 0 (by ring) F hFN
        obtain ⟨E, D, a, f, b, hT, hE, _hEa, hD⟩ :=
          PaperM2.lemma_3_4 W hF0 (m := 2 * N + 1) (by omega)
        let p : E⟦-N⟧ ⟶ (F⟦N⟧)⟦-N⟧ := (-N).negOnePow • a⟦-N⟧'
        let q : (F⟦N⟧)⟦-N⟧ ⟶ D⟦-N⟧ := (-N).negOnePow • f⟦-N⟧'
        let r : D⟦-N⟧ ⟶ (E⟦-N⟧)⟦(1 : ℤ)⟧ :=
          (-N).negOnePow • b⟦-N⟧' ≫ (shiftFunctorComm C 1 (-N)).hom.app E
        let S : Triangle C := Triangle.mk p q r
        have hS : S ∈ distTriang C :=
          (Triangle.mk a f b).shift_distinguished hT (-N)
        let eF : (F⟦N⟧)⟦-N⟧ ≅ F := shiftShiftNeg F N
        let u : F ⟶ D⟦-N⟧ := eF.inv ≫ q
        let T₂ : Triangle C := Triangle.mk (p ≫ eF.hom) u r
        have hT₂ : T₂ ∈ distTriang C := by
          apply isomorphic_distinguished S hS T₂
          exact Triangle.isoMk _ _ (Iso.refl _) eF.symm (Iso.refl _)
            (by
              change (p ≫ eF.hom) ≫ eF.inv = 𝟙 _ ≫ p
              rw [Category.id_comp, Category.assoc, eF.hom_inv_id, Category.comp_id])
            (by
              change (eF.inv ≫ q) ≫ 𝟙 _ = eF.inv ≫ q
              simp)
            (by
              change r ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 _) = 𝟙 _ ≫ r
              simp)
        have hEshift : envelope W.G (-W.A - N) (W.A + N) (E⟦-N⟧) := by
          have hh := map_shift_envelope W.G (1 - (2 * N + 1) - W.A) W.A (-N) hE
          simpa only [show 1 - (2 * N + 1) - W.A - -N = -W.A - N by ring,
            show W.A - -N = W.A + N by ring] using hh
        have hDshift : W.t.le (-N - 1) (D⟦-N⟧) :=
          W.t.le_shift (-(2 * N + 1)) (-N) (-N - 1) (by ring) D hD
        have hle := shift_aisle_inclusion h₁ (1 : ℤ)
        rw [show -N - 1 = -N - 1 by ring, show 0 - 1 = -1 by ring] at hle
        exact ⟨E⟦-N⟧, D⟦-N⟧, p ≫ eF.hom, u, r, hT₂,
          lemma31_2_mono W.G (by omega) (by omega) (E⟦-N⟧) hEshift,
          hle _ hDshift⟩ }

@[simp] lemma rebasePaperWeakApproximationDataTStructure_G
    (W : PaperWeakApproximationData C) (t' : TStructure C)
    (h : TStructureEquivalent W.t t') :
    (rebasePaperWeakApproximationDataTStructure W t' h).G = W.G := rfl

@[simp] lemma rebasePaperWeakApproximationDataTStructure_t
    (W : PaperWeakApproximationData C) (t' : TStructure C)
    (h : TStructureEquivalent W.t t') :
    (rebasePaperWeakApproximationDataTStructure W t' h).t = t' := rfl

end TStructureChange

section EndpointReplacement

variable {DZ : Type uZ} {DX : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} DX] [Category.{v} DU]
  [Preadditive DZ] [Preadditive DX] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DX] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DX ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor DX n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DX] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DX]
  [CategoryTheory.IsTriangulated DU]

/-- Complete an open-endpoint setup with closed approximation data whose
generator is merely isomorphic to the normalized closed generator. -/
def replaceClosedApproximationIso (S : PaperOpenEndpointSetup DZ DX DU)
    (WZ : PaperWeakApproximationData DZ) (ht : WZ.t = S.tZ)
    (e : WZ.G ≅ S.R.iStar.obj (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU)) :
    PaperSetupMainMinimal DZ DX DU :=
  PaperOpenEndpointSetup.toPaperSetupMainMinimal
    (S := S) (WZ := rebasePaperWeakApproximationData WZ e) (ht := ht) (hG := rfl)

/-- Replace the open approximation package in a seed, allowing its generator
to match the seed's chosen generator only up to isomorphism. -/
def replaceOpenApproximationIso (S : PaperOpenEndpointSetup DZ DX DU)
    (WU : PaperWeakApproximationData DU) (ht : WU.t = S.tU)
    (e : WU.G ≅ S.GU) : PaperOpenEndpointSetup DZ DX DU where
  R := S.R
  tD := S.tD
  tZ := S.tZ
  tU := S.tU
  approxU := rebasePaperWeakApproximationData WU e
  GU := S.GU
  G' := S.G'
  G'_compact := S.G'_compact
  G'_paperGenerates := S.G'_paperGenerates
  m := S.m
  jStar_G'_mem := S.jStar_G'_mem
  normalized_biproduct := S.normalized_biproduct
  tD_compactlyGenerated := S.tD_compactlyGenerated
  tZ_compactlyGenerated := S.tZ_compactlyGenerated
  tU_compactlyGenerated := S.tU_compactlyGenerated
  approxU_t := ht
  approxU_G := rfl

/-- The same replacement at the geometric seed level. -/
def replaceOpenApproximationSeedIso (I : PaperSchemeOpenClosedSeed DZ DX DU)
    (WU : PaperWeakApproximationData DU) (ht : WU.t = I.setup.tU)
    (e : WU.G ≅ I.setup.GU) : PaperSchemeOpenClosedSeed DZ DX DU where
  geometry := I.geometry
  setup := replaceOpenApproximationIso I.setup WU ht e
  perfectX := I.perfectX
  perfectU := I.perfectU
  perfectZ := I.perfectZ
  supportedOnZ := I.supportedOnZ
  supported_iff := I.supported_iff

/-- LP open/closed gluing with arbitrary supplied endpoint approximation
packages.  Their `t`-structures and generators need only agree with those of
the normalized geometric seed, with generator agreement up to isomorphism. -/
theorem satisfiesPaperWAAt_of_openClosed_endpointsIso
    (I : PaperSchemeOpenClosedSeed DZ DX DU)
    (WZ : PaperWeakApproximationData DZ) (htZ : WZ.t = I.setup.tZ)
    (eZ : WZ.G ≅ I.setup.R.iStar.obj
      (I.setup.G'⟦I.setup.m⟧ ⊞ I.setup.R.jShriek.obj I.setup.GU))
    (WU : PaperWeakApproximationData DU) (htU : WU.t = I.setup.tU)
    (eU : WU.G ≅ I.setup.GU)
    [HasCoproducts.{v} DZ] [HasCoproducts.{v} DX] [HasCoproducts.{v} DU]
    (hvan : CompactHomZeroAtTop DX) :
    SatisfiesPaperWAAt DX I.setup.tD := by
  let I' := replaceOpenApproximationSeedIso I WU htU eU
  let J := PaperSchemeOpenClosedSeed.toPaperSchemeOpenClosedDerived
    (I := I') (WZ := rebasePaperWeakApproximationData WZ eZ) (ht := htZ) (hG := rfl)
  obtain ⟨W, ht, _⟩ := J.exists_paperData_of_compactHomZeroAtTop hvan
  exact ⟨W, ht⟩

end EndpointReplacement

section SupportedScheme

open RelativeFM.SchemeNeemanFiniteCoverAssemblyM5

/-- The open/closed geometry attached to an open subscheme. -/
noncomputable def openClosedGeometry {X : Scheme.{u}} (V : X.Opens) :
    RelativeWeakApprox.SchemeOpenClosed.{u} where
  X := X
  U := V
  j := V.ι
  Z := (V : Set X)ᶜ
  Z_closed := V.isOpen.isClosed_compl
  Z_eq := by rw [Scheme.Opens.opensRange_ι]

/-- Supported LP gluing in the `D_qc` model, with both endpoint approximation
packages supplied and matched up to isomorphism. -/
theorem neemanSupportedWeakApproximability_of_openClosed_endpointsIso
    {g : RelativeWeakApprox.SchemeOpenClosed.{u}}
    {SX SZ : TopologicalSpace.Closeds g.X}
    {SU : TopologicalSpace.Closeds g.U}
    (I : DqcSupportedNeemanOpenClosedSeed g SX SZ SU)
    (WZ : PaperWeakApproximationData (DqcSupported g.X SZ))
    (htZ : WZ.t = I.setup.tZ)
    (eZ : WZ.G ≅ I.setup.R.iStar.obj
      (I.setup.G'⟦I.setup.m⟧ ⊞ I.setup.R.jShriek.obj I.setup.GU))
    (WU : PaperWeakApproximationData (DqcSupported g.U SU))
    (htU : WU.t = I.setup.tU) (eU : WU.G ≅ I.setup.GU)
    [HasCoproducts.{u + 1} (DqcSupported g.X SZ)]
    [HasCoproducts.{u + 1} (DqcSupported g.X SX)]
    [HasCoproducts.{u + 1} (DqcSupported g.U SU)]
    (htD : I.setup.tD = dqcSupportedStandardTStructure g.X SX)
    (hvan : CompactHomZeroAtTop (DqcSupported g.X SX)) :
    NeemanSupportedWeakApproximability g.X SX := by
  obtain ⟨W, ht⟩ := satisfiesPaperWAAt_of_openClosed_endpointsIso
    I WZ htZ eZ WU htU eU hvan
  exact ⟨⟨W, ht.trans htD⟩⟩

/-- Exact remaining geometric completion of a supported open/closed seed and
two standard endpoint approximation packages.

For an actual qcqs instantiation the intended sources are the open/closed
localization sequence (GL26 Appendix A), Neeman Theorem 3.2(i)--(iii) for the
compact/perfect and normalized `t`-structure fields, and bounded perfect Ext
(Stacks 09M4) for `compactHomZeroAtTop`.  No field asserts weak approximability
of the middle category.  The structure is stated without a compact-space
hypothesis so it can serve the repository's current universal fourth field;
in that extra generality 09M4 alone is not a proof of `compactHomZeroAtTop`. -/
structure SupportedNeemanOpenClosedCompletion
    {g : RelativeWeakApprox.SchemeOpenClosed.{u}}
    {SX SZ : TopologicalSpace.Closeds g.X}
    {SU : TopologicalSpace.Closeds g.U}
    (I : DqcSupportedNeemanOpenClosedSeed g SX SZ SU)
    (WZ : DqcSupportedStandardPaperWeakApproximationData g.X SZ)
    (WU : DqcSupportedStandardPaperWeakApproximationData g.U SU) : Prop where
  preferredZ : TStructureEquivalent (dqcSupportedStandardTStructure g.X SZ) I.setup.tZ
  isoZ : Nonempty (WZ.1.G ≅ I.setup.R.iStar.obj
    (I.setup.G'⟦I.setup.m⟧ ⊞ I.setup.R.jShriek.obj I.setup.GU))
  preferredU : TStructureEquivalent (dqcSupportedStandardTStructure g.U SU) I.setup.tU
  isoU : Nonempty (WU.1.G ≅ I.setup.GU)
  preferredD : TStructureEquivalent (dqcSupportedStandardTStructure g.X SX) I.setup.tD
  coproductZ : HasCoproducts.{u + 1} (DqcSupported g.X SZ)
  coproductX : HasCoproducts.{u + 1} (DqcSupported g.X SX)
  coproductU : HasCoproducts.{u + 1} (DqcSupported g.U SU)
  compactHomZeroAtTop : CompactHomZeroAtTop (DqcSupported g.X SX)

/-- The completion fields imply the standard supported conclusion. -/
theorem neemanSupportedWeakApproximability_of_completion
    {g : RelativeWeakApprox.SchemeOpenClosed.{u}}
    {SX SZ : TopologicalSpace.Closeds g.X}
    {SU : TopologicalSpace.Closeds g.U}
    (I : DqcSupportedNeemanOpenClosedSeed g SX SZ SU)
    (WZ : DqcSupportedStandardPaperWeakApproximationData g.X SZ)
    (WU : DqcSupportedStandardPaperWeakApproximationData g.U SU)
    (K : SupportedNeemanOpenClosedCompletion I WZ WU) :
    NeemanSupportedWeakApproximability g.X SX := by
  letI := K.coproductZ
  letI := K.coproductX
  letI := K.coproductU
  have hZ : TStructureEquivalent WZ.1.t I.setup.tZ := by
    rw [WZ.2]
    exact K.preferredZ
  have hU : TStructureEquivalent WU.1.t I.setup.tU := by
    rw [WU.2]
    exact K.preferredU
  let WZ' := rebasePaperWeakApproximationDataTStructure WZ.1 I.setup.tZ hZ
  let WU' := rebasePaperWeakApproximationDataTStructure WU.1 I.setup.tU hU
  obtain ⟨W, ht⟩ := satisfiesPaperWAAt_of_openClosed_endpointsIso
    I WZ' (by rfl) (by change WZ.1.G ≅ _; exact K.isoZ.some)
    WU' (by rfl) (by change WU.1.G ≅ I.setup.GU; exact K.isoU.some)
    K.compactHomZeroAtTop
  have heq : TStructureEquivalent W.t (dqcSupportedStandardTStructure g.X SX) := by
    apply tStructureEquivalent_symm
    rw [ht]
    exact K.preferredD
  exact ⟨⟨rebasePaperWeakApproximationDataTStructure W _ heq, rfl⟩⟩

/-- The geometric input needed to populate exactly the fourth field of
`NeemanSupportedCoverInput`, using the two endpoint hypotheses of that field.
The completion is allowed to depend on those endpoint data, rather than
silently replacing them by unrelated approximation packages. -/
def NeemanOpenClosedCompletionInput : Prop :=
  ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X] (V : X.Opens)
    (Z : TopologicalSpace.Closeds X),
    IsCompactClosedComplement Z → IsCompactOpen V →
    ∀ (WZ : DqcSupportedStandardPaperWeakApproximationData X (closedDiff V Z))
      (WU : DqcSupportedStandardPaperWeakApproximationData V (openClosedSupport V Z)),
    ∃ I : DqcSupportedNeemanOpenClosedSeed.{u, u + 1} (openClosedGeometry V)
      Z (closedDiff V Z) (openClosedSupport V Z),
      SupportedNeemanOpenClosedCompletion I WZ WU

/-- Populate the open/closed gluing field from the exact geometric completion.
This theorem has the field's original non-quasi-compact generality; no Stacks
09M4 hypothesis is smuggled past its quasi-compactness assumptions. -/
theorem open_closed_glue_of_completionInput (J : NeemanOpenClosedCompletionInput.{u}) :
    ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X] (V : X.Opens)
      (Z : TopologicalSpace.Closeds X),
      IsCompactClosedComplement Z → IsCompactOpen V →
      NeemanSupportedWeakApproximability X (closedDiff V Z) →
      NeemanSupportedWeakApproximability V (openClosedSupport V Z) →
      NeemanSupportedWeakApproximability X Z := by
  intro X _ V Z hcZ hcV hclosed hopen
  obtain ⟨WZ⟩ := hclosed
  obtain ⟨WU⟩ := hopen
  obtain ⟨I, K⟩ := J V Z hcZ hcV WZ WU
  exact neemanSupportedWeakApproximability_of_completion I WZ WU K

/-- Replace only the fourth field of the cover input.  The affine base,
scheme-isomorphism transport, and excision fields are unchanged. -/
theorem neemanSupportedCoverInputOfCompletion
    (of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X]
      (Z : TopologicalSpace.Closeds X), IsCompactClosedComplement Z →
      NeemanSupportedWeakApproximability X Z)
    (of_iso : ∀ {X Y : Scheme.{u}} (e : X ≅ Y)
      (Z : TopologicalSpace.Closeds Y),
      NeemanSupportedWeakApproximability X (isoPreimageClosed e Z) →
      NeemanSupportedWeakApproximability Y Z)
    (excision : ∀ {X : Scheme.{u}} (U : X.Opens)
      (Z : TopologicalSpace.Closeds X), (Z : Set X) ⊆ (U : Set X) →
      NeemanSupportedWeakApproximability U (openClosedSupport U Z) →
      NeemanSupportedWeakApproximability X Z)
    (J : NeemanOpenClosedCompletionInput.{u}) :
    SchemeNeemanFiniteCoverAssemblyM5.NeemanSupportedCoverInput.{u} where
  of_isAffine := of_isAffine
  of_iso := of_iso
  excision := excision
  open_closed_glue := open_closed_glue_of_completionInput J

/-- Final qcqs assembly with the open/closed step supplied by the normalized
completion input. -/
theorem neemanSupported_of_qcqs_of_completionInput
    (of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X]
      (Z : TopologicalSpace.Closeds X), IsCompactClosedComplement Z →
      NeemanSupportedWeakApproximability X Z)
    (of_iso : ∀ {X Y : Scheme.{u}} (e : X ≅ Y)
      (Z : TopologicalSpace.Closeds Y),
      NeemanSupportedWeakApproximability X (isoPreimageClosed e Z) →
      NeemanSupportedWeakApproximability Y Z)
    (excision : ∀ {X : Scheme.{u}} (U : X.Opens)
      (Z : TopologicalSpace.Closeds X), (Z : Set X) ⊆ (U : Set X) →
      NeemanSupportedWeakApproximability U (openClosedSupport U Z) →
      NeemanSupportedWeakApproximability X Z)
    (J : NeemanOpenClosedCompletionInput.{u})
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Z : TopologicalSpace.Closeds X) (hcZ : IsCompactClosedComplement Z) :
    NeemanSupportedWeakApproximability X Z :=
  SchemeNeemanFiniteCoverAssemblyM5.neemanSupported_of_qcqs
    (neemanSupportedCoverInputOfCompletion of_isAffine of_iso excision J) X Z hcZ

/-! ### The compact open/closed field actually used by the qcqs induction -/

open RelativeFM.SchemeFiniteCoverInductionM5
open RelativeFM.SchemeSupportedFiniteCoverInductionM5

/-- Supported cover inputs with open/closed gluing required only on a
quasi-compact ambient scheme.  This is sufficient for the qcqs induction and
matches the hypotheses of the geometric compact-generation and Ext theorems. -/
structure CompactSupportedOpenCoverInductionData
    (Q : ∀ {X : Scheme.{u}}, Set X → Prop) : Prop where
  of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X] (Z : Set X),
    IsClosed Z → _root_.IsCompact Zᶜ → Q Z
  of_iso : ∀ {X Y : Scheme.{u}} (e : X ≅ Y) (Z : Set Y),
    Q (e.hom.homeomorph ⁻¹' Z) → Q Z
  excision : ∀ {X : Scheme.{u}} (U : X.Opens) (Z : Set X),
    IsClosed Z → Z ⊆ (U : Set X) → Q (openSupport U Z) → Q Z
  open_closed_glue : ∀ {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (V : X.Opens) (Z : Set X),
    IsClosed Z → _root_.IsCompact Zᶜ → _root_.IsCompact (V : Set X) →
    Q (Z \ (V : Set X)) → Q (openSupport V Z) → Q Z

section CompactAbstract

variable {Q : ∀ {X : Scheme.{u}}, Set X → Prop}
  (J : CompactSupportedOpenCoverInductionData Q)

include J

/-- Compact-glue supported induction data give the ordinary open-cover
induction.  Compactness of the ambient scheme at the gluing node follows from
`U ⊔ V = ⊤` and compactness of `U` and `V`. -/
theorem compactSupported_toOpenCoverInductionData :
    OpenCoverInductionData (UniversallySupported Q) := by
  apply of_twoOpenGluing
  · intro X _ Z hZ hcZ
    exact J.of_isAffine X Z hZ hcZ
  · intro X Y e hX Z hZ hcZ
    exact J.of_iso e Z (hX _ (hZ.preimage e.hom.homeomorph.continuous)
      (e.hom.homeomorph.isCompact_preimage.mpr hcZ))
  · intro X _ U V hcover hcU hcV hU hV _ Z hZ hcZ
    have hZ₁closed : IsClosed (Z \ (V : Set X)) := hZ.sdiff V.isOpen
    have hcZ₁ : _root_.IsCompact (Z \ (V : Set X))ᶜ := by
      rw [Set.compl_sdiff]
      exact hcV.union hcZ
    have hZ₁U : (Z \ (V : Set X)) ⊆ (U : Set X) := by
      intro x hx
      have hxUV : x ∈ ((U ⊔ V : X.Opens) : Set X) := by
        rw [hcover]
        exact Set.mem_univ x
      rw [Opens.coe_sup] at hxUV
      rcases hxUV with hxU | hxV
      · exact hxU
      · exact (hx.2 hxV).elim
    have hcTop : _root_.IsCompact ((U ⊔ V : X.Opens) : Set X) := by
      rw [Opens.coe_sup]
      exact hcU.union hcV
    rw [hcover] at hcTop
    have hcUniv : _root_.IsCompact (Set.univ : Set X) := by simpa using hcTop
    letI : CompactSpace X := isCompact_univ_iff.mp hcUniv
    apply J.open_closed_glue V Z hZ hcZ hcV
    · apply J.excision U (Z \ (V : Set X)) hZ₁closed hZ₁U
      exact hU _ (hZ₁closed.preimage U.ι.isOpenEmbedding.isEmbedding.continuous)
        (isCompact_compl_openSupport U (Z \ (V : Set X)) hcU hZ₁closed hcZ₁)
    · exact hV _ (hZ.preimage V.ι.isOpenEmbedding.isEmbedding.continuous)
        (isCompact_compl_openSupport V Z hcV hZ hcZ)

/-- Finite-affine-cover induction using the weaker compact gluing field. -/
theorem compactSupported_of_qcqs (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (Z : Set X) (hZ : IsClosed Z)
    (hcZ : _root_.IsCompact Zᶜ) : Q Z :=
  SchemeFiniteCoverInductionM5.of_qcqs
    (compactSupported_toOpenCoverInductionData J) X Z hZ hcZ

end CompactAbstract

/-- The actual geometric input for compact open/closed gluing. -/
structure NeemanCompactSupportedCoverInput : Prop where
  of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X]
    (Z : TopologicalSpace.Closeds X),
    IsCompactClosedComplement Z → NeemanSupportedWeakApproximability X Z
  of_iso : ∀ {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y),
    NeemanSupportedWeakApproximability X (isoPreimageClosed e Z) →
    NeemanSupportedWeakApproximability Y Z
  excision : ∀ {X : Scheme.{u}} (U : X.Opens)
    (Z : TopologicalSpace.Closeds X), (Z : Set X) ⊆ (U : Set X) →
    NeemanSupportedWeakApproximability U (openClosedSupport U Z) →
    NeemanSupportedWeakApproximability X Z
  open_closed_glue : ∀ {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (V : X.Opens) (Z : TopologicalSpace.Closeds X),
    IsCompactClosedComplement Z → IsCompactOpen V →
    NeemanSupportedWeakApproximability X (closedDiff V Z) →
    NeemanSupportedWeakApproximability V (openClosedSupport V Z) →
    NeemanSupportedWeakApproximability X Z

/-- Normalized completions are needed only on qcqs schemes.  In particular an
instantiation may use the quasi-compactness hypotheses of Stacks 09M4 to
construct the last `CompactHomZeroAtTop` field. -/
def NeemanCompactOpenClosedCompletionInput : Prop :=
  ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (V : X.Opens)
    (Z : TopologicalSpace.Closeds X),
    IsCompactClosedComplement Z → IsCompactOpen V →
    ∀ (WZ : DqcSupportedStandardPaperWeakApproximationData X (closedDiff V Z))
      (WU : DqcSupportedStandardPaperWeakApproximationData V (openClosedSupport V Z)),
    ∃ I : DqcSupportedNeemanOpenClosedSeed.{u, u + 1} (openClosedGeometry V)
      Z (closedDiff V Z) (openClosedSupport V Z),
      SupportedNeemanOpenClosedCompletion I WZ WU

/-- Populate the compact version of the open/closed field. -/
theorem compact_open_closed_glue_of_completionInput
    (J : NeemanCompactOpenClosedCompletionInput.{u}) :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (V : X.Opens) (Z : TopologicalSpace.Closeds X),
      IsCompactClosedComplement Z → IsCompactOpen V →
      NeemanSupportedWeakApproximability X (closedDiff V Z) →
      NeemanSupportedWeakApproximability V (openClosedSupport V Z) →
      NeemanSupportedWeakApproximability X Z := by
  intro X _ _ V Z hcZ hcV hclosed hopen
  obtain ⟨WZ⟩ := hclosed
  obtain ⟨WU⟩ := hopen
  obtain ⟨I, K⟩ := J V Z hcZ hcV WZ WU
  exact neemanSupportedWeakApproximability_of_completion I WZ WU K

/-- Package the other three original inputs with the compact completion. -/
theorem neemanCompactSupportedCoverInputOfCompletion
    (of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X]
      (Z : TopologicalSpace.Closeds X), IsCompactClosedComplement Z →
      NeemanSupportedWeakApproximability X Z)
    (of_iso : ∀ {X Y : Scheme.{u}} (e : X ≅ Y)
      (Z : TopologicalSpace.Closeds Y),
      NeemanSupportedWeakApproximability X (isoPreimageClosed e Z) →
      NeemanSupportedWeakApproximability Y Z)
    (excision : ∀ {X : Scheme.{u}} (U : X.Opens)
      (Z : TopologicalSpace.Closeds X), (Z : Set X) ⊆ (U : Set X) →
      NeemanSupportedWeakApproximability U (openClosedSupport U Z) →
      NeemanSupportedWeakApproximability X Z)
    (J : NeemanCompactOpenClosedCompletionInput.{u}) :
    NeemanCompactSupportedCoverInput.{u} where
  of_isAffine := of_isAffine
  of_iso := of_iso
  excision := excision
  open_closed_glue := compact_open_closed_glue_of_completionInput J

variable (K : NeemanCompactSupportedCoverInput.{u})

include K

/-- Set-level adapter for the compact cover input. -/
theorem neemanCompact_toSetInductionData :
    CompactSupportedOpenCoverInductionData
      (fun {X : Scheme.{u}} ↦ NeemanSetProperty (X := X)) where
  of_isAffine := by
    intro X _ Z hZ hcZ hZ'
    exact K.of_isAffine X ⟨Z, hZ'⟩ hcZ
  of_iso := by
    intro X Y e Z hQ hZ
    exact K.of_iso e ⟨Z, hZ⟩
      (hQ (hZ.preimage e.hom.homeomorph.continuous))
  excision := by
    intro X U Z hZ hsub hQ hZ'
    apply K.excision U ⟨Z, hZ'⟩ hsub
    exact hQ (IsClosed.preimage U.ι.isOpenEmbedding.isEmbedding.continuous hZ)
  open_closed_glue := by
    intro X _ _ V Z hZ hcZ hcV hclosed hopen hZ'
    apply K.open_closed_glue V ⟨Z, hZ'⟩ hcZ hcV
    · exact hclosed (hZ.sdiff V.isOpen)
    · exact hopen (hZ.preimage V.ι.isOpenEmbedding.isEmbedding.continuous)

/-- Final qcqs Neeman assembly using only compact open/closed gluing. -/
theorem neemanSupported_of_qcqs_with_compactGlue
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Z : TopologicalSpace.Closeds X) (hcZ : IsCompactClosedComplement Z) :
    NeemanSupportedWeakApproximability X Z := by
  have h : NeemanSetProperty (X := X) (Z : Set X) :=
    compactSupported_of_qcqs (neemanCompact_toSetInductionData K)
      X (Z : Set X) Z.isClosed hcZ
  exact h Z.isClosed

omit K in
/-- Final qcqs assembly taking the three other inputs and only the compact
version of the normalized open/closed completion. -/
theorem neemanSupported_of_qcqs_of_compactCompletionInput
    (of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X]
      (Z : TopologicalSpace.Closeds X), IsCompactClosedComplement Z →
      NeemanSupportedWeakApproximability X Z)
    (of_iso : ∀ {X Y : Scheme.{u}} (e : X ≅ Y)
      (Z : TopologicalSpace.Closeds Y),
      NeemanSupportedWeakApproximability X (isoPreimageClosed e Z) →
      NeemanSupportedWeakApproximability Y Z)
    (excision : ∀ {X : Scheme.{u}} (U : X.Opens)
      (Z : TopologicalSpace.Closeds X), (Z : Set X) ⊆ (U : Set X) →
      NeemanSupportedWeakApproximability U (openClosedSupport U Z) →
      NeemanSupportedWeakApproximability X Z)
    (J : NeemanCompactOpenClosedCompletionInput.{u})
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Z : TopologicalSpace.Closeds X) (hcZ : IsCompactClosedComplement Z) :
    NeemanSupportedWeakApproximability X Z :=
  neemanSupported_of_qcqs_with_compactGlue
    (neemanCompactSupportedCoverInputOfCompletion of_isAffine of_iso excision J)
    X Z hcZ

end SupportedScheme

end
end RelativeFM.SchemeOpenClosedGlueM3Smww27cuj

#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.envelope_le_of_generatorIso
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.rebasePaperWeakApproximationData
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.replaceClosedApproximationIso
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.replaceOpenApproximationIso
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.replaceOpenApproximationSeedIso
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.satisfiesPaperWAAt_of_openClosed_endpointsIso

#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.neemanSupportedWeakApproximability_of_openClosed_endpointsIso
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.neemanSupportedWeakApproximability_of_completion
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.open_closed_glue_of_completionInput
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.neemanSupportedCoverInputOfCompletion
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.neemanSupported_of_qcqs_of_completionInput

#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.compactSupported_toOpenCoverInductionData
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.compactSupported_of_qcqs
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.compact_open_closed_glue_of_completionInput
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.neemanCompactSupportedCoverInputOfCompletion
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.neemanCompact_toSetInductionData
#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.neemanSupported_of_qcqs_with_compactGlue

#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.rebasePaperWeakApproximationDataTStructure

#print axioms RelativeFM.SchemeOpenClosedGlueM3Smww27cuj.neemanSupported_of_qcqs_of_compactCompletionInput
