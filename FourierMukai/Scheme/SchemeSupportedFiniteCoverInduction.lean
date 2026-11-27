/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.SchemeFiniteCoverInduction

/-!
# Supported finite-cover induction

This module sharpens `SchemeFiniteCoverInductionM5` to the invariant used in
Neeman's proof of Theorem 3.2(iv).  A supported property `Q` takes a scheme `X`
and a closed subset `Z` whose complement is quasi-compact.  The induction needs
only:

* the affine supported base case;
* invariance under scheme isomorphism;
* supported excision from an open `U` containing the support; and
* the open/closed recollement step for `Z \ V` and `Z` restricted to `V`.

In particular, the two-open rule for unsupported weak approximability on
`U`, `V`, and `U ∩ V` is not sufficient to express Neeman's argument: the closed
endpoint is a supported category.  Here that distinction is part of the Lean
interface rather than an informal comment.
-/

@[expose] public section

namespace RelativeFM.SchemeSupportedFiniteCoverInductionM5

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry Set
open RelativeFM.SchemeFiniteCoverInductionM5

universe u

/-- Restriction of a subset of `X` to an open subscheme `U`. -/
def openSupport {X : Scheme.{u}} (U : X.Opens) (Z : Set X) : Set U :=
  U.ι ⁻¹' Z

/-- A property of a scheme and every closed subset with quasi-compact
complement.  For the intended application, `Q X Z` is zero-detection weak
approximability of the repository's `D_qc,Z(X)` model. -/
def UniversallySupported (Q : ∀ {X : Scheme.{u}}, Set X → Prop)
    (X : Scheme.{u}) : Prop :=
  ∀ Z : Set X, IsClosed Z → IsCompact Zᶜ → Q Z

/-- The restriction of an admissible closed support to a compact open has
quasi-compact complement there. -/
lemma isCompact_compl_openSupport {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U : X.Opens) (Z : Set X) (hcU : IsCompact (U : Set X))
    (hZ : IsClosed Z) (hcZ : IsCompact Zᶜ) :
    IsCompact (openSupport U Z)ᶜ := by
  rw [U.ι.isOpenEmbedding.isEmbedding.isCompact_iff, openSupport,
    Set.image_compl_preimage, Scheme.Opens.range_ι, Set.sdiff_eq]
  exact QuasiSeparatedSpace.inter_isCompact (U : Set X) Zᶜ
    U.isOpen hcU hZ.isOpen_compl hcZ

/-- The geometric inputs for supported finite-affine-cover induction.  These
are hypotheses on an abstract supported property, not assertions that the
repository has already constructed its scheme-level recollement. -/
structure SupportedOpenCoverInductionData (Q : ∀ {X : Scheme.{u}}, Set X → Prop) :
    Prop where
  /-- Neeman's affine case, for every closed support with qc complement. -/
  of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X] (Z : Set X),
    IsClosed Z → IsCompact Zᶜ → Q Z
  /-- Transport along an isomorphism of schemes. -/
  of_iso : ∀ {X Y : Scheme.{u}} (e : X ≅ Y) (Z : Set Y),
    Q (e.hom.homeomorph ⁻¹' Z) → Q Z
  /-- Supported excision: a closed support contained in an open can be
  computed on that open.  This is the geometric input explicitly singled out
  in the former `SchemeGluingReduction.lean`. -/
  excision : ∀ {X : Scheme.{u}} (U : X.Opens) (Z : Set X),
    IsClosed Z → Z ⊆ (U : Set X) → Q (openSupport U Z) → Q Z
  /-- Open/closed recollement, with closed part supported on `Z \ V` and open
  part supported on the restriction of `Z` to `V`. -/
  open_closed_glue : ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X] (V : X.Opens) (Z : Set X),
    IsClosed Z → IsCompact Zᶜ → IsCompact (V : Set X) →
    Q (Z \ (V : Set X)) → Q (openSupport V Z) → Q Z

variable {Q : ∀ {X : Scheme.{u}}, Set X → Prop}
  (J : SupportedOpenCoverInductionData Q)

include J

/-- Restricting the closed part `Z \ V` to `U` and the original support to `V`
turns excision plus recollement into two-open gluing for the universally
supported property.  The unsupported property of `U ∩ V` is not used. -/
theorem toOpenCoverInductionData :
    OpenCoverInductionData (UniversallySupported Q) := by
  apply of_twoOpenGluing
  · intro X _ Z hZ hcZ
    exact J.of_isAffine X Z hZ hcZ
  · intro X Y e hX Z hZ hcZ
    exact J.of_iso e Z (hX _ (hZ.preimage e.hom.homeomorph.continuous)
      (e.hom.homeomorph.isCompact_preimage.mpr hcZ))
  · intro X _ U V hcover hcU hcV hU hV _ Z hZ hcZ
    have hZ₁closed : IsClosed (Z \ (V : Set X)) := hZ.sdiff V.isOpen
    have hcZ₁ : IsCompact (Z \ (V : Set X))ᶜ := by
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
    apply J.open_closed_glue V Z hZ hcZ hcV
    · apply J.excision U (Z \ (V : Set X)) hZ₁closed hZ₁U
      exact hU _ (hZ₁closed.preimage U.ι.isOpenEmbedding.isEmbedding.continuous)
        (isCompact_compl_openSupport U (Z \ (V : Set X)) hcU hZ₁closed hcZ₁)
    · exact hV _ (hZ.preimage V.ι.isOpenEmbedding.isEmbedding.continuous)
        (isCompact_compl_openSupport V Z hcV hZ hcZ)

/-- **Supported finite-affine-cover induction for qcqs schemes.**  This is
Neeman's induction shape: the affine base applies to the supported part
`Z \ V`, excision moves it from the affine open to the ambient scheme, and the
inductive hypothesis supplies the restriction of `Z` to the remaining open. -/
theorem supported_of_qcqs (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Z : Set X) (hZ : IsClosed Z) (hcZ : IsCompact Zᶜ) : Q Z :=
  SchemeFiniteCoverInductionM5.of_qcqs (toOpenCoverInductionData J) X Z hZ hcZ

end RelativeFM.SchemeSupportedFiniteCoverInductionM5
