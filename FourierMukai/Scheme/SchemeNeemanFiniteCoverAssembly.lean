/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.SchemeWeakApproxStatement
import FourierMukai.Scheme.SchemeSupportedFiniteCoverInduction

/-!
# Neeman's supported finite-cover assembly

This file specializes the abstract supported induction to the repository's
actual zero-detection scheme statement.  It deliberately does not claim the
affine supported base, scheme-isomorphism transport, supported excision, or the
open/closed recollement: those are the fields of
`NeemanSupportedCoverInput`.  Once they are supplied, `neemanSupported_of_qcqs`
is Neeman Theorem 3.2(iv) in the all-sheaves model.
-/

@[expose] public section

namespace RelativeFM.SchemeNeemanFiniteCoverAssemblyM5

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry Set
open RelativeFM.SchemeWeakApproxStatementM1
open RelativeFM.SchemeSupportedFiniteCoverInductionM5

universe u

/-- The closed support supported on the restriction of `Z` to an open. -/
def openClosedSupport {X : Scheme.{u}} (U : X.Opens)
    (Z : TopologicalSpace.Closeds X) : TopologicalSpace.Closeds U :=
  ⟨openSupport U (Z : Set X),
    Z.isClosed.preimage U.ι.isOpenEmbedding.isEmbedding.continuous⟩

/-- The closed part `Z \ V` used by open/closed gluing. -/
def closedDiff {X : Scheme.{u}} (V : X.Opens)
    (Z : TopologicalSpace.Closeds X) : TopologicalSpace.Closeds X :=
  ⟨(Z : Set X) \ (V : Set X), Z.isClosed.sdiff V.isOpen⟩

/-- Pullback of a closed support along an isomorphism of schemes. -/
def isoPreimageClosed {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y) : TopologicalSpace.Closeds X :=
  ⟨e.hom.homeomorph ⁻¹' (Z : Set Y),
    Z.isClosed.preimage e.hom.homeomorph.continuous⟩

/-- Quasi-compactness of the complement of a closed support, with the
carrier universe fixed explicitly at the definition site. -/
def IsCompactClosedComplement {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) : Prop :=
  _root_.IsCompact (Z : Set X)ᶜ

/-- Quasi-compactness of an open subscheme. -/
def IsCompactOpen {X : Scheme.{u}} (U : X.Opens) : Prop :=
  _root_.IsCompact (U : Set X)

/-- The set-level form of the repository's supported statement.  The extra
closedness proof is necessary because the abstract induction manipulates raw
sets; `TopologicalSpace.Closeds` packages the same proof directly. -/
def NeemanSetProperty {X : Scheme.{u}} (Z : Set X) : Prop :=
  ∀ hZ : IsClosed Z, NeemanSupportedWeakApproximability X ⟨Z, hZ⟩

/-- The exact geometric inputs needed to prove Neeman's supported statement
by finite affine covers.  These fields are propositions about the actual
`D_qc,Z` model, not fields restating the final qcqs conclusion on a scheme
whose covers are already known. -/
structure NeemanSupportedCoverInput : Prop where
  /-- Affine supported Neeman base case. -/
  of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X]
    (Z : TopologicalSpace.Closeds X),
    IsCompactClosedComplement Z →
    NeemanSupportedWeakApproximability X Z
  /-- Transport of supported weak approximability along a scheme isomorphism. -/
  of_iso : ∀ {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y),
    NeemanSupportedWeakApproximability X (isoPreimageClosed e Z) →
    NeemanSupportedWeakApproximability Y Z
  /-- Supported excision for a closed subset contained in an open. -/
  excision : ∀ {X : Scheme.{u}} (U : X.Opens)
    (Z : TopologicalSpace.Closeds X), (Z : Set X) ⊆ (U : Set X) →
    NeemanSupportedWeakApproximability U (openClosedSupport U Z) →
    NeemanSupportedWeakApproximability X Z
  /-- Zero-detection open/closed gluing. -/
  open_closed_glue : ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X] (V : X.Opens)
    (Z : TopologicalSpace.Closeds X),
    IsCompactClosedComplement Z → IsCompactOpen V →
    NeemanSupportedWeakApproximability X (closedDiff V Z) →
    NeemanSupportedWeakApproximability V (openClosedSupport V Z) →
    NeemanSupportedWeakApproximability X Z

variable (J : NeemanSupportedCoverInput.{u})

include J

/-- Forget the packaged closedness proofs to use the abstract support
induction.  No geometric field is discharged in this construction. -/
theorem toSetInductionData :
    SupportedOpenCoverInductionData (fun {X : Scheme.{u}} ↦ NeemanSetProperty (X := X)) where
  of_isAffine := by
    intro X _ Z hZ hcZ hZ'
    exact J.of_isAffine X ⟨Z, hZ'⟩ hcZ
  of_iso := by
    intro X Y e Z hQ hZ
    exact J.of_iso e ⟨Z, hZ⟩
      (hQ (hZ.preimage e.hom.homeomorph.continuous))
  excision := by
    intro X U Z hZ hsub hQ hZ'
    apply J.excision U ⟨Z, hZ'⟩ hsub
    exact hQ (IsClosed.preimage U.ι.isOpenEmbedding.isEmbedding.continuous hZ)
  open_closed_glue := by
    intro X _ V Z hZ hcZ hcV hclosed hopen hZ'
    apply J.open_closed_glue V ⟨Z, hZ'⟩ hcZ hcV
    · exact hclosed (hZ.sdiff V.isOpen)
    · exact hopen (hZ.preimage V.ι.isOpenEmbedding.isEmbedding.continuous)

/-- **Neeman finite-cover induction in the repository's model.**  The output
is zero-detection `PaperWeakApproximationData` at the restricted standard
`t`-structure on `D_qc,Z(X)`, bundled as `NeemanSupportedWeakApproximability`.
No affine-base, excision or recollement theorem is assumed beyond the explicit
input `J`. -/
theorem neemanSupported_of_qcqs (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (Z : TopologicalSpace.Closeds X)
    (hcZ : IsCompactClosedComplement Z) :
    NeemanSupportedWeakApproximability X Z := by
  have h : NeemanSetProperty (X := X) (Z : Set X) :=
    supported_of_qcqs (toSetInductionData J) X (Z : Set X) Z.isClosed hcZ
  exact h Z.isClosed

end RelativeFM.SchemeNeemanFiniteCoverAssemblyM5
