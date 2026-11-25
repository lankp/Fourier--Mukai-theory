/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.SchemeNeemanFiniteCoverAssembly
import FourierMukai.Scheme.SchemeSupportedTwoOpen

/-!
# Supported excision for the all-sheaves `D_qc` model

This module supplies the categorical part of supported excision and isolates
its geometric content. If `Z` is closed in `X` and `Z ⊆ U` for an open `U`,
extension by zero gives an equivalence

`D_qc,Z(U) ≌ D_qc,Z(X)`.

The geometric input `StacksSupportedExcisionInput` is the translation of
Stacks **08DF**, parts (1) and (2), to the repository's cohomological-support
model. The AxiomMath/Stacks source is
`Topology/Sheaves/Cohomology/SupportedComplexes/PushforwardAndRestriction.lean`:
part (1) makes a supported complex isomorphic to the derived pushforward of
its restriction, and part (2) identifies extension by zero with that derived
pushforward. Restriction and extension by zero preserve quasicoherence here
because quasicoherence is local and the second covering open is `X ∖ Z`, on
which the cohomology sheaves vanish. The field `homology_isZero_iff` records
the resulting cohomological exactness, not weak approximability itself.

Thus the results in this file rest on Stacks **08DF** (with the local
quasicoherence statement **01BD**, already proved in this repository). No
Stacks declaration is imported: on Lean 4.33.1 the dependency is an explicit
input proposition. That proposition is not the supported Neeman conclusion;
it merely supplies a triangulated equivalence and its cohomology statement.

The same datum is also the correct left-endpoint equivalence for open/closed
recollement: in a cover `X = U ∪ V`, the closed complement of `U` is contained
in `V`, so excision compares the supported category on `V` with the closed
endpoint on `X`. It does not use unsupported approximation data on `U ∩ V`.
-/

@[expose] public section

namespace RelativeFM.SchemeSupportedExcisionM2

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry Set
open RelativeWeakApprox
open RelativeFM.SchemeWeakApproxStatementM1
open RelativeFM.SchemeNeemanFiniteCoverAssemblyM5

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The exact geometric content of Stacks 08DF in the repository's supported
`D_qc` model. The functor goes from the open to the ambient scheme, as does
extension by zero. Its chosen quasi-inverse is restriction. No approximation
data or compact generation occurs in this structure. -/
structure SupportedExcisionDatum {X : Scheme.{u}} (U : X.Opens)
    (Z : TopologicalSpace.Closeds X) where
  /-- Extension by zero on supported quasicoherent-cohomology categories,
  together with its restriction quasi-inverse. -/
  equivalence : DqcSupported U (openClosedSupport U Z) ≌ DqcSupported X Z
  /-- Shift compatibility of the derived functor. -/
  commShift : equivalence.functor.CommShift ℤ
  /-- Exactness on distinguished triangles. -/
  isTriangulated : letI := commShift; equivalence.functor.IsTriangulated
  /-- Additivity of the derived functor. -/
  additive : equivalence.functor.Additive
  /-- The chosen quasi-inverse (restriction) detects zero cohomology on these
  supported objects. This implies compatibility with both standard
  `t`-structures; it is not an additional assumption about approximation. -/
  homology_isZero_iff : ∀ (Y : DqcSupported X Z) (i : ℤ),
    IsZero (cohomologySheaf (equivalence.functor.inv.obj Y).obj i) ↔
      IsZero (cohomologySheaf Y.obj i)

/-- The Stacks-08DF geometric input, universally quantified over precisely the
situation used by supported excision. `Nonempty` hides no propositional gap:
the existential contains the actual functor, its equivalence and exactness
data, and its cohomology statement. -/
structure StacksSupportedExcisionInput : Prop where
  /-- AxiomMath/Stacks, Tag **08DF**, translated to `DqcSupported`. -/
  tag_08DF : ∀ {X : Scheme.{u}} (U : X.Opens) (Z : TopologicalSpace.Closeds X),
    (Z : Set X) ⊆ (U : Set X) → Nonempty (SupportedExcisionDatum U Z)

/-- A Stacks-08DF excision equivalence transports the restricted standard
`t`-structure to the restricted standard `t`-structure. -/
theorem transportTStructure_eq_dqcSupportedStandard {X : Scheme.{u}} {U : X.Opens}
    {Z : TopologicalSpace.Closeds X} (E : SupportedExcisionDatum U Z) :
    letI : E.equivalence.functor.IsEquivalence := inferInstance
    letI : E.equivalence.functor.CommShift ℤ := E.commShift
    letI : E.equivalence.functor.IsTriangulated := E.isTriangulated
    transportTStructure E.equivalence.functor
      (dqcSupportedStandardTStructure U (openClosedSupport U Z)) =
        dqcSupportedStandardTStructure X Z := by
  letI : E.equivalence.functor.IsEquivalence := inferInstance
  letI : E.equivalence.functor.CommShift ℤ := E.commShift
  letI : E.equivalence.functor.IsTriangulated := E.isTriangulated
  apply RelativeWeakApprox.TStructure.ext_le_zero
  ext Y
  rw [transportTStructure_le]
  rw [dqcSupportedStandardTStructure_le, dqcSupportedStandardTStructure_le]
  rw [TStructure.le_iff_isLE, TStructure.le_iff_isLE]
  change DerivedCategory.IsLE (E.equivalence.functor.inv.obj Y).obj 0 ↔
    DerivedCategory.IsLE Y.obj 0
  rw [DerivedCategory.isLE_iff, DerivedCategory.isLE_iff]
  constructor <;> intro h i hi
  · exact (E.homology_isZero_iff Y i).mp (h i hi)
  · exact (E.homology_isZero_iff Y i).mpr (h i hi)

/-- Transport zero-detection supported Neeman data across a Stacks-08DF
excision equivalence. The output retains the restricted standard
`t`-structure, not merely an arbitrary transported `t`-structure. -/
theorem neemanSupportedWeakApproximability_of_excisionDatum {X : Scheme.{u}}
    {U : X.Opens} {Z : TopologicalSpace.Closeds X}
    (E : SupportedExcisionDatum U Z)
    (h : NeemanSupportedWeakApproximability U (openClosedSupport U Z)) :
    NeemanSupportedWeakApproximability X Z := by
  letI : E.equivalence.functor.IsEquivalence := inferInstance
  letI : E.equivalence.functor.CommShift ℤ := E.commShift
  letI : E.equivalence.functor.IsTriangulated := E.isTriangulated
  letI : E.equivalence.functor.Additive := E.additive
  obtain ⟨W, hW⟩ := h
  refine ⟨⟨transportPaperWeakApproximationData E.equivalence.functor W, ?_⟩⟩
  rw [transportPaperWeakApproximationData_t, hW]
  exact transportTStructure_eq_dqcSupportedStandard E

/-- The exact `excision` field required by
`NeemanSupportedCoverInput`, discharged from Stacks 08DF. -/
theorem neemanSupportedWeakApproximability_of_stacksExcision
    (S : StacksSupportedExcisionInput.{u}) {X : Scheme.{u}} (U : X.Opens)
    (Z : TopologicalSpace.Closeds X) (hsub : (Z : Set X) ⊆ (U : Set X))
    (h : NeemanSupportedWeakApproximability U (openClosedSupport U Z)) :
    NeemanSupportedWeakApproximability X Z := by
  obtain ⟨E⟩ := S.tag_08DF U Z hsub
  exact neemanSupportedWeakApproximability_of_excisionDatum E h

/-- If an open immersion and `V` cover `X`, the closed complement of the
image is contained in `V`.  This is the set-theoretic side condition for
excision at the closed endpoint of open/closed recollement. -/
theorem compl_opensRange_subset_of_sup_eq_top {X : Scheme.{u}} {Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (V : X.Opens)
    (hcover : j.opensRange ⊔ V = ⊤) :
    ((j.opensRange : X.Opens) : Set X)ᶜ ⊆ (V : Set X) := by
  intro x hx
  have hxUV : x ∈ ((j.opensRange ⊔ V : X.Opens) : Set X) := by
    rw [hcover]
    exact Set.mem_univ x
  rw [Opens.coe_sup] at hxUV
  rcases hxUV with hxU | hxV
  · exact (hx hxU).elim
  · exact hxV

/-- The closed complement used by `SchemeOpenClosed` is supported on the second
open of a cover. -/
theorem SchemeOpenClosed.closedComplement_subset {g : SchemeOpenClosed.{u}}
    (V : g.X.Opens) (hcover : g.j.opensRange ⊔ V = ⊤) :
    (g.Z : Set g.X) ⊆ (V : Set g.X) := by
  rw [g.Z_eq]
  exact compl_opensRange_subset_of_sup_eq_top g.j V hcover

/-- Stacks 08DF supplies the open/closed left-endpoint excision equivalence.
The source is supported on the restriction of the closed complement to `V`;
it is not the unsupported category `Dqc V`. -/
theorem stacksExcisionDatum_closedComplement
    (S : StacksSupportedExcisionInput.{u}) {g : SchemeOpenClosed.{u}}
    (V : g.X.Opens) (hcover : g.j.opensRange ⊔ V = ⊤) :
    Nonempty (SupportedExcisionDatum V
      (SchemeSupportedTwoOpenM3.closedComplement g)) :=
  S.tag_08DF V _ (SchemeOpenClosed.closedComplement_subset V hcover)

/-- The three inputs to finite-cover induction other than supported excision.
Separating them makes it unambiguous that Stacks 08DF discharges no affine,
transport or open/closed-gluing statement. -/
structure NeemanSupportedCoverInputWithoutExcision : Prop where
  /-- Affine supported Neeman base case. -/
  of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X]
    (Z : TopologicalSpace.Closeds X),
    IsCompactClosedComplement Z → NeemanSupportedWeakApproximability X Z
  /-- Transport of supported weak approximability along a scheme isomorphism. -/
  of_iso : ∀ {X Y : Scheme.{u}} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds Y),
    NeemanSupportedWeakApproximability X (isoPreimageClosed e Z) →
    NeemanSupportedWeakApproximability Y Z
  /-- Zero-detection open/closed gluing. -/
  open_closed_glue : ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (V : X.Opens) (Z : TopologicalSpace.Closeds X),
    IsCompactClosedComplement Z → IsCompactOpen V →
    NeemanSupportedWeakApproximability X (closedDiff V Z) →
    NeemanSupportedWeakApproximability V (openClosedSupport V Z) →
    NeemanSupportedWeakApproximability X Z

/-- Add the Stacks-08DF excision field to the other three finite-cover
inputs. -/
theorem NeemanSupportedCoverInputWithoutExcision.toCoverInput
    (J : NeemanSupportedCoverInputWithoutExcision.{u})
    (S : StacksSupportedExcisionInput.{u}) : NeemanSupportedCoverInput.{u} where
  of_isAffine := J.of_isAffine
  of_iso := J.of_iso
  excision := fun U Z hsub h ↦
    neemanSupportedWeakApproximability_of_stacksExcision S U Z hsub h
  open_closed_glue := J.open_closed_glue

/-- Neeman's supported qcqs conclusion with the excision input explicitly
supplied by Stacks 08DF. The affine base, isomorphism transport and
open/closed gluing remain exactly the fields of `J`. -/
theorem neemanSupported_of_qcqs_with_stacksExcision
    (J : NeemanSupportedCoverInputWithoutExcision.{u})
    (S : StacksSupportedExcisionInput.{u})
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Z : TopologicalSpace.Closeds X) (hcZ : IsCompactClosedComplement Z) :
    NeemanSupportedWeakApproximability X Z :=
  SchemeNeemanFiniteCoverAssemblyM5.neemanSupported_of_qcqs
    (J.toCoverInput S) X Z hcZ

end
end RelativeFM.SchemeSupportedExcisionM2

#print axioms RelativeFM.SchemeSupportedExcisionM2.transportTStructure_eq_dqcSupportedStandard
#print axioms RelativeFM.SchemeSupportedExcisionM2.neemanSupportedWeakApproximability_of_excisionDatum
#print axioms RelativeFM.SchemeSupportedExcisionM2.neemanSupportedWeakApproximability_of_stacksExcision
#print axioms RelativeFM.SchemeSupportedExcisionM2.NeemanSupportedCoverInputWithoutExcision.toCoverInput
#print axioms RelativeFM.SchemeSupportedExcisionM2.neemanSupported_of_qcqs_with_stacksExcision
#print axioms RelativeFM.SchemeSupportedExcisionM2.compl_opensRange_subset_of_sup_eq_top
#print axioms RelativeFM.SchemeSupportedExcisionM2.SchemeOpenClosed.closedComplement_subset
#print axioms RelativeFM.SchemeSupportedExcisionM2.stacksExcisionDatum_closedComplement
