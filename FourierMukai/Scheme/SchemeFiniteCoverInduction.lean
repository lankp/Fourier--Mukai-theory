/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Finite-affine-cover induction for qcqs schemes

This file isolates the purely topological/schematic part of the finite-cover
step in Neeman's Theorem 3.2(iv).  It is deliberately independent of a choice
of derived-category model.

There are two inductions.  On a separated scheme, intersections of affine
opens are affine, so one can induct on a finite affine open cover directly.
On a general quasi-compact quasi-separated scheme, the intersection arising
when one adds an affine open is merely quasi-compact.  It is, however, an open
subscheme of an affine scheme, hence quasi-affine and separated, so the first
induction applies to it.  Thus no separatedness hypothesis detrimental to the
final qcqs statement is introduced, and no intersection of affine opens in a
non-separated scheme is asserted to be affine.

The predicate `P` is intended to be instantiated by the repository's
zero-detection scheme weak-approximability property.  The fields below are
precisely the affine base, invariance under scheme isomorphism, and the local
form of the two-open gluing rule.  The latter glues `U` and `V` over `U ⊆ finsets`.
-/

@[expose] public section

namespace RelativeFM.SchemeFiniteCoverInductionM5

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

/-- The scheme-theoretic inputs needed for finite-affine-cover induction.
`P` is expected to be `NeemanWeakApproximability` after the derived-category
statement and two-open gluing theorem have been supplied.

The gluing field is the restriction of the usual two-open rule to the open
subscheme `U ⊔ V`; this local form avoids repeatedly changing the ambient
scheme in the induction. -/


structure OpenCoverInductionData (P : Scheme.{u} → Prop) : Prop where
  /-- The affine base case. -/
  of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X], P X
  /-- Invariance under isomorphism of schemes. -/
  of_iso : ∀ {X Y : Scheme.{u}}, (X ≅ Y) → P X → P Y
  /-- Two-open gluing, stated locally for an arbitrary union of opens. -/
  glue_openUnion : ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X] (U V : X.Opens),
    IsCompact (U : Set X) → IsCompact (V : Set X) →
    P U → P V → P ((U ⊓ V : X.Opens) : Scheme.{u}) → P ((U ⊔ V : X.Opens) : Scheme.{u})

variable {P : Scheme.{u} → Prop}

/-- Build the local-open gluing input from the more familiar version in which
`U` and `V` cover the ambient scheme.  All the isomorphisms below are the
canonical isomorphisms between an open immersion and its range. -/
theorem of_twoOpenGluing
    (of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X], P X)
    (of_iso : ∀ {X Y : Scheme.{u}}, (X ≅ Y) → P X → P Y)
    (glue_cover : ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X] (U V : X.Opens), U ⊔ V = ⊤ →
      IsCompact (U : Set X) → IsCompact (V : Set X) →
      P U → P V → P ((U ⊓ V : X.Opens) : Scheme.{u}) → P X) :
    OpenCoverInductionData P where
  of_isAffine := of_isAffine
  of_iso := of_iso
  glue_openUnion := by
    intro X _ U V hcU hcV hU hV hUV
    let Y : X.Opens := U ⊔ V
    let _ : QuasiSeparatedSpace (Y : Scheme.{u}) := Y.isOpenEmbedding.quasiSeparatedSpace
    let fU : (U : Scheme.{u}) ⟶ (Y : Scheme.{u}) := X.homOfLE le_sup_left
    let fV : (V : Scheme.{u}) ⟶ (Y : Scheme.{u}) := X.homOfLE le_sup_right
    let fUV : ((U ⊓ V : X.Opens) : Scheme.{u}) ⟶ (Y : Scheme.{u}) :=
      X.homOfLE (inf_le_left.trans le_sup_left)
    have hcover : fU.opensRange ⊔ fV.opensRange = ⊤ := by
      dsimp [fU, fV, Y]
      rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE,
        ← Scheme.Hom.preimage_sup]
      exact (U ⊔ V).ι_preimage_self
    have hcUr : IsCompact (fU.opensRange : Set (Y : Scheme.{u})) := by
      apply isCompact_iff_compactSpace.mpr
      exact @Homeomorph.compactSpace _ _ _ _ (isCompact_iff_compactSpace.mp hcU)
        fU.isOpenEmbedding.isEmbedding.toHomeomorph
    have hcVr : IsCompact (fV.opensRange : Set (Y : Scheme.{u})) := by
      apply isCompact_iff_compactSpace.mpr
      exact @Homeomorph.compactSpace _ _ _ _ (isCompact_iff_compactSpace.mp hcV)
        fV.isOpenEmbedding.isEmbedding.toHomeomorph
    have hUVrange : fUV.opensRange = fU.opensRange ⊓ fV.opensRange := by
      dsimp [fUV, fU, fV, Y]
      rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE,
        Scheme.opensRange_homOfLE, ← Scheme.Hom.preimage_inf]
    have hUr : P fU.opensRange := of_iso fU.isoOpensRange hU
    have hVr : P fV.opensRange := of_iso fV.isoOpensRange hV
    have hUVr : P ((fU.opensRange ⊓ fV.opensRange : (Y : Scheme.{u}).Opens) : Scheme.{u}) := by
      rw [← hUVrange]
      exact of_iso fUV.isoOpensRange hUV
    exact glue_cover fU.opensRange fV.opensRange hcover hcUr hcVr hUr hVr hUVr

variable {P : Scheme.{u} → Prop} (I : OpenCoverInductionData P)

include I

/-- An affine open has the affine base property. -/
lemma of_isAffineOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) : P U := by
  let _ : IsAffine U := hU
  exact I.of_isAffine U

/-- The empty open is covered by the affine base case. -/
lemma of_bot (X : Scheme.{u}) : P ((⊥ : X.Opens) : Scheme.{u}) :=
  of_isAffineOpen I (isAffineOpen_bot X)

/-- Passing from the top open back to the ambient scheme. -/
lemma of_top {X : Scheme.{u}} (h : P ((⊤ : X.Opens) : Scheme.{u})) : P X :=
  I.of_iso X.topIso h

omit I in
/-- Compactness of a finite union of affine opens. -/
lemma isCompact_finsetSup {X : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    IsCompact ((s.sup U : X.Opens) : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sup_insert]
      exact (hU a).isCompact.union ih

/-- The separated finite-cover induction.  The induction hypothesis is
quantified over the affine family because the intersection step replaces
`U i` by `U i ⊓ U a`. -/
lemma separated_finsetSup {X : Scheme.{u}} [X.IsSeparated]
    {ι : Type*} (s : Finset ι) :
    ∀ (U : ι → X.Opens), (∀ i, IsAffineOpen (U i)) → P (s.sup U : X.Opens) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro U hU
      simpa using of_bot I X
  | @insert a s ha ih =>
      intro U hU
      have hW : P (s.sup U : X.Opens) := ih U hU
      have hA : P (U a) := of_isAffineOpen I (hU a)
      have hinter : P (s.sup U ⊓ U a : X.Opens) := by
        rw [Finset.sup_inf_distrib_right]
        exact ih (fun i ↦ U i ⊓ U a) (fun i ↦ (hU i).inf (hU a))
      simpa [Finset.sup_insert, sup_comm] using I.glue_openUnion (s.sup U) (U a) (isCompact_finsetSup s U hU) (hU a).isCompact
        hW hA hinter

/-- A finite affine open cover, given as a finite supremum equal to `⊤`, proves
the property on a separated scheme. -/
lemma of_finsetSup_eq_top_of_isSeparated {X : Scheme.{u}} [X.IsSeparated]
    {ι : Type*} {s : Finset ι} {U : ι → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : s.sup U = ⊤) : P X := by
  apply of_top I
  rw [← hcover]
  exact separated_finsetSup I s U hU

/-- Every compact separated scheme has a finite affine open cover, and hence
satisfies the induction conclusion. -/
lemma of_compact_of_isSeparated (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated] : P X := by
  let 𝒰 := X.affineCover.finiteSubcover
  let U : 𝒰.I₀ → X.Opens := fun i ↦ (𝒰.f i).opensRange
  have hU : ∀ i, IsAffineOpen (U i) := fun i ↦ isAffineOpen_opensRange (𝒰.f i)
  have hsup : (Finset.univ.sup U) = ⨆ i, U i := by
    apply le_antisymm
    · exact Finset.sup_le (fun i _ ↦ le_iSup U i)
    · exact iSup_le (fun i ↦ Finset.le_sup (f := U) (Finset.mem_univ i))
  apply of_finsetSup_eq_top_of_isSeparated I hU
  rw [hsup]
  exact 𝒰.iSup_opensRange

/-- The general finite-cover induction.  No separatedness assumption is made
on `X`: the intersection at each step is quasi-affine because it is a compact
open of an affine open. -/
lemma quasiSeparated_finsetSup {X : Scheme.{u}} [QuasiSeparatedSpace X]
    {ι : Type*} (s : Finset ι) (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    P (s.sup U : X.Opens) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using of_bot I X
  | @insert a s ha ih =>
      have hW : P (s.sup U : X.Opens) := ih
      have hA : P (U a) := of_isAffineOpen I (hU a)
      have hcW : IsCompact ((s.sup U : X.Opens) : Set X) := isCompact_finsetSup s U hU
      have hcInter : IsCompact (((s.sup U ⊓ U a : X.Opens) : Set X)) := by
        simpa only [Opens.coe_inf] using
          QuasiSeparatedSpace.inter_isCompact ((s.sup U : X.Opens) : Set X) (U a : Set X)
            (s.sup U : X.Opens).isOpen hcW (U a).isOpen (hU a).isCompact
      let _ : CompactSpace ((s.sup U ⊓ U a : X.Opens) : Scheme.{u}) :=
        isCompact_iff_compactSpace.mp hcInter
      let _ : IsAffine ((U a : X.Opens) : Scheme.{u}) := hU a
      let _ : ((s.sup U ⊓ U a : X.Opens) : Scheme.{u}).IsQuasiAffine :=
        Scheme.IsQuasiAffine.of_isImmersion (X.homOfLE (inf_le_right :
          s.sup U ⊓ U a ≤ U a))
      have hinter : P (s.sup U ⊓ U a : X.Opens) := of_compact_of_isSeparated I _
      simpa [Finset.sup_insert, sup_comm] using I.glue_openUnion (s.sup U) (U a) (isCompact_finsetSup s U hU) (hU a).isCompact
        hW hA hinter

/-- A finite affine open cover proves the property on a quasi-separated
ambient scheme. -/
lemma of_finsetSup_eq_top_of_quasiSeparated {X : Scheme.{u}} [QuasiSeparatedSpace X]
    {ι : Type*} {s : Finset ι} {U : ι → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : s.sup U = ⊤) : P X := by
  apply of_top I
  rw [← hcover]
  exact quasiSeparated_finsetSup I s U hU

/-- **Finite-affine-cover induction for qcqs schemes.**  Instantiate `P` with
zero-detection weak approximability.  No compact-generation, eventual-vanishing
or recollement assertion is hidden in this theorem; those are exactly what is
needed to construct `OpenCoverInductionData` from the affine and two-open
Neeman steps. -/
theorem of_qcqs (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] : P X := by
  let 𝒰 := X.affineCover.finiteSubcover
  let U : 𝒰.I₀ → X.Opens := fun i ↦ (𝒰.f i).opensRange
  have hU : ∀ i, IsAffineOpen (U i) := fun i ↦ isAffineOpen_opensRange (𝒰.f i)
  have hsup : (Finset.univ.sup U) = ⨆ i, U i := by
    apply le_antisymm
    · exact Finset.sup_le (fun i _ ↦ le_iSup U i)
    · exact iSup_le (fun i ↦ Finset.le_sup (f := U) (Finset.mem_univ i))
  apply of_finsetSup_eq_top_of_quasiSeparated I hU
  rw [hsup]
  exact 𝒰.iSup_opensRange

omit I in
/-- The same qcqs induction with the two-open gluing hypothesis in its usual
ambient-cover form.  This is the intended interface to the scheme-level
weak-approximability gluing theorem. -/
theorem of_qcqs_of_twoOpenGluing (P : Scheme.{u} → Prop)
    (of_isAffine : ∀ (X : Scheme.{u}) [IsAffine X], P X)
    (of_iso : ∀ {X Y : Scheme.{u}}, (X ≅ Y) → P X → P Y)
    (glue_cover : ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X] (U V : X.Opens), U ⊔ V = ⊤ →
      IsCompact (U : Set X) → IsCompact (V : Set X) →
      P U → P V → P ((U ⊓ V : X.Opens) : Scheme.{u}) → P X)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] : P X :=
  of_qcqs (of_twoOpenGluing of_isAffine of_iso glue_cover) X

end RelativeFM.SchemeFiniteCoverInductionM5
