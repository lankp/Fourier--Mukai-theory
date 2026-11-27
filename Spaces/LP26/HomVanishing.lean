/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.LP26.Inputs
import Spaces.Supported.CompactGeneration

/-!
# LP26 Lemmas 5.5 and 5.6: `Hom(G, G[n]) = 0` for `n ≫ 0`, over algebraic spaces

Lank–Pauwels, *Gluing weak approximability along recollements* (LP26), §5
(`sec:proof_of_results`):

* **Lemma 5.5** (`lem:compact_ext_vanishing`): for `X` a quasi-compact quasi-separated algebraic
  space and `G` a compact object of `D_qc(X)`, there is `N` with `Hom(G, G[n]) = 0` for all
  `n > N` (`lemma_5_5`, and `lemma_5_5_dqc` with the morphisms taken in `D_qc(X)`).
* **Lemma 5.6** (`lem:perf_vanishing`): for `S ⊆ |X|` closed with quasi-compact complement and
  `G'` a compact generator of `D_{qc,S}(X)`, `Hom(G', G'[n]) = 0` for `n ≫ 0` (`lemma_5_6`, and
  `lemma_5_6_dqcZ` with the morphisms taken in `D_{qc,S}(X)`).  Only the compactness of `G'` is
  used (`lemma_5_6_of_isCompactObject`).

## Proof

LP26 deduces Lemma 5.5 from Stacks 09M8 (compact ⇒ perfect), 08J7, 08JJ, 0GFH and 0GFI.  Here
the argument is shorter and uses what AxiomMath has: `G` is perfect (09M8,
`Tag09M8Input`), hence bounded above, `G ∈ D^{≤ m}` (`PerfectBoundedAboveInput`); by half of
Stacks 09MB (1) (`Tag09MBInput`) there is `N₀` with `Hom(G, L) = 0` for every `L ∈ D_qc(X)` with
`L ∈ D^{≤ -N₀}`; and `G[n] ∈ D^{≤ m - n} ⊆ D^{≤ -N₀}` once `n ≥ m + N₀`.  Lemma 5.6 follows as in
LP26: a compact object of `D_{qc,S}(X)` is perfect (Stacks 0AED, `Supported.Tag0AEDInput`), hence
compact in `D_qc(X)` (09M8), and Lemma 5.5 applies.  LP26 cites GL26 Remark A.5 for this step;
0AED is the statement used here.

## Rendering

* `D_qc(X)` is AxiomMath's `QuasicoherentDerivedCategory` and `D_{qc,S}(X)` the category
  `Supported.DqcZ X S` of `Spaces/Supported/CompactGeneration.lean`; "compact" is
  `IsCompactObject.{u}` (direct sums indexed by `Type u`, Stacks 07LS), as there.
* The first forms (`lemma_5_5`, `lemma_5_6`) take the morphisms `G ⟶ G[n]` in `D(𝒪_X)`; since
  `D_qc(X)` and `D_{qc,S}(X)` are full triangulated subcategories, these are the morphisms of the
  paper, and `lemma_5_5_dqc`, `lemma_5_6_dqcZ` state it with the morphisms and the shift of the
  subcategory (whose triangulated structure comes from the two `Prop` instances of
  `Spaces/Supported/CompactGeneration.lean`).
* `X` quasi-separated is `IsAbsolutelyQuasiSeparated B S hS hZ X.1`, as in
  `Spaces/Supported/CompactGeneration.lean`.

## Assumptions

The tagged AxiomMath inputs `Tag09M8Input`, `PerfectBoundedAboveInput`, `Tag09MBInput`
(`Spaces/LP26/Inputs.lean`) and `Supported.Tag0AEDInput`; nothing else.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.LP26

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

open Supported

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Quasi-coherent cohomology is stable under shifts: `H^i(E[n]) ≅ H^{i+n}(E)`. -/
theorem qcohDerived_shift (X : AlgebraicSpaces B S hS)
    {E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (hE : qcohDerived X E) (n : ℤ) :
    qcohDerived X (E⟦n⟧) := fun i =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) 0).shiftIso n i (n + i)
      rfl).app E).symm (hE (n + i))

/-- **Lemma 5.5** (`lem:compact_ext_vanishing`), with the morphisms in `D(𝒪_X)`: for `X` a
quasi-compact quasi-separated algebraic space and `G` a compact object of `D_qc(X)`, there is an
integer `N` such that every morphism `G ⟶ G[n]` with `n > N` is zero.  From Stacks 09M8, the
boundedness of perfect objects and half of Stacks 09MB (1) (module docstring). -/
theorem lemma_5_5 (h09M8 : Tag09M8Input B S hS) (hbd : PerfectBoundedAboveInput B S hS)
    (h09MB : Tag09MBInput B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (G : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (hG : IsCompactObject.{u} G) :
    ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G.obj ⟶ G.obj⟦n⟧, f = 0 := by
  have hP := (h09M8 hZ X hqc hqs G).1 hG
  obtain ⟨m, hm⟩ := hbd hqc G.obj hP
  obtain ⟨N₀, hN₀⟩ := h09MB hZ X hqc hqs G hG
  refine ⟨m + N₀, fun n hn f => hN₀ _ (qcohDerived_shift X G.property n) ?_ f⟩
  have := DerivedCategory.TStructure.t.isLE_shift G.obj m n (m - n) (by omega)
  exact DerivedCategory.TStructure.t.isLE_of_le _ (m - n) (-N₀) (by omega)

/-- A morphism `G ⟶ G[n]` in a full triangulated subcategory vanishes as soon as the morphisms
`G ⟶ G[n]` of the ambient category do. -/
theorem eq_zero_of_ambient {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.Faithful] (G : C) (n : ℤ) (h : ∀ g : F.obj G ⟶ (F.obj G)⟦n⟧, g = 0) (f : G ⟶ G⟦n⟧) :
    f = 0 := by
  apply F.map_injective
  rw [Functor.map_zero, ← cancel_mono ((F.commShiftIso n).hom.app G), zero_comp]
  exact h _

/-- **Lemma 5.5** (`lem:compact_ext_vanishing`), with the morphisms and the shift of `D_qc(X)`:
for `X` a quasi-compact quasi-separated algebraic space and `G` a compact object of `D_qc(X)`,
`Hom_{D_qc(X)}(G, G[n]) = 0` for all `n > N`.  The triangulated structure of `D_qc(X)` is the
`Prop` instance of Stacks 06UQ (`Supported.isTriangulated_qcohDerived`). -/
theorem lemma_5_5_dqc (h09M8 : Tag09M8Input B S hS) (hbd : PerfectBoundedAboveInput B S hS)
    (h09MB : Tag09MBInput B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) [(qcohDerived X).IsTriangulated]
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (G : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (hG : IsCompactObject.{u} G) :
    ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G ⟶ G⟦n⟧, f = 0 := by
  obtain ⟨N, hN⟩ := lemma_5_5 h09M8 hbd h09MB hZ X hqc hqs G hG
  exact ⟨N, fun n hn f => eq_zero_of_ambient (qcohDerived X).ι G n (hN n hn) f⟩

/-- **Lemma 5.6** (`lem:perf_vanishing`), from compactness alone, with the morphisms in `D(𝒪_X)`:
for `X` quasi-compact quasi-separated, `T ⊆ |X|` closed with quasi-compact complement and `G'`
a compact object of `D_{qc,T}(X)`, there is `N` with `Hom(G', G'[n]) = 0` for all `n > N`.
From Stacks 0AED, 09M8 and Lemma 5.5. -/
theorem lemma_5_6_of_isCompactObject (h09M8 : Tag09M8Input B S hS)
    (hbd : PerfectBoundedAboveInput B S hS) (h09MB : Tag09MBInput B S hS)
    (h0AED : Tag0AEDInput B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (G' : DqcZ X T) (hG' : IsCompactObject.{u} G') :
    ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G'.obj.obj ⟶ G'.obj.obj⟦n⟧, f = 0 :=
  lemma_5_5 h09M8 hbd h09MB hZ X hqc hqs G'.obj
    ((h09M8 hZ X hqc hqs G'.obj).2 ((h0AED hZ X hqc hqs T hT hTc G').1 hG'))

/-- **Lemma 5.6** (`lem:perf_vanishing`), with the morphisms in `D(𝒪_X)`: for `X` a
quasi-compact quasi-separated algebraic space, `T ⊆ |X|` closed with quasi-compact complement and
`G'` a compact generator of `D_{qc,T}(X)` (compact, `IsCompactObject.{u}`, and generating,
`IsPaperGenerator`), `Hom(G', G'[n]) = 0` for `n ≫ 0`.  The generation hypothesis is LP26's and
is not used (`lemma_5_6_of_isCompactObject`). -/
theorem lemma_5_6 (h09M8 : Tag09M8Input B S hS)
    (hbd : PerfectBoundedAboveInput B S hS) (h09MB : Tag09MBInput B S hS)
    (h0AED : Tag0AEDInput B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) [(qcohDerived X).IsTriangulated]
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (G' : DqcZ X T) (hG' : IsCompactObject.{u} G')
    (_hgen : RelativeWeakApprox.IsPaperGenerator G') :
    ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G'.obj.obj ⟶ G'.obj.obj⟦n⟧, f = 0 :=
  lemma_5_6_of_isCompactObject h09M8 hbd h09MB h0AED hZ X hqc hqs T hT hTc G' hG'

/-- **Lemma 5.6** (`lem:perf_vanishing`), with the morphisms and the shift of `D_{qc,T}(X)`:
for `G'` a compact generator of `D_{qc,T}(X)`, `Hom_{D_{qc,T}(X)}(G', G'[n]) = 0` for `n ≫ 0`. -/
theorem lemma_5_6_dqcZ (h09M8 : Tag09M8Input B S hS)
    (hbd : PerfectBoundedAboveInput B S hS) (h09MB : Tag09MBInput B S hS)
    (h0AED : Tag0AEDInput B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) [(qcohDerived X).IsTriangulated]
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (G' : DqcZ X T) (hG' : IsCompactObject.{u} G')
    (hgen : RelativeWeakApprox.IsPaperGenerator G') :
    ∃ N : ℤ, ∀ n : ℤ, N < n → ∀ f : G' ⟶ G'⟦n⟧, f = 0 := by
  obtain ⟨N, hN⟩ := lemma_5_6 h09M8 hbd h09MB h0AED hZ X hqc hqs T hT hTc G' hG' hgen
  exact ⟨N, fun n hn f => eq_zero_of_ambient (ιZ X T) G' n (hN n hn) f⟩

end RelativeFM.Spaces.LP26
