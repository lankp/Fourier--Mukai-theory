/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.LP26.Inputs
import Spaces.LP26.StandardTStructure
import Spaces.Statements.NonVacuity

/-!
# LP26 Lemma 5.9: `𝒯^-_c` of `D_{qc,S}(X)` is the pseudo-coherent part, over algebraic spaces

Lank–Pauwels, *Gluing weak approximability along recollements* (LP26), §5
(`sec:proof_of_results`), **Lemma 5.9** (`lem:characterize_T-_c`): for `X` a quasi-compact
quasi-separated algebraic space (satisfying standard W.A.), `S ⊆ |X|` closed with quasi-compact
complement and `𝒯 := D_{qc,S}(X)`, the category `𝒯^-_c` consists of the objects of `𝒯` that are
pseudo-coherent in `D(X)`; if `X` is Noetherian, `𝒯^-_c = D^-_{coh,S}(X)` and
`𝒯^b_c = D^b_{coh,S}(X)`.

## Main definitions and results

* `minusC t P` and `boundedC t P`: for a pretriangulated category with a `t`-structure `t` and a
  class `P` of objects (the compact ones), LP26's `𝒯^-_c` (`sec:prelim_t-structures_t_structures`:
  for every `n > 0` a distinguished triangle `D → E → F → D[1]` with `D` compact and
  `F ∈ 𝒯^{≤ -n}`) and `𝒯^b_c = 𝒯^b ∩ 𝒯^-_c` (`𝒯^b` is Mathlib's `TStructure.bounded`).
* `lemma_5_9`: for `E ∈ D_{qc,T}(X)` (the paper's `S` is `T` here, `S` being the base scheme),
  `E ∈ 𝒯^-_c` for the standard `t`-structure iff `E` is pseudo-coherent in `D(𝒪_X)`.
* `lemma_5_9_minus_noetherian`, `lemma_5_9_bounded_noetherian`: for `X` Noetherian,
  `E ∈ 𝒯^-_c` iff `E` is bounded above with coherent cohomology sheaves, and `E ∈ 𝒯^b_c` iff `E`
  is bounded with coherent cohomology sheaves; `lemma_5_9_minus_eq`, `lemma_5_9_bounded_eq` state
  the equalities `𝒯^-_c = D^-_{coh,T}(X)`, `𝒯^b_c = D^b_{coh,T}(X)` as properties of objects of
  `D(𝒪_X)`.
* `nonVacuity_lemma_5_9`, `nonVacuity_lemma_5_9_noetherian`: the hypotheses are satisfiable and
  `𝒯^-_c` is not empty.

## Proof

As in LP26.  If `E ∈ 𝒯^-_c` and `n > 0`, take `D → E → F → D[1]` with `D` compact and
`F ∈ 𝒯^{≤ -n}`: `D` is perfect (Stacks 0AED), hence pseudo-coherent (08G8); `F` is
`(1 - n)`-pseudo-coherent (`H^j(F) = 0` for `j ≥ 1 - n`); so `E` is `(1 - n)`-pseudo-coherent
(08FV (2)), and pseudo-coherent (08FU (2), with the monotonicity `isPseudoCoherentFrom_of_le`
proved here).  Conversely, if `E` is pseudo-coherent and `n > 0`, the open immersion with image
`|X| ∖ T` is quasi-compact (Stacks 073B (1), 03E4; the compactness of `|X| ∖ T` is the
hypothesis), so Stacks 08HP gives a perfect `P` supported on `T` and `α : P → E` which is an
isomorphism on `Hⁱ` for `i > 1 - n` and onto on `H^{1-n}`; `P ∈ D_qc` and is compact in `𝒯`
(0AED), and the cone of `α` in `𝒯` lies in `𝒯^{≤ -n}` by the long exact cohomology sequence
(Mathlib's `DerivedCategory.HomologySequence`, `isZero_homology_obj₃_of_epi_of_mono`).  For `X`
Noetherian, Stacks 08IK identifies the pseudo-coherent objects of `D_qc(X)` with `D^-_coh(X)`.

## Rendering, and how the statement differs from LP26's

* **The `t`-structure.**  LP26 computes `𝒯^-_c` for a `t`-structure in the preferred equivalence
  class; its hypothesis "`X` satisfies standard W.A." (Definition 5.3, `def:wa_spaces`) is used
  only to know that the standard `t`-structure lies in that class (Neeman, Facts 1.26(i)), so
  that `𝒯^-_c` may be computed for it (CHNS, Remark 4.1.5).  Here `𝒯^-_c` is computed for the
  standard `t`-structure `standardTStructure X T` (`Spaces/LP26/StandardTStructure.lean`), and
  the statement holds **without** the W.A. hypothesis.  What is not formalized: Definition 5.3
  (it needs the coproduct universe of `wave8/universe-bridge`) and the independence of `𝒯^-_c`
  from the representative of the preferred class, so the identification of this `𝒯^-_c` with the
  paper's under standard W.A. is a gap (it is the paper's first proof step, a citation).
* **Compact** is `IsCompactObject.{u}` in `𝒯 = D_{qc,T}(X)` (direct sums indexed by `Type u`,
  Stacks 07LS), as in `Spaces/LP26/HomVanishing.lean`; `𝒯^{≤ -n}` is
  `(standardTStructure X T).le (-n)`.  `𝒯^- = ⋃_{n ≥ 0} 𝒯^{≤ n}` is Mathlib's `t.minus`
  (`∃ n : ℤ`; the same, since `𝒯^{≤ n} ⊆ 𝒯^{≤ max n 0}`), and likewise `𝒯^+`, `𝒯^b`.
* **Pseudo-coherent** is AxiomMath's `RingedSite.IsPseudoCoherent` on the small étale ringed site
  (the repository's `Spaces.IsPseudoCoherent`, Stacks 08FT).  "Supported on `S`" is automatic:
  the objects of `𝒯` are supported on `T`.
* **Noetherian** is AxiomMath's `IsNoetherian` (Stacks 03EA).  `D^-_{coh,T}(X)` is
  `derivedCategoryBMinus (Spaces.coh X)` (bounded above, coherent and quasi-coherent cohomology,
  the body of `Spaces.DminusCoh`) supported on `T`, and `D^b_{coh,T}(X)` the same with
  `derivedCategoryBBounded`; they are written out because `Spaces.DminusCoh` is elaborated in the
  instance context of `Spaces/Categories.lean`, not AxiomMath's (`Spaces/Supported/Inputs.lean`).
* `X` quasi-separated is `IsAbsolutelyQuasiSeparated B S hS hZ X.1`, as in
  `Spaces/Supported/CompactGeneration.lean`; the two `Prop` instances making `D_qc(X)` and
  `D_{qc,T}(X)` triangulated are instance arguments, as there.

## Assumptions

The tagged AxiomMath inputs `Supported.Tag0AEDInput` (0AED) and, from `Spaces/LP26/Inputs.lean`,
`PerfectPseudoCoherentInput` (08G8), `Tag08FVTwoInput` (08FV (2)),
`PseudoCoherentFromOfIsLEInput`, `Tag08FU2Input` (08FU (2)), `PerfectQcohInput`, `Tag08HPInput`
(08HP), `Tag073BInput` (073B (1)), `OpenSubspaceQuasiCompactInput` (06RV, 03IR, 03E4) and, for
the Noetherian clauses, `Tag08IKInput` (08IK); nothing else.  Non-vacuity also uses the inputs of
`Supported.lemma_A_9` and `Supported.AffineQuasiSeparatedInput`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry AlgebraicGeometry.Space
open scoped ZeroObject

namespace RelativeFM.Spaces.LP26

universe u

section Definitions

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **`𝒯^-_c`** (LP26 §2, `sec:prelim_t-structures_t_structures`): for a `t`-structure `t` and a
class `P` of objects (the compact objects `𝒯^c`), the objects `E` such that for every `n > 0`
there is a distinguished triangle `D → E → F → D[1]` with `D ∈ P` and `F ∈ 𝒯^{≤ -n}`. -/
def minusC (t : TStructure C) (P : ObjectProperty C) : ObjectProperty C := fun E =>
  ∀ n : ℤ, 0 < n → ∃ (D F : C) (f : D ⟶ E) (g : E ⟶ F) (h : F ⟶ D⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C ∧ P D ∧ t.le (-n) F

/-- **`𝒯^b_c := 𝒯^b ∩ 𝒯^-_c`** (LP26 §2, `sec:prelim_t-structures_t_structures`), with `𝒯^b`
Mathlib's `TStructure.bounded` (`𝒯^+ ∩ 𝒯^-`). -/
def boundedC (t : TStructure C) (P : ObjectProperty C) : ObjectProperty C := fun E =>
  t.bounded E ∧ minusC t P E

end Definitions

section Homology

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

/-- In a distinguished triangle `K → L → M → K[1]` of `D(A)`, if `H^i(K) → H^i(L)` is onto and
`H^{i+1}(K) → H^{i+1}(L)` is one-to-one, then `H^i(M) = 0` (the long exact cohomology sequence,
Mathlib's `DerivedCategory.HomologySequence`). -/
theorem isZero_homology_obj₃_of_epi_of_mono (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang _) (i : ℤ)
    (h₁ : Epi ((DerivedCategory.homologyFunctor A i).map T.mor₁))
    (h₂ : Mono ((DerivedCategory.homologyFunctor A (i + 1)).map T.mor₁)) :
    IsZero ((DerivedCategory.homologyFunctor A i).obj T.obj₃) := by
  have hz := (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 h₁
  have hδ := (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1)).1 h₂
  have he := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1)).2 hδ
  rw [hz] at he
  exact IsZero.of_epi_zero ((DerivedCategory.homologyFunctor A i).obj T.obj₂) _

end Homology

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

open Supported

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Pseudo-coherence: monotonicity -/

/-- `a`-pseudo-coherence of a complex implies `b`-pseudo-coherence for `b ≥ a` (the same local
approximations; proved from the definition, Stacks 08FT). -/
theorem isPseudoCoherentComplexFrom_of_le {X : AlgebraicSpaces B S hS}
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) {a b : ℤ}
    (h : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentComplexFrom K a) (hab : a ≤ b) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentComplexFrom K b := by
  intro U
  obtain ⟨T, hT, hmem⟩ := h U
  refine ⟨T, hT, fun {V} g hg => ?_⟩
  obtain ⟨P, hP, α, hiso, hepi⟩ := hmem g hg
  refine ⟨P, hP, α, fun j hj => hiso j (lt_of_le_of_lt hab hj), ?_⟩
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact hepi
  · have := hiso b hlt
    infer_instance

/-- `a`-pseudo-coherence of an object of `D(𝒪_X)` implies `b`-pseudo-coherence for `b ≥ a`. -/
theorem isPseudoCoherentFrom_of_le {X : AlgebraicSpaces B S hS}
    {E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} {a b : ℤ}
    (h : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E a) (hab : a ≤ b) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E b := by
  obtain ⟨K, hK, he⟩ := h
  exact ⟨K, isPseudoCoherentComplexFrom_of_le K hK hab, he⟩

/-! ### The quasi-compact complement -/

/-- **The open immersion with image `|X| ∖ T` is quasi-compact** when `X` is quasi-separated and
`|X| ∖ T` is compact (LP26's appeal to Stacks 073B in the proof of Lemma 5.9): the open subspace
is quasi-compact (Stacks 06RV, 03IR, 03E4), and a morphism from a quasi-compact space into a
quasi-separated one is quasi-compact (073B (1)). -/
theorem isQuasiCompact_ι_compl (hqcs : OpenSubspaceQuasiCompactInput B S hS)
    (h073B : Tag073BInput B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) :
    IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι := by
  set G := (openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩
  have hrange : Set.range (pointsMap B S hS G.1.toFunctor G.1.ι) = Tᶜ := by
    rw [← openSubspacesOrderIso_apply B S hS X.1 X.2, OrderIso.apply_symm_apply]
  exact h073B hZ X.2 hqs (hqcs X.2 G.2 (hrange ▸ hTc)) G.1.ι

/-! ### Lemma 5.9 -/

variable (X : AlgebraicSpaces B S hS)

/-- The cohomology of a zero object of `D_{qc,T}(X)` vanishes. -/
theorem isZero_homology_of_isZero [(qcohDerived X).IsTriangulated] (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    {E : DqcZ X T} (hE : IsZero E) (j : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) j).obj E.obj.obj) :=
  (DerivedCategory.homologyFunctor _ j).map_isZero ((ιZ X T).map_isZero hE)

/-- `𝒯^-_c` for the standard `t`-structure of `D_{qc,T}(X)` and the compact objects. -/
abbrev standardMinusC [(qcohDerived X).IsTriangulated] (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)] :
    ObjectProperty (DqcZ X T) :=
  minusC (standardTStructure X T) (fun D => IsCompactObject.{u} D)

/-- `𝒯^b_c` for the standard `t`-structure of `D_{qc,T}(X)` and the compact objects. -/
abbrev standardBoundedC [(qcohDerived X).IsTriangulated] (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)] :
    ObjectProperty (DqcZ X T) :=
  boundedC (standardTStructure X T) (fun D => IsCompactObject.{u} D)

/-- A compact object of `D_{qc,T}(X)` lies in `𝒯^-_c` (the triangle `D → D → 0 → D[1]`). -/
theorem standardMinusC_of_isCompactObject [(qcohDerived X).IsTriangulated]
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (D : DqcZ X T) (hD : IsCompactObject.{u} D) : standardMinusC X T D := fun n _ =>
  ⟨D, 0, 𝟙 D, 0, 0, contractible_distinguished D, hD,
    (standardTStructure_le_iff X T 0 (-n)).2 fun j _ => isZero_homology_of_isZero X T
      (isZero_zero _) j⟩

/-- **Lemma 5.9** (`lem:characterize_T-_c`), first claim, over algebraic spaces: for `X` a
quasi-compact quasi-separated algebraic space, `T ⊆ |X|` closed with quasi-compact complement and
`𝒯 = D_{qc,T}(X)` with its standard `t`-structure, an object `E` of `𝒯` lies in `𝒯^-_c` iff it is
pseudo-coherent in `D(𝒪_X)`.  The paper's hypothesis "standard W.A." only places the standard
`t`-structure in the preferred class and is not needed (module docstring, "Rendering"). -/
theorem lemma_5_9 (h0AED : Tag0AEDInput B S hS) (h08G8 : PerfectPseudoCoherentInput B S hS)
    (h08FV : Tag08FVTwoInput B S hS) (hle : PseudoCoherentFromOfIsLEInput B S hS)
    (h08FU : Tag08FU2Input B S hS) (hpqc : PerfectQcohInput B S hS) (h08HP : Tag08HPInput B S hS)
    (h073B : Tag073BInput B S hS) (hqcs : OpenSubspaceQuasiCompactInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [(qcohDerived X).IsTriangulated]
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) (E : DqcZ X T) :
    standardMinusC X T E ↔ (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E.obj.obj := by
  constructor
  · intro hE
    refine (h08FU X _).2 fun m => ?_
    obtain ⟨D, F, f, g, k, hdist, hD, hF⟩ := hE (max 1 (1 - m)) (by omega)
    have hdist' := (ιZ X T).map_distinguished _ hdist
    have hDpc := (h08FU X _).1 (h08G8 X ((h0AED hZ X hqc hqs T hT hTc D).1 hD)) (1 - max 1 (1 - m))
    have hFle : F.obj.obj.IsLE (1 - max 1 (1 - m) - 1) := by
      rw [TStructure.le_iff_isLE, standardTStructure_isLE_iff] at hF
      convert hF using 2
      omega
    have hEpc := h08FV X (1 - max 1 (1 - m)) _ hdist' hDpc (hle X F.obj.obj _ hFle)
    exact isPseudoCoherentFrom_of_le hEpc (by omega)
  · intro hE n hn
    obtain ⟨r, hr⟩ := h08HP hZ X.1 X.2 hqc hqs T hT
      (isQuasiCompact_ι_compl hqcs h073B hZ X hqs T hT hTc)
    obtain ⟨P, hPperf, hPsupp, α, hiso, hepi⟩ :=
      hr E.obj (1 - n) ((h08FU X _).1 hE _) fun i _ => E.property i
    let P' : DqcZ X T := ⟨⟨P, hpqc X P hPperf⟩, hPsupp⟩
    let α' : P' ⟶ E := (ιZ X T).preimage α
    obtain ⟨F, g, k, hdist⟩ := distinguished_cocone_triangle α'
    refine ⟨P', F, α', g, k, hdist, (h0AED hZ X hqc hqs T hT hTc P').2 hPperf, ?_⟩
    have hdist' := (ιZ X T).map_distinguished _ hdist
    have hmor : ((ιZ X T).mapTriangle.obj (Triangle.mk α' g k)).mor₁ = α :=
      (ιZ X T).map_preimage (X := P') (Y := E) α
    rw [standardTStructure_le_iff]
    intro j hj
    refine isZero_homology_obj₃_of_epi_of_mono _ hdist' j ?_ ?_
    · rw [hmor]
      rcases eq_or_lt_of_le (show 1 - n ≤ j by omega) with rfl | hlt
      · exact hepi
      · have := hiso j hlt
        infer_instance
    · rw [hmor]
      have := hiso (j + 1) (by omega)
      infer_instance

/-! ### The Noetherian clauses -/

/-- `E ∈ 𝒯^+` for the standard `t`-structure of `D_{qc,T}(X)` iff `E` is bounded below in
`D(𝒪_X)`. -/
theorem standardTStructure_plus_iff [(qcohDerived X).IsTriangulated] (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)] (E : DqcZ X T) :
    (standardTStructure X T).plus E ↔ DerivedCategoryB.IsBoundedBelow E.obj.obj :=
  exists_congr fun n => by rw [standardTStructure_isGE_iff, DerivedCategory.isGE_iff]

/-- `E ∈ 𝒯^-` for the standard `t`-structure of `D_{qc,T}(X)` iff `E` is bounded above in
`D(𝒪_X)`. -/
theorem standardTStructure_minus_iff [(qcohDerived X).IsTriangulated] (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)] (E : DqcZ X T) :
    (standardTStructure X T).minus E ↔ DerivedCategoryB.IsBoundedAbove E.obj.obj :=
  exists_congr fun n => by rw [standardTStructure_isLE_iff, DerivedCategory.isLE_iff]

/-- **Lemma 5.9** (`lem:characterize_T-_c`), second claim, `? = -`: for `X` a Noetherian algebraic
space and `T ⊆ |X|` closed with quasi-compact complement, an object `E` of `𝒯 = D_{qc,T}(X)` lies
in `𝒯^-_c` iff it is bounded above with coherent cohomology sheaves, i.e. `E ∈ D^-_{coh,T}(X)`
(from `lemma_5_9` and Stacks 08IK). -/
theorem lemma_5_9_minus_noetherian (h0AED : Tag0AEDInput B S hS)
    (h08G8 : PerfectPseudoCoherentInput B S hS) (h08FV : Tag08FVTwoInput B S hS)
    (hle : PseudoCoherentFromOfIsLEInput B S hS) (h08FU : Tag08FU2Input B S hS)
    (hpqc : PerfectQcohInput B S hS) (h08HP : Tag08HPInput B S hS) (h073B : Tag073BInput B S hS)
    (hqcs : OpenSubspaceQuasiCompactInput B S hS) (h08IK : Tag08IKInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [(qcohDerived X).IsTriangulated]
    (hN : IsNoetherian B S hS hZ X.1) (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) (E : DqcZ X T) :
    standardMinusC X T E ↔
      DerivedCategoryB.IsBoundedAbove E.obj.obj ∧
        ∀ i : ℤ, SheafOfModules.IsCoherentOnSite
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E.obj.obj) :=
  (lemma_5_9 X h0AED h08G8 h08FV hle h08FU hpqc h08HP h073B hqcs hZ hN.1 hN.2.1 T hT hTc E).trans
    (h08IK X.1 X.2 hZ hN E.obj.obj E.obj.property)

/-- **Lemma 5.9** (`lem:characterize_T-_c`), second claim, `? = b`: for `X` Noetherian, an object
`E` of `𝒯 = D_{qc,T}(X)` lies in `𝒯^b_c = 𝒯^b ∩ 𝒯^-_c` iff it is bounded with coherent cohomology
sheaves, i.e. `E ∈ D^b_{coh,T}(X)`. -/
theorem lemma_5_9_bounded_noetherian (h0AED : Tag0AEDInput B S hS)
    (h08G8 : PerfectPseudoCoherentInput B S hS) (h08FV : Tag08FVTwoInput B S hS)
    (hle : PseudoCoherentFromOfIsLEInput B S hS) (h08FU : Tag08FU2Input B S hS)
    (hpqc : PerfectQcohInput B S hS) (h08HP : Tag08HPInput B S hS) (h073B : Tag073BInput B S hS)
    (hqcs : OpenSubspaceQuasiCompactInput B S hS) (h08IK : Tag08IKInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [(qcohDerived X).IsTriangulated]
    (hN : IsNoetherian B S hS hZ X.1) (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) (E : DqcZ X T) :
    standardBoundedC X T E ↔
      DerivedCategoryB.IsBounded E.obj.obj ∧
        ∀ i : ℤ, SheafOfModules.IsCoherentOnSite
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E.obj.obj) := by
  have h := lemma_5_9_minus_noetherian X h0AED h08G8 h08FV hle h08FU hpqc h08HP h073B hqcs h08IK
    hZ hN T hT hTc E
  have hp := standardTStructure_plus_iff X T E
  have hm := standardTStructure_minus_iff X T E
  change ((standardTStructure X T).plus E ∧ (standardTStructure X T).minus E) ∧
    standardMinusC X T E ↔ _
  rw [hp, hm, h]
  exact ⟨fun ⟨⟨h₁, _⟩, h₂, h₃⟩ => ⟨⟨h₁, h₂⟩, h₃⟩, fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨⟨h₁, h₂⟩, h₂, h₃⟩⟩

/-- **Lemma 5.9** (`lem:characterize_T-_c`), `𝒯^-_c = D^-_{coh,T}(X)` as properties of objects of
`D(𝒪_X)`: for `X` Noetherian, `E ∈ D(𝒪_X)` is (the image of) an object of `𝒯^-_c` iff it is
bounded above with coherent (and quasi-coherent) cohomology sheaves (`derivedCategoryBMinus` of
`Spaces.coh X`, the body of `Spaces.DminusCoh X`) supported on `T`. -/
theorem lemma_5_9_minus_eq (h0AED : Tag0AEDInput B S hS)
    (h08G8 : PerfectPseudoCoherentInput B S hS) (h08FV : Tag08FVTwoInput B S hS)
    (hle : PseudoCoherentFromOfIsLEInput B S hS) (h08FU : Tag08FU2Input B S hS)
    (hpqc : PerfectQcohInput B S hS) (h08HP : Tag08HPInput B S hS) (h073B : Tag073BInput B S hS)
    (hqcs : OpenSubspaceQuasiCompactInput B S hS) (h08IK : Tag08IKInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [(qcohDerived X).IsTriangulated]
    (hN : IsNoetherian B S hS hZ X.1) (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (∃ E' : DqcZ X T, (ιZ X T).obj E' = E ∧ standardMinusC X T E') ↔
      DerivedCategoryB.derivedCategoryBMinus (coh X) E ∧
        CohomologySupportedOn B S hS X.1 X.2 T E := by
  have h := lemma_5_9_minus_noetherian X h0AED h08G8 h08FV hle h08FU hpqc h08HP h073B hqcs h08IK
    hZ hN T hT hTc
  constructor
  · rintro ⟨E', rfl, hE'⟩
    obtain ⟨hb, hc⟩ := (h E').1 hE'
    exact ⟨⟨hb, fun i => ⟨E'.obj.property i, hc i⟩⟩, E'.property⟩
  · rintro ⟨⟨hb, hc⟩, hs⟩
    exact ⟨⟨⟨E, fun i => (hc i).1⟩, hs⟩, rfl, (h _).2 ⟨hb, fun i => (hc i).2⟩⟩

/-- **Lemma 5.9** (`lem:characterize_T-_c`), `𝒯^b_c = D^b_{coh,T}(X)` as properties of objects of
`D(𝒪_X)`: for `X` Noetherian, `E ∈ D(𝒪_X)` is (the image of) an object of `𝒯^b_c` iff it is
bounded with coherent (and quasi-coherent) cohomology sheaves (`derivedCategoryBBounded` of
`Spaces.coh X`) supported on `T`. -/
theorem lemma_5_9_bounded_eq (h0AED : Tag0AEDInput B S hS)
    (h08G8 : PerfectPseudoCoherentInput B S hS) (h08FV : Tag08FVTwoInput B S hS)
    (hle : PseudoCoherentFromOfIsLEInput B S hS) (h08FU : Tag08FU2Input B S hS)
    (hpqc : PerfectQcohInput B S hS) (h08HP : Tag08HPInput B S hS) (h073B : Tag073BInput B S hS)
    (hqcs : OpenSubspaceQuasiCompactInput B S hS) (h08IK : Tag08IKInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [(qcohDerived X).IsTriangulated]
    (hN : IsNoetherian B S hS hZ X.1) (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (∃ E' : DqcZ X T, (ιZ X T).obj E' = E ∧ standardBoundedC X T E') ↔
      DerivedCategoryB.derivedCategoryBBounded (coh X) E ∧
        CohomologySupportedOn B S hS X.1 X.2 T E := by
  have h := lemma_5_9_bounded_noetherian X h0AED h08G8 h08FV hle h08FU hpqc h08HP h073B hqcs h08IK
    hZ hN T hT hTc
  constructor
  · rintro ⟨E', rfl, hE'⟩
    obtain ⟨hb, hc⟩ := (h E').1 hE'
    exact ⟨⟨hb, fun i => ⟨E'.obj.property i, hc i⟩⟩, E'.property⟩
  · rintro ⟨⟨hb, hc⟩, hs⟩
    exact ⟨⟨⟨E, fun i => (hc i).1⟩, hs⟩, rfl, (h _).2 ⟨hb, fun i => (hc i).2⟩⟩

/-! ### Non-vacuity -/

/-- **Non-vacuity of Lemma 5.9** (first claim): for every quasi-compact quasi-separated algebraic
space `X` (for instance `X = h_{T₀}` with `T₀` affine, `Supported.nonVacuity_affine_univ`) and
`T = |X|` (closed, with empty hence compact complement), `𝒯^-_c` contains the compact generator
`P` of `D_{qc,T}(X)` (Stacks 0AEC, 0AED), and `lemma_5_9` applies to it: `P` is pseudo-coherent.
The two instance arguments hold for every `X` (`nonVacuity_lemma_5_6_instances`). -/
theorem nonVacuity_lemma_5_9 (h0AEC : Tag0AECInput B S hS) (h0AED : Tag0AEDInput B S hS)
    (h08G8 : PerfectPseudoCoherentInput B S hS) (h08FV : Tag08FVTwoInput B S hS)
    (hle : PseudoCoherentFromOfIsLEInput B S hS) (h08FU : Tag08FU2Input B S hS)
    (hpqc : PerfectQcohInput B S hS) (h08HP : Tag08HPInput B S hS) (h073B : Tag073BInput B S hS)
    (hqcs : OpenSubspaceQuasiCompactInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [(qcohDerived X).IsTriangulated]
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 Set.univ)] :
    _root_.IsClosed (Set.univ : Set (points B S hS X.1)) ∧
      _root_.IsCompact (Set.univ : Set (points B S hS X.1))ᶜ ∧
      ∃ E : DqcZ X Set.univ, standardMinusC X Set.univ E ∧
        (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E.obj.obj := by
  have hcl : _root_.IsClosed (Set.univ : Set (points B S hS X.1)) := isClosed_univ
  have hco : _root_.IsCompact (Set.univ : Set (points B S hS X.1))ᶜ := by
    rw [Set.compl_univ]; exact isCompact_empty
  obtain ⟨P, -, hPc, -⟩ := lemma_A_9_generator h0AEC h0AED X hqc hZ hqs Set.univ hcl hco
  have hP := standardMinusC_of_isCompactObject X Set.univ P hPc
  exact ⟨hcl, hco, P, hP,
    (lemma_5_9 X h0AED h08G8 h08FV hle h08FU hpqc h08HP h073B hqcs hZ hqc hqs Set.univ hcl hco
      P).1 hP⟩

/-- **Non-vacuity of the Noetherian clauses of Lemma 5.9**: over an affine, locally Noetherian base
scheme `S` (for instance `S = Spec ℤ`), the base `S` is a Noetherian algebraic space
(`Statements.isNoetherianSpace_baseSpace`), and with `T = |S|`, `𝒯^-_c` contains the compact
generator `P` of `D_{qc,T}(S)`, which `lemma_5_9_minus_noetherian` places in `D^-_{coh,T}(S)`. -/
theorem nonVacuity_lemma_5_9_noetherian (hqsA : Statements.AffineQuasiSeparatedInput B S hS)
    (h0AEC : Tag0AECInput B S hS) (h0AED : Tag0AEDInput B S hS)
    (h08G8 : PerfectPseudoCoherentInput B S hS) (h08FV : Tag08FVTwoInput B S hS)
    (hle : PseudoCoherentFromOfIsLEInput B S hS) (h08FU : Tag08FU2Input B S hS)
    (hpqc : PerfectQcohInput B S hS) (h08HP : Tag08HPInput B S hS) (h073B : Tag073BInput B S hS)
    (hqcs : OpenSubspaceQuasiCompactInput B S hS) (h08IK : Tag08IKInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [IsAffine S] [IsLocallyNoetherian S]
    [(qcohDerived (baseSpace B S hS)).IsTriangulated]
    [ObjectProperty.IsTriangulated
      (CohomologySupportedOn B S hS (baseSpace B S hS).1 (baseSpace B S hS).2 Set.univ)] :
    IsNoetherian B S hS hZ (baseSpace B S hS).1 ∧
      ∃ E : DqcZ (baseSpace B S hS) Set.univ, standardMinusC (baseSpace B S hS) Set.univ E ∧
        DerivedCategoryB.IsBoundedAbove E.obj.obj ∧
        ∀ i : ℤ, SheafOfModules.IsCoherentOnSite
          ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (baseSpace B S hS).1 (baseSpace B S hS).2) i).obj
              E.obj.obj) := by
  have hN : IsNoetherian B S hS hZ (baseSpace B S hS).1 :=
    Statements.isNoetherianSpace_baseSpace B S hS hqsA hZ
  obtain ⟨hcl, hco, P, hP, -⟩ := nonVacuity_lemma_5_9 (baseSpace B S hS) h0AEC h0AED h08G8 h08FV
    hle h08FU hpqc h08HP h073B hqcs hZ hN.1 hN.2.1
  exact ⟨hN, P, hP, (lemma_5_9_minus_noetherian (baseSpace B S hS) h0AED h08G8 h08FV hle h08FU
    hpqc h08HP h073B hqcs h08IK hZ hN Set.univ hcl hco P).1 hP⟩

end RelativeFM.Spaces.LP26
