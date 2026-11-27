/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.LP26.Recollement
import Spaces.LP26.HomVanishing
import Spaces.Stacks.Corollaries

/-!
# LP26 Definition 5.3 and Proposition 5.8 over algebraic spaces

Lank–Pauwels, *Gluing weak approximability along recollements* (LP26), §5:

* **Definition 5.3** (`def:wa_spaces`): a quasi-compact quasi-separated algebraic space `X`
  satisfies **W.A.** if `D_{qc,S}(X)` is weakly approximable for every closed `S ⊆ |X|` with
  quasi-compact complement, and **standard W.A.** if for every such `S` there are weak
  approximation data `(G, D^{≤ 0}_{qc,S}(X), A)` for the standard `t`-structure.
  `SatisfiesWA`, `SatisfiesStandardWA`; `satisfiesWA_of_satisfiesStandardWA` is the remark
  following the definition.
* **Proposition 5.8** (`prop:A8`), W.A. part: for an elementary distinguished square
  `(U ⊆ X, f : Y ⟶ X)` of quasi-compact quasi-separated algebraic spaces, if `U` and `Y` satisfy
  W.A., so does `X` (`proposition_5_8`).

## Proof (LP26's)

Fix `S`.  The open–closed recollement `D_{qc,|U| ∩ S}(U) → D_{qc,S}(X) → D_{qc,S ∩ T}(X)`,
`T = |X| ∖ |U|` (GL26 Lemma A.4, `lemma_A_4`).  The left term is weakly approximable because `U`
satisfies W.A. (`|U| ∖ (|U| ∩ S)` is quasi-compact, `CompactComplPreimageInput`); the right term
is equivalent to `D_{qc,f⁻¹(S ∩ T)}(Y)` (GL26 Lemma A.6, `lemma_A_6`), which is weakly
approximable because `Y` does, and weak approximability is invariant under triangulated
equivalences (`SumUniverse.satisfiesPaperWA_iff_of_equivalence`).  `D_{qc,S}(X)` has a compact
generator `G'` (Stacks 0AEC, 0AED) with `Hom(G', G'[n]) = 0` for `n ≫ 0` (LP26 Lemma 5.6,
`lemma_5_6_dqcZ`), so LP26 Theorem 1.1 (`Spaces.Stacks.theorem_1_1_univ`, for the coproduct
universe `u` of AxiomMath's `D(𝒪_X)`) gives that `D_{qc,S}(X)` is weakly approximable.

## Non-vacuity

`proposition_5_8_nonVacuity`: every hypothesis of `proposition_5_8` holds for the square
`(⊤ ⊆ X, ⊤.ι)` on the empty algebraic space `X` (the open subspace of `∅` in any
quasi-separated space), whose spaces satisfy W.A. because all their categories `D_{qc,T}` are zero
(`satisfiesWA_of_isEmpty`).  A non-empty space satisfying W.A. is the affine base case of LP26
Corollary 1.2, not yet available in this form.

## Rendering

* Weak approximability is `SumUniverse.SatisfiesPaperWA.{u}` (LP26 Definition 2.1 with compactness
  and coproducts for `Type u`-indexed direct sums, the sums of AxiomMath's model).
* An elementary distinguished square is AxiomMath's `IsElementaryDistinguishedSquare` (Stacks
  08GM): `U` is the open subspace `Uo` (`edsOpenSpace`), `Y` is `V` (`edsEtaleSpace`), `f` is
  `edsEtaleMap`.  "Of quasi-compact quasi-separated algebraic spaces" is the six hypotheses
  `hXqc … hVqs`.
* The instance arguments are the `Prop` instances that make the categories `D_{qc,S}` triangulated
  (as in `Spaces/LP26/Recollement.lean`).

## What is not proved: the standard W.A. part of Proposition 5.8

LP26 also proves "if `U` and `Y` satisfy standard W.A., so does `X`".  Its argument compares the
standard `t`-structure on `D_{qc,S}(X)` with the `t`-structure glued from the standard ones on the
outer terms, and uses that the glued `t`-structure is in the preferred equivalence class (via the
proof of LP26 Theorem 1.1 and Setup 4.4) and BNP Lemma 3.7 (weak approximation data exist for
every `t`-structure in the preferred class).  These are not available for the coproduct
universe `u` of `D(𝒪_X)` in the tree (`WeakApprox/WeakApproxBounds.lean` has them at the Hom
universe only, and the glued `t`-structure of a `RelativeWeakApprox.Recollement` is not
constructed as a `TStructure` there), so this part is left open; nothing is assumed about it.

## Assumptions

The tagged AxiomMath inputs of `lemma_A_4`, `lemma_A_6`, `lemma_5_6_dqcZ` and `Tag073BInput`,
`Tag0AECInput`, `Tag0AEDInput` (all named in the hypotheses); for non-vacuity also
`SupportEmptyInput`, `EDSTopInput`, `OpenSubspaceQuasiCompactInput`; nothing else.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Space RelativeWeakApprox

namespace RelativeFM.Spaces.LP26

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

open Supported

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Definition 5.3 -/

section Definition

variable (X : AlgebraicSpaces B S hS) [(qcohDerived X).IsTriangulated]
  [∀ T, ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]

/-- **Definition 5.3** (`def:wa_spaces`), W.A.: `D_{qc,T}(X)` is weakly approximable
(`SumUniverse.SatisfiesPaperWA.{u}`) for every closed `T ⊆ |X|` with quasi-compact complement.
LP26 defines it for `X` quasi-compact quasi-separated; the predicate makes sense for every `X`. -/
def SatisfiesWA : Prop :=
  ∀ T : Set (points B S hS X.1), IsClosed T → _root_.IsCompact Tᶜ →
    SumUniverse.SatisfiesPaperWA.{u} (DqcZ X T)

/-- **Definition 5.3** (`def:wa_spaces`), standard W.A.: for every closed `T ⊆ |X|` with
quasi-compact complement there are weak approximation data `(G, D^{≤ 0}_{qc,T}(X), A)` whose
`t`-structure is the standard one (`standardTStructure X T`). -/
def SatisfiesStandardWA : Prop :=
  ∀ T : Set (points B S hS X.1), IsClosed T → _root_.IsCompact Tᶜ →
    ∃ W : SumUniverse.PaperWeakApproximationData.{u} (DqcZ X T), W.t = standardTStructure X T

/-- **Remark after Definition 5.3**: standard W.A. implies W.A. -/
theorem satisfiesWA_of_satisfiesStandardWA (h : SatisfiesStandardWA X) : SatisfiesWA X :=
  fun T hT hTc => ⟨(h T hT hTc).choose⟩

end Definition

/-! ### Proposition 5.8 -/

section Proposition

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- **Proposition 5.8** (`prop:A8`), W.A. part, over algebraic spaces.  Let `(U ⊆ X, f : Y ⟶ X)`
be an elementary distinguished square (Stacks 08GM) of quasi-compact quasi-separated algebraic
spaces.  If `U` and `Y` satisfy W.A. (Definition 5.3), so does `X`.

The standard W.A. part of LP26's proposition is not included (module docstring). -/
theorem proposition_5_8 (h08FA : Tag08FAInput B S hS) (h08F4 : Tag08F4Input B S hS)
    (h0AFJ : Tag0AFJInput B S hS) (hpb : PullbackSupportInput B S hS)
    (hdisj : PullbackDisjointInput B S hS) (hres : EtaleRestrictionSupportInput B S hS)
    (hcounit : OpenImmersionCounitInput B S hS) (hperf : PerfectPullbackInput B S hS)
    (h08F3 : Tag08F3Input B S hS) (hsum : SupportedDirectSumsInput B S hS)
    (h0AEC : Tag0AECInput B S hS) (h0AED : Tag0AEDInput B S hS) (h079Q : Tag079QInput.{u})
    (h0A8G : Tag0A8GInput.{u}) (hRAC : RightAdjointCoproductsInput.{u})
    (hqcs : QuasiCompactSourceInput B S hS) (hcpt : CompactComplPreimageInput B S hS)
    (h08GGu : Tag08GGUnitInput B S hS) (h08GGc : Tag08GGCounitInput B S hS)
    (h073B : Tag073BInput B S hS) (h073B2 : Tag073BTwoInput B S hS)
    (h09M8 : Tag09M8Input B S hS) (hbd : PerfectBoundedAboveInput B S hS)
    (h09MB : Tag09MBInput B S hS)
    {X : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor X.1} {fV : V ⟶ X.1}
    (hsq : IsElementaryDistinguishedSquare B S hS X.2 Uo fV)
    [(qcohDerived X).IsTriangulated] [(qcohDerived (edsOpenSpace hsq)).IsTriangulated]
    [(qcohDerived (edsEtaleSpace hsq)).IsTriangulated]
    [∀ T, ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    [∀ T, ObjectProperty.IsTriangulated
      (CohomologySupportedOn B S hS (edsOpenSpace hsq).1 (edsOpenSpace hsq).2 T)]
    [∀ T, ObjectProperty.IsTriangulated
      (CohomologySupportedOn B S hS (edsEtaleSpace hsq).1 (edsEtaleSpace hsq).2 T)]
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hVqc : IsQuasiCompactSpace B S hS V) (hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V)
    (hU : SatisfiesWA (edsOpenSpace hsq)) (hY : SatisfiesWA (edsEtaleSpace hsq)) :
    SatisfiesWA X := by
  intro W hW hWc
  let j := edsOpenMap hsq
  have hj : IsOpenImmersion B S hS j.hom := hsq.isOpenSubspace.2
  have hjqc : IsQuasiCompact B S hS j.hom := h073B hZ X.2 hXqs hUqc j.hom
  let T := (Set.range (pointsMap B S hS (edsOpenSpace hsq).1 j.hom))ᶜ
  -- the recollement (GL26 Lemma A.4)
  have hR := lemma_A_4 h08FA h08F4 h0AFJ hpb hdisj hres hcounit hperf h08F3 hsum h0AEC h0AED
    h079Q h0A8G hRAC hqcs hcpt hZ hXqc hXqs j hj hjqc W hW hWc
  let R := hR.choose
  -- the left term
  have hUW : SumUniverse.SatisfiesPaperWA.{u}
      (DqcZ (edsOpenSpace hsq) (pointsMap B S hS _ j.hom ⁻¹' W)) :=
    hU _ (hW.preimage (continuous_pointsMap B S hS j.hom)) (hcpt hZ j hUqc hXqs W hW hWc)
  -- the right term, through the equivalence of GL26 Lemma A.6
  have hUqc' : IsQuasiCompactSpace B S hS (edsOpenSpace hsq).1 := hUqc
  have hT : IsClosed T :=
    (isOpenMap_pointsMap_of_isOpenImmersion B S hS j.hom hj).isOpen_range.isClosed_compl
  have hWT : IsClosed (W ∩ T) := hW.inter hT
  have hWTc : _root_.IsCompact (W ∩ T)ᶜ := by
    rw [Set.compl_inter, compl_compl]
    have := compactSpace_points_of_isQuasiCompactSpace B S hS (edsOpenSpace hsq).2 hUqc'
    exact hWc.union (isCompact_range (continuous_pointsMap B S hS j.hom))
  have hVW : SumUniverse.SatisfiesPaperWA.{u} (DqcZ (edsEtaleSpace hsq) (edsW hsq (W ∩ T))) :=
    hY _ (hWT.preimage (continuous_pointsMap B S hS (edsEtaleMap hsq).hom))
      (hcpt hZ (edsEtaleMap hsq) hVqc hXqs (W ∩ T) hWT hWTc)
  have hA6 := lemma_A_6_aux h08FA h08F4 h0AFJ hpb h08GGu h08GGc h073B h073B2 hsq hZ hXqs hVqc hVqs
    (W ∩ T) hWT Set.inter_subset_right
  let adj := edsAdj h08FA h08F4 h0AFJ hpb h073B h073B2 hsq hZ hXqs hVqc hVqs (W ∩ T) hWT
  have := hA6.1
  have := hA6.2.1
  let e := adj.toEquivalence
  let : e.functor.CommShift ℤ := pullZ_commShift h08F4 hpb (edsEtaleMap hsq) (W ∩ T)
  let : e.inverse.CommShift ℤ := pushZ_commShift h08FA h0AFJ (edsEtaleMap hsq) (W ∩ T)
    (isQuasiCompact_edsEtaleMap h073B hsq hZ hXqs hVqc)
    (isQuasiSeparated_edsEtaleMap h073B2 hsq hZ hVqs) hWT
  have : e.functor.IsTriangulated := pullZ_isTriangulated h08F4 hpb (edsEtaleMap hsq) (W ∩ T)
  have : e.inverse.IsTriangulated := pushZ_isTriangulated h08FA h0AFJ (edsEtaleMap hsq) (W ∩ T)
    (isQuasiCompact_edsEtaleMap h073B hsq hZ hXqs hVqc)
    (isQuasiSeparated_edsEtaleMap h073B2 hsq hZ hVqs) hWT
  have : e.functor.Additive := Functor.IsTriangulated.instAdditive _
  have hTW : SumUniverse.SatisfiesPaperWA.{u} (DqcZ X (W ∩ T)) :=
    (SumUniverse.satisfiesPaperWA_iff_of_equivalence e).2 hVW
  -- the middle term: a compact generator with eventually vanishing self-extensions
  have hgen := lemma_A_9_generator h0AEC h0AED X hXqc hZ hXqs W hW hWc
  let G' := hgen.choose
  have hG'c : IsCompactObject.{u} G' := hgen.choose_spec.2.1
  have hG'g : IsPaperGenerator G' := hgen.choose_spec.2.2
  have hvan := lemma_5_6_dqcZ h09M8 hbd h09MB h0AED hZ X hXqc hXqs W hW hWc G' hG'c hG'g
  -- LP26 Theorem 1.1
  have : LocallySmall.{u} (DqcZ (edsOpenSpace hsq) (pointsMap B S hS _ j.hom ⁻¹' W)) :=
    locallySmall_dqcZ h079Q _ _
  have : LocallySmall.{u} (DqcZ X W) := locallySmall_dqcZ h079Q X W
  have : LocallySmall.{u} (DqcZ X (W ∩ T)) := locallySmall_dqcZ h079Q X (W ∩ T)
  have : HasCoproducts.{u} (DqcZ (edsOpenSpace hsq) (pointsMap B S hS _ j.hom ⁻¹' W)) :=
    hasCoproducts h08F3 hsum _ _ (hW.preimage (continuous_pointsMap B S hS j.hom))
  have : HasCoproducts.{u} (DqcZ X W) := hasCoproducts h08F3 hsum X W hW
  have : HasCoproducts.{u} (DqcZ X (W ∩ T)) := hasCoproducts h08F3 hsum X (W ∩ T) hWT
  refine (Stacks.theorem_1_1_univ.{u} R hUW hTW G'
    ((Stacks.isCompactObject_iff_sumUniverse_isCompactAb G').1 hG'c) hG'g).2 ?_
  obtain ⟨N, hN⟩ := hvan
  exact ⟨N + 1, fun n hn f => hN n (by omega) f⟩

end Proposition

/-! ### Non-vacuity -/

section NonVacuity

open PaperHypothesesW6.NonVacuity in
/-- A pretriangulated category all of whose objects are zero is weakly approximable, for every
coproduct universe `w` (it is equivalent to `ZeroSub C`, `zeroSub_satisfiesPaperWA_univ`). -/
theorem satisfiesPaperWA_of_forall_isZero.{w, v', u'} {C : Type u'} [Category.{v'} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (h : ∀ X : C, IsZero X) : SumUniverse.SatisfiesPaperWA.{w} C := by
  let F := (zeroProp C).ι
  have : F.EssSurj := ⟨fun X => ⟨⟨X, h X⟩, ⟨Iso.refl _⟩⟩⟩
  have : F.IsEquivalence := { }
  let e := F.asEquivalence
  let : e.functor.CommShift ℤ := (inferInstance : F.CommShift ℤ)
  have : e.functor.IsTriangulated := (inferInstance : F.IsTriangulated)
  have : e.functor.Additive := (inferInstance : F.Additive)
  let := e.commShiftInverse ℤ
  have := e.commShift_of_functor ℤ
  have : e.inverse.IsTriangulated := e.toAdjunction.isTriangulated_rightAdjoint
  exact (SumUniverse.satisfiesPaperWA_iff_of_equivalence e).1 (zeroSub_satisfiesPaperWA_univ C)

/-- **An algebraic space with no points satisfies W.A.** (Definition 5.3): every `D_{qc,T}` is
zero, its objects having cohomology sheaves with empty support (Stacks 04K5). -/
theorem satisfiesWA_of_isEmpty (hempty : SupportEmptyInput B S hS) (Y : AlgebraicSpaces B S hS)
    [(qcohDerived Y).IsTriangulated]
    [∀ T, ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS Y.1 Y.2 T)]
    (h : IsEmpty (points B S hS Y.1)) : SatisfiesWA Y := fun T _ _ =>
  satisfiesPaperWA_of_forall_isZero fun E => by
    refine IsZero.of_full_of_faithful_of_isZero (ιZ Y T) E ?_
    have hH : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS Y.1 Y.2) i).obj E.obj.obj) := fun i =>
      (hempty Y _).1 (Set.eq_empty_of_isEmpty _)
    have : E.obj.obj.IsLE 0 := (DerivedCategory.isLE_iff _ _).2 fun i _ => hH i
    have : E.obj.obj.IsGE 1 := (DerivedCategory.isGE_iff _ _).2 fun i _ => hH i
    exact DerivedCategory.TStructure.t.isZero E.obj.obj 0 1

/-- The open subspace of an algebraic space with no points (the open subspace of `∅ ⊆ |X₀|`). -/
def emptySubspace (X₀ : AlgebraicSpaces B S hS) :
    {G : Subfunctor X₀.1 // IsOpenSubspace B S hS G} :=
  (openSubspacesOrderIso B S hS X₀.1 X₀.2).symm ⟨∅, isOpen_empty⟩

/-- The algebraic space with no points: the open subspace of `∅ ⊆ |X₀|`. -/
def emptySpace (X₀ : AlgebraicSpaces B S hS) : AlgebraicSpaces B S hS :=
  ⟨(emptySubspace X₀).1.toFunctor, (emptySubspace X₀).2.1⟩

theorem isEmpty_points_emptySpace (X₀ : AlgebraicSpaces B S hS) :
    IsEmpty (points B S hS (emptySpace X₀).1) := by
  have h : Set.range (pointsMap B S hS (emptySubspace X₀).1.toFunctor (emptySubspace X₀).1.ι) =
      ∅ := by
    rw [emptySubspace, ← openSubspacesOrderIso_apply B S hS X₀.1 X₀.2, OrderIso.apply_symm_apply]
  exact ⟨fun p => (Set.eq_empty_iff_forall_notMem.1 h) _ ⟨p, rfl⟩⟩

/-- **Non-vacuity of `proposition_5_8`**: there is an elementary distinguished square of
quasi-compact quasi-separated algebraic spaces whose open part and étale part satisfy W.A., so
that every hypothesis of `proposition_5_8` (with the instance arguments, which 06UQ and
`SupportTriangulatedInput` give for every space) holds: the empty open subspace `X` of any
quasi-separated `X₀` (for instance an affine one, `Supported.nonVacuity_affine_univ`), with the
square `(⊤ ⊆ X, ⊤.ι)`.  (A non-empty example is the affine base case of LP26 Corollary 1.2, the
task following this one.) -/
theorem proposition_5_8_nonVacuity (hempty : SupportEmptyInput B S hS)
    (hEDS : EDSTopInput B S hS) (hqcO : OpenSubspaceQuasiCompactInput B S hS)
    [∀ Y : AlgebraicSpaces B S hS, (qcohDerived Y).IsTriangulated]
    [∀ (Y : AlgebraicSpaces B S hS) T, ObjectProperty.IsTriangulated
      (CohomologySupportedOn B S hS Y.1 Y.2 T)]
    (hZ : B.Contains (⊤_ Scheme.{u})) (X₀ : AlgebraicSpaces B S hS)
    (hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀.1) :
    ∃ (X : AlgebraicSpaces B S hS) (hsq : IsElementaryDistinguishedSquare B S hS X.2
        (⊤ : Subfunctor X.1) (⊤ : Subfunctor X.1).ι),
      IsQuasiCompactSpace B S hS X.1 ∧ IsAbsolutelyQuasiSeparated B S hS hZ X.1 ∧
      IsQuasiCompactSpace B S hS (⊤ : Subfunctor X.1).toFunctor ∧
      IsAbsolutelyQuasiSeparated B S hS hZ (⊤ : Subfunctor X.1).toFunctor ∧
      SatisfiesWA (edsOpenSpace hsq) ∧ SatisfiesWA (edsEtaleSpace hsq) := by
  let X := emptySpace X₀
  have hXe := isEmpty_points_emptySpace X₀
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    hqcO X₀.2 (emptySubspace X₀).2 (by
      have hr : Set.range (pointsMap B S hS (emptySubspace X₀).1.toFunctor
          (emptySubspace X₀).1.ι) = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun _ ⟨p, _⟩ => hXe.elim p
      rw [hr]
      exact isCompact_empty)
  have hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X.2 hX₀qs
      (isQuasiSeparated_of_mono' (emptySubspace X₀).1.ι)
  have hsq := hEDS X.2 (isOpenSubspace_top X.2)
  have e : (⊤ : Subfunctor X.1).toFunctor ≅ X.1 := asIso (⊤ : Subfunctor X.1).ι
  have hTe : IsEmpty (points B S hS (⊤ : Subfunctor X.1).toFunctor) :=
    (pointsMap B S hS _ (⊤ : Subfunctor X.1).ι).isEmpty
  refine ⟨X, hsq, hXqc, hXqs, IsQuasiCompactSpace.of_iso B S hS hXqc e.symm,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hsq.isAlgebraicSpace hXqs
      (isQuasiSeparated_of_mono' (⊤ : Subfunctor X.1).ι),
    satisfiesWA_of_isEmpty hempty _ hTe, satisfiesWA_of_isEmpty hempty _ hTe⟩

end NonVacuity

end RelativeFM.Spaces.LP26
