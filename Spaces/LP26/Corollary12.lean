/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.LP26.Proposition58
import Spaces.Affine.WeakApprox

/-!
# LP26 Corollary 1.2 over algebraic spaces

Lank–Pauwels, *Gluing weak approximability along recollements* (LP26), **Corollary 1.2**
(`cor:weak_approx_spaces`): for `X` a quasi-compact quasi-separated algebraic space and `S ⊆ |X|`
closed with quasi-compact complement, `D_{qc,S}(X)` is weakly approximable; in particular
`D_qc(X)` is.

## Main results

* `corollary_1_2`: `X` quasi-compact and quasi-separated satisfies W.A. (LP26 Definition 5.3,
  `def:wa_spaces`, `SatisfiesWA`): `D_{qc,S}(X)` is weakly approximable for every closed `S` with
  quasi-compact complement (first claim).
* `corollary_1_2_dqc`: `D_qc(X)` (AxiomMath's `QuasicoherentDerivedCategory`) is weakly
  approximable (second claim, the case `S = |X|`).
* `satisfiesWA_space`: the affine base case in the form of Definition 5.3 (every closed `S` with
  quasi-compact complement of `|Spec R|` is `V(I)`, `I` finitely generated; the affine base case
  `Affine.lp26_cor_1_2_affine`, wave 7, then gives it).
* `satisfiesWA_of_iso`: W.A. is invariant under isomorphisms of algebraic spaces (by Proposition
  5.8 applied to the elementary distinguished square `(∅ ⊆ Y, X ≅ Y)`).
* `UniverseDescent.satisfiesPaperWA_of_max`: in a locally `w`-small triangulated category with
  `Type w`-indexed direct sums, weak approximability for direct sums indexed by a larger universe
  implies it for `Type w`-indexed ones (only `w`-many summands of an existing direct sum are
  nonzero, `UniverseDescent.small_nonzero`).  It takes the affine base case, stated with direct
  sums indexed by the Hom universe `Type (u + 1)` of `D(𝒪_X)`, to the coproduct universe `u` of
  Definition 5.3 and Proposition 5.8.  Mathlib only.

## Proof (LP26's induction)

Let `P(W)` say that the quasi-compact open subspace `W ⊆ X` satisfies W.A.  By the induction
principle Stacks 09IT (AxiomMath's `qcqs_induction_on_enlargement`, `Tag09ITInput`), started at
the empty open subspace, it suffices that `P(∅)` holds (no points, `satisfiesWA_of_isEmpty`) and
that for an elementary distinguished square `(W₁ ⊆ W₂, f : V ⟶ W₂)` with `V` affine, `P(W₁)`
implies `P(W₂)`: the open part of the square is isomorphic to `W₁`, `V` to an affine `h_T`, both
satisfy W.A. (`P(W₁)`, `satisfiesWA_space`, `satisfiesWA_of_iso`), and Proposition 5.8
(`prop:A8`, `proposition_5_8`) gives W.A. for `W₂`.

## Difference from LP26

* LP26 assumes moreover that `X` has quasi-finite separated diagonal.  The statements here do not:
  the induction starts at the empty open subspace rather than at the schematic locus, so only
  affine spaces enter and no hypothesis on the diagonal is used.  The statements are therefore
  stronger than the paper's.
* Weak approximability is `SumUniverse.SatisfiesPaperWA.{u}`: LP26 Definition 2.1 with
  compactness and coproducts for `Type u`-indexed direct sums, the sums of AxiomMath's model (as in
  `proposition_5_8`).  Its `t`-structure is existential.

## What is not proved

* **Standard W.A.** (Definition 5.3: weak approximation data whose `t`-structure is the standard
  one) is proved in `Spaces/LP26/StandardWA.lean` (`corollary_1_2_standard`, wave 9), from the
  standard part of Proposition 5.8 and standard W.A. of affine spaces.
* **Coherence** (third claim: `D_{qc,S}(X)` is coherent when `X` is Noetherian).  LP26 derives it
  from standard W.A., LP26 Lemma 5.9 (`lem:characterize_T-_c`, `Spaces/LP26/Lemma59.lean`) and
  Canonaco–Haesemeyer–Neeman–Stellari, Example 10.1.2; neither standard W.A. nor that example (nor
  the notion of a coherent triangulated category) is in the tree.  Nothing is assumed about it.

## Assumptions

Only tagged AxiomMath inputs, all named in the hypotheses: those of `proposition_5_8`; of the
affine base case (`Affine.Tag06Z0ExactInput`, `Affine.Tag06Z0QcohInput`, `Affine.Tag06Z0Input`,
`Affine.Tag07TYInput`); `SupportEmptyInput`, `OpenSubspaceQuasiCompactInput`,
`AffineQuasiSeparatedInput`; and two new ones, `Tag09ITInput` (Stacks 09IT) and
`EDSOfComplSubsetInput` (Stacks 08GM), in `Spaces/LP26/Inputs.lean`.  For non-vacuity also
`Tag06UQInput`, `SupportTriangulatedInput`, `ContainsTerminalInput`, `Affine.Tag021RInput`.  The
instance arguments (`D_qc` and the supports triangulated) are given for every space by Stacks 06UQ
and `SupportTriangulatedInput` (`corollary_1_2_nonVacuity`).  AxiomMath's
`isOpenImmersion_of_isIso` is reproduced (`isOpenImmersion_of_isIso'`), not assumed.

## Non-vacuity

`corollary_1_2_nonVacuity`: for an object `T₀` of the site with affine, non-empty underlying
scheme, `X = h_{T₀}` has a point, is quasi-compact and quasi-separated, and satisfies W.A.
`corollary_1_2_int_witness`: `T₀ = Spec ℤ` in some big fppf site (`Affine.Tag021RInput`) is such
an object.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Space RelativeWeakApprox

namespace RelativeFM.Spaces.LP26

universe w v v' u

namespace UniverseDescent

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- In a locally `w`-small preadditive category, the members of a family with a direct sum
that are not zero form a `w`-small set. -/
theorem small_nonzero [LocallySmall.{w} C] {J : Type v'} (f : J → C) [HasCoproduct f] :
    Small.{w} {j : J // ¬ IsZero (f j)} := by
  classical
  refine small_of_injective
    (f := fun j : {j : J // ¬ IsZero (f j)} => Sigma.π f j.1 ≫ Sigma.ι f j.1) ?_
  rintro ⟨j, hj⟩ ⟨k, hk⟩ h
  by_contra hne
  have hjk : j ≠ k := fun e => hne (Subtype.ext e)
  have h2 := congrArg (Sigma.ι f j ≫ ·) h
  have hself : Sigma.ι f j ≫ Sigma.π f j = 𝟙 _ := by simp
  simp only [reassoc_of% hself, Sigma.ι_π_of_ne_assoc _ hjk, zero_comp] at h2
  apply hj
  rw [IsZero.iff_id_eq_zero, ← hself, h2, zero_comp]

/-- A direct sum indexed by any type is the direct sum of its nonzero members. -/
noncomputable def sigmaNonzeroIso {J : Type v'} (f : J → C) [HasCoproduct f]
    [HasCoproduct (fun j : {j : J // ¬ IsZero (f j)} => f j.1)] :
    (∐ fun j : {j : J // ¬ IsZero (f j)} => f j.1) ≅ ∐ f := by
  classical
  exact
  { hom := Sigma.desc fun j => Sigma.ι f j.1
    inv := Sigma.desc fun j => if h : IsZero (f j) then 0 else
      Sigma.ι (fun j : {j : J // ¬ IsZero (f j)} => f j.1) ⟨j, h⟩
    hom_inv_id := by
      ext ⟨j, hj⟩
      simp [hj]
    inv_hom_id := by
      ext j
      by_cases hj : IsZero (f j)
      · simp only [Sigma.ι_comp_desc_assoc, hj, dite_true, zero_comp, Category.comp_id]
        exact (hj.eq_of_src _ _)
      · simp [hj] }

/-- **Closure under all existing direct sums.**  In a locally `w`-small preadditive category
with `Type w`-indexed direct sums, an isomorphism-closed property closed under
`Type w`-indexed direct sums is closed under every existing direct sum, whatever its index
universe: only `w`-many members are nonzero (`small_nonzero`). -/
theorem isClosedUnderColimitsOfShape_discrete [LocallySmall.{w} C] [HasCoproducts.{w} C]
    (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms]
    [∀ J : Type w, Q.IsClosedUnderColimitsOfShape (Discrete J)] (J : Type v') :
    Q.IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    let f : J → C := fun j => h.diag.obj ⟨j⟩
    have : HasColimit h.diag := ⟨⟨⟨_, h.isColimit⟩⟩⟩
    have : HasCoproduct f := hasColimit_of_iso (Discrete.natIsoFunctor (F := h.diag)).symm
    let e : X ≅ ∐ f := h.isColimit.coconePointUniqueUpToIso (colimit.isColimit h.diag) ≪≫
      HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := h.diag))
    refine Q.prop_of_iso e.symm ?_
    let J' := {j : J // ¬ IsZero (f j)}
    have := small_nonzero.{w} f
    let eq : Discrete (Shrink.{w} J') ≌ Discrete J' := Discrete.equivalence (equivShrink J').symm
    have : HasColimitsOfShape (Discrete J') C := hasColimitsOfShape_of_equivalence eq
    have : Q.IsClosedUnderColimitsOfShape (Discrete J') :=
      ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence eq
    refine Q.prop_of_iso (sigmaNonzeroIso f) ?_
    exact Q.prop_colimit _ fun j => h.prop_diag_obj _

/-- **Compactness descends to a smaller coproduct universe**: an object compact against
`Type (max w v')`-indexed direct sums is compact against `Type w`-indexed ones (reindex a
`Type w`-indexed family along `ULift`). -/
theorem isCompactAb_of_max {K : C} (hK : SumUniverse.IsCompactAb.{max w v'} K) :
    SumUniverse.IsCompactAb.{w} K := by
  classical
  constructor
  intro I _ E _
  let E' : ULift.{v'} I → C := fun i => E i.down
  let c' : Cofan E' := Cofan.mk (∐ E) fun i => Sigma.ι E i.down
  have hc' : IsColimit c' := Cofan.IsColimit.mk c' (fun s => Sigma.desc fun i => s.inj ⟨i⟩)
    (fun s ⟨i⟩ => Sigma.ι_comp_desc (fun i => s.inj ⟨i⟩) i)
    (fun s m hm => Sigma.hom_ext (f := E) m _ fun i => by
      rw [Sigma.ι_comp_desc]
      exact hm ⟨i⟩)
  have hb := SumUniverse.bijective_sumMap_of_isColimit hK hc'
  let φ : (DirectSum I fun i => (K ⟶ E i)) →+ (DirectSum (ULift.{v'} I) fun i => (K ⟶ E' i)) :=
    DirectSum.toAddMonoid fun i => DirectSum.of (fun i : ULift.{v'} I => (K ⟶ E' i)) ⟨i⟩
  let ψ : (DirectSum (ULift.{v'} I) fun i => (K ⟶ E' i)) →+ (DirectSum I fun i => (K ⟶ E i)) :=
    DirectSum.toAddMonoid fun i => DirectSum.of (fun i : I => (K ⟶ E i)) i.down
  have hψφ : ψ.comp φ = AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro i y
    simp [φ, ψ]
  have hφψ : φ.comp ψ = AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro i y
    simp [φ, ψ]
  let α : (DirectSum I fun i => (K ⟶ E i)) ≃+ (DirectSum (ULift.{v'} I) fun i => (K ⟶ E' i)) :=
    AddMonoidHom.toAddEquiv φ ψ hψφ hφψ
  refine SumUniverse.bijective_of_comm (SumUniverse.sumMap K c') _ α (AddEquiv.refl _)
    (fun x => ?_) hb
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i g =>
    simp [α, φ, c', SumUniverse.sumMap]
  | add x y hx hy =>
    simp only [map_add] at hx hy ⊢
    rw [hx, hy]

end

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The coproduct closure descends**: in a locally `w`-small category with `Type w`-indexed
direct sums, `Coprod.{v'} P ≤ Coprod.{w} P` for every index universe `v'`. -/
theorem coprod_le [LocallySmall.{w} C] [HasCoproducts.{w} C] (P : ObjectProperty C) :
    SumUniverse.Coprod.{v'} P ≤ SumUniverse.Coprod.{w} P := by
  have : ∀ J : Type v', (SumUniverse.Coprod.{w} P).IsClosedUnderColimitsOfShape (Discrete J) :=
    fun J => isClosedUnderColimitsOfShape_discrete.{w} _ J
  exact SumUniverse.Coprod.le SumUniverse.Coprod.le_coprod

/-- The envelopes descend likewise. -/
theorem envelope_le [LocallySmall.{w} C] [HasCoproducts.{w} C] (H : C) (a b : ℤ) :
    SumUniverse.envelope.{v'} H a b ≤ SumUniverse.envelope.{w} H a b :=
  ObjectProperty.monotone_retractClosure (coprod_le.{w} _)

/-- **Weak approximability descends to a smaller coproduct universe**: in a locally `w`-small
category with `Type w`-indexed direct sums, weak approximability for `Type (max w v')`-indexed
direct sums (LP26 Definition 2.1) implies it for `Type w`-indexed ones, with the same
generator, `t`-structure and bound. -/
theorem satisfiesPaperWA_of_max [LocallySmall.{w} C] [HasCoproducts.{w} C]
    (h : SumUniverse.SatisfiesPaperWA.{max w v'} C) : SumUniverse.SatisfiesPaperWA.{w} C := by
  obtain ⟨W⟩ := h
  exact ⟨{
    G := W.G
    t := W.t
    A := W.A
    A_pos := W.A_pos
    G_compact := isCompactAb_of_max W.G_compact
    G_paperGenerates := W.G_paperGenerates
    G_mem_le := W.G_mem_le
    hom_vanishing := W.hom_vanishing
    exists_triangle := fun F hF => by
      obtain ⟨E, D, f, g, k, hT, hE, hD⟩ := W.exists_triangle F hF
      exact ⟨E, D, f, g, k, hT, envelope_le.{w} _ _ _ _ hE, hD⟩ }⟩

end

end UniverseDescent

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

open Supported

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The affine base case -/

section Affine

/-- The inclusion `D_{qc,T}(X) ⥤ D(𝒪_X)`, with target spelled `D B S hS X` (the repository's
spelling, `Spaces/Categories.lean`, of AxiomMath's `DerivedCategory (Modules …)`). -/
abbrev ιZD (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) :
    DqcZ X T ⥤ D B S hS X :=
  ιZ X T

/-- `D_{qc,T}(X)` is equivalent to the full subcategory of `D(𝒪_X)` on `Spaces.DqcSupported X T`
(the same objects, `dqcSupported_iff_exists`), by a triangulated functor. -/
def toDqcSupported (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) :
    DqcZ X T ⥤ (DqcSupported X T).FullSubcategory :=
  (DqcSupported X T).lift (ιZD X T) fun E => ⟨E.obj.property, E.property⟩

section

variable (X : AlgebraicSpaces B S hS) [(qcohDerived X).IsTriangulated]
    (T : Set (points B S hS X.1))
    [ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T)]
    [(DqcSupported X T).IsTriangulated]

/-- `ιZD` commutes with shifts (that of the composite of the two inclusions). -/
instance : (ιZD X T).CommShift ℤ :=
  (inferInstance : ((qcSupportedOn X T).ι ⋙ (qcohDerived X).ι).CommShift ℤ)

/-- `ιZD` is triangulated (the composite of the two inclusions is). -/
instance : (ιZD X T).IsTriangulated :=
  (inferInstance : ((qcSupportedOn X T).ι ⋙ (qcohDerived X).ι).IsTriangulated)

/-- `toDqcSupported` commutes with shifts (Mathlib's `ObjectProperty.commShiftLift`). -/
instance : (toDqcSupported X T).CommShift ℤ := ObjectProperty.commShiftLift _ _ _

/-- `toDqcSupported` is triangulated (Mathlib's `ObjectProperty.isTriangulated_lift`). -/
instance : (toDqcSupported X T).IsTriangulated := ObjectProperty.isTriangulated_lift _ _ _

/-- `toDqcSupported` is an equivalence: fully faithful (as `ιZ` is) and essentially surjective
(same objects). -/
instance : (toDqcSupported X T).IsEquivalence := by
  have : (ιZD X T).Full := (inferInstance : (ιZ X T).Full)
  have : (ιZD X T).Faithful := (inferInstance : (ιZ X T).Faithful)
  have : (toDqcSupported X T).Full := ObjectProperty.instFullFullSubcategoryLift _ _ _
  have : (toDqcSupported X T).Faithful := ObjectProperty.instFaithfulFullSubcategoryLift _ _ _
  have : (toDqcSupported X T).EssSurj :=
    ⟨fun E => ⟨⟨⟨E.obj, E.property.1⟩, E.property.2⟩, ⟨Iso.refl _⟩⟩⟩
  exact { }

/-- Weak approximability (for any coproduct universe) passes from the full subcategory
`DqcSupported X T` of `D(𝒪_X)` to `D_{qc,T}(X)`. -/
theorem satisfiesPaperWA_dqcZ_of_dqcSupported
    (h : SumUniverse.SatisfiesPaperWA.{w} (DqcSupported X T).FullSubcategory) :
    SumUniverse.SatisfiesPaperWA.{w} (DqcZ X T) := by
  let e := (toDqcSupported X T).asEquivalence
  let : e.functor.CommShift ℤ := (inferInstance : (toDqcSupported X T).CommShift ℤ)
  have : e.functor.IsTriangulated := (inferInstance : (toDqcSupported X T).IsTriangulated)
  have : e.functor.Additive := ⟨fun {E F f g} => by
    ext
    exact (ιZ X T).map_add⟩
  let := e.commShiftInverse ℤ
  have := e.commShift_of_functor ℤ
  have : e.inverse.IsTriangulated := e.toAdjunction.isTriangulated_rightAdjoint
  exact (SumUniverse.satisfiesPaperWA_iff_of_equivalence e).2 h

/-- **From the Hom universe to `Type u`-indexed direct sums on `D_{qc,T}(X)`**: weak
approximability of `DqcSupported X T` in the repository's sense (`PaperM2`, direct sums indexed
by the Hom universe `Type (u + 1)`) gives weak approximability of `D_{qc,T}(X)` for
`Type u`-indexed direct sums, `T` closed (`satisfiesPaperWA_dqcZ_of_dqcSupported`, then
`UniverseDescent.satisfiesPaperWA_of_max` with Stacks 079Q and 08F3). -/
theorem satisfiesPaperWA_dqcZ_of_paperM2 (h079Q : Tag079QInput.{u}) (h08F3 : Tag08F3Input B S hS)
    (hsum : SupportedDirectSumsInput B S hS) (hT : IsClosed T)
    (h : PaperM2.SatisfiesPaperWA (DqcSupported X T).FullSubcategory) :
    SumUniverse.SatisfiesPaperWA.{u} (DqcZ X T) := by
  have : LocallySmall.{u} (DqcZ X T) := locallySmall_dqcZ h079Q _ _
  have : HasCoproducts.{u} (DqcZ X T) := hasCoproducts h08F3 hsum _ _ hT
  have : (DqcSupported X T).IsStableUnderShift ℤ := inferInstance
  have : ∀ n : ℤ, (shiftFunctor (D B S hS X) n).Additive := inferInstance
  have : ∀ n : ℤ, (shiftFunctor (DqcSupported X T).FullSubcategory n).Additive :=
    fun n => inferInstance
  exact UniverseDescent.satisfiesPaperWA_of_max.{u, u + 1, u + 1, u + 1}
    (satisfiesPaperWA_dqcZ_of_dqcSupported _ _ ((SumUniverse.satisfiesPaperWA_iff _).2 h))

end

end Affine

section AffineBase

open _root_.RelativeFM.Spaces.Affine in
/-- **Closed subsets of `|Spec R|` with quasi-compact complement are the `V(I)`, `I` finitely
generated** (Mathlib's `PrimeSpectrum.isCompact_isOpen_iff_ideal`, along the homeomorphism
`|h_U| ≃ₜ X_U ≃ₜ Spec R`, AxiomMath's `schemePointsHomeomorph`, Stacks 03BX). -/
theorem exists_fg_eq_zeroLocusPoints (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (T : Set (points B S hS (yoneda.obj U)))
    (hT : IsClosed T) (hTc : _root_.IsCompact Tᶜ) :
    ∃ I : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤), I.FG ∧ T = zeroLocusPoints U I := by
  let h := (schemePointsHomeomorph B S hS U).trans
    (Scheme.homeoOfIso ((BigFppfOver.toScheme B S hS).obj U).isoSpec)
  obtain ⟨I, hI, e⟩ := PrimeSpectrum.isCompact_isOpen_iff_ideal.1
    ⟨hTc.image h.continuous, h.isOpenMap _ hT.isOpen_compl⟩
  refine ⟨I, hI, ?_⟩
  ext p
  have hp : p ∈ Tᶜ ↔ h p ∈ (PrimeSpectrum.zeroLocus (I : Set _))ᶜ := by
    rw [e]
    exact ⟨fun hp => ⟨p, hp, rfl⟩, fun ⟨q, hq, hqp⟩ => h.injective hqp ▸ hq⟩
  simp only [Set.mem_compl_iff] at hp
  exact not_iff_not.1 hp

/-- **Corollary 1.2** (`cor:weak_approx_spaces`), affine base case, in the form of Definition 5.3: an affine
algebraic space `h_U` (`U` an object of the site with affine underlying scheme) satisfies W.A.:
for every closed `T ⊆ |h_U|` with quasi-compact complement, `D_{qc,T}(h_U)` is weakly
approximable for `Type u`-indexed direct sums.  From the affine base case over spaces
(`Affine.lp26_cor_1_2_affine`, `T = V(I)` with `I` finitely generated by
`exists_fg_eq_zeroLocusPoints`), transported to `D_{qc,T}` (`satisfiesPaperWA_dqcZ_of_dqcSupported`)
and descended from the Hom universe `u + 1` to `u` (`UniverseDescent.satisfiesPaperWA_of_max`,
with Stacks 079Q and 08F3). -/
theorem satisfiesWA_space (hex : Affine.Tag06Z0ExactInput B S hS)
    (hq : Affine.Tag06Z0QcohInput B S hS) (h06Z0 : Affine.Tag06Z0Input B S hS)
    (h07TY : Affine.Tag07TYInput B S hS) (h079Q : Tag079QInput.{u})
    (h08F3 : Tag08F3Input B S hS) (hsum : SupportedDirectSumsInput B S hS)
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [(qcohDerived (Affine.space U)).IsTriangulated]
    [∀ T, ObjectProperty.IsTriangulated
      (CohomologySupportedOn B S hS (Affine.space U).1 (Affine.space U).2 T)] :
    SatisfiesWA (Affine.space U) := by
  intro T hT hTc
  obtain ⟨I, hI, rfl⟩ := exists_fg_eq_zeroLocusPoints U T hT hTc
  obtain ⟨hinst, hWA⟩ := Affine.lp26_cor_1_2_affine hex hq h06Z0 h07TY U I hI
  exact satisfiesPaperWA_dqcZ_of_paperM2 _ _ h079Q h08F3 hsum hT hWA

end AffineBase

/-! ### Invariance of W.A. under isomorphisms -/

section Iso

/-- **An isomorphism of algebraic spaces is an open immersion.**  AxiomMath's two-line proof of
`AlgebraicGeometry.Space.isOpenImmersion_of_isIso` (`Spaces/QuasiSeparatedCriteria.lean`, outside
the import list), reproduced. -/
theorem isOpenImmersion_of_isIso' {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    [IsIso f] : IsOpenImmersion B S hS f := by
  refine MorphismProperty.relative.of_exists (fun a g ↦ ⟨a, g ≫ inv f, 𝟙 a, ?_, ?_⟩)
  · exact IsPullback.of_vert_isIso ⟨by simp⟩
  · change AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (𝟙 a))
    rw [CategoryTheory.Functor.map_id]
    infer_instance

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable [∀ Y : AlgebraicSpaces B S hS, (qcohDerived Y).IsTriangulated]
  [∀ (Y : AlgebraicSpaces B S hS) T,
    ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS Y.1 Y.2 T)]

/-- **W.A. (Definition 5.3) is invariant under isomorphisms** of quasi-compact quasi-separated
algebraic spaces.  Proof: for `e : X ≅ Y`, the empty open subspace of `Y` and `e` form an
elementary distinguished square (`EDSOfComplSubsetInput`: `e` is an open immersion onto all of
`|Y|`), whose open part satisfies W.A. (it has no points, `satisfiesWA_of_isEmpty`); Proposition
5.8 (`proposition_5_8`) then passes W.A. from `X` to `Y`. -/
theorem satisfiesWA_of_iso (h08FA : Tag08FAInput B S hS) (h08F4 : Tag08F4Input B S hS)
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
    (hEDSc : EDSOfComplSubsetInput B S hS) (hempty : SupportEmptyInput B S hS)
    (hqcO : OpenSubspaceQuasiCompactInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (e : X.1 ≅ Y.1)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (h : SatisfiesWA X) : SatisfiesWA Y := by
  let U := emptySubspace Y
  have hUe : IsEmpty (points B S hS U.1.toFunctor) := isEmpty_points_emptySpace Y
  have hsq : IsElementaryDistinguishedSquare B S hS Y.2 U.1 e.hom :=
    hEDSc Y.2 U.1 U.2 X.2 e.hom (isOpenImmersion_of_isIso' e.hom)
      (fun y _ => pointsMap_surjective_of_isIso B S hS e.hom y)
  have hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor := hqcO Y.2 U.2 (by
    have hr : Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun _ ⟨p, _⟩ => hUe.elim p
    rw [hr]
    exact isCompact_empty)
  exact proposition_5_8 h08FA h08F4 h0AFJ hpb hdisj hres hcounit hperf h08F3 hsum h0AEC
    h0AED h079Q h0A8G hRAC hqcs hcpt h08GGu h08GGc h073B h073B2 h09M8 hbd h09MB
    hsq hZ hYqc hYqs hUqc hXqc hXqs (satisfiesWA_of_isEmpty hempty _ hUe) h

end Iso

/-! ### LP26 Corollary 1.2 -/

section Corollary

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable [∀ Y : AlgebraicSpaces B S hS, (qcohDerived Y).IsTriangulated]
  [∀ (Y : AlgebraicSpaces B S hS) T,
    ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS Y.1 Y.2 T)]

/-- **Corollary 1.2** (`cor:weak_approx_spaces`), first claim, over algebraic spaces: a
quasi-compact quasi-separated algebraic space `X` satisfies W.A. (Definition 5.3): for every
closed `S ⊆ |X|` with quasi-compact complement, `D_{qc,S}(X)` is weakly approximable
(`SumUniverse.SatisfiesPaperWA.{u}`: LP26 Definition 2.1 with `Type u`-indexed direct sums).

LP26 assumes moreover that `X` has quasi-finite separated diagonal; this statement does not, and
is therefore stronger: the induction here starts at the empty open subspace, so only affine spaces
enter and no hypothesis on the diagonal is used.  LP26's proof gives standard W.A.; only W.A. is
proved here (module docstring, "What is not proved").

Proof (LP26's induction): `P(W)`: the quasi-compact open subspace `W` satisfies W.A.  `P(∅)`:
`satisfiesWA_of_isEmpty`.  Step: an elementary distinguished square `(W₁ ⊆ W₂, f : V ⟶ W₂)` with
`V` affine; the open part is isomorphic to `W₁` and `V` to an affine `h_T`, which satisfy W.A.
(`P(W₁)`, `satisfiesWA_space`; transported by `satisfiesWA_of_iso`), so `W₂` does by Proposition
5.8 (`proposition_5_8`).  Stacks 09IT (`Tag09ITInput`) gives `P(X)`. -/
theorem corollary_1_2 (h08FA : Tag08FAInput B S hS) (h08F4 : Tag08F4Input B S hS)
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
    (hEDSc : EDSOfComplSubsetInput B S hS) (hempty : SupportEmptyInput B S hS)
    (hqcO : OpenSubspaceQuasiCompactInput B S hS) (h09IT : Tag09ITInput B S hS)
    (hqsAff : AffineQuasiSeparatedInput B S hS)
    (hex : Affine.Tag06Z0ExactInput B S hS) (hq : Affine.Tag06Z0QcohInput B S hS)
    (h06Z0 : Affine.Tag06Z0Input B S hS) (h07TY : Affine.Tag07TYInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    SatisfiesWA X := by
  have qsSub : ∀ (W : Subfunctor X.1) (hW : IsAlgebraicSpace B S hS W.toFunctor),
      IsAbsolutelyQuasiSeparated B S hS hZ W.toFunctor := fun W hW =>
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hW hXqs (isQuasiSeparated_of_mono' W.ι)
  let P : Subfunctor X.1 → Prop := fun W => ∀ hW : IsOpenSubspace B S hS W,
    IsQuasiCompactSpace B S hS W.toFunctor → SatisfiesWA ⟨W.toFunctor, hW.1⟩
  -- the base: the empty open subspace
  have hE : IsEmpty (points B S hS (emptySubspace X).1.toFunctor) := isEmpty_points_emptySpace X
  have hEqc : IsQuasiCompactSpace B S hS (emptySubspace X).1.toFunctor :=
    hqcO X.2 (emptySubspace X).2 (by
      have hr : Set.range (pointsMap B S hS _ (emptySubspace X).1.ι) = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun _ ⟨p, _⟩ => hE.elim p
      rw [hr]
      exact isCompact_empty)
  have hPE : P (emptySubspace X).1 := fun _ _ => satisfiesWA_of_isEmpty hempty _ hE
  -- the step: LP26 Proposition 5.8
  have hstep : ∀ (W₁ W₂ : Subfunctor X.1), IsOpenSubspace B S hS W₁ →
      ∀ (hW₂ : IsOpenSubspace B S hS W₂),
      IsQuasiCompactSpace B S hS W₁.toFunctor →
      IsQuasiCompactSpace B S hS W₂.toFunctor →
      ∀ hle : W₁ ≤ W₂, (emptySubspace X).1 ≤ W₁ →
      ∀ {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W₂.toFunctor),
        (∃ T : BigFppfOver B S hS,
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧ Nonempty (V ≅ yoneda.obj T)) →
        IsElementaryDistinguishedSquare B S hS hW₂.1
          (Subfunctor.range (Subfunctor.homOfLe hle)) f →
        P W₁ → P W₂ := by
    intro W₁ W₂ hW₁ hW₂ hqc₁ hqc₂ hle _ V f hVaff hsq₀ hP₁ _ _
    let X₂ : AlgebraicSpaces B S hS := ⟨W₂.toFunctor, hW₂.1⟩
    have hsq : IsElementaryDistinguishedSquare B S hS X₂.2
        (Subfunctor.range (Subfunctor.homOfLe hle)) f := hsq₀
    -- the open part, isomorphic to `W₁`
    let eU : W₁.toFunctor ≅ (Subfunctor.range (Subfunctor.homOfLe hle)).toFunctor :=
      asIso (Subfunctor.toRange (Subfunctor.homOfLe hle))
    have hUqc := IsQuasiCompactSpace.of_iso B S hS hqc₁ eU
    have hUqs : IsAbsolutelyQuasiSeparated B S hS hZ
        (Subfunctor.range (Subfunctor.homOfLe hle)).toFunctor :=
      isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hsq.isOpenSubspace.1
        (qsSub W₂ hW₂.1) (isQuasiSeparated_of_mono' (Subfunctor.range (Subfunctor.homOfLe hle)).ι)
    have hU : SatisfiesWA (edsOpenSpace hsq) :=
      satisfiesWA_of_iso h08FA h08F4 h0AFJ hpb hdisj hres hcounit hperf h08F3 hsum h0AEC
        h0AED h079Q h0A8G hRAC hqcs hcpt h08GGu h08GGc h073B h073B2 h09M8 hbd h09MB
        hEDSc hempty hqcO hZ (X := ⟨W₁.toFunctor, hW₁.1⟩) (Y := edsOpenSpace hsq) eU hqc₁
        (qsSub W₁ hW₁.1) hUqc hUqs (hP₁ hW₁ hqc₁)
    -- the étale part, isomorphic to an affine `h_T`
    obtain ⟨T, hT, ⟨eV⟩⟩ := hVaff
    have hTqc : IsQuasiCompactSpace B S hS (yoneda.obj T) :=
      isQuasiCompact_yoneda_of_compact B S hS T inferInstance
    have hTqs := hqsAff hZ T hT
    have hVqc : IsQuasiCompactSpace B S hS V := IsQuasiCompactSpace.of_iso B S hS hTqc eV.symm
    have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V :=
      isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hsq.isAlgebraicSpace hTqs
        (isQuasiSeparated_of_mono' eV.hom)
    have hY : SatisfiesWA (edsEtaleSpace hsq) :=
      satisfiesWA_of_iso h08FA h08F4 h0AFJ hpb hdisj hres hcounit hperf h08F3 hsum h0AEC
        h0AED h079Q h0A8G hRAC hqcs hcpt h08GGu h08GGc h073B h073B2 h09M8 hbd h09MB
        hEDSc hempty hqcO hZ (X := Affine.space T) (Y := edsEtaleSpace hsq) eV.symm
        hTqc hTqs hVqc hVqs
        (satisfiesWA_space hex hq h06Z0 h07TY h079Q h08F3 hsum T)
    exact proposition_5_8 h08FA h08F4 h0AFJ hpb hdisj hres hcounit hperf h08F3 hsum h0AEC
      h0AED h079Q h0A8G hRAC hqcs hcpt h08GGu h08GGc h073B h073B2 h09M8 hbd h09MB
      (X := X₂) hsq hZ hqc₂ (qsSub W₂ hW₂.1) hUqc hVqc hVqs hU hY
  -- Stacks 09IT
  have hTop := h09IT hZ X hXqc hXqs (emptySubspace X).1 (emptySubspace X).2 hEqc P hPE hstep
  have hTqc : IsQuasiCompactSpace B S hS (⊤ : Subfunctor X.1).toFunctor :=
    IsQuasiCompactSpace.of_iso B S hS hXqc (asIso (⊤ : Subfunctor X.1).ι).symm
  exact satisfiesWA_of_iso h08FA h08F4 h0AFJ hpb hdisj hres hcounit hperf h08F3 hsum h0AEC
    h0AED h079Q h0A8G hRAC hqcs hcpt h08GGu h08GGc h073B h073B2 h09M8 hbd h09MB
    hEDSc hempty hqcO hZ (X := ⟨(⊤ : Subfunctor X.1).toFunctor, (isOpenSubspace_top X.2).1⟩)
    (Y := X) (asIso (⊤ : Subfunctor X.1).ι) hTqc (qsSub ⊤ (isOpenSubspace_top X.2).1)
    hXqc hXqs (hTop (isOpenSubspace_top X.2) hTqc)

/-- The inclusion `D_{qc,|X|}(X) ⥤ D_qc(X)` is an equivalence: every object is supported on
`|X|` (as `Supported.isEquivalence_ι_univ`, `Spaces/Supported/Preferred.lean`). -/
instance isEquivalence_ι_univ' (X : AlgebraicSpaces B S hS) :
    (qcSupportedOn X (Set.univ : Set (points B S hS X.1))).ι.IsEquivalence where
  essSurj := ⟨fun E => ⟨⟨E, fun _ => Set.subset_univ _⟩, ⟨Iso.refl _⟩⟩⟩

/-- **Corollary 1.2** (`cor:weak_approx_spaces`), second claim ("in particular", the case
`S = |X|`): for `X` quasi-compact and quasi-separated, `D_qc(X)` (AxiomMath's
`QuasicoherentDerivedCategory`) is weakly approximable (LP26 Definition 2.1 with `Type u`-indexed
direct sums).  From `corollary_1_2` at `S = |X|` (closed, with empty complement), along the
triangulated equivalence `D_{qc,|X|}(X) ≌ D_qc(X)`.  As for `corollary_1_2`, the hypothesis of
quasi-finite separated diagonal is not needed. -/
theorem corollary_1_2_dqc (h08FA : Tag08FAInput B S hS) (h08F4 : Tag08F4Input B S hS)
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
    (hEDSc : EDSOfComplSubsetInput B S hS) (hempty : SupportEmptyInput B S hS)
    (hqcO : OpenSubspaceQuasiCompactInput B S hS) (h09IT : Tag09ITInput B S hS)
    (hqsAff : AffineQuasiSeparatedInput B S hS)
    (hex : Affine.Tag06Z0ExactInput B S hS) (hq : Affine.Tag06Z0QcohInput B S hS)
    (h06Z0 : Affine.Tag06Z0Input B S hS) (h07TY : Affine.Tag07TYInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    SumUniverse.SatisfiesPaperWA.{u} (QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) := by
  have h := corollary_1_2 h08FA h08F4 h0AFJ hpb hdisj hres hcounit hperf h08F3 hsum h0AEC
    h0AED h079Q h0A8G hRAC hqcs hcpt h08GGu h08GGc h073B h073B2 h09M8 hbd h09MB hEDSc hempty hqcO
    h09IT hqsAff hex hq h06Z0 h07TY hZ X hXqc hXqs Set.univ isClosed_univ
    (by rw [Set.compl_univ]; exact isCompact_empty)
  let e := (qcSupportedOn X (Set.univ : Set (points B S hS X.1))).ι.asEquivalence
  let : e.functor.CommShift ℤ :=
    (inferInstance : (qcSupportedOn X (Set.univ : Set (points B S hS X.1))).ι.CommShift ℤ)
  have : e.functor.IsTriangulated :=
    (inferInstance : (qcSupportedOn X (Set.univ : Set (points B S hS X.1))).ι.IsTriangulated)
  have : e.functor.Additive :=
    (inferInstance : (qcSupportedOn X (Set.univ : Set (points B S hS X.1))).ι.Additive)
  let := e.commShiftInverse ℤ
  have := e.commShift_of_functor ℤ
  have : e.inverse.IsTriangulated := e.toAdjunction.isTriangulated_rightAdjoint
  exact (SumUniverse.satisfiesPaperWA_iff_of_equivalence e).1 h

end Corollary

/-! ### Non-vacuity -/

section NonVacuity

/-- **Corollary 1.2** (`cor:weak_approx_spaces`), non-vacuity of `corollary_1_2` (CLAUDE.md, verification step 5): for an object `T₀` of the
site with affine, non-empty underlying scheme, the affine algebraic space `X = h_{T₀}` is
non-empty (it has a point), quasi-compact and quasi-separated, the instance arguments hold
(Stacks 06UQ and `SupportTriangulatedInput`), and `X` satisfies W.A. by `corollary_1_2`.  Such a
`T₀` exists: `corollary_1_2_int_witness`. -/
theorem corollary_1_2_nonVacuity (h06 : Tag06UQInput B S hS)
    (hsuppT : SupportTriangulatedInput B S hS) (hterm : ContainsTerminalInput.{u})
    (h08FA : Tag08FAInput B S hS) (h08F4 : Tag08F4Input B S hS)
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
    (hEDSc : EDSOfComplSubsetInput B S hS) (hempty : SupportEmptyInput B S hS)
    (hqcO : OpenSubspaceQuasiCompactInput B S hS) (h09IT : Tag09ITInput B S hS)
    (hqsAff : AffineQuasiSeparatedInput B S hS)
    (hex : Affine.Tag06Z0ExactInput B S hS) (hq : Affine.Tag06Z0QcohInput B S hS)
    (h06Z0 : Affine.Tag06Z0Input B S hS) (h07TY : Affine.Tag07TYInput B S hS)
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (hne : Nonempty ((BigFppfOver.toScheme B S hS).obj T₀)) :
    Nonempty (points B S hS (Affine.space T₀).1) ∧
      IsQuasiCompactSpace B S hS (Affine.space T₀).1 ∧
      IsAbsolutelyQuasiSeparated B S hS (hterm B) (Affine.space T₀).1 ∧
      haveI := isTriangulated_qcohDerived h06 (Affine.space T₀)
      haveI := isTriangulated_support hsuppT (Affine.space T₀)
      SatisfiesWA (Affine.space T₀) := by
  obtain ⟨hqc, hqs', -, -⟩ := nonVacuity_affine_univ hqsAff (hterm B) T₀ hT₀
  have : ∀ Y : AlgebraicSpaces B S hS, (qcohDerived Y).IsTriangulated :=
    fun Y => isTriangulated_qcohDerived h06 Y
  have : ∀ (Y : AlgebraicSpaces B S hS) T,
      ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS Y.1 Y.2 T) :=
    fun Y => isTriangulated_support hsuppT Y
  refine ⟨⟨(schemePointsHomeomorph B S hS T₀).symm hne.some⟩, hqc, hqs', ?_⟩
  exact corollary_1_2 h08FA h08F4 h0AFJ hpb hdisj hres hcounit hperf h08F3 hsum h0AEC
    h0AED h079Q h0A8G hRAC hqcs hcpt h08GGu h08GGc h073B h073B2 h09M8 hbd h09MB hEDSc hempty hqcO
    h09IT hqsAff hex hq h06Z0 h07TY (hterm B) (Affine.space T₀) hqc hqs'

/-- **A witness for `corollary_1_2_nonVacuity`**: some big fppf site contains `Spec ℤ`
(`Affine.Tag021RInput`), and over it the object `Spec ℤ` (`Affine.intObject`) has affine,
non-empty underlying scheme. -/
theorem corollary_1_2_int_witness (h021R : Affine.Tag021RInput.{0}) :
    ∃ (B : BigFppfSite.{0}) (hS : B.Contains (Spec (.of ℤ))),
      IsAffine ((BigFppfOver.toScheme B _ hS).obj (Affine.intObject B hS)) ∧
      Nonempty ((BigFppfOver.toScheme B _ hS).obj (Affine.intObject B hS)) := by
  obtain ⟨B, hS⟩ := h021R (Spec (.of ℤ))
  exact ⟨B, hS, inferInstance, inferInstanceAs (Nonempty (Spec (.of ℤ)))⟩

end NonVacuity

end RelativeFM.Spaces.LP26
