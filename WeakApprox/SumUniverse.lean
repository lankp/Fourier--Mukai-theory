/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.PaperGeneratorM2
import WeakApprox.CompactAb
import WeakApprox.CompactThick

/-!
# Direct sums indexed by a universe independent of the Hom universe

Source: Lank--Pauwels, *Gluing weak approximability along recollements* (LP26), §2.1.2
(`sec:prelim_t-structures_compact_generation`) and Definition 2.1 (`def:weak_approx`).

The repository's `Coprod`, `envelope`, `IsCompactAb`, `PaperWeakApproximationData`,
`SatisfiesPaperWA` and `IsClassicalGeneratorOnCompacts` index direct sums by the Hom universe
`v` of the category.  AxiomMath's derived categories `D(𝒪_X)` have morphisms in
`Type (u + 1)` and direct sums indexed by `Type u` only: a `Type (u + 1)`-indexed direct sum
of `𝒪_X`-modules does not exist.  This file defines the same notions for a **coproduct
universe `w`**, independent of `v`, in the namespace `RelativeWeakApprox.SumUniverse`, and
proves that at `w = v` they are the repository's notions.

## Main definitions

* `SumUniverse.Coprod.{w} P`: the closure of `P` under isomorphisms, `Type w`-indexed
  coproducts and extensions (`Coprod` with `J : Type w`).
* `SumUniverse.envelope.{w} H a b = smd(Coprod.{w}(H[a,b]))`.
* `SumUniverse.IsCompactAb.{w} K`: compactness against `Type w`-indexed direct sums, in the
  form of Stacks 07LS: for every family `E : I → C`, `I : Type w`, with a direct sum, the map
  `⨁ i, (K ⟶ E i) → (K ⟶ ∐ E)`, `(f_i) ↦ ∑ f_i ≫ ι_i`, is bijective.  This is AxiomMath's
  `IsCompactObject.{w}` (bridge in `Spaces/Stacks/Bridges.lean`).
* `SumUniverse.PaperWeakApproximationData.{w} C`, `SumUniverse.SatisfiesPaperWA.{w} C`:
  Definition 2.1 with `IsCompactAb.{w}` and `envelope.{w}`.
* `SumUniverse.IsClassicalGeneratorOnCompacts.{w} G`.

`IsPaperGenerator` (zero detection by the shifts) involves no direct sum and is unchanged.

## Main results

* `coprod_eq`, `envelope_eq`, `isCompactAb_iff`, `satisfiesPaperWA_iff`,
  `isClassicalGeneratorOnCompacts_iff`: at `w = v` the notions are the repository's.
* `isCompactAb_iff_bijective_of_isColimit`: compactness tested on arbitrary colimit cofans.
* `isCompactAb_leftAdjoint_obj`: a left adjoint whose right adjoint is additive and preserves
  `Type w`-indexed coproducts preserves `IsCompactAb.{w}`; the two categories may have
  different Hom universes.  Hence `isCompactAb_functor_obj_iff` (invariance under additive
  equivalences, across Hom universes).

## Assumptions

None.  Mathlib only.
-/

@[expose] public section

namespace RelativeWeakApprox.SumUniverse

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe w v v' u u'

/-! ### Compactness against `Type w`-indexed direct sums -/

section Compact

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **Compactness** against `Type w`-indexed direct sums (Stacks 07LS): for every family
`E : I → C` with `I : Type w` whose direct sum exists, the map
`⨁ i, (K ⟶ E i) → (K ⟶ ∐ E)`, `(f_i) ↦ ∑ f_i ≫ ι_i`, is bijective.  At `w = v` this is the
repository's `RelativeWeakApprox.IsCompactAb` (`isCompactAb_iff`). -/
class IsCompactAb (K : C) : Prop where
  bijective {I : Type w} [DecidableEq I] (E : I → C) [HasCoproduct E] :
    Function.Bijective (DirectSum.toAddMonoid fun i => Preadditive.rightComp K (Sigma.ι E i))

/-- The finite-support comparison map `⨁ i, (K ⟶ f i) → (K ⟶ c.pt)` of a cofan. -/
noncomputable abbrev sumMap (K : C) {I : Type w} [DecidableEq I] {f : I → C} (c : Cofan f) :
    (DirectSum I fun i => (K ⟶ f i)) →+ (K ⟶ c.pt) :=
  DirectSum.toAddMonoid fun i => Preadditive.rightComp K (c.inj i)

/-- Compactness tested on an arbitrary colimit cofan: the comparison map for a colimit cofan
`c` is the one for the chosen coproduct, followed by the isomorphism `∐ f ≅ c.pt`. -/
theorem bijective_sumMap_of_isColimit {K : C} (hK : IsCompactAb.{w} K) {I : Type w}
    [DecidableEq I] {f : I → C} {c : Cofan f} (hc : IsColimit c) :
    Function.Bijective (sumMap K c) := by
  have : HasCoproduct f := ⟨⟨⟨c, hc⟩⟩⟩
  let e : ∐ f ≅ c.pt := colimit.isoColimitCocone ⟨c, hc⟩
  have he : ∀ i, Sigma.ι f i ≫ e.hom = c.inj i := fun i =>
    colimit.isoColimitCocone_ι_hom ⟨c, hc⟩ (Discrete.mk i)
  have hpost : Function.Bijective (Preadditive.rightComp K e.hom) :=
    ⟨fun a b hab => by
        change a ≫ e.hom = b ≫ e.hom at hab
        simpa using congrArg (· ≫ e.inv) hab,
      fun g => ⟨g ≫ e.inv, by change (g ≫ e.inv) ≫ e.hom = g; simp⟩⟩
  have hcomp : (Preadditive.rightComp K e.hom).comp
      (DirectSum.toAddMonoid fun i => Preadditive.rightComp K (Sigma.ι f i)) = sumMap K c := by
    apply DirectSum.addHom_ext
    intro i y
    rw [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of, ← he]
    exact Category.assoc _ _ _
  rw [← hcomp, AddMonoidHom.coe_comp]
  exact hpost.comp (hK.bijective f)

/-- Compactness is the bijectivity of the comparison map for every colimit cofan of every
`Type w`-indexed family. -/
theorem isCompactAb_iff_bijective_of_isColimit (K : C) :
    IsCompactAb.{w} K ↔ ∀ (I : Type w) [DecidableEq I] (f : I → C) (c : Cofan f),
      IsColimit c → Function.Bijective (sumMap K c) := by
  refine ⟨fun hK I _ f c hc => bijective_sumMap_of_isColimit hK hc, fun h => ⟨?_⟩⟩
  intro I _ E _
  exact h I E (Cofan.mk (∐ E) (Sigma.ι E)) (colimit.isColimit (Discrete.functor E))

/-- Bijectivity transfers along a square of additive maps whose vertical maps are additive
equivalences. -/
lemma bijective_of_comm {A B A' B' : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [AddCommMonoid A'] [AddCommMonoid B'] (f : A →+ B) (g : A' →+ B') (α : A' ≃+ A)
    (β : B' ≃+ B) (h : ∀ x, β (g x) = f (α x)) (hf : Function.Bijective f) :
    Function.Bijective g := by
  have hg : ⇑g = β.symm ∘ f ∘ α := funext fun x => by
    simp only [Function.comp_apply, ← h, AddEquiv.symm_apply_apply]
  rw [hg]
  exact β.symm.bijective.comp (hf.comp α.bijective)

lemma mapRange_addEquiv_of {ι : Type*} [DecidableEq ι] {β γ : ι → Type*}
    [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)] (φ : ∀ i, β i ≃+ γ i) (i : ι)
    (y : β i) :
    DFinsupp.mapRange.addEquiv φ (DirectSum.of β i y) = DirectSum.of γ i (φ i y) :=
  DFinsupp.mapRange_single (hf := fun i => map_zero (φ i))

/-- Compactness is invariant under isomorphism. -/
theorem isCompactAb_of_iso {X Y : C} (e : X ≅ Y) (hX : IsCompactAb.{w} X) :
    IsCompactAb.{w} Y := by
  constructor
  intro I _ E _
  let φi : ∀ i, (Y ⟶ E i) ≃+ (X ⟶ E i) := fun i =>
    { toFun := fun g => e.hom ≫ g
      invFun := fun g => e.inv ≫ g
      left_inv := fun g => by simp
      right_inv := fun g => by simp
      map_add' := fun a b => Preadditive.comp_add _ _ _ _ _ _ }
  let ψ : (Y ⟶ ∐ E) ≃+ (X ⟶ ∐ E) :=
    { toFun := fun g => e.hom ≫ g
      invFun := fun g => e.inv ≫ g
      left_inv := fun g => by simp
      right_inv := fun g => by simp
      map_add' := fun a b => Preadditive.comp_add _ _ _ _ _ _ }
  refine bijective_of_comm _ _ (DFinsupp.mapRange.addEquiv φi) ψ (fun x => ?_) (hX.bijective E)
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i g =>
    rw [mapRange_addEquiv_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    exact (Category.assoc _ _ _).symm
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- Zero objects are compact. -/
theorem isCompactAb_of_isZero {X : C} (hX : IsZero X) : IsCompactAb.{w} X := by
  constructor
  intro I _ E _
  have : ∀ Y : C, Subsingleton (X ⟶ Y) := fun Y => ⟨fun a b => hX.eq_of_src a b⟩
  have : Subsingleton (DirectSum I fun i => (X ⟶ E i)) :=
    ⟨fun a b => DFinsupp.ext fun i => Subsingleton.elim _ _⟩
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun g => ⟨0, Subsingleton.elim _ _⟩⟩

variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- **Compactness along an adjunction**, across Hom universes: if `F ⊣ G` with `G` additive and
preserving `Type w`-indexed coproducts, then `F` sends compact objects to compact objects.
The Hom groups `F X ⟶ E i` and `X ⟶ G E i` are identified by the adjunction, naturally in
`E i`, and `G` carries the direct sum of `E` to a direct sum of the `G E i`. -/
theorem isCompactAb_leftAdjoint_obj {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Additive]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) G] {X : C}
    (hX : IsCompactAb.{w} X) : IsCompactAb.{w} (F.obj X) := by
  constructor
  intro I _ E _
  let c : Cofan E := Cofan.mk (∐ E) (Sigma.ι E)
  have hc : IsColimit c := colimit.isColimit (Discrete.functor E)
  let cG : Cofan (fun i => G.obj (E i)) := Cofan.mk (G.obj c.pt) fun i => G.map (c.inj i)
  have hcG : IsColimit cG :=
    (Cofan.isColimitMapCoconeEquiv G E c) (isColimitOfPreserves G hc)
  let φi : ∀ i, (F.obj X ⟶ E i) ≃+ (X ⟶ G.obj (E i)) := fun i =>
    { adj.homEquiv X (E i) with
      map_add' := fun a b => by
        simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit, G.map_add,
          Preadditive.comp_add] }
  let ψ : (F.obj X ⟶ ∐ E) ≃+ (X ⟶ G.obj (∐ E)) :=
    { adj.homEquiv X (∐ E) with
      map_add' := fun a b => by
        simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit, G.map_add,
          Preadditive.comp_add] }
  refine bijective_of_comm _ _ (DFinsupp.mapRange.addEquiv φi) ψ (fun x => ?_) (bijective_sumMap_of_isColimit hX hcG)
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i g =>
    rw [mapRange_addEquiv_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    exact adj.homEquiv_naturality_right g (Sigma.ι E i)
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- **Compactness is invariant under additive equivalences**, across Hom universes. -/
theorem isCompactAb_functor_obj_iff (e : C ≌ D) [e.functor.Additive] (X : C) :
    IsCompactAb.{w} (e.functor.obj X) ↔ IsCompactAb.{w} X := by
  have : e.inverse.Additive := e.toAdjunction.right_adjoint_additive
  have : ∀ J : Type w, PreservesColimitsOfShape (Discrete J) e.inverse := fun _ =>
    e.symm.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : ∀ J : Type w, PreservesColimitsOfShape (Discrete J) e.functor := fun _ =>
    e.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : e.symm.inverse.Additive := inferInstanceAs e.functor.Additive
  have : ∀ J : Type w, PreservesColimitsOfShape (Discrete J) e.symm.inverse := fun J =>
    inferInstanceAs (PreservesColimitsOfShape (Discrete J) e.functor)
  constructor
  · intro h
    exact isCompactAb_of_iso (e.unitIso.app X).symm
      (isCompactAb_leftAdjoint_obj e.symm.toAdjunction h)
  · exact isCompactAb_leftAdjoint_obj e.toAdjunction

/-- The image `Hom(K, -)` of a cofan, as a cofan of abelian groups. -/
noncomputable abbrev homCofan (K : C) {J : Type v} {f : J → C} (c : Cofan f) :
    Cofan fun j => (preadditiveCoyoneda.obj (Opposite.op K)).obj (f j) :=
  Cofan.mk ((preadditiveCoyoneda.obj (Opposite.op K)).obj c.pt)
    fun j => (preadditiveCoyoneda.obj (Opposite.op K)).map (c.inj j)

/-- The finite-support comparison map of `homCofan K c` is `sumMap K c`. -/
lemma abCofanSum_homCofan_hom (K : C) {J : Type v} [DecidableEq J] {f : J → C}
    (c : Cofan f) : (abCofanSum (homCofan K c)).hom = sumMap K c := by
  apply DirectSum.addHom_ext
  intro j y
  exact (abCofanSum_single (homCofan K c) j y).trans
    (DirectSum.toAddMonoid_of (fun j => Preadditive.rightComp K (c.inj j)) j y).symm

/-- **At `w = v`, `IsCompactAb.{v}` is the repository's `IsCompactAb`** (the
`AddCommGrpCat`-valued `Hom(K, -)` preserves `Type v`-indexed coproducts).  The comparison of a
colimit cofan of abelian groups with the finite-support direct sum is
`bijective_abCofanSum_of_isColimit` and `isColimitCofan_of_bijective_abCofanSum`
(`WeakApprox/CompactAb.lean`). -/
theorem isCompactAb_iff (K : C) : IsCompactAb.{v} K ↔ RelativeWeakApprox.IsCompactAb K := by
  constructor
  · intro hK
    constructor
    intro J
    classical
    have : ∀ f : J → C,
        PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (Opposite.op K)) := by
      intro f
      refine ⟨fun {c} hc => ⟨?_⟩⟩
      let c' : Cofan f := c
      have hc' : IsColimit c' := hc
      refine (Cofan.isColimitMapCoconeEquiv _ f c').symm ?_
      refine isColimitCofan_of_bijective_abCofanSum (homCofan K c') ?_
      change Function.Bijective (abCofanSum (homCofan K c')).hom
      rw [abCofanSum_homCofan_hom]
      exact bijective_sumMap_of_isColimit hK hc'
    exact preservesColimitsOfShape_of_discrete _
  · intro hK
    refine (isCompactAb_iff_bijective_of_isColimit K).2 fun I _ E c hc => ?_
    have h := (Cofan.isColimitMapCoconeEquiv (preadditiveCoyoneda.obj (Opposite.op K)) E c)
      (isColimitOfPreserves (preadditiveCoyoneda.obj (Opposite.op K)) hc)
    have hb : Function.Bijective (abCofanSum (homCofan K c)).hom :=
      bijective_abCofanSum_of_isColimit h
    rwa [abCofanSum_homCofan_hom] at hb

end Compact

/-! ### Coproduct closure and envelopes with `Type w`-indexed coproducts -/

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The smallest strictly full object property containing `P` and closed under `Type w`-indexed
coproducts and extensions.  At `w = v` it is the repository's `Coprod P` (`coprod_eq`). -/
inductive Coprod (P : ObjectProperty C) : ObjectProperty C where
  | of_mem (X : C) (hX : P X) : Coprod P X
  | of_isoClosure {X Y : C} (e : X ≅ Y) (hX : Coprod P X) : Coprod P Y
  | of_colimitPresentation {X : C} {J : Type w} (pres : ColimitPresentation (Discrete J) X)
      (h : ∀ j, Coprod P (pres.diag.obj j)) : Coprod P X
  | of_extension (T : Triangle C) (hT : T ∈ distTriang C)
      (h₁ : Coprod P T.obj₁) (h₃ : Coprod P T.obj₃) : Coprod P T.obj₂

namespace Coprod

variable {P : ObjectProperty C}

instance : (Coprod.{w} P).IsClosedUnderIsomorphisms where
  of_iso e hX := .of_isoClosure e hX

instance (J : Type w) : (Coprod.{w} P).IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := by
    rintro X ⟨hX⟩
    exact .of_colimitPresentation (J := J) hX.toColimitPresentation hX.prop_diag_obj

instance : (Coprod.{w} P).IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := (Coprod.{w} P).le_isoClosure _ (.of_extension T hT h₁ h₃)

lemma le_coprod : P ≤ Coprod.{w} P := fun X hX => .of_mem X hX

/-- Monotonicity. -/
lemma monotone {P Q : ObjectProperty C} (h : P ≤ Q) : Coprod.{w} P ≤ Coprod.{w} Q := by
  intro X hX
  induction hX with
  | of_mem X hX => exact .of_mem X (h X hX)
  | of_isoClosure e _ ih => exact .of_isoClosure e ih
  | of_colimitPresentation pres _ ih => exact .of_colimitPresentation pres ih
  | of_extension T hT _ _ ih₁ ih₃ => exact .of_extension T hT ih₁ ih₃

/-- Universal property. -/
lemma le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    [∀ (J : Type w), Q.IsClosedUnderColimitsOfShape (Discrete J)]
    [Q.IsTriangulatedClosed₂] (h : P ≤ Q) : Coprod.{w} P ≤ Q := by
  intro X hX
  induction hX with
  | of_mem X hX => exact h X hX
  | of_isoClosure e hX ih => exact Q.prop_of_iso e ih
  | of_colimitPresentation pres hmem ih => exact Q.prop_of_isColimit pres.isColimit ih
  | of_extension T hT h₁ h₃ ih₁ ih₃ => exact Q.ext_of_isTriangulatedClosed₂ T hT ih₁ ih₃

/-- A chosen `Type w`-indexed coproduct of members is a member. -/
lemma of_sigma {ι : Type w} (f : ι → C) [HasCoproduct f]
    (hf : ∀ i, Coprod.{w} P (f i)) : Coprod.{w} P (∐ f) :=
  .of_colimitPresentation (.colimit (Discrete.functor f)) (fun j => hf j.as)

end Coprod

/-- **At `w = v`, `Coprod.{v}` is the repository's `Coprod`.** -/
theorem coprod_eq (P : ObjectProperty C) : Coprod.{v} P = RelativeWeakApprox.Coprod P :=
  le_antisymm (Coprod.le RelativeWeakApprox.Coprod.le_coprod)
    (RelativeWeakApprox.Coprod.le Coprod.le_coprod)

/-- `⟨H⟩^[a,b] = smd(Coprod.{w}(H[a,b]))`, with `Type w`-indexed coproducts. -/
def envelope (H : C) (a b : ℤ) : ObjectProperty C :=
  ObjectProperty.retractClosure (Coprod.{w} (shiftInterval H a b))

/-- **At `w = v`, `envelope.{v}` is the repository's `envelope`.** -/
theorem envelope_eq (H : C) (a b : ℤ) : envelope.{v} H a b = RelativeWeakApprox.envelope H a b := by
  rw [envelope, RelativeWeakApprox.envelope, coprod_eq]

/-! ### Definition 2.1 with `Type w`-indexed coproducts -/

variable (C) in
/-- **Definition 2.1** (`def:weak_approx`) with zero detection, for a coproduct universe `w`:
the fields of `RelativeWeakApprox.PaperM2.PaperWeakApproximationData`, with `IsCompactAb.{w}`
and `envelope.{w}`.  At `w = v` it is that structure (`paperData_equiv`). -/
structure PaperWeakApproximationData where
  /-- the compact generator -/
  G : C
  /-- the `t`-structure -/
  t : TStructure C
  /-- the bound -/
  A : ℤ
  A_pos : 0 < A
  G_compact : IsCompactAb.{w} G
  G_paperGenerates : IsPaperGenerator G
  G_mem_le : t.le A G
  hom_vanishing : ∀ {Y : C}, t.le (-A) Y → ∀ f : G ⟶ Y, f = 0
  exists_triangle : ∀ F : C, t.le 0 F →
    ∃ (E D : C) (f : E ⟶ F) (g : F ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ envelope.{w} G (-A) A E ∧ t.le (-1) D

variable (C) in
/-- **Weak approximability** (Definition 2.1, `def:weak_approx`) for a coproduct universe
`w`. -/
def SatisfiesPaperWA : Prop :=
  Nonempty (PaperWeakApproximationData.{w} C)

/-- At `w = v`, weak approximation data are the repository's `PaperWeakApproximationData`. -/
def paperData_equiv :
    PaperWeakApproximationData.{v} C ≃ PaperM2.PaperWeakApproximationData C where
  toFun W :=
    { G := W.G, t := W.t, A := W.A, A_pos := W.A_pos
      G_compact := (isCompactAb_iff W.G).1 W.G_compact
      G_paperGenerates := W.G_paperGenerates
      G_mem_le := W.G_mem_le
      hom_vanishing := W.hom_vanishing
      exists_triangle := fun F hF => by
        obtain ⟨E, D, f, g, h, hT, hE, hD⟩ := W.exists_triangle F hF
        exact ⟨E, D, f, g, h, hT, by rwa [← envelope_eq], hD⟩ }
  invFun W :=
    { G := W.G, t := W.t, A := W.A, A_pos := W.A_pos
      G_compact := (isCompactAb_iff W.G).2 W.G_compact
      G_paperGenerates := W.G_paperGenerates
      G_mem_le := W.G_mem_le
      hom_vanishing := W.hom_vanishing
      exists_triangle := fun F hF => by
        obtain ⟨E, D, f, g, h, hT, hE, hD⟩ := W.exists_triangle F hF
        exact ⟨E, D, f, g, h, hT, by rwa [envelope_eq], hD⟩ }
  left_inv _ := rfl
  right_inv _ := rfl

variable (C) in
/-- **At `w = v`, weak approximability is the repository's `SatisfiesPaperWA`.** -/
theorem satisfiesPaperWA_iff : SatisfiesPaperWA.{v} C ↔ PaperM2.SatisfiesPaperWA C :=
  ⟨fun ⟨W⟩ => ⟨paperData_equiv W⟩, fun ⟨W⟩ => ⟨paperData_equiv.symm W⟩⟩

/-- Classical generation of the compact objects, for a coproduct universe `w`: every
`IsCompactAb.{w}` object lies in the triangulated envelope of `G`.  At `w = v` it is the
repository's `IsClassicalGeneratorOnCompacts` (`isClassicalGeneratorOnCompacts_iff`). -/
def IsClassicalGeneratorOnCompacts (G : C) : Prop :=
  ∀ X : C, IsCompactAb.{w} X → (ObjectProperty.singleton G).triangEnvelope X

/-- At `w = v`, classical generation of the compacts is the repository's notion. -/
theorem isClassicalGeneratorOnCompacts_iff (G : C) :
    IsClassicalGeneratorOnCompacts.{v} G ↔ RelativeWeakApprox.IsClassicalGeneratorOnCompacts G :=
  forall_congr' fun X => by rw [isCompactAb_iff]

end RelativeWeakApprox.SumUniverse

#print axioms RelativeWeakApprox.SumUniverse.isCompactAb_iff
#print axioms RelativeWeakApprox.SumUniverse.isCompactAb_functor_obj_iff
#print axioms RelativeWeakApprox.SumUniverse.coprod_eq
#print axioms RelativeWeakApprox.SumUniverse.envelope_eq
#print axioms RelativeWeakApprox.SumUniverse.satisfiesPaperWA_iff
#print axioms RelativeWeakApprox.SumUniverse.isClassicalGeneratorOnCompacts_iff
