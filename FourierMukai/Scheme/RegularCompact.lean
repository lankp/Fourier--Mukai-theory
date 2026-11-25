/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.AffineCompactness
import FourierMukai.Scheme.AffineSpaltenstein

/-!
# Compactness of the regular module in the standard affine derived category

`ringObject_isCompactAb` proves `IsCompactAb (ringObject A)` in
`AffineD A = D(A-Mod)` (standard localization), with no hypothesis.  This is the
input `hAc` that the affine and supported-affine endpoints carried (README,
"What is open" item 1); it was previously obtained only from Neeman's input
(`ringObject_compact_of_compactPerfectInput`).  The fact is classical (the
regular module is a compact generator of `D(A)`; e.g. Neeman, Acta Math. 233
(2024), Thm 3.2 for `X = Spec A`), but the proof here uses neither Stacks nor
Neeman.

## The model question

With `A : Type u`, `ModuleCat.{u} A : Type (u+1)` and the standard localization
`AffineD A` has Homs in `Type (u+1)`, so `IsCompactAb` in `AffineD A` asks
`Hom(A[0], -)` to preserve every `Type (u+1)`-indexed coproduct **that exists**.
This is neither vacuous nor a different notion from the expected one:

* `small_nonzeroSupport` (audit): since `AffineD A` is `LocallySmall.{u}`, any
  existing coproduct, of any index size, has a `u`-small set of nonzero
  summands; the subsets of that support inject into `End(∐ Xⱼ)`.
* `factorsFinitelyOfSize_enlarge`: hence any such coproduct is a retract of a
  `Type u`-indexed coproduct, and these exist (`affineHasCoproductsOfUnivLE`).

So the statement in `AffineD A` is equivalent in substance to preservation of
`u`-small coproducts, which is the statement `NeemanM1.smallRingObject_isCompactAb`
proves in the small-Hom model `SmallAffineD A H`.  Both models carry a
meaningful statement; the endpoints may stay in `AffineD A`.

## Route

`FactorsFinitely H c` says every `H ⟶ ∐ Xⱼ` is a finite sum of maps through
single legs; it is universe-agnostic in the index type.
`isCompactAb_iff_factorsFinitelyOfSize` identifies `IsCompactAb` with it at the
Hom universe (injectivity of `⊕ Hom(H, Xⱼ) → Hom(H, ∐ Xⱼ)` is automatic, by
coproduct projections).  It is transported along `AffineD A ≌ SmallAffineD A H`
(`factorsFinitelyOfSize_of_equivalence`, with `ringObjectEquivIso`), then
enlarged from `Type u` to `Type (u+1)` indices.  Spaltenstein replacements come
from `Spaltenstein.affineSpaltensteinInput` (proved).

Assumptions: none.  No deviation from the paper's statement.
-/

@[expose] public section

namespace RelativeFM.RegularCompact

open CategoryTheory CategoryTheory.Limits
open RelativeWeakApprox

universe w v v' u u'

noncomputable section

section General

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The morphisms `H ⟶ c.pt` that factor through a single leg of a cofan. -/
def legMaps (H : C) {J : Type w} {X : J → C} (c : Cofan X) : Set (H ⟶ c.pt) :=
  {p | ∃ (j : J) (x : H ⟶ X j), p = x ≫ c.inj j}

/-- Every morphism `H ⟶ c.pt` is a finite sum of morphisms through single legs.
This is the surjectivity half of `⊕ⱼ Hom(H, Xⱼ) → Hom(H, ∐ Xⱼ)`; it makes sense
for an index type in any universe. -/
def FactorsFinitely (H : C) {J : Type w} {X : J → C} (c : Cofan X) : Prop :=
  ∀ q : H ⟶ c.pt, q ∈ AddSubgroup.closure (legMaps H c)

/-- `H` factors finitely through every colimit cofan indexed by `Type w`. -/
def FactorsFinitelyOfSize (H : C) : Prop :=
  ∀ (J : Type w) (X : J → C) (c : Cofan X), IsColimit c → FactorsFinitely H c

/-- Compactness gives finite factorization through coproducts indexed in the
Hom universe. -/
theorem factorsFinitelyOfSize_of_isCompactAb (H : C) [IsCompactAb H] :
    FactorsFinitelyOfSize.{v} H := by
  classical
  intro J X c hc q
  have : PreservesColimitsOfShape (Discrete J) (abCoyoneda H) :=
    preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive H).symm
  let c' : Cofan (fun j => (abCoyoneda H).obj (X j)) :=
    Cofan.mk ((abCoyoneda H).obj c.pt) (fun j => (abCoyoneda H).map (c.inj j))
  have hc' : IsColimit c' :=
    (Cofan.isColimitMapCoconeEquiv (abCoyoneda H) X c)
      (isColimitOfPreserves (abCoyoneda H) hc)
  obtain ⟨z, rfl⟩ := (bijective_abCofanSum_of_isColimit hc').2 q
  induction z using DFinsupp.induction with
  | h0 => simp [(AddSubgroup.closure (legMaps H c)).zero_mem]
  | ha j x z _ _ ih =>
    rw [map_add]
    refine AddSubgroup.add_mem _ (AddSubgroup.subset_closure ?_) ih
    exact ⟨j, x, by rw [abCofanSum_single]; rfl⟩

/-- Conversely, finite factorization through all `Type v` coproducts gives
compactness; injectivity of the comparison map is automatic (coproduct
projections). -/
theorem isCompactAb_of_factorsFinitelyOfSize (H : C) (h : FactorsFinitelyOfSize.{v} H) :
    IsCompactAb H := by
  constructor
  intro J
  classical
  have : PreservesColimitsOfShape (Discrete J) (abCoyoneda H) := by
    have : ∀ (f : J → C), PreservesColimit (Discrete.functor f) (abCoyoneda H) :=
      fun f =>
        { preserves := fun {c} hc => ⟨by
            let g : ∀ j, f j ⟶ c.pt := fun j => c.ι.app (Discrete.mk j)
            let c0 : Cofan f := Cofan.mk c.pt g
            let e : c0 ≅ c := Cocone.ext (Iso.refl _) (by
              intro j
              cases j
              simp [c0, g])
            have hc0 : IsColimit c0 := hc.ofIsoColimit e.symm
            let d : Cofan (fun j => (abCoyoneda H).obj (f j)) :=
              Cofan.mk ((abCoyoneda H).obj c.pt) (fun j => (abCoyoneda H).map (g j))
            have hd : IsColimit d := by
              apply isColimitCofan_of_bijective_abCofanSum d
              constructor
              · intro x y hxy
                ext j
                let p : c.pt ⟶ f j := coproductProjection g hc0 j
                let post : (H ⟶ c.pt) →+ (H ⟶ f j) := ((abCoyoneda H).map p).hom
                have eval (z : DFinsupp (fun k => H ⟶ f k)) :
                    (abCofanSum d z) ≫ p = z j := by
                  have hz := post.map_dfinsuppSumAddHom z (fun k => (d.inj k).hom)
                  calc
                    (abCofanSum d z) ≫ p =
                        post ((DFinsupp.sumAddHom fun k => (d.inj k).hom) z) := rfl
                    _ = (DFinsupp.sumAddHom fun k => post.comp (d.inj k).hom) z := hz
                    _ = z j := by
                      have hfun : (fun k => post.comp (d.inj k).hom) =
                          Pi.single j (AddMonoidHom.id (H ⟶ f j)) := by
                        funext k
                        by_cases hk : k = j
                        · subst k
                          ext q
                          simp [post, p, d]
                        · ext q
                          simp [post, p, d, hk]
                      rw [hfun, DFinsupp.sumAddHom_piSingle]
                      rfl
                have hz := congrArg (fun q : H ⟶ c.pt => q ≫ p) hxy
                rwa [eval x, eval y] at hz
              · intro q
                have hq : q ∈ (abCofanSum d).hom.range := by
                  refine (AddSubgroup.closure_le _).2 ?_ (h J f c0 hc0 q)
                  rintro _ ⟨j, x, rfl⟩
                  exact ⟨DFinsupp.single j x, by rw [abCofanSum_single]; rfl⟩
                exact hq
            exact (Cofan.isColimitMapCoconeEquiv (abCoyoneda H) f c).symm hd⟩ }
    exact preservesColimitsOfShape_of_discrete _
  exact preservesColimitsOfShape_of_natIso (abCoyonedaIsoPreadditive H)

/-- `IsCompactAb` is exactly finite factorization through `Type v` coproducts. -/
theorem isCompactAb_iff_factorsFinitelyOfSize (H : C) :
    IsCompactAb H ↔ FactorsFinitelyOfSize.{v} H :=
  ⟨fun _ => factorsFinitelyOfSize_of_isCompactAb H, isCompactAb_of_factorsFinitelyOfSize H⟩

end General

section Transport

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Finite factorization is invariant under isomorphism of the source. -/
theorem factorsFinitely_of_iso {H H' : C} (e : H ≅ H') {J : Type w} {X : J → C}
    {c : Cofan X} (h : FactorsFinitely H c) : FactorsFinitely H' c := by
  intro q
  let φ : (H ⟶ c.pt) →+ (H' ⟶ c.pt) :=
    { toFun := fun p => e.inv ≫ p
      map_zero' := comp_zero
      map_add' := fun _ _ => Preadditive.comp_add _ _ _ _ _ _ }
  have hq : q = φ (e.hom ≫ q) := by simp [φ]
  rw [hq, ← AddSubgroup.mem_comap]
  refine (AddSubgroup.closure_le _).2 ?_ (h (e.hom ≫ q))
  rintro _ ⟨j, x, rfl⟩
  refine AddSubgroup.subset_closure ⟨j, e.inv ≫ x, ?_⟩
  simp [φ]

variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- Finite factorization through coproducts of a fixed index size is reflected
along an equivalence, even when the two categories have different Hom
universes. -/
theorem factorsFinitelyOfSize_of_equivalence (E : C ≌ D) [E.functor.Additive] (H : C) (H' : D)
    (i : E.functor.obj H ≅ H') (h : FactorsFinitelyOfSize.{w} H') :
    FactorsFinitelyOfSize.{w} H := by
  intro J X c hc q
  let F := E.functor
  let d : Cofan (fun j => F.obj (X j)) := Cofan.mk (F.obj c.pt) (fun j => F.map (c.inj j))
  have hd : IsColimit d :=
    (Cofan.isColimitMapCoconeEquiv F X c) (isColimitOfPreserves F hc)
  have hF : FactorsFinitely (F.obj H) d :=
    factorsFinitely_of_iso i.symm (h J _ d hd)
  let ψ : (F.obj H ⟶ F.obj c.pt) →+ (H ⟶ c.pt) :=
    { toFun := fun p => F.preimage p
      map_zero' := by
        apply F.map_injective
        simp
      map_add' := fun a b => by
        apply F.map_injective
        simp }
  have hq : q = ψ (F.map q) := by simp [ψ]
  rw [hq, ← AddSubgroup.mem_comap]
  refine (AddSubgroup.closure_le _).2 ?_ (hF (F.map q))
  rintro _ ⟨j, x, rfl⟩
  refine AddSubgroup.subset_closure ⟨j, F.preimage x, ?_⟩
  apply F.map_injective
  simp [ψ, d]

end Transport

section Enlarge

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **Audit lemma.**  In a category whose Hom sets are `w`-small, the summands
of any existing coproduct that are not zero form a `w`-small set, whatever the
universe of the index type.  The subsets `S` of the nonzero support inject into
`End (∐ Xⱼ)` by `S ↦ (idempotent projecting onto the summands in S)`. -/
theorem small_nonzeroSupport [LocallySmall.{w} C] {J : Type v} {X : J → C}
    (c : Cofan X) (hc : IsColimit c) :
    Small.{w} {j : J // ¬ IsZero (X j)} := by
  classical
  let T := {j : J // ¬ IsZero (X j)}
  let e : Set T → (c.pt ⟶ c.pt) := fun S =>
    Cofan.IsColimit.desc hc fun j =>
      if h : ¬ IsZero (X j) then (if (⟨j, h⟩ : T) ∈ S then c.inj j else 0) else 0
  have hc' : IsColimit (Cofan.mk c.pt c.inj) :=
    hc.ofIsoColimit (Cocone.ext (Iso.refl _) (by rintro ⟨j⟩; simp; rfl))
  have he : Function.Injective e := by
    intro S S' hSS'
    ext ⟨j, hj⟩
    let p := coproductProjection c.inj hc' j
    have key : ∀ S : Set T, c.inj j ≫ e S ≫ p =
        if (⟨j, hj⟩ : T) ∈ S then 𝟙 _ else 0 := by
      intro S
      rw [← Category.assoc]
      simp only [e, Cofan.IsColimit.fac]
      by_cases hS : (⟨j, hj⟩ : T) ∈ S
      · simp [hS, hj, p]
      · simp [hS, hj]
    have h := (key S).symm.trans
      ((congrArg (fun m => c.inj j ≫ m ≫ p) hSS').trans (key S'))
    have hid : (𝟙 (X j)) ≠ 0 := fun h0 => hj ((IsZero.iff_id_eq_zero _).2 h0)
    by_cases hS : (⟨j, hj⟩ : T) ∈ S <;> by_cases hS' : (⟨j, hj⟩ : T) ∈ S'
    · exact iff_of_true hS hS'
    · rw [if_pos hS, if_neg hS'] at h
      exact absurd h hid
    · rw [if_neg hS, if_pos hS'] at h
      exact absurd h.symm hid
    · exact iff_of_false hS hS'
  have : Small.{w} (Set T) := small_of_injective he
  exact small_of_injective (f := fun t : T => ({t} : Set T)) Set.singleton_injective


omit [Preadditive C] in
/-- Composing a leg with an `eqToHom` along an equality of indices. -/
lemma eqToHom_comp_inj {J : Type v} {X : J → C} (c : Cofan X) {a b : J} (hab : a = b) :
    eqToHom (congrArg X hab) ≫ c.inj b = c.inj a := by
  subst hab
  simp

/-- **Universe enlargement.**  If Hom sets are `w`-small and `Type w`-indexed
coproducts exist, finite factorization through all `Type w` coproducts implies
finite factorization through every coproduct indexed in the Hom universe `v`
that exists: such a coproduct is a retract of the coproduct over its `w`-small
nonzero support (`small_nonzeroSupport`). -/
theorem factorsFinitelyOfSize_enlarge [LocallySmall.{w} C] [HasCoproducts.{w} C]
    (H : C) (h : FactorsFinitelyOfSize.{w} H) : FactorsFinitelyOfSize.{v} H := by
  classical
  intro J X c hc q
  let T := {j : J // ¬ IsZero (X j)}
  have : Small.{w} T := small_nonzeroSupport c hc
  let g : Shrink.{w} T → J := fun k => ((equivShrink T).symm k).1
  let Y : Shrink.{w} T → C := fun k => X (g k)
  let φ : ∐ Y ⟶ c.pt := Sigma.desc fun k => c.inj (g k)
  have hg : ∀ (j : J) (hj : ¬ IsZero (X j)), g (equivShrink T ⟨j, hj⟩) = j := by
    intro j hj
    simp [g]
  let ψ : c.pt ⟶ ∐ Y := Cofan.IsColimit.desc hc fun j =>
    if hj : ¬ IsZero (X j) then
      eqToHom (congrArg X (hg j hj).symm) ≫ Sigma.ι Y (equivShrink T ⟨j, hj⟩)
    else 0
  have hψφ : ψ ≫ φ = 𝟙 c.pt := by
    apply Cofan.IsColimit.hom_ext hc
    intro j
    rw [← Category.assoc, Cofan.IsColimit.fac, Category.comp_id]
    by_cases hj : ¬ IsZero (X j)
    · rw [dif_pos hj, Category.assoc, Sigma.ι_desc]
      exact eqToHom_comp_inj c (hg j hj).symm
    · exact (not_not.1 hj).eq_of_src _ _
  let d : Cofan Y := Cofan.mk (∐ Y) (Sigma.ι Y)
  have hd : IsColimit d := coproductIsCoproduct Y
  let post : (H ⟶ ∐ Y) →+ (H ⟶ c.pt) :=
    { toFun := fun p => p ≫ φ
      map_zero' := zero_comp
      map_add' := fun _ _ => Preadditive.add_comp _ _ _ _ _ _ }
  have hq : q = post (q ≫ ψ) := by simp [post, hψφ]
  rw [hq, ← AddSubgroup.mem_comap]
  refine (AddSubgroup.closure_le _).2 ?_ (h _ Y d hd (q ≫ ψ))
  rintro _ ⟨k, x, rfl⟩
  refine AddSubgroup.subset_closure ⟨g k, x, ?_⟩
  simp [post, d, φ]

end Enlarge

section Affine

open RelativeFM RelativeFM.UniverseDecision

/-- The standard-model regular module is carried to the small-model regular
module by the comparison equivalence `AffineD A ≌ SmallAffineD A H`. -/
noncomputable def ringObjectEquivIso (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) :
    (affineDEquivSmallAffineD A H).functor.obj (ringObject A) ≅ smallRingObject A H := by
  let small : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    hasDerivedCategoryOfKProjectiveReplacementData H
  let M : ModuleCat.{u} A := ModuleCat.of A A
  let K := (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj M
  exact (affineDEquivSmallAffineD A H).functor.mapIso
      ((@DerivedCategory.singleFunctorIsoCompQ _ _ _
        (HasDerivedCategory.standard _) 0).app M) ≪≫
    (Localization.compUniqFunctor
      (@DerivedCategory.Q (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
      (@DerivedCategory.Q (ModuleCat.{u} A) _ _ small)
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ))).app K ≪≫
    ((@DerivedCategory.singleFunctorIsoCompQ _ _ _ small 0).app M).symm

/-- `Hom(A, -)` on the standard model factors finitely through every
`Type u`-indexed coproduct. -/
theorem ringObject_factorsFinitelyOfSize_small (A : Type u) [CommRing A] :
    FactorsFinitelyOfSize.{u} (ringObject A) := by
  let H := Spaltenstein.affineSpaltensteinInput A
  have hs : FactorsFinitelyOfSize.{u} (smallRingObject A H) :=
    have := NeemanM1.smallRingObject_isCompactAb A H
    factorsFinitelyOfSize_of_isCompactAb _
  have : (affineDEquivSmallAffineD A H).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  exact factorsFinitelyOfSize_of_equivalence (affineDEquivSmallAffineD A H)
    (ringObject A) (smallRingObject A H) (ringObjectEquivIso A H) hs

attribute [local instance] HasDerivedCategory.standard in
/-- **Regular-module compactness in the standard model, unconditionally.**
`A[0]` is `IsCompactAb` in `AffineD A = D(A-Mod)` with its standard
localization (Hom universe `u+1`), i.e. `Hom(A[0], -)` preserves every
`Type (u+1)`-indexed coproduct that exists.  No Stacks input and no Neeman
input: Spaltenstein replacements (`affineSpaltensteinInput`) give the
small-Hom model, `NeemanM1.smallRingObject_isCompactAb` gives compactness
there, the comparison equivalence transports it to `Type u` coproducts in
`AffineD A`, and `factorsFinitelyOfSize_enlarge` passes to `Type (u+1)`. -/
theorem ringObject_isCompactAb (A : Type u) [CommRing A] :
    IsCompactAb (ringObject A) := by
  let H := Spaltenstein.affineSpaltensteinInput A
  have : LocallySmall.{u} (AffineD A) := locallySmallDerivedCategoryOfKProjectiveReplacementData H
  have : HasCoproducts.{u} (AffineD A) := affineHasCoproductsOfUnivLE A H
  exact isCompactAb_of_factorsFinitelyOfSize _
    (factorsFinitelyOfSize_enlarge _ (ringObject_factorsFinitelyOfSize_small A))

attribute [local instance] HasDerivedCategory.standard in
/-- **Non-vacuity audit.**  `IsCompactAb` in `AffineD A` tests `Type (u+1)`-indexed
coproducts, and nontrivial ones exist: the countable coproduct of copies of
`A[0]`, indexed by `ULift.{u+1} ℕ`. -/
theorem hasCoproduct_ringObject_ulift_nat (A : Type u) [CommRing A] :
    HasCoproduct (fun _ : ULift.{u+1} ℕ => ringObject A) := by
  have : HasCoproducts.{u} (AffineD A) :=
    affineHasCoproductsOfUnivLE A (Spaltenstein.affineSpaltensteinInput A)
  exact hasColimit_of_equivalence_comp (Discrete.equivalence Equiv.ulift.symm)

end Affine

end

end RelativeFM.RegularCompact

#print axioms RelativeFM.RegularCompact.isCompactAb_iff_factorsFinitelyOfSize
#print axioms RelativeFM.RegularCompact.factorsFinitelyOfSize_of_equivalence
#print axioms RelativeFM.RegularCompact.small_nonzeroSupport
#print axioms RelativeFM.RegularCompact.factorsFinitelyOfSize_enlarge
#print axioms RelativeFM.RegularCompact.ringObjectEquivIso
#print axioms RelativeFM.RegularCompact.ringObject_isCompactAb
#print axioms RelativeFM.RegularCompact.hasCoproduct_ringObject_ulift_nat
