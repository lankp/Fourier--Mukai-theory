/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Supported.DetectingInputs

/-!
# The supported form of Stacks 0GFI

GL26 **Lemma A.9** (`lem:preferred_eq_class`), preferred-class clause, needs the supported form of
Stacks 0GFI ((7) ⇒ (1)) on `D_{QCoh,T}(𝒪_X)`: for `X` quasi-compact and quasi-separated and
`T ⊆ |X|` closed with `X ∖ T ⟶ X` quasi-compact, an object `E` of `D_QCoh(𝒪_X)` supported on `T`
such that `Hom(P[-i], E) = 0` for `i ≪ 0` for every perfect `P` supported on `T` is bounded below.
AxiomMath proves 0GFI for `D_QCoh(𝒪_X)` only (`exists_isGE_of_lowHomVanishingOnCompact`).

## What is proved

* `suppDetectsBelow`: the statement above (`SuppDetectsBelow X T`), for every such `(X, T)`.

## The proof

The induction of AxiomMath's proof of 0GFI over elementary distinguished squares (Stacks 08GP,
`qcqs_induction_on_self`), carried along the preimages of `T`, as AxiomMath proves 0AEC.

* *Affine case* (`suppDetectsBelow_of_isAffineSpace`).  On an affine `V`, the trivial square
  `(V ∖ T ⊆ V, 𝟙)` and Stacks 0859 give global functions `l` with `V ∖ T = ⋃ D(aᵢ)`.  The Koszul
  object `K(l)` is perfect and supported on `T`, and `E` vanishes where some `aᵢ` is a unit; graded
  Koszul detection turns `Hom(K(l), E[n]) = 0` for `n ≤ N` into `H^q(E) = 0` for `q ≤ N`.
* *Step* (`suppDetectsBelow_of_eds`).  AxiomMath's step, with two changes.  AxiomMath gets the
  bound `N₀` on `Hom(K'[-i], E)`, `K' = f_!K(l)` with `l` cutting out `V ∖ (U ×_W V)`, from the
  hypothesis on all compact objects; `K'` need not be supported on `T`.  Here `N₀` comes from the
  perfect object `f_!K(l' ++ l)` supported on `T` (`l'` cutting out `f⁻¹T`), and `l'` is peeled
  off (`koszulSp_peel`: torsion plus injectivity of `b` on `Hom(K(l'), E|_V[n])`), using that
  `E|_V` vanishes off `f⁻¹T`.  The perfect `Q` on `W` with `P` a summand of `Q|_U` come from
  the supported Stacks 09IV.

## Assumptions

Tagged AxiomMath inputs only: those of `Spaces/Supported/DetectingInputs.lean` and
`Spaces/AxiomMathInputs.lean`/`Spaces/Supported/Inputs.lean` (06UQ, 0AED, boundedness of perfect
objects), bundled in `StepInputs`.  AxiomMath's Koszul objects and unit-locus sieves enter through
their written-out definitions (`koszulSp`, `VanishesWhereUnitSp`, `unitLocusSieveSp`).  The
theorems of the AxiomMath modules imported by `DetectingInputs` (elementary distinguished squares,
support under étale restriction, `qcqs_induction_on_self`, …) are used directly.

## Differences from Stacks 0GFI

The hypothesis is asked of the perfect objects of `D(𝒪_X)` supported on `T`, which are the
compact objects of `D_{QCoh,T}(𝒪_X)` (Stacks 0AED; the repository's
`SupportedDetectsBelowStatement`, `Spaces/Supported/Preferred.lean`, is the form with compact
objects).  The instance context is that of AxiomMath's `Spaces/Perfect/DetectingBoundedBelow.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Space
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

namespace RelativeFM.Spaces.Supported

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

attribute [local instance] pointTopology

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- `D_QCoh` is closed under isomorphisms (AxiomMath's instance for `QcohDerived`, same proof). -/
instance isClosedUnderIsomorphisms_qcohDerived {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (Y : AlgebraicSpaces B S hS) :
    (qcohDerived Y).IsClosedUnderIsomorphisms :=
  ⟨fun e h n => SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (h n)⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Generalities -/

/-- `Hom(P[-i], E) = 0` iff `Hom(P, E[i]) = 0`, in any category with a shift by `ℤ`. -/
theorem forall_hom_shift_neg_eq_zero_iff {C : Type*} [Category C] [Preadditive C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] (P E : C) (i : ℤ) :
    (∀ f : P⟦-i⟧ ⟶ E, f = 0) ↔ ∀ g : P ⟶ E⟦i⟧, g = 0 := by
  constructor
  · intro h g
    apply (shiftFunctor C (-i)).map_injective
    rw [Functor.map_zero, ← cancel_mono ((shiftFunctorCompIsoId C i (-i)
      (add_neg_cancel i)).hom.app E), zero_comp]
    exact h _
  · intro h f
    apply (shiftFunctor C i).map_injective
    rw [Functor.map_zero, ← cancel_epi ((shiftFunctorCompIsoId C (-i) i
      (neg_add_cancel i)).inv.app P), comp_zero]
    exact h _

/-- An isomorphism onto a presheaf over `S` is an étale chart of it (AxiomMath's
`isEtaleChart_of_isIso`, whose module is outside the import list; same proof). -/
theorem isEtaleChart_of_isIso' {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}
    (f : yoneda.obj T ⟶ F) [IsIso f] : IsEtaleChart B S hS F (CostructuredArrow.mk f) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda f, ?_⟩
  intro a b g fst snd h
  have h' : IsPullback (g ≫ CategoryTheory.inv f) (𝟙 (yoneda.obj a)) f g :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have _ : IsIso (yoneda.map snd) := by
    have h2 : IsIso ((h.isoIsPullback _ _ h').hom ≫ 𝟙 (yoneda.obj a)) := inferInstance
    rwa [h.isoIsPullback_hom_snd _ _ h'] at h2
  have _ : IsIso snd := isIso_of_reflects_iso snd yoneda
  have _ : IsIso ((BigFppfOver.toScheme B S hS).map snd) := inferInstance
  change Etale ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- **An affine algebraic space has a final affine étale chart** (AxiomMath's `chartOfIso` and
`isTerminalChartOfIso`, reproved). -/
theorem exists_terminal_affineChart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hXa : IsAffineSpace B S hS X) :
    ∃ T : SmallEtale B S hS X, Nonempty (IsTerminal T) ∧ IsAffineChart B S hS X T := by
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hXa
  let T : SmallEtale B S hS X := ⟨CostructuredArrow.mk i.inv, isEtaleChart_of_isIso' i.inv⟩
  refine ⟨T, ⟨IsTerminal.ofUniqueHom
    (fun A => ObjectProperty.homMk (CostructuredArrow.homMk
      (yoneda.preimage (A.obj.hom ≫ i.hom)) (by simp [T])))
    (fun A f => by
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      apply yoneda.map_injective
      have hw : yoneda.map f.hom.left ≫ i.inv = A.obj.hom := CostructuredArrow.w f.hom
      simp only [ObjectProperty.homMk_hom, CostructuredArrow.homMk_left, Functor.map_preimage]
      rw [← hw, Category.assoc, Iso.inv_hom_id, Category.comp_id])⟩, hT₀⟩

/-- `Z.fromPreimage (𝟙 F)` is an isomorphism. -/
instance isIso_fromPreimage_id {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : Subfunctor F) :
    IsIso (Z.fromPreimage (𝟙 F)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  refine ⟨fun a b h => Subtype.ext ?_, fun y => ⟨⟨y.1, y.2⟩, rfl⟩⟩
  exact congrArg Subtype.val h

/-- **The trivial elementary distinguished square** `(O ⊆ V, 𝟙_V)` of an open subspace `O` of an
algebraic space `V`. -/
theorem isElementaryDistinguishedSquare_id (V : AlgebraicSpaces B S hS) (O : Subfunctor V.1)
    (hO : IsOpenSubspace B S hS O) :
    IsElementaryDistinguishedSquare B S hS V.2 O (𝟙 V.1) where
  isAlgebraicSpace := V.2
  isOpenSubspace := hO
  isEtale := isEtale_id B S hS V.1
  isClosedComplement := (isOpen_range_pointsMap_of_isOpenImmersion B S hS O.ι hO.2).isClosed_compl
  isIsoOverComplement := inferInstance

/-- The statement proved in this file, for an algebraic space `Y` and `T ⊆ |Y|`: an object `E` of
`D_QCoh(𝒪_Y)` supported on `T` such that, for every perfect `P` supported on `T`,
`Hom(P[-i], E) = 0` for `i ≪ 0`, is bounded below. -/
def SuppDetectsBelow (Y : AlgebraicSpaces B S hS) (T : Set (points B S hS Y.1)) : Prop :=
  ∀ E : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2,
    CohomologySupportedOn B S hS Y.1 Y.2 T E.obj →
    (∀ P : DerivedCategory (Space.Modules.{u, u} B S hS Y.1 Y.2),
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect P →
      CohomologySupportedOn B S hS Y.1 Y.2 T P →
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N → ∀ f : P⟦-i⟧ ⟶ E.obj, f = 0) →
    ∃ a : ℤ, E.obj.IsGE a

section TrivialSquare

variable (hrange : RangeOpenInput B S hS) (V : AlgebraicSpaces B S hS)
  (T : Set (points B S hS V.1)) (hT : IsClosed T)

include hrange in
/-- The points of `O ×_V V`, for `O` the open subspace on `|V| ∖ T`, map onto `|V| ∖ T`. -/
theorem range_edsSnd_id :
    Set.range (pointsMap B S hS _ (edsSnd B S hS (isElementaryDistinguishedSquare_id V
      ((openSubspacesOrderIso B S hS V.1 V.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1
      ((openSubspacesOrderIso B S hS V.1 V.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).2)).hom) = Tᶜ := by
  set G := (openSubspacesOrderIso B S hS V.1 V.2).symm ⟨Tᶜ, hT.isOpen_compl⟩
  have hsq := isElementaryDistinguishedSquare_id V G.1 G.2
  have hG := hrange V.1 V.2 T hT
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    have hw := congrArg (fun φ => pointsMap B S hS _ φ.hom w) (isPullback_edsInter B S hS hsq).w
    simp only [ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp, Function.comp_apply]
      at hw
    rw [← hG]
    refine ⟨pointsMap B S hS _ (edsFst B S hS hsq).hom w, ?_⟩
    have h2 : pointsMap B S hS _ (edsEtaleHom B S hS hsq).hom
        (pointsMap B S hS _ (edsSnd B S hS hsq).hom w) =
        pointsMap B S hS _ (edsSnd B S hS hsq).hom w := by
      change pointsMap B S hS _ (𝟙 V.1) _ = _
      rw [pointsMap_id]; rfl
    rw [← h2, ← hw]
    rfl
  · intro v hv
    rw [← hG] at hv
    obtain ⟨o, rfl⟩ := hv
    obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback (edsOpenHom B S hS hsq).hom (edsEtaleHom B S hS hsq).hom) o
      (pointsMap B S hS _ G.1.ι o) (by
        change _ = pointsMap B S hS _ (𝟙 V.1) _
        rw [pointsMap_id]; rfl)
    exact ⟨w, hw⟩

end TrivialSquare

/-- `D_{QCoh,|Y|}(𝒪_Y) ⥤ D_QCoh(𝒪_Y)` is an equivalence. -/
instance isEquivalence_ι_univ_det (Y : AlgebraicSpaces B S hS) :
    (qcSupportedOn Y (Set.univ : Set (points B S hS Y.1))).ι.IsEquivalence where
  essSurj := ⟨fun E => ⟨⟨E, fun _ => Set.subset_univ _⟩, ⟨Iso.refl _⟩⟩⟩

/-- A compact object of `D_QCoh(𝒪_Y)` is perfect, for `Y` qcqs (Stacks 0AED with `T = |Y|`). -/
theorem isPerfect_of_isCompactObject_qcoh (h0AED : Tag0AEDInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (Y : AlgebraicSpaces B S hS)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (P : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) (hP : IsCompactObject.{u} P) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect P.obj := by
  let P' : (qcSupportedOn Y Set.univ).FullSubcategory := ⟨P, fun _ => Set.subset_univ _⟩
  have hP' : IsCompactObject.{u} P' :=
    (isCompactObject_iff_isCompactObject_obj (qcSupportedOn Y Set.univ).ι P').2 hP
  exact (h0AED hZ Y hYqc hYqs Set.univ isClosed_univ (by rw [Set.compl_univ]; exact isCompact_empty)
    P').1 hP'

/-- **The affine case of the supported Stacks 0GFI.**  On an affine algebraic space `Y` with a
closed `T ⊆ |Y|` whose complement has quasi-compact inclusion, the Koszul object `K(l)` on
equations `l` of `T` (from the trivial square `(|Y| ∖ T ⊆ Y, 𝟙)`, Stacks 0859) is perfect and
supported on `T`, and graded Koszul detection bounds `E` below. -/
theorem suppDetectsBelow_of_isAffineSpace (hrange : RangeOpenInput B S hS)
    (hUL : UnitLocusInput B S hS) (hKR : KoszulRestrictInput B S hS)
    (hVW : VanishesWhereUnitInput B S hS) (hKC : KoszulCompactInput B S hS)
    (hKQ : KoszulQcohInput B S hS) (hKD : KoszulDetectionInput B S hS)
    (h0AED : Tag0AEDInput B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : AlgebraicSpaces B S hS) (hYa : IsAffineSpace B S hS Y.1)
    (T : Set (points B S hS Y.1)) (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS Y.1 Y.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) :
    SuppDetectsBelow Y T := by
  intro E hEs hE
  set G := (openSubspacesOrderIso B S hS Y.1 Y.2).symm ⟨Tᶜ, hT.isOpen_compl⟩
  have hsq := isElementaryDistinguishedSquare_id Y G.1 G.2
  have hGqc : IsQuasiCompactSpace B S hS G.1.toFunctor :=
    isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS G.1.ι hYa hTqc
  have hYqs := IsAffineSpace.isAbsolutelyQuasiSeparated B S hS hZ hYa
  have hYqc := hYa.isQuasiCompactSpace
  obtain ⟨l, ha, hb⟩ := hUL hZ hsq hYa hGqc hYqs
  have hR := range_edsSnd_id hrange Y T hT
  let K := koszulSp hsq.isAlgebraicSpace l
  have hK0 := hKR hsq l hb
  have hKs : CohomologySupportedOn B S hS Y.1 Y.2 T K := by
    refine (cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback B S hS
      (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) K hK0).mono B S hS _ _ ?_
    rw [hR]
    exact fun x hx => Classical.not_not.mp hx
  obtain ⟨T₀, ⟨hT₀⟩, hT₀a⟩ := exists_terminal_affineChart hYa
  have hKp : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K :=
    isPerfect_of_isCompactObject_qcoh h0AED hZ Y hYqc hYqs ⟨K, hKQ _ _ l⟩
      (hKC _ _ T₀ hT₀ hT₀a l (hKQ _ _ l))
  obtain ⟨N, hN⟩ := hE K hKp hKs
  have horth : ∀ n : ℤ, n ≤ N → ∀ x : K ⟶ E.obj⟦n⟧, x = 0 := fun n hn =>
    (forall_hom_shift_neg_eq_zero_iff K E.obj n).1 (hN n hn)
  have hloc : ∀ b ∈ l, VanishesWhereUnitSp b E.obj :=
    hVW (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) l ha E.obj
      (isZero_etaleModulePullback_mapDerivedCategory_of_disjoint B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq) T E.obj hEs (by rw [hR]; exact disjoint_compl_left))
  refine ⟨N + 1, ?_⟩
  rw [DerivedCategory.isGE_iff]
  intro q hq
  exact hKD _ _ T₀ hT₀ hT₀a (· ≤ N) l E.obj E.property hloc horth q (by omega)

/-! ### Peeling equations off a Koszul object -/

section Peel

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}

/-- Vanishing where `a` is a unit is preserved by shifts (AxiomMath's `VanishesWhereUnit.shift`,
same proof). -/
theorem VanishesWhereUnitSp.shift {a : globalRingSp hX}
    {M : DerivedCategory (Space.Modules.{u, u} B S hS X hX)}
    (hM : VanishesWhereUnitSp a M) (n : ℤ) : VanishesWhereUnitSp a (M⟦n⟧) := fun U hU q =>
  let e := (((DerivedCategory.homologyFunctor (Space.Modules.{u, u} B S hS X hX) 0).shiftIso n q
    (n + q) rfl).app M)
  ⟨fun _ _ => (Iso.toLinearEquiv ((SheafOfModules.evaluation _ (op U)).mapIso e)).injective
    ((hM U hU (n + q)).elim _ _)⟩

/-- **Peeling.**  Let `M` be in `D_QCoh(𝒪_X)` (final affine chart), vanishing where each member of
`l'` is a unit.  If every `K(l' ++ l) ⟶ M⟦n⟧` vanishes for `n ∈ D`, so does every
`K(l) ⟶ M⟦n⟧`: a morphism out of `K(l)` is killed by a power of `b` (torsion), while `b` acts
injectively on such morphisms because the cone `K(b :: l)` of `b` has no morphism into `M⟦n⟧`.
This is the inner step of AxiomMath's proof of `isZero_homology_of_hom_koszul_eq_zero`, here
stopped at `K(l)` instead of `𝒪_X[0]`. -/
theorem koszulSp_peel (h06 : Tag06UQInput B S hS) (hKT : KoszulTorsionInput B S hS)
    (T : SmallEtale B S hS X) (hT : IsTerminal T) (hTa : IsAffineChart B S hS X T)
    (D : ℤ → Prop) (M : DerivedCategory (Space.Modules.{u, u} B S hS X hX))
    (hM : qcohDerived ⟨X, hX⟩ M) :
    ∀ (l' l : List (globalRingSp hX)), (∀ b ∈ l', VanishesWhereUnitSp b M) →
      (∀ n : ℤ, D n → ∀ x : koszulSp hX (l' ++ l) ⟶ M⟦n⟧, x = 0) →
      ∀ n : ℤ, D n → ∀ x : koszulSp hX l ⟶ M⟦n⟧, x = 0
  | [], _, _, h => h
  | b :: l', l, hloc, h => by
    refine koszulSp_peel h06 hKT T hT hTa D M hM l' l
      (fun c hc => hloc c (List.mem_cons_of_mem b hc)) (fun n hn x => ?_)
    have := h06 X hX
    obtain ⟨g, k, hT'⟩ := exists_distTriang_koszulSp_cons b (l' ++ l)
    have hinj : ∀ y : koszulSp hX (l' ++ l) ⟶ M⟦n⟧, b • y = 0 → y = 0 := by
      intro y hy
      have h1 : (b • 𝟙 (koszulSp hX (l' ++ l))) ≫ y = 0 := by
        rw [Linear.smul_comp, Category.id_comp, hy]
      obtain ⟨w, hw⟩ := Triangle.yoneda_exact₂ _ hT' y h1
      rw [hw, h n hn w, comp_zero]
    obtain ⟨N, hN⟩ := hKT X hX T hT hTa b (l' ++ l) (M⟦n⟧)
      ((qcohDerived ⟨X, hX⟩).le_shift n M hM) ((hloc b List.mem_cons_self).shift n) x
    induction N generalizing x with
    | zero => simpa using hN
    | succ k ih =>
      apply hinj
      apply ih
      rw [← mul_smul, ← pow_succ]
      exact hN

end Peel

/-! ### Adjunction and points for elementary distinguished squares -/

/-- All morphisms `A ⟶ B` vanish iff `A ⟶ B` is a subsingleton. -/
theorem forall_eq_zero_iff_subsingleton {C : Type*} [Category C] [Preadditive C] (A B : C) :
    (∀ f : A ⟶ B, f = 0) ↔ Subsingleton (A ⟶ B) :=
  ⟨fun h => ⟨fun a b => (h a).trans (h b).symm⟩, fun _ f => Subsingleton.elim f 0⟩

/-- `Hom(j_!K, F[n]) = 0` iff `Hom(K, (F|_V)[n]) = 0`, for étale `j : V ⟶ W` (the adjunction
`j_! ⊣ (-)|_V` and the commutation of restriction with shifts). -/
theorem forall_shriek_eq_zero_iff {V W : AlgebraicSpaces B S hS} (fe : V ⟶ W)
    (hfe : IsEtale B S hS fe.hom) (K : DerivedCategory (Space.Modules.{u, u} B S hS V.1 V.2))
    (F : DerivedCategory (Space.Modules.{u, u} B S hS W.1 W.2)) (n : ℤ) :
    (∀ z : (etaleModuleLowerShriek B S hS fe hfe).mapDerivedCategory.obj K ⟶ F⟦n⟧, z = 0) ↔
      ∀ x : K ⟶ ((etaleModulePullback.{u, u} B S hS fe hfe).mapDerivedCategory.obj F)⟦n⟧,
        x = 0 := by
  let adjS := (etaleModuleLowerShriekAdjunction B S hS fe hfe).mapDerivedCategory
  let φ := ((etaleModulePullback.{u, u} B S hS fe hfe).mapDerivedCategory.commShiftIso n).app F
  let e := (adjS.homEquiv K (F⟦n⟧)).trans ((Iso.refl K).homCongr φ)
  rw [forall_eq_zero_iff_subsingleton, forall_eq_zero_iff_subsingleton]
  exact e.subsingleton_congr

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The open immersion of a square is a monomorphism (AxiomMath's `mono_edsOpenHom`). -/
instance mono_edsOpenHom' : Mono (edsOpenHom B S hS hsq) :=
  (ObjectProperty.ι _).mono_of_mono_map (inferInstanceAs (Mono Uo.ι))

/-- The image of `|U ×_W V|` in `|V|` lies over `|U|`. -/
theorem range_edsSnd_subset :
    Set.range (pointsMap B S hS _ (edsSnd B S hS hsq).hom) ⊆
      pointsMap B S hS _ (edsEtaleHom B S hS hsq).hom ⁻¹'
        Set.range (pointsMap B S hS _ (edsOpenHom B S hS hsq).hom) := by
  rintro _ ⟨w, rfl⟩
  have hw := congrArg (fun φ => pointsMap B S hS _ φ.hom w) (isPullback_edsInter B S hS hsq).w
  simp only [ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp, Function.comp_apply] at hw
  exact ⟨_, hw⟩

/-- A point of `|V|` outside the image of `|U ×_W V|` lies over `|W| ∖ |U|`. -/
theorem compl_range_edsSnd_subset :
    (Set.range (pointsMap B S hS _ (edsSnd B S hS hsq).hom))ᶜ ⊆
      edsEtalePreimageComplementPoints B S hS hsq := by
  intro v hv ⟨u, hu⟩
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback (edsOpenHom B S hS hsq).hom (edsEtaleHom B S hS hsq).hom) u v hu
  exact hv ⟨w, hw⟩

end Square

/-! ### The induction step -/

/-- The inputs used by the induction step, bundled. -/
structure StepInputs (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop where
  h06 : Tag06UQInput B S hS
  h0AED : Tag0AEDInput B S hS
  hbdd : PerfectBoundedAboveInput B S hS
  hKT : KoszulTorsionInput B S hS
  hKD : KoszulDetectionInput B S hS
  hKQ : KoszulQcohInput B S hS
  hKC : KoszulCompactInput B S hS
  hUL : UnitLocusInput B S hS
  hKR : KoszulRestrictInput B S hS
  hVW : VanishesWhereUnitInput B S hS
  hEOqc : EdsOpenQcInput B S hS
  hEOqs : EdsOpenQsInput B S hS
  hOC : OpenCounitInput B S hS
  hPQ : PushforwardQcohInput B S hS
  hrange : RangeOpenInput B S hS
  hPre : PreimageQcInput B S hS
  hSS : ShriekSupportInput B S hS
  hSP : ShriekPerfectInput B S hS
  hSRO : ShriekRestrictOpenInput B S hS
  h09IV : Tag09IVInput B S hS
  hSPb : SupportPullbackInput B S hS

section Step

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}

/-- **The induction step of the supported Stacks 0GFI.**  Let `(U ⊆ W, f : V ⟶ W)` be an
elementary distinguished square with `W` qcqs, `U` quasi-compact and `V` affine, and `T ⊆ |W|`
closed with `W ∖ T ⟶ W` quasi-compact.  If the supported statement holds on `U` for `T ∩ U`, it
holds on `W` for `T`.

AxiomMath's step (`exists_isGE_of_lowHomVanishing_of_eds`) with two changes.  (1) The bound `N₀`
on `Hom(K'[-i], E)`, `K' = f_!K(l)` with `l` cutting out `V ∖ (U ×_W V)`, is not available
directly, since `K'` need not be supported on `T`; it is obtained from the supported perfect
object `f_!K(l' ++ l)`, `l'` cutting out `f⁻¹T` (trivial square on `V`), by peeling `l'` off
(`koszulSp_peel`), which uses that `E|_V` vanishes off `f⁻¹T`.  (2) The objects `Q` on `W` with
`P` a summand of `Q|_U` come from the supported Stacks 09IV. -/
theorem suppDetectsBelow_of_eds (I : StepInputs B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) (hVa : IsAffineSpace B S hS V)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hWqc : IsQuasiCompactSpace B S hS W.1)
    (T : Set (points B S hS W.1)) (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS W.1 W.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (hIH : SuppDetectsBelow (edsOpen B S hS hsq) (pointsMap B S hS Uo.toFunctor Uo.ι ⁻¹' T)) :
    SuppDetectsBelow W T := by
  intro E hEs hE
  have := I.h06 W.1 W.2
  let Ve := edsEtale B S hS hsq
  let fe := edsEtaleHom B S hS hsq
  have hfe : IsEtale B S hS fe.hom := isEtale_edsEtaleHom B S hS hsq
  have hVqc : IsQuasiCompactSpace B S hS V := hVa.isQuasiCompactSpace
  have hVqs := IsAffineSpace.isAbsolutelyQuasiSeparated B S hS hZ hVa
  have hUq := I.hEOqc hZ hsq hWqs hUqc
  have hUs := I.hEOqs hsq
  obtain ⟨T₀, ⟨hT₀⟩, hT₀a⟩ := exists_terminal_affineChart (B := B) (S := S) (hS := hS)
    (X := Ve.1) hVa
  -- the equations `l` of `V ∖ (U ×_W V)`
  obtain ⟨l, ha, hb⟩ := I.hUL hZ hsq hVa hUqc hWqs
  -- the equations `l'` of `f⁻¹T`, from the trivial square on `V`
  let TV : Set (points B S hS Ve.1) := pointsMap B S hS Ve.1 fe.hom ⁻¹' T
  have hTV : IsClosed TV := hT.preimage (continuous_pointsMap B S hS _)
  have hTVqc := I.hPre W.2 Ve.2 fe.hom T hT hTqc hTV
  set G := (openSubspacesOrderIso B S hS Ve.1 Ve.2).symm ⟨TVᶜ, hTV.isOpen_compl⟩
  have hsq0 := isElementaryDistinguishedSquare_id Ve G.1 G.2
  have hGqc : IsQuasiCompactSpace B S hS G.1.toFunctor :=
    isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS G.1.ι hVa hTVqc
  obtain ⟨l', ha', hb'⟩ := I.hUL hZ hsq0 hVa hGqc hVqs
  have hR0 := range_edsSnd_id I.hrange Ve TV hTV
  let l'' : List (globalRingSp hsq.isAlgebraicSpace) := l'
  let L : List (globalRingSp hsq.isAlgebraicSpace) := l'' ++ l
  -- `K(L)` vanishes on `U ×_W V` and on `V ∖ f⁻¹T`
  have hKL0 : IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).mapDerivedCategory.obj (koszulSp hsq.isAlgebraicSpace L)) :=
    I.hKR hsq L fun U' => (SmallEtale.topology B S hS _).superset_covering
      (show unitLocusSieveSp B S hS hsq l U' ≤ unitLocusSieveSp B S hS hsq L U' from
        fun _ _ ⟨a, hal, hu⟩ => ⟨a, List.mem_append_right l'' hal, hu⟩) (hb U')
  have hKL0' : IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq0)
      (isEtale_edsSnd B S hS hsq0)).mapDerivedCategory.obj (koszulSp hsq0.isAlgebraicSpace L)) :=
    I.hKR hsq0 L fun U' => (SmallEtale.topology B S hS _).superset_covering
      (show unitLocusSieveSp B S hS hsq0 l' U' ≤ unitLocusSieveSp B S hS hsq0 L U' from
        fun _ _ ⟨a, hal, hu⟩ => ⟨a, List.mem_append_left l hal, hu⟩) (hb' U')
  let KL := koszulSp hsq.isAlgebraicSpace L
  have hKLsT : CohomologySupportedOn B S hS Ve.1 Ve.2 TV KL := by
    refine (cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback B S hS
      (edsSnd B S hS hsq0) (isEtale_edsSnd B S hS hsq0) KL hKL0').mono B S hS _ _ ?_
    rw [hR0]
    exact fun x hx => Classical.not_not.mp hx
  have hKLsC : CohomologySupportedOn B S hS Ve.1 Ve.2
      (edsEtalePreimageComplementPoints B S hS hsq) KL :=
    (cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback B S hS
      (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) KL hKL0).mono B S hS _ _
      (compl_range_edsSnd_subset hsq)
  have hKLp : (smallEtaleRingedSite B S hS Ve.1 Ve.2).IsPerfect KL :=
    isPerfect_of_isCompactObject_qcoh I.h0AED hZ Ve hVqc hVqs ⟨KL, I.hKQ _ _ L⟩
      (I.hKC _ _ T₀ hT₀ hT₀a L (I.hKQ _ _ L))
  -- the supported perfect object `f_!K(L)` gives the bound `N₀`
  let Lsh := (etaleModuleLowerShriek B S hS fe hfe).mapDerivedCategory
  let Lv := (etaleModulePullback.{u, u} B S hS fe hfe).mapDerivedCategory
  obtain ⟨N₀, hN₀⟩ := hE (Lsh.obj KL) (I.hSP hsq KL hKLp hKLsC) (I.hSS fe hfe T hT KL hKLsT)
  have hEVq : qcohDerived Ve (Lv.obj E.obj) :=
    derivedQuasicoherent_etaleModulePullback B S hS fe hfe E.obj E.property
  have hEVs : CohomologySupportedOn B S hS Ve.1 Ve.2 TV (Lv.obj E.obj) :=
    I.hSPb fe hfe T E.obj hEs
  have hEVloc : ∀ b ∈ l', VanishesWhereUnitSp b (Lv.obj E.obj) :=
    I.hVW (edsSnd B S hS hsq0) (isEtale_edsSnd B S hS hsq0) l' ha' (Lv.obj E.obj)
      (isZero_etaleModulePullback_mapDerivedCategory_of_disjoint B S hS (edsSnd B S hS hsq0)
        (isEtale_edsSnd B S hS hsq0) TV _ hEVs (by rw [hR0]; exact disjoint_compl_left))
  have hKl : ∀ n : ℤ, n ≤ N₀ → ∀ x : koszulSp hsq.isAlgebraicSpace l ⟶ (Lv.obj E.obj)⟦n⟧,
      x = 0 :=
    koszulSp_peel I.h06 I.hKT T₀ hT₀ hT₀a (· ≤ N₀) (Lv.obj E.obj) hEVq l'' l hEVloc
      fun n hn => (forall_shriek_eq_zero_iff fe hfe KL E.obj n).1
        ((forall_hom_shift_neg_eq_zero_iff _ E.obj n).1 (hN₀ n hn))
  let Kd := koszulSp hsq.isAlgebraicSpace l
  let K' := Lsh.obj Kd
  have hN₀' : ∀ i : ℤ, i ≤ N₀ → Subsingleton (K'⟦-i⟧ ⟶ E.obj) := fun i hi =>
    (forall_eq_zero_iff_subsingleton _ _).1 ((forall_hom_shift_neg_eq_zero_iff K' E.obj i).2
      ((forall_shriek_eq_zero_iff fe hfe Kd E.obj i).2 (hKl i hi)))
  have hKd0 : IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).mapDerivedCategory.obj Kd) := I.hKR hsq l hb
  -- AxiomMath's step from here on, with `K' = f_!K(l)` and the bound `hN₀'`
  let j := edsOpenHom B S hS hsq
  have hj : IsEtale B S hS j.hom := isEtale_edsOpenHom B S hS hsq
  let Lu := (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory
  let adjD := etaleDerivedModuleAdjunction B S hS j hj
  let Eu := Lu.obj E.obj
  let RjE : DerivedCategory (Space.Modules.{u, u} B S hS W.1 W.2) :=
    (derivedPushforward (X := smallEtaleRingedTopos B S hS (edsOpen B S hS hsq))
    (Y := smallEtaleRingedTopos B S hS W) (smallEtaleRingedToposHom B S hS j)).obj Eu
  obtain ⟨C, g, h, hTr⟩ := distinguished_cocone_triangle (adjD.unit.app E.obj)
  have := I.hOC j hj
  have hLC : IsZero (Lu.obj C) :=
    Triangle.isZero₃_of_isIso₁ _ (Lu.map_distinguished _ hTr)
      (ObjectProperty.isIso_map_unit_of_isIso_counit adjD E.obj inferInstance)
  have hsubR : ∀ n : ℤ, Subsingleton (K'⟦-n⟧ ⟶ RjE) := fun n => by
    have hz : IsZero (Lu.obj (K'⟦-n⟧)) :=
      ((shiftFunctor _ (-n)).map_isZero (I.hSRO hsq Kd hKd0)).of_iso
        ((Lu.commShiftIso (-n)).app K')
    exact (adjD.homEquiv _ _).symm.subsingleton_congr.2 ⟨fun a b => hz.eq_of_src a b⟩
  have hsubC : ∀ n : ℤ, n + 1 ≤ N₀ → ∀ x : K'⟦-n⟧ ⟶ C, x = 0 := fun n hn x => by
    have hshift : Subsingleton (K'⟦-n⟧ ⟶ E.obj⟦(1 : ℤ)⟧) :=
      Stacks.DerivedTruncation.subsingleton_hom_shift_one_of_subsingleton_hom (-n) (-(n + 1))
        (by omega) (hN₀' (n + 1) hn)
    obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₃ _ hTr x (hshift.elim _ _)
    rw [hv, (hsubR n).elim v 0, zero_comp]
  have hRjE : qcohDerived W RjE :=
    I.hPQ j hUq hUs Eu (derivedQuasicoherent_etaleModulePullback B S hS j hj E.obj E.property)
  have hCq : qcohDerived W C :=
    (qcohDerived W).ext_of_isTriangulatedClosed₃ _ hTr E.property hRjE
  let M := Lv.obj C
  have hMq : qcohDerived Ve M := derivedQuasicoherent_etaleModulePullback B S hS fe hfe C hCq
  have hMs := I.hSPb fe hfe _ C
    (cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback B S hS j hj C hLC)
  have hMP : IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).mapDerivedCategory.obj M) :=
    isZero_etaleModulePullback_mapDerivedCategory_of_disjoint B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq) _ M hMs
      (Set.disjoint_left.2 fun _ hv hv' => hv' (range_edsSnd_subset hsq hv))
  have horth : ∀ n : ℤ, n ≤ N₀ - 1 → ∀ x : Kd ⟶ M⟦n⟧, x = 0 := fun n hn =>
    (forall_shriek_eq_zero_iff fe hfe Kd C n).1
      ((forall_hom_shift_neg_eq_zero_iff K' C n).1 (hsubC n (by omega)))
  have hMH := I.hKD Ve.1 Ve.2 T₀ hT₀ hT₀a (· ≤ N₀ - 1) l M hMq
    (I.hVW (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) l ha M hMP) horth
  have hCge : C.IsGE N₀ := by
    rw [DerivedCategory.isGE_iff]
    intro q hq
    refine isZero_of_isZero_restrict_eds B S hS hsq _ ?_ ?_
    · exact ((DerivedCategory.homologyFunctor _ q).map_isZero hLC).of_iso
        (((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryHomologyIso q).app C).symm
    · exact (hMH q (show q ≤ N₀ - 1 by omega)).of_iso
        (((etaleModulePullback.{u, u} B S hS fe hfe).mapDerivedCategoryHomologyIso q).app C).symm
  -- `E|_U` satisfies the hypothesis on `U`
  have hEUs : CohomologySupportedOn B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2
      (pointsMap B S hS Uo.toFunctor Uo.ι ⁻¹' T) Eu := I.hSPb j hj T E.obj hEs
  have hEUq : qcohDerived (edsOpen B S hS hsq) Eu :=
    derivedQuasicoherent_etaleModulePullback B S hS j hj E.obj E.property
  have hEU : ∀ P' : DerivedCategory (Space.Modules.{u, u} B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2),
      (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).IsPerfect P' →
      CohomologySupportedOn B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2
        (pointsMap B S hS Uo.toFunctor Uo.ι ⁻¹' T) P' →
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N → ∀ f : P'⟦-i⟧ ⟶ Eu, f = 0 := by
    intro P' hP' hP's
    -- `openSubspaceSpace Uo _` (the spelling of 09IV) is `edsOpen hsq` by definition
    obtain ⟨Q, -, hQ, hQs, s₀, r₀, hsr₀, -⟩ := I.h09IV hZ W hWqc hWqs Uo hsq.isOpenSubspace hUqc
      T hT hTqc E P' hP' hP's (0 : P' ⟶ Eu)
    let s : P' ⟶ Lu.obj Q := s₀
    let r : Lu.obj Q ⟶ P' := r₀
    have hsr : s ≫ r = 𝟙 P' := hsr₀
    obtain ⟨b, hb⟩ := I.hbdd hWqc Q hQ
    obtain ⟨NQ, hNQ⟩ := hE Q hQ hQs
    refine ⟨min NQ (N₀ - b - 1), fun k hk f => ?_⟩
    have hR : ∀ f' : Q⟦-k⟧ ⟶ RjE, f' = 0 := fun f' => by
      have hb' : (Q⟦-k⟧).IsLE (b + k) :=
        DerivedCategory.TStructure.t.isLE_shift Q b (-k) (b + k) (by omega)
      have hfg : f' ≫ g = 0 :=
        DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (b + k) N₀ (by omega) hb' hCge
      obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₂ _ hTr f' hfg
      rw [hv, hNQ k (le_trans hk (min_le_left _ _)) v, zero_comp]
    have hsub : ∀ y : Lu.obj (Q⟦-k⟧) ⟶ Eu, y = 0 := fun y =>
      Subsingleton.elim (h := (adjD.homEquiv _ _).subsingleton_congr.2
        ⟨fun a b => (hR a).trans (hR b).symm⟩) y 0
    have h1 : ∀ y : (Lu.obj Q)⟦-k⟧ ⟶ Eu, y = 0 := fun y =>
      (cancel_epi ((Lu.commShiftIso (-k)).hom.app Q)).1
        ((hsub ((Lu.commShiftIso (-k)).hom.app Q ≫ y)).trans comp_zero.symm)
    calc f = (s⟦-k⟧' ≫ r⟦-k⟧') ≫ f := by
          rw [← Functor.map_comp, hsr, CategoryTheory.Functor.map_id, Category.id_comp]
      _ = 0 := by rw [Category.assoc, h1 (r⟦-k⟧' ≫ f), comp_zero]
  obtain ⟨m, hm⟩ := hIH ⟨Eu, hEUq⟩ hEUs hEU
  have hRm : RjE.IsGE m := by
    change DerivedCategory.TStructure.t.IsGE RjE m
    rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (m - 1) m (by omega)]
    intro A f hA
    have hA' : A.IsLE (m - 1) := hA
    have hLA : (Lu.obj A).IsLE (m - 1) := by
      rw [DerivedCategory.isLE_iff] at hA' ⊢
      intro q hq
      exact ((etaleModulePullback.{u, u} B S hS j hj).map_isZero (hA' q hq)).of_iso
        (((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryHomologyIso q).app A)
    have : DerivedCategory.TStructure.t.IsGE Eu m := hm
    have hsub : Subsingleton (Lu.obj A ⟶ Eu) := ⟨fun x y => by
      rw [DerivedCategory.TStructure.t.zero x (m - 1) m (by omega),
        DerivedCategory.TStructure.t.zero y (m - 1) m (by omega)]⟩
    exact ((adjD.homEquiv A Eu).subsingleton_congr.1 hsub).elim _ _
  refine ⟨min (N₀ + 1) m, ?_⟩
  have h₁ : (C⟦(-1 : ℤ)⟧).IsGE (N₀ + 1) :=
    DerivedCategory.TStructure.t.isGE_shift C N₀ (-1) (N₀ + 1) (by omega)
  have h₁' : (C⟦(-1 : ℤ)⟧).IsGE (min (N₀ + 1) m) :=
    DerivedCategory.TStructure.t.isGE_of_ge _ _ _ (min_le_left _ _)
  have h₂' : RjE.IsGE (min (N₀ + 1) m) :=
    DerivedCategory.TStructure.t.isGE_of_ge _ _ _ (min_le_right _ _)
  exact DerivedCategory.TStructure.t.isGE₂ _ (inv_rot_of_distTriang _ hTr) _ h₁' h₂'

end Step

/-! ### The induction -/

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **The supported Stacks 0GFI** ((7) ⇒ (1) on `D_{QCoh,T}(𝒪_X)`): for `X` quasi-compact and
quasi-separated and `T ⊆ |X|` closed with `X ∖ T ⟶ X` quasi-compact, an object `E` of
`D_QCoh(𝒪_X)` supported on `T` with `Hom(P[-i], E) = 0` for `i ≪ 0` for every perfect `P`
supported on `T` is bounded below.  The induction principle of Stacks 08GP
(`qcqs_induction_on_self`), with the affine case `suppDetectsBelow_of_isAffineSpace` and the
step `suppDetectsBelow_of_eds`, as AxiomMath proves 0AEC
(`exists_isSupportedPerfectGenerator`). -/
theorem suppDetectsBelow (I : StepInputs B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) :
    SuppDetectsBelow X T := by
  have h := qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (fun Y g => ∀ hY : IsAlgebraicSpace B S hS Y,
      SuppDetectsBelow ⟨Y, hY⟩ (pointsMap B S hS Y g ⁻¹' T))
    (fun V hV hY => by
      have hTV : IsClosed (pointsMap B S hS V.1.left.1 V.1.hom.hom ⁻¹' T) :=
        hT.preimage (continuous_pointsMap B S hS _)
      exact suppDetectsBelow_of_isAffineSpace I.hrange I.hUL I.hKR I.hVW I.hKC I.hKQ I.hKD
        I.h0AED hZ ⟨V.1.left.1, hY⟩ hV _ hTV (I.hPre X.2 hY V.1.hom.hom T hT hTqc hTV))
    (fun W V U f _ hsq hWqc hWqs hUqc hVaff hPU _ _ hY => by
      let g := W.1.hom.hom
      have hTW : IsClosed (pointsMap B S hS W.1.left.1 g ⁻¹' T) :=
        hT.preimage (continuous_pointsMap B S hS _)
      have hTWqc := I.hPre X.2 hY g T hT hTqc hTW
      have hU := hPU hsq.isOpenSubspace.1
      have hset : pointsMap B S hS U.toFunctor (U.ι ≫ g) ⁻¹' T =
          pointsMap B S hS U.toFunctor U.ι ⁻¹' (pointsMap B S hS W.1.left.1 g ⁻¹' T) := by
        rw [pointsMap_comp, Set.preimage_comp]
      rw [hset] at hU
      exact suppDetectsBelow_of_eds (W := ⟨W.1.left.1, hY⟩) I hZ hsq hVaff hUqc hWqs hWqc _ hTW
        hTWqc hU)
  have hX := h X.2
  rwa [pointsMap_id, Set.preimage_id] at hX

end RelativeFM.Spaces.Supported
