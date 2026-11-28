/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Duality.Basic
import Spaces.LP26.Recollement
import Spaces.LP26.OpenPushforward

/-!
# GL26 Lemma 2.22 (`lem:neeman187`): `f^× ≅ f^!` for proper `f`, over algebraic spaces

Guisado Villalgordo–Lank (GL26), **Lemma 2.22** (`lem:neeman187`, Neeman 2023, Theorem 1.8.7):
let `f : Y ⟶ X` be a 1-morphism of `(Sp/S)_{Noeth,sep,fp}`; if `f` is proper, there is a natural
isomorphism `f^× ≅ f^!` on `D_qc`.

`lemma_2_22` proves it for **every** Nagata compactification `f = p ∘ j` defining `f^!`
(`upperShriek`); `upperTimesIsoUpperShriek` is the isomorphism.  It holds more generally for
`f : Y ⟶ X` proper with `Y` quasi-compact and quasi-separated and `X` quasi-separated
(`upperTimesIsoUpperShriek` takes only these hypotheses).

## Proof

Let `f = p ∘ j`, `j : Y ⟶ Y'` an open immersion and `p : Y' ⟶ X` proper.

1. `j` is proper (Stacks 04NX (2): `p ∘ j = f` is proper and `p` is separated), so its image
   `|j|(|Y|)` is open (`j` is an open immersion) and closed (`j` is universally closed).
2. **`Rj_* ⊣ Lj^*` on `D(𝒪)`** for an open immersion `j : U ⟶ X` with closed image `W`
   (`pushPullAdj`).  Let `V ⊆ X` be the open subspace with `|V| = |X| ∖ W`.
   * For `M ∈ D(𝒪_U)` and `N` supported on `|X| ∖ W`, every `Rj_*M ⟶ N` is zero
     (`hom_push_eq_zero`): the unit `N ⟶ Rv_*(N|_V)` is invertible (Stacks 08GG (1)(a), for the
     elementary distinguished square `(W ⊆ X, v)`), and `(Rj_*M)|_V = 0` because `Rj_*M` is
     supported on the closed set `W` (Stacks 0AFJ), which `|V|` misses (Stacks 08GF, 04K5).
   * For `E ∈ D(𝒪_X)`, the cone `C` of the unit `E ⟶ Rj_*Lj^*E` restricts to zero on `U`
     (the counit `Lj^*Rj_* ⟶ 1` is invertible: `Rj_*` is fully faithful), so `C` is supported on
     `|X| ∖ W` (Stacks 08GF), and so are its shifts.  Hence composing with the unit is a
     bijection `Hom(Rj_*M, E) ≃ Hom(Rj_*M, Rj_*Lj^*E)` (`bijective_comp_unit`), and
     `Hom(Rj_*M, Rj_*Lj^*E) ≃ Hom(M, Lj^*E)` by full faithfulness of `Rj_*`.
3. Restricting to `D_qc` (Stacks 08FA, 08F4), `Lj^*` is a right adjoint of `Rj_*`, hence
   `j^× ≅ Lj^*` on `D_qc` (`upperTimesIsoPullQc`, uniqueness of adjoints).
4. `f^× ≅ (p ∘ j)^× ≅ j^× ∘ p^× ≅ Lj^* ∘ p^× = f^!` by `δ(j, p)` (`upperTimesCompIso`).

## Assumptions

AxiomMath theorems only, as tagged inputs: `Tag08FAInput`, `Tag08F4Input`, `Tag0E55Input`,
`Tag04NXInput`, and from `Spaces/LP26/Inputs.lean` `QuasiCompactSourceInput`, `Tag073BInput`,
`OpenImmersionCounitInput`, `EDSOfComplSubsetInput`, `Tag08GGUnitInput`, `PullbackDisjointInput`,
`Tag0AFJInput`, `EtaleRestrictionSupportInput`, and `Supported.SupportTriangulatedInput`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Duality

open RelativeFM.Spaces RelativeFM.Spaces.LP26 RelativeFM.Spaces.Supported

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### `Rj_* ⊣ Lj^*` for an open immersion with closed image -/

section OpenClosed

variable {U X : AlgebraicSpaces B S hS} (j : U ⟶ X)

/-- For an adjunction `L ⊣ R`, `ψ ≫ η = η ≫ R(L ψ)`, i.e. `homEquiv (L.map ψ) = ψ ≫ η`. -/
private theorem homEquiv_map_eq {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {P Q : C} (ψ : P ⟶ Q) :
    adj.homEquiv _ _ (L.map ψ) = ψ ≫ adj.unit.app Q := by
  rw [Adjunction.homEquiv_unit]
  exact (adj.unit.naturality ψ).symm

/-- **Morphisms from `Rj_*M` to an object supported off the image of `j` vanish**, for `j` an
open immersion with closed image (Stacks 08GG (1)(a), 0AFJ, 08GF). -/
theorem hom_push_eq_zero (hEDS : EDSOfComplSubsetInput B S hS) (h08GGu : Tag08GGUnitInput B S hS)
    (hdisj : PullbackDisjointInput B S hS) (h0AFJ : Tag0AFJInput B S hS)
    (hj : IsOpenImmersion B S hS j.hom)
    (hcl : IsClosed (Set.range (pointsMap B S hS U.1 j.hom)))
    (M : D B S hS U)
    {N : D B S hS X}
    (hN : CohomologySupportedOn B S hS X.1 X.2 (Set.range (pointsMap B S hS U.1 j.hom))ᶜ N)
    (φ : (push j).obj M ⟶ N) : φ = 0 := by
  set W := Set.range (pointsMap B S hS U.1 j.hom) with hWdef
  have hWo : IsOpen W := (isOpenMap_pointsMap_of_isOpenImmersion B S hS j.hom hj).isOpen_range
  have hUo := isOpenSubspace_openSubspaceOfPoints B S hS X.2 W hWo
  have hVo := isOpenSubspace_openSubspaceOfPoints B S hS X.2 Wᶜ hcl.isOpen_compl
  have hrU := range_pointsMap_ι_openSubspaceOfPoints B S hS (F := X.1) W
  have hrV := range_pointsMap_ι_openSubspaceOfPoints B S hS (F := X.1) Wᶜ
  have hsq := hEDS X.2 (openSubspaceOfPoints B S hS X.1 W) hUo hVo.1
    (openSubspaceOfPoints B S hS X.1 Wᶜ).ι hVo.2 (by rw [hrU, hrV])
  let v := edsEtaleMap hsq
  let adjv := etaleDerivedModuleAdjunction B S hS v (isEtale_edsEtaleMap hsq)
  have hη : IsIso (adjv.unit.app N) := h08GGu hsq adjv N (by rwa [hrU])
  -- `Rj_*M` is supported on the closed set `W`, which `|V|` misses.
  have hsupp : CohomologySupportedOn B S hS X.1 X.2 W ((push j).obj M) :=
    push_supported h0AFJ W j hcl (fun i => by
      rw [hWdef, Set.preimage_range]
      exact Set.subset_univ _)
  have h0 : IsZero ((smallEtaleDerivedModulePullback B S hS v).obj ((push j).obj M)) :=
    hdisj v W _ hsupp (by
      change Disjoint (Set.range (pointsMap B S hS _ (openSubspaceOfPoints B S hS X.1 Wᶜ).ι)) W
      rw [hrV]
      exact disjoint_compl_left)
  have h0' : IsZero ((etaleModulePullback.{u, u} B S hS v
      (isEtale_edsEtaleMap hsq)).mapDerivedCategory.obj ((push j).obj M)) :=
    h0.of_iso ((smallEtaleDerivedModulePullbackIsoEtale B S hS v _).app _).symm
  have hcomp : φ ≫ adjv.unit.app N = 0 ≫ adjv.unit.app N := by
    have e1 := homEquiv_map_eq adjv φ
    have e2 := homEquiv_map_eq adjv (0 : (push j).obj M ⟶ N)
    have e3 : (etaleModulePullback.{u, u} B S hS v (isEtale_edsEtaleMap hsq)).mapDerivedCategory.map
        φ = (etaleModulePullback.{u, u} B S hS v (isEtale_edsEtaleMap hsq)).mapDerivedCategory.map
          (0 : (push j).obj M ⟶ N) := h0'.eq_of_src _ _
    rw [e3] at e1
    exact e1.symm.trans e2
  exact (Iso.cancel_iso_hom_right φ 0 (@asIso _ _ _ _ _ hη)).1 hcomp

variable (hcounit : OpenImmersionCounitInput B S hS) (hres : EtaleRestrictionSupportInput B S hS)
  (hsuppT : SupportTriangulatedInput B S hS)

/-- The adjunction `Lj^* ⊣ Rj_*` on `D(𝒪)` (`Spaces.pullPushAdj`, Stacks 07A6). -/
abbrev pullPushModAdj : pull j ⊣ push j := pullPushAdj j

include hcounit hres in
/-- **The cone of the unit `E ⟶ Rj_*Lj^*E` is supported off the image of `j`**, for `j` an open
immersion: its restriction to `U` vanishes, the counit `Lj^*Rj_* ⟶ 1` being invertible (`Rj_*`
is fully faithful, `OpenImmersionCounitInput`), and an object whose restriction to `U` vanishes
is supported off `|U|` (Stacks 08GF, `EtaleRestrictionSupportInput`). -/
theorem exists_triangle_unit (hj : IsOpenImmersion B S hS j.hom)
    (E : D B S hS X) :
    ∃ (C : D B S hS X)
      (g : (push j).obj ((pull j).obj E) ⟶ C) (h : C ⟶ E⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk ((pullPushModAdj j).unit.app E) g h ∈ distTriang _ ∧
        CohomologySupportedOn B S hS X.1 X.2 (Set.range (pointsMap B S hS U.1 j.hom))ᶜ C := by
  obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle
    ((pullPushModAdj j).unit.app E)
  refine ⟨C, g, h, hT, ?_⟩
  have hff := pushFullyFaithful hcounit j hj
  have := hff.full
  have := hff.faithful
  have hiso : IsIso ((pull j).map ((pullPushModAdj j).unit.app E)) := by
    have h1 := (pullPushModAdj j).left_triangle_components E
    have : IsIso ((pull j).map ((pullPushModAdj j).unit.app E) ≫
        (pullPushModAdj j).counit.app ((pull j).obj E)) := by
      rw [h1]; exact CategoryTheory.IsIso.id _
    exact IsIso.of_isIso_comp_right _ ((pullPushModAdj j).counit.app ((pull j).obj E))
  have hz : IsZero ((pull j).obj C) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ ((pull j).map_distinguished _ hT)).2 hiso
  have hét := isEtale_of_isOpenImmersion B S hS hj
  exact hres j hét C (hz.of_iso ((smallEtaleDerivedModulePullbackIsoEtale B S hS j hét).app C).symm)

variable (hEDS : EDSOfComplSubsetInput B S hS) (h08GGu : Tag08GGUnitInput B S hS)
  (hdisj : PullbackDisjointInput B S hS) (h0AFJ : Tag0AFJInput B S hS)

include hcounit hres hsuppT hEDS h08GGu hdisj h0AFJ in
/-- **Composing with the unit `E ⟶ Rj_*Lj^*E` is a bijection on morphisms out of `Rj_*M`**, for
`j` an open immersion with closed image: the cone of the unit and its desuspension are supported
off the image of `j` (`exists_triangle_unit`), so morphisms from `Rj_*M` into them vanish
(`hom_push_eq_zero`). -/
theorem bijective_comp_unit (hj : IsOpenImmersion B S hS j.hom)
    (hcl : IsClosed (Set.range (pointsMap B S hS U.1 j.hom)))
    (M : D B S hS U)
    (E : D B S hS X) :
    Function.Bijective (fun φ : (push j).obj M ⟶ E => φ ≫ (pullPushModAdj j).unit.app E) := by
  obtain ⟨C, g, h, hT, hC⟩ := exists_triangle_unit j hcounit hres hj E
  have hC' : CohomologySupportedOn B S hS X.1 X.2 (Set.range (pointsMap B S hS U.1 j.hom))ᶜ
      (C⟦(-1 : ℤ)⟧) :=
    ((isTriangulated_support hsuppT X
      (Set.range (pointsMap B S hS U.1 j.hom))ᶜ).toIsStableUnderShift.isStableUnderShiftBy
        (-1 : ℤ)).le_shift C hC
  constructor
  · intro φ₁ φ₂ h12
    simp only at h12
    have h0 : (φ₁ - φ₂) ≫ (Pretriangulated.Triangle.invRotate
        (Pretriangulated.Triangle.mk ((pullPushModAdj j).unit.app E) g h)).mor₂ = 0 := by
      change (φ₁ - φ₂) ≫ (pullPushModAdj j).unit.app E = 0
      rw [Preadditive.sub_comp, h12, sub_self]
    obtain ⟨k, hk⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _
      (Pretriangulated.inv_rot_of_distTriang _ hT) (φ₁ - φ₂) h0
    have hk0 : k = 0 := hom_push_eq_zero j hEDS h08GGu hdisj h0AFJ hj hcl M hC' k
    rw [hk0, zero_comp] at hk
    exact sub_eq_zero.1 hk
  · intro ψ
    obtain ⟨φ, hφ⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _ hT ψ
      (hom_push_eq_zero j hEDS h08GGu hdisj h0AFJ hj hcl M hC (ψ ≫ g))
    exact ⟨φ, hφ.symm⟩

/-- **`Rj_* ⊣ Lj^*` on `D(𝒪)`** for `j : U ⟶ X` an open immersion with closed image: the
bijection `Hom(Rj_*M, E) ≃ Hom(Rj_*M, Rj_*Lj^*E) ≃ Hom(M, Lj^*E)` (`bijective_comp_unit`, then
full faithfulness of `Rj_*`). -/
def pushPullAdj (hj : IsOpenImmersion B S hS j.hom)
    (hcl : IsClosed (Set.range (pointsMap B S hS U.1 j.hom))) : push j ⊣ pull j :=
  let hff := pushFullyFaithful hcounit j hj
  let e := fun M E => Equiv.ofBijective _
    (bijective_comp_unit j hcounit hres hsuppT hEDS h08GGu hdisj h0AFJ hj hcl M E)
  have he : ∀ M E (x : (push j).obj M ⟶ (push j).obj ((pull j).obj E)),
      (e M E).symm x ≫ (pullPushModAdj j).unit.app E = x := fun M E x =>
    Equiv.ofBijective_apply_symm_apply _ _ x
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M E => (e M E).trans hff.homEquiv.symm
      homEquiv_naturality_left_symm := fun {M' M E} f g => by
        apply (e M' E).injective
        simp only [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
        change hff.homEquiv (f ≫ g) = ((push j).map f ≫ (e M E).symm (hff.homEquiv g)) ≫ _
        rw [Category.assoc, he]
        exact (push j).map_comp f g
      homEquiv_naturality_right := fun {M E E'} f g => by
        apply hff.homEquiv.injective
        simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
        change (f ≫ g) ≫ (pullPushModAdj j).unit.app E' =
          (push j).map (hff.preimage (f ≫ (pullPushModAdj j).unit.app E) ≫ (pull j).map g)
        rw [Functor.map_comp, hff.map_preimage, Category.assoc, Category.assoc,
          Adjunction.unit_naturality] }

variable (h08FA : Tag08FAInput B S hS) (h08F4 : Tag08F4Input B S hS)

/-- **`Rj_* ⊣ Lj^*` on `D_qc`** for an open immersion with closed image: the restriction of
`pushPullAdj` to the full subcategories `D_qc` (Mathlib's `Adjunction.restrictFullyFaithful`). -/
def pushQcPullQcAdj (hj : IsOpenImmersion B S hS j.hom)
    (hcl : IsClosed (Set.range (pointsMap B S hS U.1 j.hom)))
    (hjqc : IsQuasiCompact B S hS j.hom) (hjqs : IsQuasiSeparated B S hS j.hom) :
    pushQc h08FA j hjqc hjqs ⊣ pullQc h08F4 j :=
  (pushPullAdj j hcounit hres hsuppT hEDS h08GGu hdisj h0AFJ hj hcl).restrictFullyFaithful
    (Dqc U).fullyFaithfulι (Dqc X).fullyFaithfulι
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

variable (hZ : B.Contains (⊤_ Scheme.{u})) (h0E55 : Tag0E55Input B S hS)

variable {hZ} in
/-- **`j^× ≅ Lj^*` on `D_qc`** for an open immersion `j` with closed image (uniqueness of right
adjoints of `Rj_*`). -/
def upperTimesIsoPullQc (hjq : IsQcqsHom hZ j) (hj : IsOpenImmersion B S hS j.hom)
    (hcl : IsClosed (Set.range (pointsMap B S hS U.1 j.hom))) :
    upperTimes h08FA h0E55 j hjq ≅ pullQc h08F4 j :=
  (upperTimesAdj h08FA h0E55 j hjq).rightAdjointUniq
    (pushQcPullQcAdj j hcounit hres hsuppT hEDS h08GGu hdisj h0AFJ h08FA h08F4 hj hcl hjq.qc hjq.qs)

end OpenClosed

/-! ### Lemma 2.22 -/

section Lemma222

variable (h08FA : Tag08FAInput B S hS) (h08F4 : Tag08F4Input B S hS)
  (h0E55 : Tag0E55Input B S hS) (hqcs : QuasiCompactSourceInput B S hS)
  (h04NX : Tag04NXInput B S hS) (h073B : Tag073BInput B S hS)
  (hcounit : OpenImmersionCounitInput B S hS) (hres : EtaleRestrictionSupportInput B S hS)
  (hsuppT : SupportTriangulatedInput B S hS) (hEDS : EDSOfComplSubsetInput B S hS)
  (h08GGu : Tag08GGUnitInput B S hS) (hdisj : PullbackDisjointInput B S hS)
  (h0AFJ : Tag0AFJInput B S hS)

variable {hZ : B.Contains (⊤_ Scheme.{u})}

/-- `f^×` depends on `f` only (transport along an equality of morphisms). -/
def upperTimesCongr {X Y : AlgebraicSpaces B S hS} {f f' : X ⟶ Y} (h : f = f')
    (hf : IsQcqsHom hZ f) (hf' : IsQcqsHom hZ f') :
    upperTimes h08FA h0E55 f hf ≅ upperTimes h08FA h0E55 f' hf' := by
  subst h; exact Iso.refl _

/-- **The isomorphism `f^× ≅ f^!` of Lemma 2.22** (`lem:neeman187`) for a proper `f : Y ⟶ X`,
`Y` quasi-compact quasi-separated and `X` quasi-compact quasi-separated, and *any* Nagata
compactification `c : f = p ∘ j` defining `f^! = Lj^* ∘ p^×`:
`f^× ≅ (p ∘ j)^× ≅ j^× ∘ p^× ≅ Lj^* ∘ p^×` (`upperTimesCompIso`, `upperTimesIsoPullQc`; `j` is
proper by Stacks 04NX (2), so its image is closed). -/
def upperTimesIsoUpperShriek {Y X : AlgebraicSpaces B S hS} {f : Y ⟶ X} (hf : IsQcqsHom hZ f)
    (hfp : IsProper B S hS f.hom) (c : Compactification f)
    (hXqc : IsQuasiCompactSpace B S hS X.1) :
    upperTimes h08FA h0E55 f hf ≅ upperShriek h08FA h08F4 h0E55 hqcs c hXqc hf.tgtQs :=
  have hpq := c.isQcqsHom_p hqcs hXqc hf.tgtQs
  have hjp : IsProper B S hS (c.j.hom ≫ c.p.hom) := by
    have := c.fac
    rw [← this] at hfp
    exact hfp
  have hjprop : IsProper B S hS c.j.hom :=
    h04NX Y.2 c.space.2 X.2 c.j.hom c.p.hom hjp c.isProper_p.1
  have hcl : IsClosed (Set.range (pointsMap B S hS Y.1 c.j.hom)) :=
    (isClosedMap_pointsMap_of_pullback_fst_id B S hS c.j.hom
      (hjprop.2.2 _ c.space.2 (𝟙 _))).isClosed_range
  have hjq : IsQcqsHom hZ c.j :=
    ⟨hf.srcQc, hf.srcQs, hpq.srcQs, h073B hZ c.space.2 hpq.srcQs hf.srcQc c.j.hom,
      isQuasiSeparated_of_isOpenImmersion c.j c.isOpenImmersion_j⟩
  have hjpq : IsQcqsHom hZ (c.j ≫ c.p) := by rw [c.fac]; exact hf
  upperTimesCongr h08FA h0E55 c.fac.symm hf hjpq ≪≫
    upperTimesCompIso h08FA h0E55 c.j c.p hjq hpq hjpq ≪≫
    Functor.isoWhiskerLeft (upperTimes h08FA h0E55 c.p hpq)
      (upperTimesIsoPullQc c.j hcounit hres hsuppT hEDS h08GGu hdisj h0AFJ h08FA h08F4 h0E55 hjq
        c.isOpenImmersion_j hcl)

include h04NX h073B hcounit hres hsuppT hEDS h08GGu hdisj h0AFJ in
/-- **Lemma 2.22** (`lem:neeman187`): let `f : Y ⟶ X` be a 1-morphism of `(Sp/S)_{Noeth,sep,fp}`.
If `f` is proper, there is a natural isomorphism `f^× ≅ f^!` on `D_qc`, for `f^! = Lj^* ∘ p^×`
defined by any Nagata compactification `f = p ∘ j`. -/
theorem lemma_2_22 {Y X : AlgebraicSpaces B S hS} {f : Y ⟶ X} (hf : IsNoethSepFpHom hZ f)
    (hfp : Statements.IsProperHom f) (c : Compactification f) :
    Nonempty (upperTimes h08FA h0E55 f hf.isQcqsHom ≅
      upperShriek h08FA h08F4 h0E55 hqcs c hf.noetherian_target.1 hf.noetherian_target.2.1) :=
  ⟨upperTimesIsoUpperShriek h08FA h08F4 h0E55 hqcs h04NX h073B hcounit hres hsuppT hEDS h08GGu
    hdisj h0AFJ hf.isQcqsHom hfp c hf.noetherian_target.1⟩

end Lemma222

end RelativeFM.Spaces.Duality
