/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.PaperLemma34M2
import WeakApprox.Recollement
import WeakApprox.PLift
import WeakApprox.Lemma34
import WeakApprox.Lemma42
import WeakApprox.Closure
import WeakApprox.Shift
import WeakApprox.Functoriality
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.Tactic

/-!
# Lemma 4.6: lifts to aisles

This file proves the core lift construction of Lemma 4.6 of Lank--Pauwels.

Found by a member of the Ultramath run `smwunmkmj` (direction D3).
The only universe restriction is the one already present in
`WeakApprox.Functoriality`: the three categories have a common hom universe.
The source of the morphism is transported along the canonical shift
commutation isomorphism; this is the identification made in the paper.

The approximation triangle is unshifted explicitly.  For the Hom-exactness
step we use the shift by one of the approximation triangle, rather than the
paper's auxiliary morphisms `ξ[-1]` and `ξ''[1]`; the resulting cone morphism
is negated, which takes account of the sign in the shift of a triangle.
-/

@[expose] public section

namespace RelativeWeakApprox.PaperM2

open RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

universe v uZ uD uU

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [IsTriangulated DZ] [IsTriangulated D] [IsTriangulated DU]

/- We use `PLift` from `WeakApprox.PLift`, whose commuting condition is
`iStar.map q = θ.hom ≫ f'`, i.e. the paper's `i^*q = f' ∘ θ`. -/

/-- The shifted approximation triangle (4.2), with the bounds obtained from
Lemma 3.4.  Here `K = A+1` and `B = 3*A`. -/
theorem lemma_4_6_approximation (R : Recollement DZ D DU)
    (WU : PaperWeakApproximationData DU) (tD : TStructure D) (tZ : TStructure DZ)
    (hglue : tD.le 0 = gluedLe R.iStar R.jStar tZ WU.t 0)
    {Y : D} (hY : tD.le (WU.A + 1) Y) :
    ∃ (W V : DU) (w : W ⟶ R.jStar.obj Y) (c : R.jStar.obj Y ⟶ V)
      (d : V ⟶ W⟦(1 : ℤ)⟧),
      Triangle.mk w c d ∈ distTriang DU ∧
      envelope WU.G (1 - 3 * WU.A) (2 * WU.A + 1) W ∧
      WU.t.le (WU.A + 1) W ∧ WU.t.le (-2 * WU.A) V := by
  let A : ℤ := WU.A
  let K : ℤ := A + 1
  let M : DU := R.jStar.obj Y
  have hM : WU.t.le K M := by
    exact lemma_4_2_jStar R.iStar R.jStar tD tZ WU.t hglue K hY
  have hMK : WU.t.le 0 (M⟦K⟧) :=
    WU.t.le_shift K K 0 (by simp) M hM
  obtain ⟨E, V', a, c', d', hT', hE, hE0, hV'⟩ :=
    lemma_3_4 WU hMK (m := 3 * A + 1) (by
      dsimp [A]
      have := WU.A_pos
      omega)
  let W : DU := E⟦-K⟧
  let V : DU := V'⟦-K⟧
  let S : Triangle DU := (Triangle.shiftFunctor DU (-K)).obj (Triangle.mk a c' d')
  let eM : S.obj₂ ≅ M := shiftShiftNeg M K
  let w : W ⟶ M := S.mor₁ ≫ eM.hom
  let c : M ⟶ V := eM.inv ≫ S.mor₂
  let d : V ⟶ W⟦(1 : ℤ)⟧ := S.mor₃
  have hS : S ∈ distTriang DU := Triangle.shift_distinguished _ hT' (-K)
  have hT : Triangle.mk w c d ∈ distTriang DU := by
    apply isomorphic_distinguished S hS
    exact Triangle.isoMk _ _ (Iso.refl _) eM.symm (Iso.refl _)
      (by
        change (S.mor₁ ≫ eM.hom) ≫ eM.inv = 𝟙 _ ≫ S.mor₁
        simp)
      (by
        change (eM.inv ≫ S.mor₂) ≫ 𝟙 _ = eM.inv ≫ S.mor₂
        simp)
      (by
        change S.mor₃ ≫ (shiftFunctor DU 1).map (𝟙 _) = 𝟙 _ ≫ S.mor₃
        simp)
  have hW : envelope WU.G (1 - 3 * A) (2 * A + 1) W := by
    have h := map_shift_envelope WU.G (1 - (3 * A + 1) - A) A (-K) hE
    have hlo : 1 - (3 * A + 1) - A - -K = 1 - 3 * A := by
      dsimp [K]
      ring
    have hhi : A - -K = 2 * A + 1 := by
      dsimp [K]
      ring
    rw [hlo, hhi] at h
    exact h
  have hWa : WU.t.le K W := by
    exact WU.t.le_shift 0 (-K) K (by simp) E hE0
  have hVa : WU.t.le (-2 * A) V := by
    apply WU.t.le_shift (-(3 * A + 1)) (-K) (-2 * A) (by
      dsimp [K]
      ring) V' hV'
  exact ⟨W, V, w, c, d, hT, hW, hWa, hVa⟩

/-- The Hom-vanishing (4.3), expressed directly in the shift convention used
below.  It follows from the glued-aisle bounds and the global vanishing of
`Hom(G, D^{≤-A})`. -/
theorem lemma_4_6_vanishing (R : Recollement DZ D DU)
    (tD : TStructure D) (tZ : TStructure DZ) (tU : TStructure DU)
    (hglue : tD.le 0 = gluedLe R.iStar R.jStar tZ tU 0)
    (G : D) {A : ℤ}
    (hvan : ∀ {Z : D}, tD.le (-A) Z → ∀ f : G ⟶ Z, f = 0)
    {V : DU} (hV : tU.le (-2 * A) V) {n : ℤ} (hn : n ≤ A)
    (f : G⟦n⟧ ⟶ R.jShriek.obj V⟦(1 : ℤ)⟧) : f = 0 := by
  have hjV : tD.le (-2 * A) (R.jShriek.obj V) :=
    lemma_4_2_jShriek R.iStar R.jShriek R.jStar tD tZ tU hglue
      R.jShriekAdj R.iStar_jShriek (-2 * A) hV
  have hs : tD.le (n - 1 - 2 * A) (R.jShriek.obj V⟦1 - n⟧) :=
    tD.le_shift (-2 * A) (1 - n) (n - 1 - 2 * A) (by ring) _ hjV
  have hs' : tD.le (-A) (R.jShriek.obj V⟦1 - n⟧) :=
    tD.le_monotone (by omega) _ hs
  have htarget : tD.le (-A) ((R.jShriek.obj V⟦(1 : ℤ)⟧)⟦-n⟧) := by
    apply (tD.le (-A)).prop_of_iso
      ((shiftFunctorAdd' D (1 : ℤ) (-n) (1 - n) rfl).app (R.jShriek.obj V))
    exact hs'
  let f₀ : G ⟶ ((R.jShriek.obj V⟦(1 : ℤ)⟧)⟦-n⟧) :=
    (shiftShiftNeg G n).inv ≫ f⟦-n⟧'
  have hf₀ : f₀ = 0 := hvan htarget f₀
  apply (shiftFunctor D (-n)).map_injective
  rw [Functor.map_zero, ← cancel_epi (shiftShiftNeg G n).inv, comp_zero]
  exact hf₀

/-- The envelope bound for `j_!W`.  Coproduct preservation is proved from the
adjunction `j_! ⊣ j^*`; it is not added as a hypothesis. -/
theorem lemma_4_6_envelope_jShriek [HasCoproducts.{v} DU] [HasCoproducts.{v} D]
    (R : Recollement DZ D DU) (WU : PaperWeakApproximationData DU) (G : D)
    (hGU : envelope G 0 0 (R.jShriek.obj WU.G)) {W : DU}
    (hW : envelope WU.G (1 - 3 * WU.A) (2 * WU.A + 1) W) :
    envelope G (-3 * WU.A) (3 * WU.A) (R.jShriek.obj W) := by
  letI (ι : Type v) : PreservesColimitsOfShape (Discrete ι) R.jShriek := by
    letI := Adjunction.leftAdjoint_preservesColimits.{v, v} R.jShriekAdj
    infer_instance
  have hmap := lemma_3_1_3 R.jShriek WU.G G
    (1 - 3 * WU.A) (2 * WU.A + 1) 0 0 hGU hW
  simp only [add_zero] at hmap
  exact lemma31_2_mono G (by have := WU.A_pos; omega)
    (by have := WU.A_pos; omega) _ hmap

/-- The property `P` of Setup 4.4, with `K = A+1` and `B = 3*A`. -/
def lemma46P (G : D) (tD : TStructure D) (A : ℤ) : ObjectProperty D := fun E =>
  envelope G (-3 * A) (3 * A) E ∧ tD.le (A + 1) E

/-- **Lemma 4.6.**  Every morphism from `(i^*G)[n]` to `i^*Y`, with
`Y ∈ D^{≤A+1}` and `-A-1 ≤ n ≤ A`, has a `P`-lift for
`P = ⟨G⟩^[-3A,3A] ∩ D^{≤A+1}`.

The weak approximation data on `D_U` supplies the common bound `A`; `hG_le`,
`hGU`, and `hvan` are respectively the statements `G ∈ D^{≤0}`,
`j_!G_U ∈ ⟨G⟩^[0,0]`, and `Hom(G,D^{≤-A}) = 0` from Setup 4.4.  The glued aisle
is specified by `hglue`.  The `HasCoproducts` hypotheses are needed by the
project's general functoriality theorem for envelopes.  No additional
recollement compatibility is assumed.  “Admits a lift” is rendered as
`Nonempty (PLift ...)`, because `PLift` contains categorical data and the
existence theorems for distinguished triangles eliminate only into `Prop`. -/
theorem lemma_4_6 [HasCoproducts.{v} DU] [HasCoproducts.{v} D]
    (R : Recollement DZ D DU) (WU : PaperWeakApproximationData DU)
    (tD : TStructure D) (tZ : TStructure DZ)
    (hglue : tD.le 0 = gluedLe R.iStar R.jStar tZ WU.t 0)
    (G : D) (hG_le : tD.le 0 G)
    (hGU : envelope G 0 0 (R.jShriek.obj WU.G))
    (hvan : ∀ {Z : D}, tD.le (-WU.A) Z → ∀ f : G ⟶ Z, f = 0)
    {Y : D} (hY : tD.le (WU.A + 1) Y) {n : ℤ}
    (hn₁ : -WU.A - 1 ≤ n) (hn₂ : n ≤ WU.A)
    (f' : (R.iStar.obj G)⟦n⟧ ⟶ R.iStar.obj Y) :
    Nonempty (PLift R.iStar (lemma46P G tD WU.A) f') := by
  obtain ⟨W, V, w, c, d, hT, hW, hWa, hV⟩ :=
    lemma_4_6_approximation R WU tD tZ hglue hY
  let J : Triangle D := R.jShriek.mapTriangle.obj (Triangle.mk w c d)
  have hJ : J ∈ distTriang D := R.jShriek.map_distinguished _ hT
  let S : Triangle D := (Triangle.shiftFunctor D (1 : ℤ)).obj J
  have hS : S ∈ distTriang D := Triangle.shift_distinguished J hJ (1 : ℤ)
  let f₀ : R.iStar.obj (G⟦n⟧) ⟶ R.iStar.obj Y :=
    (R.iStar.commShiftIso n).hom.app G ≫ f'
  let g : G⟦n⟧ ⟶ R.iLower.obj (R.iStar.obj Y) := R.iStarAdj.homEquiv _ _ f₀
  have hf₀ : f₀ = R.iStar.map g ≫ R.iStarAdj.counit.app (R.iStar.obj Y) := by
    calc
      f₀ = (R.iStarAdj.homEquiv _ _).symm (R.iStarAdj.homEquiv _ _ f₀) :=
        ((R.iStarAdj.homEquiv _ _).symm_apply_apply f₀).symm
      _ = _ := R.iStarAdj.homEquiv_counit _ _ g
  let ξ : G⟦n⟧ ⟶ R.jShriek.obj (R.jStar.obj Y)⟦(1 : ℤ)⟧ :=
    g ≫ R.firstConnecting.app Y
  obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₂ S hS ξ
    (lemma_4_6_vanishing R tD tZ WU.t hglue G hvan hV hn₂ _)
  change G⟦n⟧ ⟶ R.jShriek.obj W⟦(1 : ℤ)⟧ at z
  obtain ⟨Q, α, β, hTop⟩ := distinguished_cocone_triangle₂ (-z)
  change ξ = z ≫ ((1 : ℤ).negOnePow • (R.jShriek.map w)⟦(1 : ℤ)⟧') at hz
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul] at hz
  have hcomm : (-z) ≫ (R.jShriek.map w)⟦(1 : ℤ)⟧' =
      g ≫ R.firstConnecting.app Y := by
    simpa only [ξ, Preadditive.neg_comp, Preadditive.comp_neg] using hz.symm
  obtain ⟨q, _hq₁, hq₂⟩ := complete_distinguished_triangle_morphism₂
    (Triangle.mk α β (-z)) (R.firstTriangle Y) hTop (R.first_distinguished Y)
    (R.jShriek.map w) g hcomm
  change Q ⟶ Y at q
  change β ≫ g = q ≫ R.iStarAdj.unit.app Y at hq₂
  have hβ : IsIso (R.iStar.map β) := by
    let T' := R.iStar.mapTriangle.obj (Triangle.mk α β (-z))
    have hT' : T' ∈ distTriang DZ := R.iStar.map_distinguished _ hTop
    have hzero : IsZero T'.obj₁ := R.iStar_jShriek_isZero W
    have h := (T'.isZero₁_iff_isIso₂ hT').1 hzero
    exact h
  let θ : R.iStar.obj Q ≅ (R.iStar.obj G)⟦n⟧ :=
    asIso (R.iStar.map β) ≪≫ (R.iStar.commShiftIso n).app G
  have hmapq : R.iStar.map β ≫ R.iStar.map g =
      R.iStar.map q ≫ R.iStar.map (R.iStarAdj.unit.app Y) := by
    calc
      R.iStar.map β ≫ R.iStar.map g = R.iStar.map (β ≫ g) :=
        (R.iStar.map_comp β g).symm
      _ = R.iStar.map (q ≫ R.iStarAdj.unit.app Y) := congrArg (fun k => R.iStar.map k) hq₂
      _ = R.iStar.map q ≫ R.iStar.map (R.iStarAdj.unit.app Y) :=
        R.iStar.map_comp q (R.iStarAdj.unit.app Y)
  have hq : R.iStar.map q = θ.hom ≫ f' := by
    calc
      R.iStar.map q = R.iStar.map q ≫
          (R.iStar.map (R.iStarAdj.unit.app Y) ≫
            R.iStarAdj.counit.app (R.iStar.obj Y)) := by
        rw [R.iStarAdj.left_triangle_components, Category.comp_id]
      _ = (R.iStar.map q ≫ R.iStar.map (R.iStarAdj.unit.app Y)) ≫
          R.iStarAdj.counit.app (R.iStar.obj Y) := by rw [Category.assoc]
      _ = (R.iStar.map β ≫ R.iStar.map g) ≫
          R.iStarAdj.counit.app (R.iStar.obj Y) := by rw [← hmapq]
      _ = R.iStar.map β ≫
          (R.iStar.map g ≫ R.iStarAdj.counit.app (R.iStar.obj Y)) := by
        rw [Category.assoc]
      _ = R.iStar.map β ≫ f₀ := by rw [← hf₀]
      _ = θ.hom ≫ f' := by simp [θ, f₀, Category.assoc]
  have hJWenv : envelope G (-3 * WU.A) (3 * WU.A) (R.jShriek.obj W) :=
    lemma_4_6_envelope_jShriek R WU G hGU hW
  have hJWa : tD.le (WU.A + 1) (R.jShriek.obj W) :=
    lemma_4_2_jShriek R.iStar R.jShriek R.jStar tD tZ WU.t hglue
      R.jShriekAdj R.iStar_jShriek (WU.A + 1) hWa
  have hGnenv : envelope G (-3 * WU.A) (3 * WU.A) (G⟦n⟧) := by
    apply lemma31_2_mono G (a := -WU.A) (b := WU.A + 1)
      (by have := WU.A_pos; omega) (by have := WU.A_pos; omega)
    apply lemma_3_1_1_contains
    refine ⟨-n, by omega, by omega, ⟨?_⟩⟩
    rw [neg_neg]
  have hGna : tD.le (WU.A + 1) (G⟦n⟧) := by
    have h := tD.le_shift 0 n (-n) (by omega) G hG_le
    exact tD.le_monotone (by omega) _ h
  have hQenv : envelope G (-3 * WU.A) (3 * WU.A) Q := by
    let _ := lemma_3_1_1_extensions G (-3 * WU.A) (3 * WU.A)
    exact (envelope G (-3 * WU.A) (3 * WU.A)).ext_of_isTriangulatedClosed₂
      (Triangle.mk α β (-z)) hTop hJWenv hGnenv
  have hQa : tD.le (WU.A + 1) Q :=
    (tD.isLE₂ (Triangle.mk α β (-z)) hTop (WU.A + 1) ⟨hJWa⟩ ⟨hGna⟩).le
  exact ⟨⟨Q, q, θ, ⟨hQenv, hQa⟩, hq⟩⟩

end RelativeWeakApprox.PaperM2
