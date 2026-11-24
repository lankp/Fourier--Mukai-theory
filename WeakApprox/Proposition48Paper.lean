/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.Setup44
import WeakApprox.Lemma46
import WeakApprox.Proposition48
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.Tactic

/-!
# Proposition 4.8 from its paper hypotheses

The library's `WeakApprox/Proposition48.lean` proves Proposition 4.8 with
Lemma 4.6 as an explicit premise `hlemma46`.  This file discharges it: the
liftable class is strictly full, closed under small coproducts and under
extensions, contains the shifts `(i^*G)⟦n⟧` for `-A-1 ≤ n ≤ A`, and satisfies
the two displayed inclusions, from exactly the paper's hypotheses `hglue`,
`hG_le`, `hGU`, `hvan`.

Two improvements over the version with the premise: coproducts on `D_Z` are
*constructed* from those on `D` (the fully faithful right adjoint `i_*` makes
`D_Z` a reflective subcategory), so only `[HasCoproducts.{v} D]` and
`[HasCoproducts.{v} DU]` are assumed; and the `Setup44` instance discharges the
three Lemma 4.6 inputs from the setup's own fields.

Found by a member of the Ultramath run `smwur4wqg` (direction D4).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v uZ uD uU

noncomputable section

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

/-- **Proposition 4.8, with Lemma 4.6 supplied by its paper hypotheses.**
For `P = ⟨G⟩^[-3A,3A] ∩ D^{≤A+1}` and `K = D^{≤A+1}`, the liftable class
has exactly the six conclusions of `proposition_4_8`.  No premise universally
quantifying over the shifts in Lemma 4.6 is assumed.  Coproducts on `D_Z`,
used by Lemma 3.1(5), are constructed from those on `D`: `i_*` is a fully
faithful right adjoint, so `D_Z` is a reflective subcategory of `D`. -/
theorem proposition_4_8_of_lemma_4_6
    [HasCoproducts.{v} DU] [HasCoproducts.{v} D]
    (R : Recollement DZ D DU) (WU : WeakApproximationData DU)
    (tD : TStructure D) (tZ : TStructure DZ)
    (hglue : tD.le 0 = gluedLe R.iStar R.jStar tZ WU.t 0)
    (G : D) (hG_le : tD.le 0 G)
    (hGU : envelope G 0 0 (R.jShriek.obj WU.G))
    (hvan : ∀ {Z : D}, tD.le (-WU.A) Z → ∀ f : G ⟶ Z, f = 0) :
    (liftableClass R.iStar (lemma46P G tD WU.A) (tD.le (WU.A + 1))).IsClosedUnderIsomorphisms ∧
    (∀ J : Type v, (liftableClass R.iStar (lemma46P G tD WU.A)
      (tD.le (WU.A + 1))).IsClosedUnderColimitsOfShape (Discrete J)) ∧
    (liftableClass R.iStar (lemma46P G tD WU.A)
      (tD.le (WU.A + 1))).IsTriangulatedClosed₂ ∧
    (∀ n : ℤ, -WU.A - 1 ≤ n → n ≤ WU.A →
      liftableClass R.iStar (lemma46P G tD WU.A)
        (tD.le (WU.A + 1)) ((R.iStar.obj G)⟦n⟧)) ∧
    envelope (R.iStar.obj G) (-WU.A) WU.A ≤
      Coprod (shiftInterval (R.iStar.obj G) (-WU.A) (WU.A + 1)) ∧
    Coprod (shiftInterval (R.iStar.obj G) (-WU.A) (WU.A + 1)) ≤
      liftableClass R.iStar (lemma46P G tD WU.A) (tD.le (WU.A + 1)) := by
  letI : Reflective R.iLower := ⟨_, R.iStarAdj⟩
  letI : HasCoproducts.{v} DZ := fun _ => hasColimitsOfShape_of_reflective R.iLower
  letI : (envelope G (-3 * WU.A) (3 * WU.A)).IsClosedUnderIsomorphisms :=
    lemma_3_1_1_strictlyFull G (-3 * WU.A) (3 * WU.A)
  letI : (lemma46P G tD WU.A).IsClosedUnderIsomorphisms := {
    of_iso := fun e hX => ⟨(envelope G (-3 * WU.A) (3 * WU.A)).prop_of_iso e hX.1,
      (tD.le (WU.A + 1)).prop_of_iso e hX.2⟩ }
  letI : (tD.le (WU.A + 1)).IsTriangulatedClosed₂ :=
    TStructure.le_isTriangulatedClosed₂ tD (WU.A + 1)
  letI : (envelope G (-3 * WU.A) (3 * WU.A)).IsTriangulatedClosed₂ :=
    lemma_3_1_1_extensions G (-3 * WU.A) (3 * WU.A)
  letI : (lemma46P G tD WU.A).IsTriangulatedClosed₂ := by
    apply ObjectProperty.IsTriangulatedClosed₂.mk'
    intro T hT h₁ h₃
    exact ⟨(envelope G (-3 * WU.A) (3 * WU.A)).ext_of_isTriangulatedClosed₂
      T hT h₁.1 h₃.1, (tD.isLE₂ T hT (WU.A + 1) ⟨h₁.2⟩ ⟨h₃.2⟩).le⟩
  letI (J : Type v) :
      (lemma46P G tD WU.A).IsClosedUnderColimitsOfShape (Discrete J) := by
    letI : (envelope G (-3 * WU.A) (3 * WU.A)).IsClosedUnderColimitsOfShape
        (Discrete J) := lemma_3_1_1_coproducts G (-3 * WU.A) (3 * WU.A) J
    letI : (tD.le (WU.A + 1)).IsClosedUnderColimitsOfShape (Discrete J) :=
      TStructure.le_isClosedUnderColimitsOfShape tD (WU.A + 1) (Discrete J)
    refine ⟨?_⟩
    rintro X ⟨p⟩
    exact ⟨(envelope G (-3 * WU.A) (3 * WU.A)).prop_of_isColimit p.isColimit
        (fun j => (p.prop_diag_obj j).1),
      (tD.le (WU.A + 1)).prop_of_isColimit p.isColimit
        (fun j => (p.prop_diag_obj j).2)⟩
  letI (J : Type v) : PreservesColimitsOfShape (Discrete J) R.iStar := by
    letI := Adjunction.leftAdjoint_preservesColimits.{v, v} R.iStarAdj
    infer_instance
  have hPK : lemma46P G tD WU.A ≤ tD.le (WU.A + 1) := fun _ hX => hX.2
  have hKshift : ∀ {X : D}, tD.le (WU.A + 1) X → tD.le (WU.A + 1) (X⟦(1 : ℤ)⟧) := by
    intro X hX
    apply tD.le_monotone (show WU.A + 1 - 1 ≤ WU.A + 1 by omega)
    exact tD.le_shift (WU.A + 1) 1 (WU.A + 1 - 1) (by ring) X hX
  have hlemma46 : ∀ n : ℤ, -WU.A - 1 ≤ n → n ≤ WU.A →
      liftableClass R.iStar (lemma46P G tD WU.A)
        (tD.le (WU.A + 1)) ((R.iStar.obj G)⟦n⟧) := by
    intro n hn₁ hn₂ Y hY f'
    exact lemma_4_6 R WU tD tZ hglue G hG_le hGU hvan hY hn₁ hn₂ f'
  exact proposition_4_8 R.iStar (lemma46P G tD WU.A) (tD.le (WU.A + 1))
    G WU.A hPK hKshift hlemma46

/-- **Proposition 4.8, final inclusion, from the hypotheses of Lemma 4.6.**
This is the corresponding `Coprod (shiftInterval ...) ≤ liftableClass` form;
it is the last conjunct of `proposition_4_8_of_lemma_4_6`, with no separate
Lemma 4.6 premise. -/
theorem coprod_shiftInterval_le_liftableClass_of_lemma_4_6
    [HasCoproducts.{v} DU] [HasCoproducts.{v} D]
    (R : Recollement DZ D DU) (WU : WeakApproximationData DU)
    (tD : TStructure D) (tZ : TStructure DZ)
    (hglue : tD.le 0 = gluedLe R.iStar R.jStar tZ WU.t 0)
    (G : D) (hG_le : tD.le 0 G)
    (hGU : envelope G 0 0 (R.jShriek.obj WU.G))
    (hvan : ∀ {Z : D}, tD.le (-WU.A) Z → ∀ f : G ⟶ Z, f = 0) :
    Coprod (shiftInterval (R.iStar.obj G) (-WU.A) (WU.A + 1)) ≤
      liftableClass R.iStar (lemma46P G tD WU.A) (tD.le (WU.A + 1)) :=
  (proposition_4_8_of_lemma_4_6 R WU tD tZ hglue G hG_le hGU hvan).2.2.2.2.2

namespace Setup44

/-- **Proposition 4.8 under Setup 4.4.**  The three inputs to Lemma 4.6 are
discharged by `G_mem_le_zero`, `jShriek_GU_mem_envelope_zero`, and
`G_hom_vanishing`; the glued-aisle identity and the identifications of the
weak approximation data are the other Setup 4.4 fields.  The resulting six
conclusions use exactly `S.P`, `S.K`, `S.G`, and `S.A`.  No separate coproduct
assumption on `D_Z` is necessary: it follows from the one on `D` and the
recollement, as in `proposition_4_8_of_lemma_4_6`. -/
theorem proposition_4_8 [HasCoproducts.{v} DU] [HasCoproducts.{v} D]
    (S : Setup44 DZ D DU) :
    (liftableClass S.R.iStar S.P (S.tD.le S.K)).IsClosedUnderIsomorphisms ∧
    (∀ J : Type v, (liftableClass S.R.iStar S.P
      (S.tD.le S.K)).IsClosedUnderColimitsOfShape (Discrete J)) ∧
    (liftableClass S.R.iStar S.P (S.tD.le S.K)).IsTriangulatedClosed₂ ∧
    (∀ n : ℤ, -S.A - 1 ≤ n → n ≤ S.A →
      liftableClass S.R.iStar S.P (S.tD.le S.K) ((S.R.iStar.obj S.G)⟦n⟧)) ∧
    envelope (S.R.iStar.obj S.G) (-S.A) S.A ≤
      Coprod (shiftInterval (S.R.iStar.obj S.G) (-S.A) (S.A + 1)) ∧
    Coprod (shiftInterval (S.R.iStar.obj S.G) (-S.A) (S.A + 1)) ≤
      liftableClass S.R.iStar S.P (S.tD.le S.K) := by
  have hglue : S.tD.le 0 = gluedLe S.R.iStar S.R.jStar S.tZ S.approxU.t 0 := by
    rw [S.approxU_t]
    exact S.tD_glued
  have hGU : envelope S.G 0 0 (S.R.jShriek.obj S.approxU.G) := by
    rw [S.approxU_G]
    exact S.jShriek_GU_mem_envelope_zero
  have hvan : ∀ {Z : D}, S.tD.le (-S.approxU.A) Z → ∀ f : S.G ⟶ Z, f = 0 := by
    intro Z hZ f
    rw [S.approxU_A] at hZ
    exact S.G_hom_vanishing hZ f
  have hP : S.P = lemma46P S.G S.tD S.approxU.A := by
    ext Z
    simp only [P, B, K, lemma46P, S.approxU_A, ObjectProperty.prop_inf_iff, neg_mul]
  rw [hP]
  simpa only [K, S.approxU_A] using
    (proposition_4_8_of_lemma_4_6 S.R S.approxU S.tD S.tZ hglue S.G
      S.G_mem_le_zero hGU hvan)

/-- **Proposition 4.8 under Setup 4.4, final inclusion.**  This is the
`Coprod (shiftInterval ...) ≤ liftableClass` consequence used in the two-stage
proof of Theorem 1.1, with Lemma 4.6 proved rather than supplied as a premise. -/
theorem coprod_shiftInterval_le_liftableClass [HasCoproducts.{v} DU]
    [HasCoproducts.{v} D] (S : Setup44 DZ D DU) :
    Coprod (shiftInterval (S.R.iStar.obj S.G) (-S.A) (S.A + 1)) ≤
      liftableClass S.R.iStar S.P (S.tD.le S.K) :=
  S.proposition_4_8.2.2.2.2.2

end Setup44

end
end RelativeWeakApprox

#print axioms RelativeWeakApprox.proposition_4_8_of_lemma_4_6
#print axioms RelativeWeakApprox.Setup44.proposition_4_8
#print axioms RelativeWeakApprox.Setup44.coprod_shiftInterval_le_liftableClass
