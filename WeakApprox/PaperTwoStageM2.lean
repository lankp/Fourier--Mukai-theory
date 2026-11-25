/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.PaperSetup44M2
import WeakApprox.PaperLemma46M2
import WeakApprox.Proposition48
import WeakApprox.WeakApproximable
import Mathlib.Tactic

/-!
# The reverse implication in Theorem 1.1

This file assembles the closing argument of §4 of Lank--Pauwels.  Starting with
an approximation of `i^*F`, Proposition 4.8 lifts its first morphism to `D`.
After taking the cone, Lemma 4.6's approximation (which is the shifted form of
Lemma 3.4) approximates its `j^*`-component.  Remark 3.2(2) glues the two
approximations, and Lemma 4.2 detects the required aisle bound.
-/

@[expose] public section

namespace RelativeWeakApprox.PaperM2

open RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v uZ uD uU

namespace PaperSetup44

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- The glued-aisle identity with the `t`-structure of the supplied data on
`D_U`.  This is only a repackaging of `PaperSetup44.tD_glued`. -/
theorem tD_glued_approxU (S : PaperSetup44 DZ D DU) :
    S.tD.le 0 = gluedLe S.R.iStar S.R.jStar S.tZ S.approxU.t 0 := by
  rw [S.approxU_t]
  exact S.tD_glued

/-- The `j_!G_U` envelope hypothesis with the generator of the supplied data
on `D_U`. -/
theorem jShriek_approxU_G_mem_envelope_zero (S : PaperSetup44 DZ D DU) :
    envelope S.G 0 0 (S.R.jShriek.obj S.approxU.G) := by
  rw [S.approxU_G]
  exact S.jShriek_GU_mem_envelope_zero

/-- The Hom-vanishing hypothesis with the bound of the supplied data on
`D_U`. -/
theorem hom_vanishing_approxU (S : PaperSetup44 DZ D DU) {Y : D}
    (hY : S.tD.le (-S.approxU.A) Y) (f : S.G ⟶ Y) : f = 0 := by
  rw [S.approxU_A] at hY
  exact S.G_hom_vanishing hY f

/-- Lemma 4.6, specialized to `PaperSetup44` and its class `P`. -/
theorem exists_PLift (S : PaperSetup44 DZ D DU) [HasCoproducts.{v} D] [HasCoproducts.{v} DU]
    {Y : D} (hY : S.tD.le S.K Y) {n : ℤ}
    (hn₁ : -S.A - 1 ≤ n) (hn₂ : n ≤ S.A)
    (f' : (S.R.iStar.obj S.G)⟦n⟧ ⟶ S.R.iStar.obj Y) :
    Nonempty (PLift S.R.iStar S.P f') := by
  have hY' : S.tD.le (S.approxU.A + 1) Y := by
    simpa only [K, S.approxU_A] using hY
  have hn₁' : -S.approxU.A - 1 ≤ n := by simpa only [S.approxU_A] using hn₁
  have hn₂' : n ≤ S.approxU.A := by simpa only [S.approxU_A] using hn₂
  have hP : S.P = lemma46P S.G S.tD S.approxU.A := by
    ext Z
    simp only [P, B, K, lemma46P, S.approxU_A, ObjectProperty.prop_inf_iff, neg_mul]
  rw [hP]
  exact lemma_4_6 S.R S.approxU S.tD S.tZ S.tD_glued_approxU S.G S.G_mem_le_zero
    S.jShriek_approxU_G_mem_envelope_zero (fun hY f => S.hom_vanishing_approxU hY f)
    hY' hn₁' hn₂' f'

/-- The first stage of the closing argument in Theorem 1.1.  Proposition 4.8
lifts an approximation of `i^*F`; the cone of the lifted morphism has its
`i^*`-component in degree at most `-1`. -/
theorem exists_firstApproximation (S : PaperSetup44 DZ D DU)
    [HasCoproducts.{v} DZ] [HasCoproducts.{v} D] [HasCoproducts.{v} DU]
    {F : D} (hF : S.tD.le 0 F) :
    ∃ (E N : D) (q : E ⟶ F) (r : F ⟶ N) (s : N ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk q r s ∈ distTriang D ∧
      envelope S.G (-S.B) S.B E ∧ S.tD.le S.K E ∧
      S.tZ.le (-1) (S.R.iStar.obj N) := by
  have hiF : S.approxZ.t.le 0 (S.R.iStar.obj F) := by
    rw [S.approxZ_t]
    exact lemma_4_2_iStar S.R.iStar S.R.jStar S.tD S.tZ S.tU S.tD_glued 0 hF
  obtain ⟨E', Z, f', g', h', hT', hE', hZ⟩ := S.approxZ.exists_triangle _ hiF
  have hE'' : envelope (S.R.iStar.obj S.G) (-S.A) S.A E' := by
    simpa only [S.approxZ_G, S.approxZ_A, G] using hE'
  have hZ' : S.tZ.le (-1) Z := by
    rw [← S.approxZ_t]
    exact hZ
  have hFK : S.tD.le S.K F := by
    apply S.tD.le_monotone (show 0 ≤ S.K by dsimp [K]; have := S.A_pos; omega) F hF
  letI : S.P.IsClosedUnderIsomorphisms := S.P_isClosedUnderIsomorphisms
  letI : S.P.IsTriangulatedClosed₂ := S.P_extensions
  letI : (S.tD.le S.K).IsTriangulatedClosed₂ :=
    TStructure.le_isTriangulatedClosed₂ S.tD S.K
  letI (J : Type v) : PreservesColimitsOfShape (Discrete J) S.R.iStar := by
    letI := Adjunction.leftAdjoint_preservesColimits.{v, v} S.R.iStarAdj
    infer_instance
  letI (J : Type v) : S.P.IsClosedUnderColimitsOfShape (Discrete J) :=
    S.P_coproducts J
  have hPK : S.P ≤ S.tD.le S.K := fun _ hX => hX.2
  have hKshift : ∀ {X : D}, S.tD.le S.K X → S.tD.le S.K (X⟦(1 : ℤ)⟧) := by
    intro X hX
    apply S.tD.le_monotone (show S.K - 1 ≤ S.K by omega)
    exact S.tD.le_shift S.K 1 (S.K - 1) (by ring) X hX
  have hlemma : ∀ n : ℤ, -S.A - 1 ≤ n → n ≤ S.A →
      liftableClass S.R.iStar S.P (S.tD.le S.K) ((S.R.iStar.obj S.G)⟦n⟧) := by
    intro n hn₁ hn₂ Y hY f'
    exact S.exists_PLift hY hn₁ hn₂ f'
  obtain ⟨hstrict, hcoprod, hext, hshifts, henvelope, hlifts⟩ :=
    proposition_4_8 S.R.iStar S.P (S.tD.le S.K) S.G S.A hPK hKshift hlemma
  have hEC : Coprod (shiftInterval (S.R.iStar.obj S.G) (-S.A) (S.A + 1)) E' :=
    henvelope E' hE''
  obtain ⟨L⟩ := hlifts E' hEC hFK f'
  obtain ⟨N, r, s, hN⟩ := distinguished_cocone_triangle L.q
  let Ti := S.R.iStar.mapTriangle.obj (Triangle.mk L.q r s)
  have hTi : Ti ∈ distTriang DZ := S.R.iStar.map_distinguished _ hN
  let φ := completeDistinguishedTriangleMorphism Ti (Triangle.mk f' g' h') hTi hT'
    L.θ.hom (𝟙 (S.R.iStar.obj F)) (by
      change S.R.iStar.map L.q ≫ 𝟙 (S.R.iStar.obj F) = L.θ.hom ≫ f'
      rw [Category.comp_id, L.comm])
  haveI : IsIso φ.hom₁ := by change IsIso L.θ.hom; infer_instance
  haveI : IsIso φ.hom₂ := by change IsIso (𝟙 (S.R.iStar.obj F)); infer_instance
  haveI : IsIso φ.hom₃ := by
    apply isIso₃_of_isIso₁₂ φ hTi hT'
    · infer_instance
    · infer_instance
  let eN' := asIso φ.hom₃
  let eN : Ti.obj₃ ≅ Z := eN'
  have hiN : S.tZ.le (-1) (S.R.iStar.obj N) :=
    (S.tZ.le (-1)).prop_of_iso eN.symm hZ'
  exact ⟨L.source, N, L.q, r, s, hN, L.source_mem.1, L.source_mem.2, hiN⟩

end PaperSetup44

section Theorem11

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- **Theorem 1.1, reverse implication (the §4 assembly).**  Under Setup 4.4,
the displayed normalized generator, glued `t`-structure, and bound `B = 3A`
form weak approximation data on `D`.

The approximation triangle is obtained in two stages.  Proposition 4.8 lifts
an approximation of `i^*F`; Lemma 4.6's approximation of the `j^*`-component
of its cone supplies the second map; Remark 3.2(2) produces the final source.
The final cone lies in `D^{≤-1}` by Lemma 4.2, and its source lies in
`⟨G⟩^[-B,B]` by extension closure. -/
theorem theorem_1_1_of_setup (S : PaperSetup44 DZ D DU)
    [HasCoproducts.{v} DZ] [HasCoproducts.{v} D] [HasCoproducts.{v} DU] :
    ∃ (W : PaperWeakApproximationData D), W.t = S.tD ∧ W.G = S.G ∧ W.A = S.B := by
  have hBpos : 0 < S.B := by dsimp [PaperSetup44.B]; have := S.A_pos; omega
  have hGmem : S.tD.le S.B S.G := by
    apply S.tD.le_monotone (show 0 ≤ S.B by omega) S.G S.G_mem_le_zero
  have hvan : ∀ {Y : D}, S.tD.le (-S.B) Y → ∀ f : S.G ⟶ Y, f = 0 := by
    intro Y hY f
    apply S.G_hom_vanishing _ f
    exact S.tD.le_monotone (by dsimp [PaperSetup44.B]; have := S.A_pos; omega) Y hY
  refine ⟨{
    G := S.G
    t := S.tD
    A := S.B
    A_pos := hBpos
    G_compact := S.G_compact
    G_paperGenerates := S.G_paperGenerates
    G_mem_le := hGmem
    hom_vanishing := hvan
    exists_triangle := ?_ }, rfl, rfl, rfl⟩
  intro F hF
  obtain ⟨E, N, q, r, s, hN, hE, hEK, hiN⟩ := S.exists_firstApproximation hF
  have hFK : S.tD.le S.K F := by
    apply S.tD.le_monotone (show 0 ≤ S.K by dsimp [PaperSetup44.K]; have := S.A_pos; omega) F hF
  have hEKshift : S.tD.le S.K (E⟦(1 : ℤ)⟧) := by
    apply S.tD.le_monotone (show S.K - 1 ≤ S.K by omega)
    exact S.tD.le_shift S.K 1 (S.K - 1) (by ring) E hEK
  have hNK : S.tD.le S.K N := by
    exact (S.tD.isLE₂ (Triangle.mk q r s).rotate (rot_of_distTriang _ hN) S.K
      ⟨hFK⟩ ⟨hEKshift⟩).le
  have hNK' : S.tD.le (S.approxU.A + 1) N := by
    simpa only [PaperSetup44.K, S.approxU_A] using hNK
  obtain ⟨X, V, w, c, d, hXV, hX, hXK, hV⟩ :=
    lemma_4_6_approximation S.R S.approxU S.tD S.tZ S.tD_glued_approxU hNK'
  let p : S.R.jShriek.obj X ⟶ N := (S.R.jShriekAdj.homEquiv X N).symm w
  obtain ⟨C, k, l, hC⟩ := distinguished_cocone_triangle p
  let Ti := S.R.iStar.mapTriangle.obj (Triangle.mk p k l)
  have hTi : Ti ∈ distTriang DZ := S.R.iStar.map_distinguished _ hC
  have hzero : IsZero Ti.obj₁ := S.R.iStar_jShriek_isZero X
  haveI : IsIso (S.R.iStar.map k) := (Ti.isZero₁_iff_isIso₂ hTi).1 hzero
  let ei : S.R.iStar.obj N ≅ S.R.iStar.obj C := asIso (S.R.iStar.map k)
  have hiC : S.tZ.le (-1) (S.R.iStar.obj C) :=
    (S.tZ.le (-1)).prop_of_iso ei hiN
  let Tj := S.R.jStar.mapTriangle.obj (Triangle.mk p k l)
  have hTj : Tj ∈ distTriang DU := S.R.jStar.map_distinguished _ hC
  let eX : Tj.obj₁ ≅ X := (asIso (S.R.jShriekAdj.unit.app X)).symm
  have hw : w = S.R.jShriekAdj.unit.app X ≫ S.R.jStar.map p := by
    change w = S.R.jShriekAdj.unit.app X ≫
      S.R.jStar.map ((S.R.jShriekAdj.homEquiv X N).symm w)
    simpa only [Equiv.apply_symm_apply] using
      (S.R.jShriekAdj.homEquiv_unit
        (f := (S.R.jShriekAdj.homEquiv X N).symm w))
  have hcomm : Tj.mor₁ = eX.hom ≫ w := by
    change S.R.jStar.map p = inv (S.R.jShriekAdj.unit.app X) ≫ w
    rw [hw]
    simp
  obtain ⟨l', hX'⟩ := exists_distinguished_triangle_same_mor₂ Tj hTj eX w hcomm
  let φV := completeDistinguishedTriangleMorphism (Triangle.mk w c d)
    (Triangle.mk w Tj.mor₂ l') hXV hX' (𝟙 X) (𝟙 (S.R.jStar.obj N)) (by
      change w ≫ 𝟙 (S.R.jStar.obj N) = 𝟙 X ≫ w
      simp)
  haveI : IsIso φV.hom₁ := by change IsIso (𝟙 X); infer_instance
  haveI : IsIso φV.hom₂ := by change IsIso (𝟙 (S.R.jStar.obj N)); infer_instance
  haveI : IsIso φV.hom₃ := by
    apply isIso₃_of_isIso₁₂ φV hXV hX'
    · infer_instance
    · infer_instance
  let eV' := asIso φV.hom₃
  let eV : V ≅ Tj.obj₃ := eV'
  have hV' : S.approxU.t.le (-1) V := by
    apply S.approxU.t.le_monotone (show -2 * S.approxU.A ≤ -1 by have := S.approxU.A_pos; omega)
    exact hV
  have hjC : S.tU.le (-1) (S.R.jStar.obj C) := by
    rw [← S.approxU_t]
    exact (S.approxU.t.le (-1)).prop_of_iso eV hV'
  obtain ⟨E', f, h, hE'⟩ := distinguished_cocone_triangle₁ (r ≫ k)
  obtain ⟨u, v, huv⟩ := remark_3_2_2 r k q s p l f h hN hC hE'
  have hJX : envelope S.G (-S.B) S.B (S.R.jShriek.obj X) := by
    simpa only [PaperSetup44.B, S.approxU_A, neg_mul] using
      lemma_4_6_envelope_jShriek S.R S.approxU S.G
        S.jShriek_approxU_G_mem_envelope_zero hX
  have hE'env : envelope S.G (-S.B) S.B E' := by
    letI : (envelope S.G (-S.B) S.B).IsTriangulatedClosed₂ :=
      lemma_3_1_1_extensions S.G (-S.B) S.B
    exact (envelope S.G (-S.B) S.B).ext_of_isTriangulatedClosed₂
      (Triangle.mk u v (p ≫ s)) huv hE hJX
  have hCle : S.tD.le (-1) C := by
    rw [lemma_4_2 S.R.iStar S.R.jStar S.tD S.tZ S.tU S.tD_glued (-1)]
    exact ⟨hiC, hjC⟩
  exact ⟨E', C, f, r ≫ k, h, hE', hE'env, hCle⟩

/-- The categorical consequence of Theorem 1.1: Setup 4.4 implies that `D`
satisfies weak approximability (Definition 5.3). -/
theorem satisfiesPaperWA_of_setup (S : PaperSetup44 DZ D DU)
    [HasCoproducts.{v} DZ] [HasCoproducts.{v} D] [HasCoproducts.{v} DU] :
    SatisfiesPaperWA D := by
  obtain ⟨W, _⟩ := theorem_1_1_of_setup S
  exact ⟨W⟩

end Theorem11
end RelativeWeakApprox.PaperM2

#print axioms RelativeWeakApprox.PaperM2.theorem_1_1_of_setup
#print axioms RelativeWeakApprox.PaperM2.satisfiesPaperWA_of_setup
