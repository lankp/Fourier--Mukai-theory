/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.RefuteIntGenerator
import FourierMukai.Scheme.RefuteLargeCoproducts
import FourierMukai.Scheme.M6Transport
import Mathlib.Algebra.Category.Grp.Ulift

/-!
# F2 in the small-Hom model `SmallAffineD ℤ H`

Second half of refutation **F2** of `results/OPEN_INPUTS.md` §0 (task
`wave6/vacuity-refutations`); the large model is `Scheme/RefuteIntGenerator.lean`.

## Compactness lifts from the small to the large model

`SmallAffineD A H` (Hom universe `u`) and `AffineD A` (Hom universe `u+1`) are
equivalent (`CapstoneM6.affineQhComparison`), but `IsCompactAb` quantifies over
`Type u`-indexed coproducts in the first and `Type (u+1)`-indexed ones in the second,
so `M6Transport` could only transport compactness downwards and kept the upward
direction as the explicit parameter `liftCompact` of `perfectToCompactInput_of_small`.
Here it is proved (`isCompactAb_affineQhComparison_inverse`):

1. (`preservesColimitsOfShape_of_equivalence_small_to_large`) along an equivalence
   from a `u`-Hom category to a `(u+1)`-Hom category, `Hom(E⁻¹G, -)` is
   `ulift ∘ Hom(G, E -)`, so it preserves `Type u`-indexed coproducts when `G` is
   compact;
2. (`isCompactAb_of_locallySmall`) in a locally `u`-small preadditive category, an
   object whose `Hom` preserves `Type u`-indexed coproducts preserves all
   `Type (u+1)`-indexed ones: in an existing coproduct `∐_J X_j`, the nonzero
   summands form a `u`-small set (their power set injects into `End(∐ X_j)`, as in
   F1), and zero summands can be dropped on both sides (`isColimitCofanRestrict`,
   `isColimitCofanExtend`).

`AffineD A` is locally `u`-small by Spaltenstein (`VacuityF1.affineD_locallySmall`).
Consequently every compact object of `SmallAffineD A H` is in `SmallPerf A H`
(`smallPerf_of_isCompactAb`), for every commutative ring `A`, with no hypothesis.

## The refutation

`not_isGenerator_of_isCompactAb_smallInt`: no compact object of `SmallAffineD ℤ H`
is an `IsGenerator`, by `VacuityF2.not_isGenerator_of_mem_triangEnvelope_int` in the
small model.  Corollaries: `WeakApproximationData (SmallAffineD ℤ H)` is empty,
`SatisfiesWA (SmallAffineD ℤ H)` is false, and `SetupMainMinimal DZ (SmallAffineD ℤ H) DU`
is empty, so the pinned `RelativeFM.affine_theorem_1_1_small` is vacuous at `ℤ`
(`affine_theorem_1_1_small_hypotheses_false_int`).

Nothing is assumed.
-/

@[expose] public section

namespace RelativeFM.VacuityF2

open CategoryTheory CategoryTheory.Limits Opposite
open RelativeFM RelativeWeakApprox

universe v u w uC uD uZ uU

noncomputable section

section Restrict

variable {D : Type uD} [Category.{v} D] [HasZeroMorphisms D]

/-- Dropping zero summands: the restriction of a colimit cofan to the indices
outside which all summands are zero is still a colimit cofan. -/
def isColimitCofanRestrict {J : Type w} {X : J → D} (p : J → Prop)
    (hp : ∀ j, ¬ p j → IsZero (X j)) {P : D} {ι : ∀ j, X j ⟶ P}
    (h : IsColimit (Cofan.mk P ι)) :
    IsColimit (Cofan.mk P (fun s : {j // p j} => ι s.1)) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun t => Cofan.IsColimit.desc h (fun j => if hj : p j then t.inj ⟨j, hj⟩ else 0)) ?_ ?_
  · intro t s
    have := Cofan.IsColimit.fac h (fun j => if hj : p j then t.inj ⟨j, hj⟩ else 0) s.1
    simpa [s.2] using this
  · intro t m hm
    apply Cofan.IsColimit.hom_ext h
    intro j
    rw [Cofan.IsColimit.fac]
    by_cases hj : p j
    · simpa [hj] using hm ⟨j, hj⟩
    · simpa [hj] using (hp j hj).eq_of_src _ _

/-- Adding zero summands to a colimit cofan gives a colimit cofan. -/
def isColimitCofanExtend {J : Type w} {X : J → D} (p : J → Prop)
    (hp : ∀ j, ¬ p j → IsZero (X j)) {P : D} {ι : ∀ j, X j ⟶ P}
    (h : IsColimit (Cofan.mk P (fun s : {j // p j} => ι s.1))) :
    IsColimit (Cofan.mk P ι) := by
  refine Cofan.IsColimit.mk _ (fun t => Cofan.IsColimit.desc h (fun s => t.inj s.1)) ?_ ?_
  · intro t j
    by_cases hj : p j
    · exact Cofan.IsColimit.fac h (fun s => t.inj s.1) ⟨j, hj⟩
    · exact (hp j hj).eq_of_src _ _
  · intro t m hm
    apply Cofan.IsColimit.hom_ext h
    intro s
    rw [Cofan.IsColimit.fac]
    exact hm s.1

end Restrict

section LocallySmall

variable {C : Type uC} [Category.{v + 1} C] [Preadditive C]

/-- In a preadditive category, a leg of a colimit cofan whose summand is nonzero is
nonzero. -/
lemma cofan_inj_ne_zero {J : Type (v + 1)} {X : J → C} {c : Cofan X} (hc : IsColimit c)
    (j : J) (hj : ¬ IsZero (X j)) : c.inj j ≠ 0 := by
  classical
  intro h
  apply hj
  rw [IsZero.iff_id_eq_zero]
  have hf := Cofan.IsColimit.fac hc
    (fun k => if hk : k = j then eqToHom (congrArg X hk) else 0) j
  rw [h, Limits.zero_comp, dite_eq_left rfl, eqToHom_refl] at hf
  exact hf.symm

/-- In a locally `v`-small preadditive category with `(v+1)`-Homs, the nonzero
summands of an existing coproduct form a `v`-small set. -/
lemma small_nonzero_summands [LocallySmall.{v} C] {J : Type (v + 1)} {X : J → C}
    {c : Cofan X} (hc : IsColimit c) : Small.{v} {j // ¬ IsZero (X j)} := by
  classical
  let S := {j // ¬ IsZero (X j)}
  let Φ : Set S → (c.pt ⟶ c.pt) := fun T => Cofan.IsColimit.desc hc
    (fun j => if hj : ¬ IsZero (X j) then (if (⟨j, hj⟩ : S) ∈ T then c.inj j else 0) else 0)
  have hΦ : Function.Injective Φ := by
    intro T₁ T₂ hT
    ext ⟨j, hj⟩
    have h := congrArg (fun g => c.inj j ≫ g) hT
    simp only [Φ, Cofan.IsColimit.fac, dite_eq_left hj] at h
    have hne := cofan_inj_ne_zero hc j hj
    by_cases h₁ : (⟨j, hj⟩ : S) ∈ T₁ <;> by_cases h₂ : (⟨j, hj⟩ : S) ∈ T₂
    · exact iff_of_true h₁ h₂
    · rw [ite_eq_left h₁, ite_eq_right h₂] at h
      exact absurd h hne
    · rw [ite_eq_right h₁, ite_eq_left h₂] at h
      exact absurd h.symm hne
    · exact iff_of_false h₁ h₂
  have : Small.{v} (Set S) := small_of_injective hΦ
  exact small_of_injective (f := fun s : S => ({s} : Set S)) Set.singleton_injective

/-- **Lifting compactness across one universe.**  In a locally `v`-small preadditive
category with `(v+1)`-Homs, if `Hom(G, -)` preserves `Type v`-indexed coproducts then
`G` is compact (`Type (v+1)`-indexed coproducts). -/
theorem isCompactAb_of_locallySmall [LocallySmall.{v} C] (G : C)
    (hG : ∀ J : Type v, PreservesColimitsOfShape (Discrete J)
      (preadditiveCoyoneda.obj (op G))) : IsCompactAb G := by
  refine ⟨fun J => ⟨fun {K} => ?_⟩⟩
  let F := preadditiveCoyoneda.obj (op G)
  let X : J → C := K.obj ∘ Discrete.mk
  suffices PreservesColimit (Discrete.functor X) F from
    preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor (F := K)).symm
  refine ⟨fun {c₀} hc => ⟨?_⟩⟩
  let c : Cofan X := c₀
  let p : J → Prop := fun j => ¬ IsZero (X j)
  have hp : ∀ j, ¬ p j → IsZero (X j) := fun j hj => not_not.1 hj
  have hsmall : Small.{v} {j // p j} := small_nonzero_summands hc
  have hc' : IsColimit (Cofan.mk c.pt c.inj) := hc
  have hS := isColimitCofanRestrict p hp hc'
  have : PreservesColimitsOfShape (Discrete {j // p j}) F := by
    have := hG (Shrink.{v} {j // p j})
    exact preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{v} {j // p j}).symm) F
  have hFS := (isColimitMapCoconeCofanMkEquiv F (fun s : {j // p j} => X s.1) (fun s => c.inj s.1))
    (isColimitOfPreserves F hS)
  have hFp : ∀ j, ¬ p j → IsZero (F.obj (X j)) := fun j hj => F.map_isZero (hp j hj)
  have hF := isColimitCofanExtend (X := fun j => F.obj (X j))
    (ι := fun j => F.map (c.inj j)) p hFp hFS
  exact (isColimitMapCoconeCofanMkEquiv F X c.inj).symm hF

end LocallySmall

section Equivalence

variable {C : Type uC} [Category.{v + 1} C] [Preadditive C]
variable {D : Type uD} [Category.{v} D] [Preadditive D]

/-- `Hom(F X, -) ≅ ulift ∘ Hom(X, G -)` for an adjunction `F ⊣ G` from a `v`-Hom
category to a `(v+1)`-Hom category. -/
def preadditiveCoyonedaSmallToLargeIso {F : D ⥤ C} {G : C ⥤ D} [F.Additive] (adj : F ⊣ G)
    (X : D) :
    G ⋙ preadditiveCoyoneda.obj (op X) ⋙ AddCommGrpCat.uliftFunctor.{v + 1, v} ≅
      preadditiveCoyoneda.obj (op (F.obj X)) :=
  NatIso.ofComponents
    (fun Y => (AddEquiv.ulift.trans (adj.homAddEquiv X Y).symm).toAddCommGrpIso)
    (fun g => by
      ext ⟨f⟩
      change (adj.homEquiv X _).symm (f ≫ G.map g) = (adj.homEquiv X _).symm f ≫ g
      exact adj.homEquiv_naturality_right_symm f g)

/-- Along an equivalence `E : C ≌ D` with `C` of Hom universe `v+1` and `D` of Hom
universe `v`, `Hom(E⁻¹ G, -)` preserves `Type v`-indexed coproducts when `G` is
compact in `D`. -/
theorem preservesColimitsOfShape_of_equivalence_small_to_large (E : C ≌ D)
    [E.functor.Additive] {G : D} (hG : IsCompactAb G) (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op (E.inverse.obj G))) := by
  have : PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G)) :=
    hG.preserves J
  have : PreservesColimitsOfShape (Discrete J)
      (E.functor ⋙ preadditiveCoyoneda.obj (op G) ⋙ AddCommGrpCat.uliftFunctor.{v + 1, v}) :=
    inferInstance
  have : E.symm.functor.Additive := (inferInstance : E.inverse.Additive)
  exact preservesColimitsOfShape_of_natIso
    (preadditiveCoyonedaSmallToLargeIso E.symm.toAdjunction G)

end Equivalence

section Affine

open CapstoneM6

/-- **Compactness lifts from `SmallAffineD A H` to `AffineD A`** along the inverse of
the comparison equivalence `affineQhComparison A H`.  This discharges the parameter
`liftCompact` of `CapstoneM6.perfectToCompactInput_of_small`. -/
theorem isCompactAb_affineQhComparison_inverse (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (X : SmallAffineD A H) (hX : IsCompactAb X) :
    IsCompactAb ((affineQhComparison A H).inverse.obj X) := by
  have := VacuityF1.affineD_locallySmall A
  have : (affineQhComparison A H).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  exact isCompactAb_of_locallySmall _
    (preservesColimitsOfShape_of_equivalence_small_to_large (affineQhComparison A H) hX)

/-- **Compact ⇒ perfect in the small-Hom model**, unconditionally, for every
commutative ring: lift compactness to `AffineD A`, apply
`Stacks07LT.M4.perf_of_compact_unconditional`, and transport `Perf` back
(`CapstoneM6.smallPerf_iff_perf_affineQhComparison_inverse`). -/
theorem smallPerf_of_isCompactAb (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (X : SmallAffineD A H) (hX : IsCompactAb X) : SmallPerf A H X :=
  (smallPerf_iff_perf_affineQhComparison_inverse A H X).2
    (Stacks07LT.M4.perf_of_compact_unconditional A
      (isCompactAb_affineQhComparison_inverse A H X hX))

end Affine

section SmallInt

/-- **F2 (small-Hom model).**  No compact object of `SmallAffineD ℤ H` satisfies
`IsGenerator`. -/
theorem not_isGenerator_of_isCompactAb_smallInt (H : AffineSpaltensteinInput ℤ)
    (G : SmallAffineD ℤ H) (hG : IsCompactAb G) : ¬ IsGenerator G := by
  let : HasDerivedCategory.{0} (ModuleCat.{0} ℤ) :=
    UniverseDecision.hasDerivedCategoryOfKProjectiveReplacementData H
  exact not_isGenerator_of_mem_triangEnvelope_int (smallPerf_of_isCompactAb ℤ H G hG)

/-- **F2, corollary.**  `WeakApproximationData (SmallAffineD ℤ H)` is empty. -/
theorem isEmpty_weakApproximationData_smallInt (H : AffineSpaltensteinInput ℤ) :
    IsEmpty (WeakApproximationData (SmallAffineD ℤ H)) :=
  ⟨fun W => not_isGenerator_of_isCompactAb_smallInt H W.G W.G_compact W.G_generates⟩

/-- **F2, corollary.**  `SatisfiesWA (SmallAffineD ℤ H)` is false. -/
theorem not_satisfiesWA_smallInt (H : AffineSpaltensteinInput ℤ) :
    ¬ SatisfiesWA (SmallAffineD ℤ H) :=
  fun ⟨W⟩ => (isEmpty_weakApproximationData_smallInt H).false W

variable (H : AffineSpaltensteinInput ℤ) (DZ : Type uZ) (DU : Type uU)
  [Category.{0} DZ] [Category.{0} DU]
  [Preadditive DZ] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DU]

/-- **F2, corollary.**  `SetupMainMinimal DZ (SmallAffineD ℤ H) DU` is empty. -/
theorem isEmpty_setupMainMinimal_smallInt :
    IsEmpty (SetupMainMinimal DZ (SmallAffineD ℤ H) DU) :=
  ⟨fun S => not_isGenerator_of_isCompactAb_smallInt H S.G' S.G'_compact S.G'_generates⟩

/-- **F2, corollary.**  The hypotheses of the pinned `RelativeFM.affine_theorem_1_1_small`
are unsatisfiable at `A = ℤ`: its `SetupMainMinimal DZ (SmallAffineD ℤ H) DU`
argument has no inhabitant. -/
theorem affine_theorem_1_1_small_hypotheses_false_int
    (S : SetupMainMinimal DZ (SmallAffineD ℤ H) DU)
    (_C : SmallAffineDerivedCoproducts ℤ H DZ DU)
    (_h09SR : Stacks09SR (SmallAffineD ℤ H)) : False :=
  (isEmpty_setupMainMinimal_smallInt H DZ DU).false S

end SmallInt

end

end RelativeFM.VacuityF2

#print axioms RelativeFM.VacuityF2.isColimitCofanRestrict
#print axioms RelativeFM.VacuityF2.isColimitCofanExtend
#print axioms RelativeFM.VacuityF2.small_nonzero_summands
#print axioms RelativeFM.VacuityF2.isCompactAb_of_locallySmall
#print axioms RelativeFM.VacuityF2.preservesColimitsOfShape_of_equivalence_small_to_large
#print axioms RelativeFM.VacuityF2.isCompactAb_affineQhComparison_inverse
#print axioms RelativeFM.VacuityF2.smallPerf_of_isCompactAb
#print axioms RelativeFM.VacuityF2.not_isGenerator_of_isCompactAb_smallInt
#print axioms RelativeFM.VacuityF2.isEmpty_weakApproximationData_smallInt
#print axioms RelativeFM.VacuityF2.not_satisfiesWA_smallInt
#print axioms RelativeFM.VacuityF2.isEmpty_setupMainMinimal_smallInt
#print axioms RelativeFM.VacuityF2.affine_theorem_1_1_small_hypotheses_false_int
