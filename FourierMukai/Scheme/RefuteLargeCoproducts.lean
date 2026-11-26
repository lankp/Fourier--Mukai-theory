/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.AffineSpaltenstein
import FourierMukai.Scheme.AffineUniverse
import FourierMukai.Scheme.Neeman32Inputs
import FourierMukai.Scheme.PerfectRingStacks

/-!
# F1: `D(A-Mod)` has no `Type (u+1)`-indexed coproducts

Refutation **F1** of `results/OPEN_INPUTS.md` §0 (task `wave6/vacuity-refutations`,
rule 3 of `CLAUDE.md`).

`AffineD A = D(A-Mod)` is the standard Mathlib localization; for `A : Type u` its
morphisms live in `Type (u+1)`, so `HasCoproducts.{u+1} (AffineD A)` asks for
coproducts indexed by every `I : Type (u+1)`.  This is **false** for every nonzero
commutative ring `A` (`not_hasCoproducts_affineD`):

* `AffineD A` is locally `u`-small, by the proved Spaltenstein replacement data
  (`Spaltenstein.affineSpaltensteinInput`) and
  `UniverseDecision.locallySmallDerivedCategoryOfKProjectiveReplacementData`;
* if `C = ∐_{I} X` existed for `I = Type u` and an object `X` with `𝟙 X ≠ 0`
  (here `X = A[0]`), then `S ↦ desc (fun i => if S i then 𝟙 X else 0)` would inject
  `I → Bool` into `Hom(C, X)`, hence `Type u` into a `u`-small set, contradicting
  Mathlib's `not_small_type`.

The general form `not_hasCoproducts_of_locallySmall` holds in any preadditive
category that is locally `u`-small and has an object with nonzero identity.

**Consequences.**  `AffineDerivedCoproducts A DZ DU` (whose field `hasCoproductsA`
is `HasCoproducts.{u+1} (AffineD A)`) is empty for nontrivial `A`
(`isEmpty_affineDerivedCoproducts`).  Hence the hypotheses of the pinned
`RelativeFM.affine_theorem_1_1_unconditional` and
`RelativeFM.StacksGluing.affine_theorem_1_1_stacks07LT` are unsatisfiable for every
nontrivial `A` (`affine_theorem_1_1_unconditional_hypotheses_false`,
`affine_theorem_1_1_stacks07LT_hypotheses_false`): both theorems are vacuous except
for the zero ring.  The same holds for `RelativeFM.affine_theorem_1_1` and every
other declaration taking an `AffineDerivedCoproducts` argument.  The small-Hom model
`SmallAffineD` (coproducts indexed by `Type u`, `smallAffineHasCoproducts`) is not
affected.

Nothing is assumed: no Stacks field, no named hypothesis.  The negated
propositions are the tree's own definitions (`HasCoproducts.{u+1} (AffineD A)`,
`AffineDerivedCoproducts`), not re-renderings.
-/

@[expose] public section

namespace RelativeFM.VacuityF1

open CategoryTheory CategoryTheory.Limits
open RelativeFM RelativeWeakApprox

universe u v w uZ uU

noncomputable section

/-- In a preadditive category with `u`-small Hom sets, no object with nonzero
identity has a coproduct of `Type u`-many copies of itself.  (The index type
`Type u` lives in `Type (u+1)`.) -/
theorem not_hasCoproduct_of_locallySmall {C : Type w} [Category.{v} C] [Preadditive C]
    [LocallySmall.{u} C] (X : C) (hX : 𝟙 X ≠ 0) :
    ¬ HasCoproduct (fun _ : Type u => X) := by
  intro hc
  classical
  let Φ : (Type u → Bool) → (∐ (fun _ : Type u => X) ⟶ X) :=
    fun S => Sigma.desc (fun i => if S i then 𝟙 X else 0)
  have hΦ : Function.Injective Φ := by
    intro S T hST
    funext i
    have h := congrArg (fun g => Sigma.ι (fun _ : Type u => X) i ≫ g) hST
    simp only [Φ, Sigma.ι_comp_desc] at h
    cases hS : S i <;> cases hT : T i <;> simp_all
  have h1 : Small.{u} (Type u → Bool) := small_of_injective hΦ
  let ψ : Type u → (Type u → Bool) := fun x y => decide (y = x)
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h := congrFun hxy x
    simp only [ψ, decide_true] at h
    exact of_decide_eq_true h.symm
  have h2 : Small.{u} (Type u) := small_of_injective hψ
  exact not_small_type.{u, u} h2

/-- A locally `u`-small preadditive category with an object whose identity is
nonzero has no coproducts indexed by `Type (u+1)`. -/
theorem not_hasCoproducts_of_locallySmall {C : Type w} [Category.{v} C] [Preadditive C]
    [LocallySmall.{u} C] (X : C) (hX : 𝟙 X ≠ 0) :
    ¬ HasCoproducts.{u + 1} C := by
  intro h
  exact not_hasCoproduct_of_locallySmall X hX inferInstance

section Affine

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- `D(A-Mod)` (standard localization) is locally `u`-small: Spaltenstein's
K-projective replacements, proved in `Scheme/AffineSpaltenstein.lean`. -/
theorem affineD_locallySmall : LocallySmall.{u} (AffineD A) :=
  UniverseDecision.locallySmallDerivedCategoryOfKProjectiveReplacementData
    (Spaltenstein.affineSpaltensteinInput A)

/-- For a nonzero ring, the identity of `A[0]` is nonzero: the single functor is
faithful and `𝟙_A ≠ 0`. -/
theorem ringObject_id_ne_zero [Nontrivial A] : 𝟙 (ringObject A) ≠ 0 := by
  intro h
  have h' : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (𝟙 (ModuleCat.of A A)) =
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map 0 := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact h
  have h'' := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map_injective h'
  have h1 := congrArg (fun g : ModuleCat.of A A ⟶ ModuleCat.of A A => g.hom (1 : A)) h''
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply] at h1
  exact one_ne_zero h1

/-- **F1.** For every nonzero commutative ring `A : Type u`, the standard derived
category `AffineD A = D(A-Mod)` does **not** have coproducts indexed by
`Type (u+1)`.  This is exactly the negation of the field `hasCoproductsA` of
`AffineDerivedCoproducts`. -/
theorem not_hasCoproducts_affineD [Nontrivial A] : ¬ HasCoproducts.{u + 1} (AffineD A) := by
  have := affineD_locallySmall A
  exact not_hasCoproducts_of_locallySmall (ringObject A) (ringObject_id_ne_zero A)

section Categories

variable (DZ : Type uZ) (DU : Type uU)
  [Category.{u + 1} DZ] [Category.{u + 1} DU]

/-- **F1, corollary.**  The coproduct package `AffineDerivedCoproducts A DZ DU` is
empty for every nonzero ring `A`, whatever `DZ` and `DU` are. -/
theorem isEmpty_affineDerivedCoproducts [Nontrivial A] :
    IsEmpty (AffineDerivedCoproducts A DZ DU) :=
  ⟨fun C => not_hasCoproducts_affineD A C.hasCoproductsA⟩

variable [Preadditive DZ] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DU]

/-- **F1, corollary.**  The hypotheses of the pinned
`RelativeFM.affine_theorem_1_1_unconditional` (a `SetupMainMinimal` with middle
category `AffineD A` and an `AffineDerivedCoproducts A DZ DU`) are never
simultaneously satisfiable when `A` is nontrivial; the theorem is vacuous for
every nonzero ring. -/
theorem affine_theorem_1_1_unconditional_hypotheses_false [Nontrivial A]
    (_S : SetupMainMinimal DZ (AffineD A) DU) (C : AffineDerivedCoproducts A DZ DU) :
    False :=
  (isEmpty_affineDerivedCoproducts A DZ DU).false C

/-- **F1, corollary.**  The hypotheses of the pinned
`RelativeFM.StacksGluing.affine_theorem_1_1_stacks07LT` are unsatisfiable for every
nontrivial `A`: its `AffineDerivedCoproducts A DZ DU` argument has no inhabitant. -/
theorem affine_theorem_1_1_stacks07LT_hypotheses_false [Nontrivial A]
    (_S : SetupMainMinimal DZ (AffineD A) DU) (C : AffineDerivedCoproducts A DZ DU)
    (_I : Stacks07LTCompactModelInput A) : False :=
  (isEmpty_affineDerivedCoproducts A DZ DU).false C

end Categories

end Affine

end

end RelativeFM.VacuityF1

#print axioms RelativeFM.VacuityF1.not_hasCoproduct_of_locallySmall
#print axioms RelativeFM.VacuityF1.not_hasCoproducts_of_locallySmall
#print axioms RelativeFM.VacuityF1.affineD_locallySmall
#print axioms RelativeFM.VacuityF1.ringObject_id_ne_zero
#print axioms RelativeFM.VacuityF1.not_hasCoproducts_affineD
#print axioms RelativeFM.VacuityF1.isEmpty_affineDerivedCoproducts
#print axioms RelativeFM.VacuityF1.affine_theorem_1_1_unconditional_hypotheses_false
#print axioms RelativeFM.VacuityF1.affine_theorem_1_1_stacks07LT_hypotheses_false
