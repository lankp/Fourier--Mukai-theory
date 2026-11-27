/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.Theorem11Paper
import WeakApprox.CompactThick
import WeakApprox.SumUniverse

/-!
# Non-vacuity of LP26 Theorem 1.1 with the paper's hypotheses

Source: Lank--Pauwels (LP26), Theorem 1.1 (`thm:glueing_weak_approx`).  This file
checks CLAUDE.md verification step 5 for `PaperHypothesesW6.theorem_1_1_paper`:
its hypotheses can be met.

## What is constructed

* `ZeroSub C`: the full triangulated subcategory of zero objects of a
  triangulated category `C`.  Every triangle in it is distinguished; it has small
  coproducts; it is weakly approximable (`zeroSub_satisfiesPaperWA`), and Stacks
  09SR holds in it (`zeroSub_tag09SR`).  For every coproduct universe `w` it has
  `Type w`-indexed coproducts, `w`-small morphism types, and it is weakly approximable in the
  sense of `SumUniverse.SatisfiesPaperWA.{w}` (`zeroSub_satisfiesPaperWA_univ`).
* `trivialRecollement D : Recollement (ZeroSub D) D D`: the recollement with
  `D_Z = 0`, `i_* = ι`, `i^* = i^! = 0` and `j_! = j^* = j_* = 𝟭`, for any
  triangulated `D` (all fields proved).

## Instances of the headline

* `theorem_1_1_paper_zero`: every hypothesis of `theorem_1_1_paper`, including
  the two Stacks 09SR hypotheses, is discharged for `trivialRecollement (ZeroSub C)`.
* `theorem_1_1_paper_affine`: for the trivial recollement
  `0 → D(A) → D(A)` of the small-Hom affine derived category `D(A)` of any
  commutative ring `A` (which has small coproducts and the proved regular-module
  weak approximation data), every hypothesis except Stacks 09SR for `D(A)` is
  discharged; that one remaining hypothesis is the Stacks-allowed input.
-/

@[expose] public section

namespace RelativeWeakApprox.PaperHypothesesW6.NonVacuity

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox RelativeWeakApprox.PaperM2
open ZeroObject

universe w v u

noncomputable section

/-! ### The zero subcategory -/

section ZeroSub

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Zero objects. -/
def zeroProp : ObjectProperty C := fun X => IsZero X

instance : (zeroProp C).IsClosedUnderIsomorphisms where
  of_iso e h := IsZero.of_iso h e.symm

instance : (zeroProp C).ContainsZero := ⟨⟨0, isZero_zero C, isZero_zero C⟩⟩

instance : (zeroProp C).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ObjectProperty.IsStableUnderShiftBy.mk <| by
    intro X hX
    rw [ObjectProperty.prop_shift_iff]
    exact Functor.map_isZero (shiftFunctor C a) hX

instance : (zeroProp C).IsTriangulatedClosed₂ :=
  .mk' fun T hT h₁ h₃ => Triangle.isZero₂_of_isZero₁₃ T hT h₁ h₃

instance : (zeroProp C).IsTriangulated where

/-- The full triangulated subcategory of zero objects. -/
abbrev ZeroSub : Type u := (zeroProp C).FullSubcategory

variable {C}

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma zeroSub_isZero (X : ZeroSub C) : IsZero X :=
  IsZero.of_full_of_faithful_of_isZero (zeroProp C).ι X X.property

/-- Every triangle in `ZeroSub C` is distinguished. -/
lemma zeroSub_distinguished (T : Triangle (ZeroSub C)) : T ∈ distTriang (ZeroSub C) := by
  refine isomorphic_distinguished _ (contractible_distinguished T.obj₁) _ ?_
  exact Triangle.isoMk _ _ (Iso.refl _) ((zeroSub_isZero _).iso (zeroSub_isZero _))
    ((zeroSub_isZero _).iso (zeroSub_isZero _))
    ((zeroSub_isZero _).eq_of_src _ _) ((zeroSub_isZero _).eq_of_src _ _)
    ((zeroSub_isZero _).eq_of_src _ _)

variable (C)

instance : HasCoproducts.{w} (ZeroSub C) := fun _ =>
  { has_colimit := fun F => HasColimit.mk
      { cocone :=
          { pt := ⟨0, isZero_zero C⟩
            ι := { app := fun _ => 0, naturality := fun _ _ _ => by simp } }
        isColimit :=
          { desc := fun _ => 0
            fac := fun _ _ => (zeroSub_isZero _).eq_of_src _ _
            uniq := fun _ _ _ => (zeroSub_isZero _).eq_of_src _ _ } } }

/-- The trivial `t`-structure on `ZeroSub C`. -/
def zeroSubTStructure : TStructure (ZeroSub C) where
  le _ := ⊤
  ge _ := ⊤
  le_shift _ _ _ _ _ _ := trivial
  ge_shift _ _ _ _ _ _ := trivial
  zero' _ _ _ _ _ := (zeroSub_isZero _).eq_of_src _ _
  le_zero_le := le_rfl
  ge_one_le := le_rfl
  exists_triangle_zero_one X :=
    ⟨X, X, trivial, trivial, 𝟙 X, 0, 0, zeroSub_distinguished _⟩

/-- Weak approximation data on `ZeroSub C` (generator `0`, `A = 1`). -/
def zeroSubPaperData : PaperWeakApproximationData (ZeroSub C) where
  G := ⟨0, isZero_zero C⟩
  t := zeroSubTStructure C
  A := 1
  A_pos := one_pos
  G_compact := isCompactAb_of_isZero (zeroSub_isZero _)
  G_paperGenerates := fun {E} _ => zeroSub_isZero E
  G_mem_le := trivial
  hom_vanishing := fun _ _ => (zeroSub_isZero _).eq_of_src _ _
  exists_triangle F _ :=
    ⟨⟨0, isZero_zero C⟩, F, 0, 𝟙 F, 0, zeroSub_distinguished _,
      ObjectProperty.le_retractClosure _ _
        (Coprod.of_mem _ (shiftInterval_self _ (by omega) (by omega))), trivial⟩

theorem zeroSub_satisfiesPaperWA : SatisfiesPaperWA (ZeroSub C) := ⟨zeroSubPaperData C⟩

/-- The morphism types of `ZeroSub C` are subsingletons, hence `w`-small for every `w`. -/
instance : LocallySmall.{w} (ZeroSub C) where
  hom_small X Y := by
    have : Subsingleton (X ⟶ Y) := ⟨fun a b => (zeroSub_isZero X).eq_of_src a b⟩
    infer_instance

/-- Weak approximation data on `ZeroSub C` for any coproduct universe `w` (generator `0`,
`A = 1`). -/
def zeroSubPaperDataUniv : SumUniverse.PaperWeakApproximationData.{w} (ZeroSub C) where
  G := ⟨0, isZero_zero C⟩
  t := zeroSubTStructure C
  A := 1
  A_pos := one_pos
  G_compact := SumUniverse.isCompactAb_of_isZero (zeroSub_isZero _)
  G_paperGenerates := fun {E} _ => zeroSub_isZero E
  G_mem_le := trivial
  hom_vanishing := fun _ _ => (zeroSub_isZero _).eq_of_src _ _
  exists_triangle F _ :=
    ⟨⟨0, isZero_zero C⟩, F, 0, 𝟙 F, 0, zeroSub_distinguished _,
      ObjectProperty.le_retractClosure _ _
        (SumUniverse.Coprod.of_mem _ (shiftInterval_self _ (by omega) (by omega))), trivial⟩

/-- `ZeroSub C` is weakly approximable for every coproduct universe `w`. -/
theorem zeroSub_satisfiesPaperWA_univ : SumUniverse.SatisfiesPaperWA.{w} (ZeroSub C) :=
  ⟨zeroSubPaperDataUniv C⟩

/-- Stacks 09SR holds trivially in `ZeroSub C`. -/
theorem zeroSub_tag09SR :
    ∀ (G : ZeroSub C), IsPaperGenerator G → IsCompactAb G → IsClassicalGeneratorOnCompacts G :=
  fun _ _ _ X _ => ObjectProperty.prop_of_isZero _ (zeroSub_isZero X)

end ZeroSub

/-! ### The trivial recollement `0 → D → D` -/

section Trivial

variable (D : Type u) [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [CategoryTheory.IsTriangulated D]

/-- The functor `D ⥤ 0`. -/
def toZero : D ⥤ ZeroSub D where
  obj _ := ⟨0, isZero_zero D⟩
  map _ := 0
  map_id _ := (zeroSub_isZero _).eq_of_src _ _
  map_comp _ _ := (zeroSub_isZero _).eq_of_src _ _

instance : (toZero D).CommShift ℤ where
  commShiftIso _ := NatIso.ofComponents
    (fun _ => (zeroSub_isZero _).iso (zeroSub_isZero _))
    (fun _ => (zeroSub_isZero _).eq_of_src _ _)
  commShiftIso_zero :=
    Iso.ext (NatTrans.ext (funext fun _ => (zeroSub_isZero _).eq_of_src _ _))
  commShiftIso_add _ _ :=
    Iso.ext (NatTrans.ext (funext fun _ => (zeroSub_isZero _).eq_of_src _ _))

instance : (toZero D).IsTriangulated where
  map_distinguished _ _ := zeroSub_distinguished _

/-- `i^* ⊣ i_*`. -/
def iStarAdj : toZero D ⊣ (zeroProp D).ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ Y =>
        { toFun := fun _ => 0
          invFun := fun _ => 0
          left_inv := fun _ => (zeroSub_isZero _).eq_of_src _ _
          right_inv := fun _ => Y.property.eq_of_tgt _ _ }
      homEquiv_naturality_left_symm := fun _ _ => (zeroSub_isZero _).eq_of_src _ _
      homEquiv_naturality_right := fun {_ _ Y'} _ _ => Y'.property.eq_of_tgt _ _ }

/-- `i_* ⊣ i^!`. -/
def iLowerAdj : (zeroProp D).ι ⊣ toZero D :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Y _ =>
        { toFun := fun _ => 0
          invFun := fun _ => 0
          left_inv := fun _ => Y.property.eq_of_src _ _
          right_inv := fun _ => (zeroSub_isZero _).eq_of_src _ _ }
      homEquiv_naturality_left_symm := fun {X' _ _} _ _ => X'.property.eq_of_src _ _
      homEquiv_naturality_right := fun _ _ => (zeroSub_isZero _).eq_of_src _ _ }

/-- **The trivial recollement** `0 → D → D`: `D_Z = 0`, `i_*` the inclusion of
the zero objects, `i^* = i^! = 0`, and `j_! = j^* = j_* = 𝟭`. -/
def trivialRecollement : Recollement (ZeroSub D) D D where
  iStar := toZero D
  iLower := (zeroProp D).ι
  iShriek := toZero D
  jShriek := 𝟭 D
  jStar := 𝟭 D
  jUpper := 𝟭 D
  iStarAdj := iStarAdj D
  iLowerAdj := iLowerAdj D
  jShriekAdj := Adjunction.id
  jStarAdj := Adjunction.id
  kernel X := ⟨fun ⟨e⟩ => ⟨⟨X, IsZero.of_iso (isZero_zero D) e⟩, ⟨Iso.refl _⟩⟩,
    fun ⟨Y, ⟨e⟩⟩ => ⟨e ≪≫ Y.property.isoZero⟩⟩
  jStar_iLower := (Functor.isZero _ fun Y => Y.property).isoZero
  iShriek_jUpper := (Functor.isZero _ fun _ => zeroSub_isZero _).isoZero
  iStar_jShriek := (Functor.isZero _ fun _ => zeroSub_isZero _).isoZero
  firstConnecting := 0
  secondConnecting := 0
  first_distinguished X := by
    refine isomorphic_distinguished _ (contractible_distinguished X) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [Adjunction.id]; rfl) ((isZero_zero D).eq_of_tgt _ _)
      ((isZero_zero D).eq_of_src _ _)
  second_distinguished X := by
    refine isomorphic_distinguished _ (contractible_distinguished₁ X) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((isZero_zero D).eq_of_src _ _) (by simp [Adjunction.id]) (by simp)

end Trivial

/-! ### Instances of the headline -/

/-- **Non-vacuity, all hypotheses.**  For any triangulated `C`, the trivial
recollement `0 → ZeroSub C → ZeroSub C` satisfies every hypothesis of
`theorem_1_1_paper`, including both Stacks 09SR hypotheses. -/
theorem theorem_1_1_paper_zero (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [CategoryTheory.IsTriangulated C] :
    SatisfiesPaperWA (ZeroSub C) ↔ ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      ∀ f : (⟨0, isZero_zero C⟩ : ZeroSub C) ⟶ (⟨0, isZero_zero C⟩ : ZeroSub C)⟦n⟧, f = 0 :=
  theorem_1_1_paper (trivialRecollement (ZeroSub C)) (zeroSub_satisfiesPaperWA _)
    (zeroSub_satisfiesPaperWA C) _ (isCompactAb_of_isZero (zeroSub_isZero _))
    (fun {E} _ => zeroSub_isZero E) (zeroSub_tag09SR C) (zeroSub_tag09SR _)

/-- The small-Hom affine derived category of `ℤ`. -/
abbrev DInt : Type 1 :=
  RelativeFM.SmallAffineD ℤ (RelativeFM.Spaltenstein.affineSpaltensteinInput ℤ)

/-- A concrete instance of `theorem_1_1_paper_zero`: `C = D(ℤ)`. -/
example : SatisfiesPaperWA (ZeroSub DInt) ↔ ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
    ∀ f : (⟨0, isZero_zero DInt⟩ : ZeroSub DInt) ⟶ (⟨0, isZero_zero DInt⟩ : ZeroSub DInt)⟦n⟧,
      f = 0 :=
  theorem_1_1_paper_zero DInt

/-- **Non-vacuity, nonzero middle term.**  For any commutative ring `A`, the
trivial recollement `0 → D(A) → D(A)` of the small-Hom affine derived category,
with `G'` the ring object, meets every hypothesis of `theorem_1_1_paper` except
Stacks 09SR for `D(A)`, which is the remaining (Stacks-allowed) argument. -/
theorem theorem_1_1_paper_affine (A : Type u) [CommRing A]
    (h09SR : ∀ (G : RelativeFM.SmallAffineD A (RelativeFM.Spaltenstein.affineSpaltensteinInput A)),
      IsPaperGenerator G → IsCompactAb G → IsClassicalGeneratorOnCompacts G) :
    SatisfiesPaperWA
        (RelativeFM.SmallAffineD A (RelativeFM.Spaltenstein.affineSpaltensteinInput A)) ↔
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
        ∀ f : (RelativeFM.AffineNeemanEndpointM3.smallRegularModulePaperData A
            (RelativeFM.Spaltenstein.affineSpaltensteinInput A)).G ⟶
          (RelativeFM.AffineNeemanEndpointM3.smallRegularModulePaperData A
            (RelativeFM.Spaltenstein.affineSpaltensteinInput A)).G⟦n⟧, f = 0 := by
  let H := RelativeFM.Spaltenstein.affineSpaltensteinInput A
  let W := RelativeFM.AffineNeemanEndpointM3.smallRegularModulePaperData A H
  have : HasCoproducts.{u} (RelativeFM.SmallAffineD A H) :=
    RelativeFM.smallAffineHasCoproductsOfUnivLE A H
  exact theorem_1_1_paper (trivialRecollement _) (zeroSub_satisfiesPaperWA _) ⟨W⟩ W.G
    W.G_compact W.G_paperGenerates h09SR (zeroSub_tag09SR _)

end

end RelativeWeakApprox.PaperHypothesesW6.NonVacuity

#print axioms RelativeWeakApprox.PaperHypothesesW6.NonVacuity.trivialRecollement
#print axioms RelativeWeakApprox.PaperHypothesesW6.NonVacuity.zeroSub_satisfiesPaperWA
#print axioms RelativeWeakApprox.PaperHypothesesW6.NonVacuity.zeroSub_satisfiesPaperWA_univ
#print axioms RelativeWeakApprox.PaperHypothesesW6.NonVacuity.theorem_1_1_paper_zero
#print axioms RelativeWeakApprox.PaperHypothesesW6.NonVacuity.theorem_1_1_paper_affine
