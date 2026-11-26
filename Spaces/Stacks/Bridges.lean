/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import StacksFrontier.CategoryTheory.Triangulated.CompactObjects.ThickSubcategory
import StacksFrontier.CategoryTheory.Triangulated.Generators
import WeakApprox.CompactAb
import WeakApprox.GeneratorBridge
import WeakApprox.Lemma43
import WeakApprox.CompactThick

/-!
# Bridges between AxiomMath/Stacks' categorical notions and the repository's

The categorical Stacks results that GL26 and LP26 use (Stacks 09SR, 09SN) are theorems of
AxiomMath/Stacks, stated with AxiomMath's notions of compact object, weak generator and
classical generator of the compact objects.  The repository states the same results with
its own notions (LP26 §2.1.2, GL26 §2.1).  This file proves that the notions agree, so
that `Spaces/Stacks/Tags.lean` can discharge the repository's `Prop`s
`OpenClosedCompletionW3.Tag09SRPaper` and `StacksInterface.Tag09SN` from AxiomMath's
theorems (gap C.10 of `results/AXIOMMATH_MAP.md`).

## What is proved

* `isCompactObject_iff_isCompactAb`: for an object `K` of a preadditive category `C`
  with Hom universe `v`, AxiomMath's `CategoryTheory.IsCompactObject.{v} K` (Stacks 07LS:
  for every `Type v`-indexed family with a coproduct, `⨁ i, (K ⟶ E i) → (K ⟶ ∐ E)` is
  bijective) is equivalent to `RelativeWeakApprox.IsCompactAb K` (the
  `AddCommGrpCat`-valued `Hom(K, -)` preserves `Type v`-indexed coproducts).  No
  coproducts are assumed in `C`.  The comparison of a colimit cofan of abelian groups with
  the finite-support direct sum is the repository's
  (`bijective_abCofanSum_of_isColimit`, `isColimitCofan_of_bijective_abCofanSum`,
  `WeakApprox/CompactAb.lean`).
* `isWeakTriangulatedGenerator_singleton_iff`: AxiomMath's
  `(ObjectProperty.singleton G).IsWeakTriangulatedGenerator` (Stacks 09SJ(3)) is
  `RelativeWeakApprox.IsPaperGenerator G` (zero detection by the shifts of `G`).
* `rightOrthogonal_ofObj_isZero_iff_isWeakTriangulatedGenerator`: the hypothesis of
  AxiomMath's 09SN, for a family `E`, is `(ObjectProperty.ofObj E).IsWeakTriangulatedGenerator`.
* `isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq`: for a pretriangulated `C` and
  a compact `G`, the repository's `IsClassicalGeneratorOnCompacts G` (every compact object
  lies in the thick envelope of `G`) is AxiomMath's `(singleton G).triangEnvelope =
  IsCompactObject.{v}` (the form of "`⟨G⟩ = D_c`" in AxiomMath's 09SR).  The inequality
  `⟨G⟩ ≤ D_c` is automatic: the compact objects form a triangulated subcategory stable
  under retracts (`RelativeWeakApprox.isCompactAb_of_mem_triangEnvelope`, proved in the
  tree without coproducts).

## Assumptions

None.  AxiomMath/Stacks is the pinned dependency of the `Spaces` library; the modules
imported here (`ThickSubcategory`, `Generators`) are on
`scripts/axiommath/spaces-imports.txt`.
-/

namespace RelativeFM.Spaces.Stacks

open CategoryTheory CategoryTheory.Limits RelativeWeakApprox

universe v u

section Compact

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- For a cofan `c` of `f : J → C` and an object `K`, the image of `c` under the additive
`Hom(K, -)`. -/
noncomputable abbrev homCofan (K : C) {J : Type v} {f : J → C} (c : Cofan f) :
    Cofan fun j => (preadditiveCoyoneda.obj (Opposite.op K)).obj (f j) :=
  Cofan.mk ((preadditiveCoyoneda.obj (Opposite.op K)).obj c.pt)
    fun j => (preadditiveCoyoneda.obj (Opposite.op K)).map (c.inj j)

/-- The finite-support comparison map of `homCofan K c` is the map
`⨁ j, (K ⟶ f j) → (K ⟶ c.pt)`, `(x_j) ↦ ∑ x_j ≫ c.inj j`, of AxiomMath's 07LS. -/
lemma abCofanSum_homCofan_hom (K : C) {J : Type v} [DecidableEq J] {f : J → C}
    (c : Cofan f) :
    (abCofanSum (homCofan K c)).hom =
      DirectSum.toAddMonoid (fun j => Preadditive.rightComp K (c.inj j)) := by
  apply DirectSum.addHom_ext
  intro j y
  exact (abCofanSum_single (homCofan K c) j y).trans
    (DirectSum.toAddMonoid_of (fun j => Preadditive.rightComp K (c.inj j)) j y).symm

/-- **Stacks 07LS** (bridge, one direction): AxiomMath's compactness
`IsCompactObject.{v} K` implies the repository's `IsCompactAb K`.  No coproducts are
assumed: for every colimit cofan `c` of a `Type v`-indexed family, the AxiomMath
bijection for the chosen coproduct `∐ f` (which exists, `c` being a colimit) is
transported along `∐ f ≅ c.pt`. -/
theorem isCompactAb_of_isCompactObject {K : C} (hK : IsCompactObject.{v} K) :
    IsCompactAb K := by
  constructor
  intro J
  classical
  have : ∀ f : J → C,
      PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (Opposite.op K)) := by
    intro f
    refine ⟨fun {c} hc => ⟨?_⟩⟩
    let c' : Cofan f := c
    have hc' : IsColimit c' := hc
    haveI : HasCoproduct f := ⟨⟨⟨c', hc'⟩⟩⟩
    refine (Cofan.isColimitMapCoconeEquiv _ f c').symm ?_
    refine isColimitCofan_of_bijective_abCofanSum (homCofan K c') ?_
    let e : ∐ f ≅ c'.pt := colimit.isoColimitCocone ⟨c', hc'⟩
    have he : ∀ j, Sigma.ι f j ≫ e.hom = c'.inj j := fun j =>
      colimit.isoColimitCocone_ι_hom ⟨c', hc'⟩ (Discrete.mk j)
    have hφ := hK.bijective_toAddMonoid_rightComp_sigmaι f
    have hpost : Function.Bijective (Preadditive.rightComp K e.hom) :=
      ⟨fun a b hab => by
          change a ≫ e.hom = b ≫ e.hom at hab
          simpa using congrArg (· ≫ e.inv) hab,
        fun g => ⟨g ≫ e.inv, by change (g ≫ e.inv) ≫ e.hom = g; simp⟩⟩
    have hcomp : (Preadditive.rightComp K e.hom).comp
        (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Sigma.ι f j)) =
          DirectSum.toAddMonoid fun j => Preadditive.rightComp K (c'.inj j) := by
      apply DirectSum.addHom_ext
      intro j y
      rw [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of, ← he]
      exact Category.assoc _ _ _
    have hbij : Function.Bijective
        (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (c'.inj j)) := by
      rw [← hcomp, AddMonoidHom.coe_comp]
      exact hpost.comp hφ
    change Function.Bijective (abCofanSum (homCofan K c')).hom
    rw [abCofanSum_homCofan_hom]
    exact hbij
  exact preservesColimitsOfShape_of_discrete _

/-- **Stacks 07LS** (bridge, other direction): the repository's `IsCompactAb K` implies
AxiomMath's compactness `IsCompactObject.{v} K`.  The image under `Hom(K, -)` of the
coproduct cofan is a colimit cofan of abelian groups, whose finite-support comparison map
is bijective (`bijective_abCofanSum_of_isColimit`). -/
theorem isCompactObject_of_isCompactAb {K : C} (hK : IsCompactAb K) :
    IsCompactObject.{v} K where
  bijective_toAddMonoid_rightComp_sigmaι {I} _ E _ := by
    let c : Cofan E := Cofan.mk (∐ E) (Sigma.ι E)
    have hc : IsColimit c := colimit.isColimit (Discrete.functor E)
    have h := (Cofan.isColimitMapCoconeEquiv (preadditiveCoyoneda.obj (Opposite.op K)) E c)
      (isColimitOfPreserves (preadditiveCoyoneda.obj (Opposite.op K)) hc)
    have hb : Function.Bijective (abCofanSum (homCofan K c)).hom :=
      bijective_abCofanSum_of_isColimit h
    rw [abCofanSum_homCofan_hom] at hb
    exact hb

/-- **Stacks 07LS** (bridge): for an object `K` of a preadditive category with Hom
universe `v`, AxiomMath's `IsCompactObject.{v} K` is the repository's `IsCompactAb K`.
No coproducts in `C` are assumed. -/
theorem isCompactObject_iff_isCompactAb (K : C) :
    IsCompactObject.{v} K ↔ IsCompactAb K :=
  ⟨isCompactAb_of_isCompactObject, isCompactObject_of_isCompactAb⟩

/-- The two compactness properties of objects coincide. -/
theorem isCompactObject_eq_isCompactAb :
    (IsCompactObject.{v, v, u} (C := C) : ObjectProperty C) = fun K => IsCompactAb K := by
  funext K
  exact propext (isCompactObject_iff_isCompactAb K)

end Compact

section Generator

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- **Stacks 09SJ(3)** (bridge): AxiomMath's weak generator
`(ObjectProperty.singleton G).IsWeakTriangulatedGenerator` is the paper's generation
condition `IsPaperGenerator G` (LP26 §2.1.2, GL26 §2.1): an object receiving only zero
maps from the shifts of `G` is zero. -/
theorem isWeakTriangulatedGenerator_singleton_iff (G : C) :
    (ObjectProperty.singleton G).IsWeakTriangulatedGenerator ↔ IsPaperGenerator G := by
  constructor
  · intro h E hE
    exact h E ((rightOrthogonal_shiftClosure_singleton_iff G E).2 hE)
  · intro h K hK
    exact h ((rightOrthogonal_shiftClosure_singleton_iff G K).1 hK)

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The hypothesis of AxiomMath's 09SN for a family `E` is AxiomMath's weak generation
by `ObjectProperty.ofObj E` (definitional). -/
theorem rightOrthogonal_ofObj_isZero_iff_isWeakTriangulatedGenerator {ι : Type*}
    (E : ι → C) :
    (∀ Y : C, ((ObjectProperty.ofObj E).shiftClosure ℤ).rightOrthogonal Y → IsZero Y) ↔
      (ObjectProperty.ofObj E).IsWeakTriangulatedGenerator :=
  Iff.rfl

/-- The triangulated envelope of a compact object consists of compact objects: the
`IsCompactAb` objects form a triangulated subcategory stable under retracts
(`RelativeWeakApprox.isCompactAb_of_mem_triangEnvelope`, `WeakApprox/CompactThick.lean`;
no coproducts needed), and the two compactness notions agree. -/
theorem triangEnvelope_singleton_le_isCompactObject (G : C) (hG : IsCompactAb G) :
    (ObjectProperty.singleton G).triangEnvelope ≤ IsCompactObject.{v, v, u} (C := C) :=
  fun _ hX => isCompactObject_of_isCompactAb (isCompactAb_of_mem_triangEnvelope hG hX)

/-- **Classical generation of the compact objects** (bridge): for a compact `G`, the
repository's `IsClassicalGeneratorOnCompacts G` (every `IsCompactAb` object lies in the
triangulated envelope of `G`) is AxiomMath's `(singleton G).triangEnvelope =
IsCompactObject.{v}` (the form of "`⟨G⟩ = D_c`" in AxiomMath's 09SR). -/
theorem isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq (G : C) (hG : IsCompactAb G) :
    IsClassicalGeneratorOnCompacts G ↔
      (ObjectProperty.singleton G).triangEnvelope = IsCompactObject.{v, v, u} (C := C) := by
  constructor
  · intro h
    refine le_antisymm (triangEnvelope_singleton_le_isCompactObject G hG) fun X hX => ?_
    exact h X (isCompactAb_of_isCompactObject hX)
  · intro h X hX
    rw [h]
    exact isCompactObject_of_isCompactAb hX

end Generator

end RelativeFM.Spaces.Stacks

#print axioms RelativeFM.Spaces.Stacks.isCompactObject_iff_isCompactAb
#print axioms RelativeFM.Spaces.Stacks.isWeakTriangulatedGenerator_singleton_iff
#print axioms RelativeFM.Spaces.Stacks.isClassicalGeneratorOnCompacts_iff_triangEnvelope_eq
