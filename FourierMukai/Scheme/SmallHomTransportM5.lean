import WeakApprox.CompactAb
import Mathlib.Algebra.Category.Grp.Ulift

@[expose] public section

namespace RelativeFM.SmallHomM5

open CategoryTheory CategoryTheory.Limits
open RelativeWeakApprox

universe v uC uD

noncomputable section

variable {C : Type uC} [Category.{v + 1} C] [Preadditive C]
variable {D : Type uD} [Category.{v} D] [Preadditive D]

/-- The additive comparison of covariant Hom functors for an adjunction whose
source Hom universe is one level larger than its target Hom universe. -/
noncomputable def preadditiveCompCoyonedaUliftIso
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] (adj : F ⊣ G) (X : C) :
    preadditiveCoyoneda.obj (.op (F.obj X)) ⋙ AddCommGrpCat.uliftFunctor.{v + 1, v} ≅
      G ⋙ preadditiveCoyoneda.obj (.op X) :=
  NatIso.ofComponents
    (fun Y => (AddEquiv.ulift.trans (adj.homAddEquiv X Y)).toAddCommGrpIso)
    (fun g => by
      ext ⟨f⟩
      change (adj.homEquiv X _) (f ≫ g) = (adj.homEquiv X _) f ≫ G.map g
      exact adj.homEquiv_naturality_right f g)

/-- Compactness descends along an equivalence from Hom universe `v + 1` to Hom
universe `v`.  Only this direction is available: the larger-Hom hypothesis
also controls coproducts indexed by every `v`-small type after shrinking. -/
theorem isCompactAb_of_equivalence_large_to_small
    (F : C ⥤ D) [F.IsEquivalence] [F.Additive]
    {X : C} (hX : IsCompactAb X) : IsCompactAb (F.obj X) where
  preserves J := by
    letI : PreservesColimitsOfShape (Discrete.{v + 1} (Shrink.{v + 1} J))
        (preadditiveCoyoneda.obj (.op X)) := hX.preserves (Shrink.{v + 1} J)
    letI : PreservesColimitsOfShape (Discrete.{v} J)
        (preadditiveCoyoneda.obj (.op X)) :=
      preservesColimitsOfShape_of_equiv
        (Discrete.equivalence (equivShrink.{v + 1, v} J).symm) _
    let E := F.asEquivalence
    letI : E.functor.Additive := by
      change F.Additive
      infer_instance
    letI : PreservesColimitsOfShape (Discrete.{v} J)
        (E.inverse ⋙ preadditiveCoyoneda.obj (.op X)) := inferInstance
    let e := preadditiveCompCoyonedaUliftIso E.toAdjunction X
    letI : PreservesColimitsOfShape (Discrete J)
        (preadditiveCoyoneda.obj (.op (F.obj X)) ⋙
          AddCommGrpCat.uliftFunctor.{v + 1, v}) :=
      preservesColimitsOfShape_of_natIso e.symm
    exact preservesColimitsOfShape_of_reflects_of_preserves _
      AddCommGrpCat.uliftFunctor.{v + 1, v}

end

end RelativeFM.SmallHomM5

#print axioms RelativeFM.SmallHomM5.preadditiveCompCoyonedaUliftIso
#print axioms RelativeFM.SmallHomM5.isCompactAb_of_equivalence_large_to_small
