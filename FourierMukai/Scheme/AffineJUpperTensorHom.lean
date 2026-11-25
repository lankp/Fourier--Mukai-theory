/-
The tensor--Hom construction of the right adjoint to local cohomology.

The main theorem is completely categorical.  In the affine application, `T` is
`C \otimes^L -`, `H` is `RHom(C,-)`, and the comparison `e` is Stacks 0A6R.
No derived tensor--Hom package is asserted or constructed in this file.
-/
import FourierMukai.Scheme.AffineJUpperAdjoint

@[expose] public section

namespace RelativeFM.Recollement.JUpperM1.TensorHom

open CategoryTheory

universe vC uC vD uD

section Generic

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (E : C ⥤ D) [E.Full] [E.Faithful]
variable (J : D ⥤ C) (T H : D ⥤ D)
variable (tensorAdj : T ⊣ H) (e : J ⋙ E ≅ T)

/-- The Hom bijection induced by full faithfulness, the comparison `e`, and
`tensorAdj`. -/
noncomputable def homEquiv (X : D) (Y : C) :
    (J.obj X ⟶ Y) ≃ (X ⟶ H.obj (E.obj Y)) where
  toFun a := tensorAdj.homEquiv X (E.obj Y) (e.inv.app X ≫ E.map a)
  invFun b := E.preimage (e.hom.app X ≫ (tensorAdj.homEquiv X (E.obj Y)).symm b)
  left_inv a := by
    dsimp
    simp only [Equiv.symm_apply_apply]
    apply E.map_injective
    rw [E.map_preimage]
    simp
  right_inv b := by
    dsimp
    rw [E.map_preimage]
    simp

/-- If a fully faithful functor makes `J` into a tensor functor, then the
corresponding internal Hom is right adjoint to `J`. -/
noncomputable def adjunction : J ⊣ E ⋙ H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv E J T H tensorAdj e
      homEquiv_naturality_right := by
        intro X Y Y' a g
        dsimp [homEquiv]
        rw [← tensorAdj.homEquiv_naturality_right]
        simp
      homEquiv_naturality_left_symm := by
        intro X' X Y a b
        dsimp [homEquiv]
        apply E.map_injective
        rw [E.map_preimage, E.map_comp, E.map_preimage]
        rw [tensorAdj.homEquiv_naturality_left_symm]
        have he := e.hom.naturality a
        dsimp only [Functor.comp_map] at he
        simp only [← Category.assoc, he] }

end Generic

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

open AffineLocalCohomology

variable (A : Type u) [CommRing A] (f : A)
variable (T H : AffineD A ⥤ AffineD A)
variable (tensorAdj : T ⊣ H)
variable (e : jStar A f ⋙ affineDZι A f ≅ T)

/-- The completion candidate induced by a derived internal Hom. -/
noncomputable abbrev jUpper : AffineDZ A f ⥤ AffineD A :=
  affineDZι A f ⋙ H

/-- The supported local-cohomology adjunction induced by tensor--Hom
adjunction. -/
noncomputable def jStarAdj : jStar A f ⊣ jUpper A f H :=
  adjunction (affineDZι A f) (jStar A f) T H tensorAdj e

/-- All subsidiary fields then follow from the general adjoint-triple and
right-adjoint transport results. -/
noncomputable def consequences : JUpperM1.Consequences A f (jUpper A f H)
    (jStarAdj A f T H tensorAdj e) :=
  JUpperM1.consequences A f (jUpper A f H) (jStarAdj A f T H tensorAdj e)

#print axioms homEquiv
#print axioms adjunction
#print axioms jStarAdj
#print axioms consequences

end
end RelativeFM.Recollement.JUpperM1.TensorHom
