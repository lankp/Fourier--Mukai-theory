import FourierMukai.Scheme.AffineLocalCohomologySupport

@[expose] public section

namespace RelativeFM.Recollement.IShriek

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Coextension of scalars along `A → A[1/f]`, the underived right adjoint of
restriction of scalars. -/
noncomputable abbrev underivedCandidate (A : Type u) [CommRing A] (f : A) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} (Away A f) :=
  ModuleCat.coextendScalars (algebraMap A (Away A f))

/-- The degreewise construction works under exactly the exactness hypothesis
needed by `Functor.mapDerivedCategory`.  In this generality this says that the
underived Hom functor is right exact, so this is a conditional special case,
not a construction for an arbitrary localization. -/
noncomputable def derivedCoextendScalars (A : Type u) [CommRing A] (f : A)
    [PreservesFiniteColimits (underivedCandidate A f)] :
    AffineD A ⥤ AffineD (Away A f) := by
  letI : (underivedCandidate A f).Additive :=
    (ModuleCat.restrictCoextendScalarsAdj
      (algebraMap A (Away A f))).right_adjoint_additive
  exact (underivedCandidate A f).mapDerivedCategory

/-- The comparison of conditional derived coextension with its degreewise
representative. -/
noncomputable abbrev derivedCoextendScalarsFactors (A : Type u) [CommRing A] (f : A)
    [PreservesFiniteColimits (underivedCandidate A f)] :
    DerivedCategory.Q ⋙ derivedCoextendScalars A f ≅
      (underivedCandidate A f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q := by
  letI : (underivedCandidate A f).Additive :=
    (ModuleCat.restrictCoextendScalarsAdj
      (algebraMap A (Away A f))).right_adjoint_additive
  exact (underivedCandidate A f).mapDerivedCategoryFactors

/-- In the exact degreewise case, the underived adjunction descends to the
unbounded derived categories. -/
noncomputable def derivedRestrictionCoextendAdjunction (A : Type u) [CommRing A] (f : A)
    [PreservesFiniteColimits (underivedCandidate A f)] :
    derivedRestrictionScalars A f ⊣ derivedCoextendScalars A f := by
  letI : (underivedCandidate A f).Additive :=
    (ModuleCat.restrictCoextendScalarsAdj
      (algebraMap A (Away A f))).right_adjoint_additive
  letI : CatCommSq
      ((ModuleCat.restrictScalars (algebraMap A (Away A f))).mapHomologicalComplex
        (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q
        (derivedRestrictionScalars A f) :=
    ⟨(derivedRestrictionScalarsFactors A f).symm⟩
  letI : CatCommSq
      ((underivedCandidate A f).mapHomologicalComplex (ComplexShape.up ℤ))
        DerivedCategory.Q DerivedCategory.Q (derivedCoextendScalars A f) :=
    ⟨(derivedCoextendScalarsFactors A f).symm⟩
  exact (Adjunction.mapComplex (ModuleCat.restrictCoextendScalarsAdj
    (algebraMap A (Away A f))) (ComplexShape.up ℤ)).localization
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} (Away A f)) (ComplexShape.up ℤ))
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    (derivedRestrictionScalars A f) (derivedCoextendScalars A f)

/-- Conditional `iShriek`, supplied directly in the shape required by
`AffineRecollementInput`. -/
noncomputable abbrev exactIShriek (A : Type u) [CommRing A] (f : A)
    [PreservesFiniteColimits (underivedCandidate A f)] :=
  derivedCoextendScalars A f

/-- The exact degreewise candidate has its canonical shift structure. -/
noncomputable instance derivedCoextendScalars_commShift (A : Type u) [CommRing A] (f : A)
    [PreservesFiniteColimits (underivedCandidate A f)] :
    (derivedCoextendScalars A f).CommShift ℤ := by
  letI : (underivedCandidate A f).Additive :=
    (ModuleCat.restrictCoextendScalarsAdj
      (algebraMap A (Away A f))).right_adjoint_additive
  change (underivedCandidate A f).mapDerivedCategory.CommShift ℤ
  infer_instance

/-- The exact degreewise candidate is triangulated. -/
noncomputable instance derivedCoextendScalars_exact (A : Type u) [CommRing A] (f : A)
    [PreservesFiniteColimits (underivedCandidate A f)] :
    (derivedCoextendScalars A f).IsTriangulated := by
  letI : (underivedCandidate A f).Additive :=
    (ModuleCat.restrictCoextendScalarsAdj
      (algebraMap A (Away A f))).right_adjoint_additive
  change (underivedCandidate A f).mapDerivedCategory.IsTriangulated
  infer_instance

/-- Any construction of the remaining adjunction supplies the shift field by
right-adjoint transport. -/
noncomputable def commShiftOfILowerAdj {A : Type u} [CommRing A] (f : A)
    {G : AffineD A ⥤ AffineD (Away A f)}
    (adj : derivedRestrictionScalars A f ⊣ G) : G.CommShift ℤ :=
  adj.rightAdjointCommShift ℤ

/-- The corresponding compatibility of the adjunction with its transported
right-adjoint shift structure. -/
noncomputable def adjunctionCommShiftOfILowerAdj {A : Type u} [CommRing A] (f : A)
    {G : AffineD A ⥤ AffineD (Away A f)}
    (adj : derivedRestrictionScalars A f ⊣ G) :
    letI : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
    adj.CommShift ℤ := by
  letI : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  exact adj.commShift_of_leftAdjoint ℤ

/-- Any construction of the remaining adjunction supplies exactness by
Mathlib's right-adjoint triangulation theorem. -/
noncomputable def exactOfILowerAdj {A : Type u} [CommRing A] (f : A)
    {G : AffineD A ⥤ AffineD (Away A f)}
    (adj : derivedRestrictionScalars A f ⊣ G) :
    letI : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
    letI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
    G.IsTriangulated := by
  letI : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  letI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  exact adj.isTriangulated_rightAdjoint

#print axioms derivedCoextendScalars
#print axioms derivedCoextendScalarsFactors
#print axioms derivedRestrictionCoextendAdjunction
#print axioms derivedCoextendScalars_commShift
#print axioms derivedCoextendScalars_exact
#print axioms commShiftOfILowerAdj
#print axioms adjunctionCommShiftOfILowerAdj
#print axioms exactOfILowerAdj

end
end RelativeFM.Recollement.IShriek
