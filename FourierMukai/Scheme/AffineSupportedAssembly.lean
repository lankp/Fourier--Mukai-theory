import FourierMukai.Scheme.AffineLocalCohomologySupport
import FourierMukai.Scheme.AffineGluing

@[expose] public section

namespace RelativeFM.AffineLocalCohomology

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The concrete supported local-cohomology functor, using the support proof
from the d4 support module. -/
noncomputable abbrev concreteJStar (A : Type u) [CommRing A] (f : A) :
    AffineD A ⥤ AffineDZ A f :=
  supportedFunctorOf A f (derivedFunctor_isSupported A f)

/-- Its comparison with the explicit local-cohomology functor. -/
noncomputable def concreteJStarFactors (A : Type u) [CommRing A] (f : A) :
    concreteJStar A f ⋙ affineDZι A f ≅ derivedFunctor A f :=
  supportedFunctorOfFactors A f (derivedFunctor_isSupported A f)

/-- The supported inclusion is left adjoint to concrete local cohomology. -/
noncomputable def concreteJShriekAdj (A : Type u) [CommRing A] (f : A) :
    affineDZι A f ⊣ concreteJStar A f :=
  supportedLocalCohomologyAdjunction A f (concreteJStar A f) (concreteJStarFactors A f)

/-- The first connecting transformation for concrete local cohomology. -/
noncomputable def concreteFirstConnecting (A : Type u) [CommRing A] (f : A) :
    derivedExtensionScalars A f ⋙ derivedRestrictionScalars A f ⟶
      concreteJStar A f ⋙ affineDZι A f ⋙ shiftFunctor (AffineD A) (1 : ℤ) :=
  supportedFirstConnecting A f (concreteJStar A f) (concreteJStarFactors A f)

/-- The concrete first gluing triangle is distinguished for every object. -/
lemma concreteFirstDistinguished (A : Type u) [CommRing A] (f : A)
    (X : AffineD A) :
    Triangle.mk ((concreteJShriekAdj A f).counit.app X)
      ((derivedExtensionRestrictionAdjunction A f).unit.app X)
      ((concreteFirstConnecting A f).app X) ∈ distTriang (AffineD A) :=
  supportedFirstTriangle_distinguished A f (concreteJStar A f) (concreteJStarFactors A f) X

/-- The kernel of concrete local cohomology is the essential image of derived
restriction from the open localization. -/
lemma concreteKernel (A : Type u) [CommRing A] (f : A) (X : AffineD A) :
    Nonempty ((concreteJStar A f).obj X ≅ 0) ↔
      ∃ Y : AffineD (Away A f),
        Nonempty (X ≅ (derivedRestrictionScalars A f).obj Y) :=
  supported_kernel A f (concreteJStar A f) (concreteJStarFactors A f) X

end
end RelativeFM.AffineLocalCohomology
