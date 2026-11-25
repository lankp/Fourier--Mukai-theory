import FourierMukai.Scheme.KProjectiveResolution
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Derived coproducts of bounded-above module complexes

Unlike `affine_hasCoproducts_zero_of_spaltenstein`, this result has no unbounded
replacement hypothesis. The bounds are allowed to vary from one summand to another.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits

universe w u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Coproducts in `D(A-Mod)` of explicitly bounded-above complexes, constructed by
bounded-above projective resolutions. This is not a `HasCoproducts` assertion for the
whole unbounded derived category. -/
theorem affine_hasCoproductQObj_boundedAbove
    (A : Type u) [CommRing A] {ι : Type w}
    (K : ι → CochainComplex (ModuleCat.{u} A) ℤ) (d : ι → ℤ)
    [HasCoproductsOfShape ι (ModuleCat.{u} A)]
    [∀ i, (K i).IsStrictlyLE (d i)] :
    HasCoproduct (fun i ↦ DerivedCategory.Q.obj (K i)) :=
  KProjectiveResolution.hasCoproductQObjOfIsStrictlyLE K d

#print axioms RelativeFM.affine_hasCoproductQObj_boundedAbove

end

end RelativeFM
