import FourierMukai.Scheme.SpaltensteinTheoremC
import FourierMukai.Scheme.AffineCoproducts
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Affine Spaltenstein replacement data
-/

@[expose] public section
namespace RelativeFM.Spaltenstein

open CategoryTheory CategoryTheory.Limits CochainComplex

universe u
noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Unbounded K-projective replacement data for modules over an arbitrary
commutative ring, obtained from the completed Theorem C interface. -/
noncomputable def affineSpaltensteinInput (A : Type u) [CommRing A] :
    RelativeFM.AffineSpaltensteinInput A := by
  letI : AB5OfSize.{0, 0} (ModuleCat.{u} A) :=
    AB5OfSize_of_univLE (ModuleCat.{u} A)
  exact replacementDataOfInput (theoremCInput (C := ModuleCat.{u} A))

#print axioms RelativeFM.Spaltenstein.affineSpaltensteinInput

end
end RelativeFM.Spaltenstein
