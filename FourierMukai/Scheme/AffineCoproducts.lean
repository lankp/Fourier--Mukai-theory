import FourierMukai.Scheme.Affine
import Mathlib.Algebra.Category.ModuleCat.Colimits
import FourierMukai.Scheme.DerivedCoproducts

/-!
# Affine derived coproducts from Spaltenstein replacements

Coproducts in `D(A-Mod)` are constructed from explicit Spaltenstein
K-projective resolutions and coproducts in the underlying module category.
All coproduct arguments are in `KProjectiveCoproduct`.

The exact row-10 size `HasCoproducts.{u+1} (ModuleCat.{u} A)` is not inferred:
families genuinely indexed in `Type (u+1)` need not have direct sums in the
category of `Type u`-small modules. See the accompanying report.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits

universe w u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Spaltenstein's unbounded K-projective replacement theorem for complexes of
`A`-modules, with its proof data exposed. This is the only unproved input to
`hasCoproductsA_of_spaltenstein`; it is not a coproduct hypothesis. -/
abbrev AffineSpaltensteinInput (A : Type u) [CommRing A] :=
  @DerivedCoproducts.KProjectiveReplacementData (ModuleCat.{u} A) _ _
    (HasDerivedCategory.standard _)

/-- **Affine derived coproducts.** Spaltenstein replacement data and
`Type w`-small coproducts in the underlying module category give `Type w`-small
coproducts in `D(A-Mod)`. The module-coproduct hypothesis is kept explicit;
in particular, this theorem does not pretend that the `w = u+1` instance is
available for `ModuleCat.{u} A`. -/
theorem affine_hasCoproducts_of_spaltenstein
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    [HasCoproducts.{w} (ModuleCat.{u} A)] :
    HasCoproducts.{w} (AffineD A) := by
  exact DerivedCoproducts.hasCoproductsOfKProjectiveReplacementData H

/-- Concrete partial result: with Spaltenstein replacements alone, universe-zero
coproducts in `D(A-Mod)` are constructed, since Mathlib has the corresponding
underlying module coproduct instance. This is not the larger row-10 universe. -/
theorem affine_hasCoproducts_zero_of_spaltenstein
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A) :
    HasCoproducts.{0} (AffineD A) :=
  affine_hasCoproducts_of_spaltenstein A H

#print axioms RelativeFM.affine_hasCoproducts_of_spaltenstein
#print axioms RelativeFM.affine_hasCoproducts_zero_of_spaltenstein

end

end RelativeFM
