/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.StatementAudit
import FourierMukai.Scheme.DerivedCoproducts

/-! # Coproducts of K-projective complexes in a `Coprod` closure -/

@[expose] public section

namespace RelativeFM.AisleGeneration.DerivedCoproduct

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits

universe w w' v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The explicit degreewise coproduct of K-projective complexes maps to a
coproduct in the derived category, and hence stays in `Coprod S`. -/
theorem coprod_Q_coproductComplex {ι : Type w'} [Small.{w} ι] [HasCoproductsOfShape ι C]
    (S : ObjectProperty (DerivedCategory C)) (K : ι → CochainComplex C ℤ)
    [∀ i, (K i).IsKProjective]
    (hK : ∀ i, Coprod S (DerivedCategory.Q.obj (K i))) :
    Coprod S (DerivedCategory.Q.obj (DerivedCoproducts.coproductComplexCocone K).pt) := by
  let pres : ColimitPresentation (Discrete ι)
      (DerivedCategory.Q.obj (DerivedCoproducts.coproductComplexCocone K).pt) :=
    { diag := Discrete.functor (fun i => DerivedCategory.Q.obj (K i))
      ι := (DerivedCoproducts.derivedCoproductCofan K).ι
      isColimit := DerivedCoproducts.derivedCoproductCofanIsColimit K }
  exact Coprod.of_colimitPresentation (P := S)
    (pres.reindex (Discrete.equivalence (equivShrink.{w} ι)).inverse)
    (fun j => hK ((equivShrink.{w} ι).symm j.as))

end

end RelativeFM.AisleGeneration.DerivedCoproduct

#print axioms RelativeFM.AisleGeneration.DerivedCoproduct.coprod_Q_coproductComplex
