import FourierMukai.Scheme.SpaltensteinColimit

/-!
# Reduction of unrestricted K-projective replacements

This file records the exact remaining inputs for Spaltenstein's Theorem C after
the stage, countable induction, and special-colimit arguments.
-/

@[expose] public section

namespace RelativeFM.Spaltenstein

open CategoryTheory CategoryTheory.Limits CochainComplex

universe w v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Missing chain-level successor map between two canonical truncations.
Mathlib already supplies the objects, bounds, and maps to the original complex. -/
structure CanonicalTruncationData (A : CochainComplex C ℤ) where
  step (n : ℕ) : A.truncLE (n : ℤ) ⟶ A.truncLE ((n + 1 : ℕ) : ℤ)
  step_ι (n : ℕ) : step n ≫ A.ιTruncLE ((n + 1 : ℕ) : ℤ) =
    A.ιTruncLE (n : ℤ)

/-- The nested canonical-truncation filtration once its successor maps have
been constructed. -/
noncomputable def canonicalFiltration {A : CochainComplex C ℤ}
    (D : CanonicalTruncationData A) : BoundedAboveFiltration A where
  B n := A.truncLE (n : ℤ)
  isStrictlyLE n := inferInstance
  step := D.step
  toA n := A.ιTruncLE (n : ℤ)
  step_toA := D.step_ι

lemma quasiIsoAt_canonicalFiltration_toA {A : CochainComplex C ℤ}
    (D : CanonicalTruncationData A) (n : ℕ) (q : ℤ) (hq : q ≤ (n : ℤ)) :
    QuasiIsoAt ((canonicalFiltration D).toA n) q :=
  A.quasiIsoAt_ιTruncLE (n : ℤ) q hq

/-- The two remaining general inputs in this development. -/
structure TheoremCInput (C : Type u) [Category.{v} C] [Abelian C] where
  exactSequentialColimit : SequentialColimitQuasiIsoInput C
  canonicalTruncation (A : CochainComplex C ℤ) : CanonicalTruncationData A
  quasiIso_colimitToA [HasColimitsOfShape ℕ C]
    (A : CochainComplex C ℤ) :
    QuasiIso (filtrationColimitToA (canonicalFiltration (canonicalTruncation A)))

/-- Spaltenstein's replacement theorem, reduced to canonical-truncation
successor maps and exact-colimit comparisons. -/
noncomputable def replacementOfInput [EnoughProjectives C] [HasDerivedCategory C]
    [HasColimitsOfShape ℕ C] [HasCoproductsOfShape ℕ C]
    [HasExactColimitsOfShape ℕ C] (H : TheoremCInput C)
    (A : CochainComplex C ℤ) : DerivedCoproducts.KProjectiveResolution (DerivedCategory.Q.obj A) :=
  resolutionOfFiltration (canonicalFiltration (H.canonicalTruncation A))
    H.exactSequentialColimit (H.quasiIso_colimitToA A)

/-- Replacement data in the interface consumed by derived coproducts. -/
noncomputable def replacementDataOfInput [EnoughProjectives C] [HasDerivedCategory C]
    [HasColimitsOfShape ℕ C] [HasCoproductsOfShape ℕ C]
    [HasExactColimitsOfShape ℕ C] (H : TheoremCInput C) :
    DerivedCoproducts.KProjectiveReplacementData C where
  resolution X :=
      let R := replacementOfInput H (DerivedCategory.Q.objPreimage X)
      { complex := R.complex
        isKProjective := R.isKProjective
        iso := R.iso ≪≫ DerivedCategory.Q.objObjPreimageIso X }

/-- Derived coproducts follow immediately from the replacement data. -/
theorem hasCoproductsOfInput [EnoughProjectives C] [HasDerivedCategory C]
    [HasColimitsOfShape ℕ C] [HasCoproductsOfShape ℕ C]
    [HasExactColimitsOfShape ℕ C] [HasCoproducts.{w} C]
    (H : TheoremCInput C) : HasCoproducts.{w} (DerivedCategory C) :=
  DerivedCoproducts.hasCoproductsOfKProjectiveReplacementData
    (replacementDataOfInput H)

#print axioms RelativeFM.Spaltenstein.replacementOfInput
#print axioms RelativeFM.Spaltenstein.replacementDataOfInput
#print axioms RelativeFM.Spaltenstein.hasCoproductsOfInput

end
end RelativeFM.Spaltenstein
