import FourierMukai.Scheme.Duality
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Descent of a fixed complex-level tensor--Hom adjunction

This file is the categorical descent step.  It does not hide either of the two
mathematical inputs: tensoring with the fixed complex and applying its Hom
complex must separately preserve quasi-isomorphisms.  Given those facts and
the underived adjunction, `Adjunction.localization` constructs the derived
adjunction and its comparisons with the complex-level functors.
-/

@[expose] public section

namespace RelativeFM.KProjectiveTensorHom

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- A fixed complex-level tensor--Hom adjunction together with exactly the two
facts needed to descend it to the derived category. -/
structure FixedComplexTensorHomModel (C : Type u) [Category.{v} C] [Abelian C]
    [MonoidalCategory (CochainComplex C ℤ)] where
  /-- The fixed first argument. -/
  K : CochainComplex C ℤ
  /-- Its complex-level internal-Hom functor. -/
  hom : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  /-- The underived tensor--Hom adjunction. -/
  tensorHomAdj : tensorLeft K ⊣ hom
  /-- K-flatness, stated as the required preservation theorem (Stacks 06Y0). -/
  quasiIso_tensor {L M : CochainComplex C ℤ} (f : L ⟶ M) [QuasiIso f] :
    QuasiIso ((tensorLeft K).map f)
  /-- Exactness of derived Hom in the target variable for this fixed source. -/
  quasiIso_hom {L M : CochainComplex C ℤ} (f : L ⟶ M) [QuasiIso f] :
    QuasiIso (hom.map f)

namespace FixedComplexTensorHomModel

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory (CochainComplex C ℤ)]
  (S : FixedComplexTensorHomModel C)

/-- The descended derived tensor functor. -/
noncomputable def derivedTensor : DerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift (tensorLeft S.K ⋙ DerivedCategory.Q)
    (fun _ _ f hf => by
      letI : QuasiIso f := (HomologicalComplex.mem_quasiIso_iff f).1 hf
      letI : QuasiIso ((tensorLeft S.K).map f) := S.quasiIso_tensor f
      exact Localization.inverts DerivedCategory.Q _ _ (by
        change HomologicalComplex.quasiIso C (.up ℤ) ((tensorLeft S.K).map f)
        exact (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))
    DerivedCategory.Q

/-- The descended derived internal-Hom functor. -/
noncomputable def derivedHom : DerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift (S.hom ⋙ DerivedCategory.Q)
    (fun _ _ f hf => by
      letI : QuasiIso f := (HomologicalComplex.mem_quasiIso_iff f).1 hf
      letI : QuasiIso (S.hom.map f) := S.quasiIso_hom f
      exact Localization.inverts DerivedCategory.Q _ _ (by
        change HomologicalComplex.quasiIso C (.up ℤ) (S.hom.map f)
        exact (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))
    DerivedCategory.Q

/-- On cochain representatives, derived tensor is computed by the ordinary
total tensor complex. -/
noncomputable def derivedTensorFactors :
    DerivedCategory.Q ⋙ derivedTensor S ≅ tensorLeft S.K ⋙ DerivedCategory.Q :=
  Localization.fac (tensorLeft S.K ⋙ DerivedCategory.Q) _ DerivedCategory.Q

/-- On cochain representatives, derived Hom is computed by the ordinary Hom
complex. -/
noncomputable def derivedHomFactors :
    DerivedCategory.Q ⋙ derivedHom S ≅ S.hom ⋙ DerivedCategory.Q :=
  Localization.fac (S.hom ⋙ DerivedCategory.Q) _ DerivedCategory.Q

/-- The derived tensor--Hom adjunction, with no Brown-representability input. -/
noncomputable def derivedTensorHomAdj : derivedTensor S ⊣ derivedHom S := by
  letI : CatCommSq (tensorLeft S.K) DerivedCategory.Q DerivedCategory.Q
      (derivedTensor S) := ⟨(derivedTensorFactors S).symm⟩
  letI : CatCommSq S.hom DerivedCategory.Q DerivedCategory.Q (derivedHom S) :=
    ⟨(derivedHomFactors S).symm⟩
  exact S.tensorHomAdj.localization DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (derivedTensor S) (derivedHom S)

/-- The Hom-set form of the derived adjunction. -/
noncomputable def derivedHomEquiv (X Y : DerivedCategory C) :
    ((derivedTensor S).obj X ⟶ Y) ≃ (X ⟶ (derivedHom S).obj Y) :=
  (derivedTensorHomAdj S).homEquiv X Y

@[simp]
lemma derivedHomEquiv_apply (X Y : DerivedCategory C)
    (f : (derivedTensor S).obj X ⟶ Y) :
    derivedHomEquiv S X Y f = (derivedTensorHomAdj S).homEquiv X Y f := rfl

end FixedComplexTensorHomModel
end
end RelativeFM.KProjectiveTensorHom

#print axioms RelativeFM.KProjectiveTensorHom.FixedComplexTensorHomModel.derivedTensor
#print axioms RelativeFM.KProjectiveTensorHom.FixedComplexTensorHomModel.derivedHom
#print axioms RelativeFM.KProjectiveTensorHom.FixedComplexTensorHomModel.derivedTensorHomAdj
