import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.SmallObject.Basic

@[expose] public section

namespace RelativeFM.ProjectiveModel

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] (I : MorphismProperty C) (κ : Cardinal.{w})
variable [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- A convenient constructor for the preservation hypothesis in the small
object argument: all sources of `I` are presentable at the iteration
cardinal. The ordinal is `κ`-filtered, so presentability preserves every
relative-cell-complex diagram in question. -/
lemma isCardinalForSmallObjectArgumentOfPresentable
    [I.IsSmall.{w}] [LocallySmall.{w} C] [HasPushouts C] [HasCoproducts.{w} C]
    [HasIterationOfShape κ.ord.ToType C]
    (h : ∀ {A B : C} (i : A ⟶ B), I i → IsCardinalPresentable A κ) :
    I.IsCardinalForSmallObjectArgument κ where
  preservesColimit {A B X Y} i hi f hf := by
    letI := h i hi
    have := preservesColimitsOfShape_of_isCardinalPresentable A κ κ.ord.ToType
    exact PreservesColimitsOfShape.preservesColimit

/-- The corresponding `HasSmallObjectArgument` constructor. -/
lemma hasSmallObjectArgumentOfPresentable
    [I.IsSmall.{w}] [LocallySmall.{w} C] [HasPushouts C] [HasCoproducts.{w} C]
    [HasIterationOfShape κ.ord.ToType C]
    (h : ∀ {A B : C} (i : A ⟶ B), I i → IsCardinalPresentable A κ) :
    I.HasSmallObjectArgument.{w} :=
  ⟨κ, inferInstance, inferInstance, isCardinalForSmallObjectArgumentOfPresentable I κ h⟩

#print axioms RelativeFM.ProjectiveModel.isCardinalForSmallObjectArgumentOfPresentable
#print axioms RelativeFM.ProjectiveModel.hasSmallObjectArgumentOfPresentable

end RelativeFM.ProjectiveModel
