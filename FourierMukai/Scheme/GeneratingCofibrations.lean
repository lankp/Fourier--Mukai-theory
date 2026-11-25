import FourierMukai.Scheme.ProjectiveModel
import FourierMukai.Scheme.SmallObjectPresentable

@[expose] public section

namespace RelativeFM.ProjectiveModel

open CategoryTheory CategoryTheory.Limits
open RelativeFM.DerivedCoproducts

universe w w₁ v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The complex consisting of `G` concentrated in degree `n`. -/
noncomputable abbrev sphere (G : C) (n : ℤ) : CochainComplex C ℤ :=
  (CochainComplex.singleFunctor C n).obj G

/-- The two-term acyclic disk with `G` in degrees `n` and `n + 1`,
implemented as the mapping cone of the identity on the `n + 1` sphere. -/
noncomputable abbrev disk (G : C) (n : ℤ) : CochainComplex C ℤ :=
  CochainComplex.mappingCone (𝟙 (sphere G (n + 1)))

/-- The canonical cofibration `S^{n+1}(G) ⟶ D^n(G)`. -/
noncomputable abbrev cell (G : C) (n : ℤ) : sphere G (n + 1) ⟶ disk G n :=
  CochainComplex.mappingCone.inr (𝟙 (sphere G (n + 1)))

/-- Hovey's generating cofibrations for the projective model structure on
unbounded complexes. See *Model Categories*, Definition 2.3.3. -/
def generatingCofibrations (G : C) : MorphismProperty (CochainComplex C ℤ) :=
  .ofHoms (cell G)

/-- The generating cofibrations form a small set. -/
lemma isSmall_generatingCofibrations [Small.{w} ℤ] (G : C) :
    (generatingCofibrations (C := C) G).IsSmall.{w} :=
  MorphismProperty.isSmall_ofHoms (cell G)

/-- Once the sphere objects are known to be presentable at `κ`, Hovey's
generating cofibrations permit the small object argument. -/
lemma hasSmallObjectArgument_generatingCofibrations [Small.{w} ℤ]
    (G : C) (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocallySmall.{w} (CochainComplex C ℤ)]
    [HasPushouts (CochainComplex C ℤ)] [HasCoproducts.{w} (CochainComplex C ℤ)]
    [HasIterationOfShape κ.ord.ToType (CochainComplex C ℤ)]
    (h : ∀ n, IsCardinalPresentable (sphere G (n + 1)) κ) :
    (generatingCofibrations G).HasSmallObjectArgument.{w} := by
  letI := isSmall_generatingCofibrations (C := C) G
  exact hasSmallObjectArgumentOfPresentable (generatingCofibrations G) κ (by
    rintro A B i ⟨n⟩
    exact h n)

/-- Explicit endpoint of the model-structure route. The RLP identity is
Hovey's characterization of trivial fibrations (*Model Categories*, Prop.
2.3.5). The presentability estimate is the other required module-specific
input (for module spheres it follows from the proof of Lemma 2.3.2). -/
noncomputable def kProjectiveReplacementDataOfGeneratingCofibrations
    [HasDerivedCategory C] (G : C) (κ : Cardinal.{w}) [Small.{w} ℤ]
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocallySmall.{w} (CochainComplex C ℤ)]
    [HasPushouts (CochainComplex C ℤ)] [HasCoproducts.{w} (CochainComplex C ℤ)]
    [HasIterationOfShape κ.ord.ToType (CochainComplex C ℤ)]
    (hpres : ∀ n, IsCardinalPresentable (sphere G (n + 1)) κ)
    (hI : (generatingCofibrations G).rlp = degreewiseEpiQuasiIso) :
    KProjectiveReplacementData C := by
  letI := hasSmallObjectArgument_generatingCofibrations G κ hpres
  exact kProjectiveReplacementDataOfSmallObject (generatingCofibrations G) hI

/-- Derived coproducts from Hovey's generating-cofibration inputs. This is
merely the existing `DerivedCoproducts` theorem applied to the replacement
data above. -/
theorem hasCoproductsDerivedOfGeneratingCofibrations
    [HasDerivedCategory C] [HasCoproducts.{w₁} C] (G : C) (κ : Cardinal.{w})
    [Small.{w} ℤ] [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocallySmall.{w} (CochainComplex C ℤ)]
    [HasPushouts (CochainComplex C ℤ)] [HasCoproducts.{w} (CochainComplex C ℤ)]
    [HasIterationOfShape κ.ord.ToType (CochainComplex C ℤ)]
    (hpres : ∀ n, IsCardinalPresentable (sphere G (n + 1)) κ)
    (hI : (generatingCofibrations G).rlp = degreewiseEpiQuasiIso) :
    HasCoproducts.{w₁} (DerivedCategory C) :=
  DerivedCoproducts.hasCoproductsOfKProjectiveReplacementData
    (kProjectiveReplacementDataOfGeneratingCofibrations G κ hpres hI)

#print axioms RelativeFM.ProjectiveModel.isSmall_generatingCofibrations
#print axioms RelativeFM.ProjectiveModel.hasSmallObjectArgument_generatingCofibrations
#print axioms RelativeFM.ProjectiveModel.kProjectiveReplacementDataOfGeneratingCofibrations
#print axioms RelativeFM.ProjectiveModel.hasCoproductsDerivedOfGeneratingCofibrations

end

end RelativeFM.ProjectiveModel
