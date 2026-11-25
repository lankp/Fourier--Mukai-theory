import FourierMukai.Scheme.DerivedCoproducts
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

@[expose] public section

namespace RelativeFM.NeemanFiniteSupportM4

open CategoryTheory CategoryTheory.Limits

universe w v u ι

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A family of complexes determines a short complex in the diagram category,
with the componentwise differentials at a chosen cohomological degree. -/
def diagramShortComplex {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {κ : Type w} {c : ComplexShape ι}
    (K : Discrete κ ⥤ HomologicalComplex C c) (i : ι) : ShortComplex (Discrete κ ⥤ C) where
  X₁ := K ⋙ HomologicalComplex.eval C c (c.prev i)
  X₂ := K ⋙ HomologicalComplex.eval C c i
  X₃ := K ⋙ HomologicalComplex.eval C c (c.next i)
  f :=
    { app := fun j => (K.obj j).d (c.prev i) i
      naturality := fun _ _ φ => (K.map φ).comm _ _ }
  g :=
    { app := fun j => (K.obj j).d i (c.next i)
      naturality := fun _ _ φ => (K.map φ).comm _ _ }
  zero := by
    ext j
    change (K.obj j).d _ _ ≫ (K.obj j).d _ _ = 0
    exact (K.obj j).d_comp_d _ _ _

@[simp] lemma diagramShortComplex_map_eval {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {κ : Type w} {c : ComplexShape ι}
    (K : Discrete κ ⥤ HomologicalComplex C c) (i : ι) (j : Discrete κ) :
    (diagramShortComplex K i).map ((evaluation (Discrete κ) C).obj j) = (K.obj j).sc i := rfl

/-- Homology of the componentwise short complex is componentwise homology. -/
noncomputable def diagramShortComplexHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {κ : Type w} {c : ComplexShape ι}
    (K : Discrete κ ⥤ HomologicalComplex C c) (i : ι) :
    (diagramShortComplex K i).homology ≅
      K ⋙ HomologicalComplex.homologyFunctor C c i :=
  NatIso.ofComponents (fun j =>
    ((ShortComplex.homologyFunctorIso ((evaluation (Discrete κ) C).obj j)).app
      (diagramShortComplex K i)).symm) (by
      intros j k φ
      obtain rfl : j = k := Discrete.ext (Discrete.eq_of_hom φ)
      obtain rfl : φ = 𝟙 j := Subsingleton.elim _ _
      simp)

/-- Evaluation identifies the degreewise colimit short complex with the short
complex of the colimit in the category of complexes. -/
noncomputable def colimitDiagramShortComplexIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {κ : Type w} {c : ComplexShape ι} (K : Discrete κ ⥤ HomologicalComplex C c)
    (i : ι) [HasColimitsOfShape (Discrete κ) C] :
    (diagramShortComplex K i).map colim ≅ (colimit K).sc i := by
  let e (d : ι) : colim.obj (K ⋙ HomologicalComplex.eval C c d) ≅
      (colimit K).X d :=
    colimit.isoColimitCocone
      ⟨_, isColimitOfPreserves (HomologicalComplex.eval C c d) (colimit.isColimit K)⟩
  exact ShortComplex.isoMk (e (c.prev i)) (e i) (e (c.next i))
    (by dsimp [e]; cat_disch) (by dsimp [e]; cat_disch)

/-- Exact colimits in an abelian category commute with homology of complexes.
The statement uses the degreewise colimit of complexes and the colimit of the
component homology diagram. -/
noncomputable def colimitHomologyIso {C : Type u} [Category.{v} C] [Abelian C]
    {κ : Type w} {c : ComplexShape ι} (K : Discrete κ ⥤ HomologicalComplex C c)
    (i : ι) [HasColimitsOfShape (Discrete κ) C]
    [HasExactColimitsOfShape (Discrete κ) C] :
    ((colimit K).sc i).homology ≅
      colimit (K ⋙ HomologicalComplex.homologyFunctor C c i) :=
  (ShortComplex.homologyFunctor C).mapIso (colimitDiagramShortComplexIso K i).symm ≪≫
    ShortComplex.mapHomologyIso (diagramShortComplex K i) colim ≪≫
      colim.mapIso (diagramShortComplexHomologyIso K i)

open RelativeFM
open CochainComplex

/-- Cohomology of the explicit derived coproduct of K-projective complexes is
the coproduct of the cohomologies. -/
noncomputable def derivedCoproductHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C] {_wD : Type*} [HasDerivedCategory.{_wD} C]
    {κ : Type w} (K : κ → CochainComplex C ℤ) [∀ i, (K i).IsKProjective]
    (n : ℤ) [HasCoproductsOfShape κ C] [HasExactColimitsOfShape (Discrete κ) C] :
    (DerivedCategory.homologyFunctor C n).obj
        (RelativeFM.DerivedCoproducts.derivedCoproductCofan K).pt ≅
      colimit (Discrete.functor K ⋙ DerivedCategory.Q ⋙
        DerivedCategory.homologyFunctor C n) := by
  let e : (RelativeFM.DerivedCoproducts.coproductComplexCocone K).pt ≅
      colimit (Discrete.functor K) :=
    (colimit.isoColimitCocone
      ⟨_, RelativeFM.DerivedCoproducts.coproductComplexCoconeIsColimit K⟩).symm
  exact (DerivedCategory.homologyFunctor C n).mapIso (DerivedCategory.Q.mapIso e) ≪≫
    (DerivedCategory.homologyFunctorFactors C n).app (colimit (Discrete.functor K)) ≪≫
    colimitHomologyIso (Discrete.functor K) n ≪≫
      colim.mapIso (Functor.isoWhiskerLeft (Discrete.functor K)
        (DerivedCategory.homologyFunctorFactors C n).symm)

end
end RelativeFM.NeemanFiniteSupportM4

#print axioms RelativeFM.NeemanFiniteSupportM4.derivedCoproductHomologyIso
#print axioms RelativeFM.NeemanFiniteSupportM4.colimitDiagramShortComplexIso
#print axioms RelativeFM.NeemanFiniteSupportM4.colimitHomologyIso
#print axioms RelativeFM.NeemanFiniteSupportM4.diagramShortComplexHomologyIso
