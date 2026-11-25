import FourierMukai.Scheme.SpaltensteinIteration
import FourierMukai.Scheme.SpecialDirectLimits
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Colimits in Spaltenstein's construction

Pointwise quasi-isomorphisms are preserved by exact countable colimits. Together
with the split-telescope theorem, this gives the colimit part of Theorem C.
-/

@[expose] public section

namespace RelativeFM.Spaltenstein

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CochainComplex

universe w w' v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type*} {c : ComplexShape ι}

/-- Short complexes read only three degrees, so they preserve degreewise
colimits of complexes. -/
noncomputable instance preservesColimitsOfShape_shortComplexFunctor
    {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C] (i : ι) :
    PreservesColimitsOfShape J (HomologicalComplex.shortComplexFunctor C c i) := by
  refine ⟨fun {_} => ⟨fun {F} hc => ⟨ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_⟩⟩⟩
  · exact isColimitOfPreserves (HomologicalComplex.eval C c (c.prev i)) hc
  · exact isColimitOfPreserves (HomologicalComplex.eval C c i) hc
  · exact isColimitOfPreserves (HomologicalComplex.eval C c (c.next i)) hc

/-- A pointwise quasi-isomorphism of short complexes stays a quasi-isomorphism
after an exact countable colimit. -/
lemma quasiIso_colim_mapShortComplex
    {D : Type u} [Category.{v} D] [Abelian D]
    [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
    {S₁ S₂ : ℕ ⥤ ShortComplex D} (φ : S₁ ⟶ S₂)
    [∀ n, ShortComplex.QuasiIso (φ.app n)] :
    ShortComplex.QuasiIso
      ((CategoryTheory.Functor.mapShortComplex (colim : (ℕ ⥤ D) ⥤ D)).map
        ((ShortComplex.FunctorEquivalence.inverse ℕ D).map φ)) := by
  let E := ShortComplex.FunctorEquivalence.inverse ℕ D
  letI : ShortComplex.QuasiIso (E.map φ) :=
    (ShortComplex.quasiIso_iff_evaluation _).2 (fun n => by
      change ShortComplex.QuasiIso (φ.app n)
      infer_instance)
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology
    (colim : (ℕ ⥤ D) ⥤ D) (E.map φ)

/-- The general AB5 input needed to transfer quasi-isomorphisms to a
sequential colimit. This is NOT a replacement assumption: it is exactly exactness
of filtered colimits, used only through homology preservation. -/
structure SequentialColimitQuasiIsoInput (C : Type u) [Category.{v} C]
    [Abelian C] where
  quasiIso_colim_map [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    {F G : ℕ ⥤ CochainComplex C ℤ} (α : F ⟶ G) [∀ n, QuasiIso (α.app n)] :
    QuasiIso (colim.map α)

/-- The chosen colimit cocone of a canonical-truncation filtration in the
category of complexes. -/
noncomputable abbrev filtrationColimitCocone
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A)
    [HasColimitsOfShape ℕ C] : Cocone (filtrationDiagram F) :=
  colimit.cocone (filtrationDiagram F)

/-- A cocone on the approximants with point `A` provided by the filtration. -/
noncomputable def filtrationToACocone {A : CochainComplex C ℤ}
    (F : BoundedAboveFiltration A) : Cocone (filtrationDiagram F) := by
  refine Cocone.mk A ?_
  apply NatTrans.ofSequence F.toA
  intro n
  simp only [filtrationDiagram, Functor.ofSequence_obj,
    Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
  exact (F.step_toA n).trans (Category.comp_id _).symm


/-- The comparison from the filtration colimit to `A`. -/
noncomputable def filtrationColimitToA {A : CochainComplex C ℤ}
    (F : BoundedAboveFiltration A) [HasColimitsOfShape ℕ C] :
    colimit (filtrationDiagram F) ⟶ A :=
  (colimit.isColimit (filtrationDiagram F)).desc (filtrationToACocone F)

/-- The induced comparison of resolutions before taking the colimit. -/
noncomputable def filteredColimitMap [EnoughProjectives C] {A : CochainComplex C ℤ}
    (F : BoundedAboveFiltration A) [HasColimitsOfShape ℕ C] :
    colimit (filteredResolutionDiagram F) ⟶ colimit (filtrationDiagram F) :=
  colim.map (filteredResolutionNatTrans F)

lemma quasiIso_filteredColimitMap [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A)
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    (H : SequentialColimitQuasiIsoInput C) : QuasiIso (filteredColimitMap F) := by
  letI (n : ℕ) : QuasiIso ((filteredResolutionNatTrans F).app n) := by
    exact (filteredResolution F n).quasiIso
  apply H.quasiIso_colim_map

lemma isKProjective_filteredColimit [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A)
    [HasColimitsOfShape ℕ C] [HasCoproductsOfShape ℕ C] :
    (colimit (filteredResolutionDiagram F)).IsKProjective := by
  letI (n : ℕ) : ((filteredResolutionDiagram F).obj n).IsKProjective := by
    exact (filteredResolution F n).isKProjective
  apply SpecialDirectLimits.isKProjective_colimit
  intro n i
  exact
    { retraction := filteredStepRetraction F n i
      id := by
        simpa only [SpecialDirectLimits.step, filteredResolutionDiagram,
          Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_obj] using
            filteredStep_retraction F n i }

/-- Once the comparison from the filtration colimit to `A` is a
quasi-isomorphism, Spaltenstein's construction gives a K-projective resolution
of `A`. -/
noncomputable def resolutionOfFiltration [EnoughProjectives C] [HasDerivedCategory C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A)
    [HasColimitsOfShape ℕ C] [HasCoproductsOfShape ℕ C]
    [HasExactColimitsOfShape ℕ C] (H : SequentialColimitQuasiIsoInput C)
    (hA : QuasiIso (filtrationColimitToA F)) :
    DerivedCoproducts.KProjectiveResolution (DerivedCategory.Q.obj A) := by
  letI : QuasiIso (filteredColimitMap F) := quasiIso_filteredColimitMap F H
  letI : (colimit (filteredResolutionDiagram F)).IsKProjective :=
    isKProjective_filteredColimit F
  letI : QuasiIso (filtrationColimitToA F) := hA
  exact
    { complex := colimit (filteredResolutionDiagram F)
      isKProjective := inferInstance
      iso := asIso (DerivedCategory.Q.map
        (filteredColimitMap F ≫ filtrationColimitToA F)) }

#print axioms RelativeFM.Spaltenstein.quasiIso_colim_mapShortComplex
#print axioms RelativeFM.Spaltenstein.isKProjective_filteredColimit
#print axioms RelativeFM.Spaltenstein.resolutionOfFiltration

end
end RelativeFM.Spaltenstein
