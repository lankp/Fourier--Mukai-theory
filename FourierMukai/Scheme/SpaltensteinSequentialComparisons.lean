import FourierMukai.Scheme.SpaltensteinReplacement
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# The two sequential-colimit comparisons in Spaltenstein's Theorem C

The exact-colimit comparison is transported from short complexes.  For the
canonical-truncation filtration, each evaluation diagram is eventually constant;
this makes the comparison to the original complex degreewise an isomorphism, so
no exactness assumption is needed for this second comparison.
-/

@[expose] public section
namespace RelativeFM.Spaltenstein

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CochainComplex

universe v u
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Exact sequential colimits preserve quasi-isomorphisms of complexes. -/
lemma quasiIso_colim_map_of_exact [HasColimitsOfShape ℕ C]
    [HasExactColimitsOfShape ℕ C]
    {F G : ℕ ⥤ CochainComplex C ℤ} (α : F ⟶ G)
    [∀ n, QuasiIso (α.app n)] : QuasiIso (colim.map α) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff]
  letI (n : ℕ) : ShortComplex.QuasiIso ((whiskerRight α
      (HomologicalComplex.shortComplexFunctor C _ i)).app n) := by
    change ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor C _ i).map (α.app n))
    rw [← quasiIsoAt_iff]
    infer_instance
  have hC := quasiIso_colim_mapShortComplex (whiskerRight α
    (HomologicalComplex.shortComplexFunctor C _ i))
  let e (H : ℕ ⥤ ShortComplex C) :
      ((ShortComplex.FunctorEquivalence.inverse ℕ C).obj H).map
        (colim : (ℕ ⥤ C) ⥤ C) ≅ colimit H :=
    ShortComplex.isoMk
      (preservesColimitIso ShortComplex.π₁ H).symm
      (preservesColimitIso ShortComplex.π₂ H).symm
      (preservesColimitIso ShortComplex.π₃ H).symm
      (by apply colimit.hom_ext; intro n
          simpa using (colimit.ι H n).comm₁₂)
      (by apply colimit.hom_ext; intro n
          simpa using (colimit.ι H n).comm₂₃)
  letI : ShortComplex.QuasiIso
      ((CategoryTheory.Functor.mapShortComplex
        (colim : (ℕ ⥤ C) ⥤ C)).map
        ((ShortComplex.FunctorEquivalence.inverse ℕ C).map
          (whiskerRight α (HomologicalComplex.shortComplexFunctor C _ i)))) := hC
  have hB : ShortComplex.QuasiIso (colim.map (whiskerRight α
      (HomologicalComplex.shortComplexFunctor C _ i))) := by
    apply ShortComplex.quasiIso_of_arrow_mk_iso
      ((CategoryTheory.Functor.mapShortComplex
        (colim : (ℕ ⥤ C) ⥤ C)).map
        ((ShortComplex.FunctorEquivalence.inverse ℕ C).map
          (whiskerRight α (HomologicalComplex.shortComplexFunctor C _ i))))
      (colim.map (whiskerRight α
        (HomologicalComplex.shortComplexFunctor C _ i)))
    exact Arrow.isoMk (e _) (e _) (by
      ext <;> apply colimit.hom_ext <;> intro n
      · simp [e]
        exact congrArg (fun k => k.τ₁) (colimit.ι_map
          (whiskerRight α (HomologicalComplex.shortComplexFunctor C _ i)) n)
      · simp [e]
        exact congrArg (fun k => k.τ₂) (colimit.ι_map
          (whiskerRight α (HomologicalComplex.shortComplexFunctor C _ i)) n)
      · simp [e]
        exact congrArg (fun k => k.τ₃) (colimit.ι_map
          (whiskerRight α (HomologicalComplex.shortComplexFunctor C _ i)) n))
  letI : ShortComplex.QuasiIso (colim.map (whiskerRight α
      (HomologicalComplex.shortComplexFunctor C _ i))) := hB
  apply ShortComplex.quasiIso_of_arrow_mk_iso
    (colim.map (whiskerRight α
      (HomologicalComplex.shortComplexFunctor C _ i)))
    ((HomologicalComplex.shortComplexFunctor C _ i).map (colim.map α))
  exact (Arrow.isoOfNatIso (preservesColimitNatIso
    (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i))
    (Arrow.mk α)).symm


lemma isIso_ιTruncLE_f_of_lt (A : CochainComplex C ℤ) (n p : ℤ) (hp : p < n) :
    IsIso ((A.ιTruncLE n).f p) := by
  change IsIso (((A.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f p).unop)
  have h : IsIso ((A.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f p) := by
    dsimp [HomologicalComplex.πTruncGE]
    rw [(ComplexShape.embeddingUpIntLE n).op.isIso_liftExtend_f_iff _ _
      (i := (n - p).natAbs) (by
        dsimp
        rw [Int.natAbs_of_nonneg (by lia)]
        ring)]
    apply A.op.isIso_restrictionToTruncGE'
    rw [ComplexShape.Embedding.op_boundaryGE_iff,
      ComplexShape.boundaryLE_embeddingUpIntLE_iff, Int.natAbs_eq_zero]
    push Not
    lia
  infer_instance

/-- The canonical truncation filtration is degreewise eventually constant. -/
lemma isEventuallyConstantFrom_canonicalFiltration_eval
    (A : CochainComplex C ℤ) (D : CanonicalTruncationData A) (p : ℤ) :
    (filtrationDiagram (canonicalFiltration D) ⋙
      HomologicalComplex.eval C _ p).IsEventuallyConstantFrom (p.natAbs + 1) := by
  intro m f
  have hm : p.natAbs + 1 ≤ m := leOfHom f
  have hp₀ : p < ((p.natAbs + 1 : ℕ) : ℤ) := by
    have := Int.le_natAbs (a := p)
    omega
  have hmz : ((p.natAbs + 1 : ℕ) : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hm
  have hpm : p < (m : ℤ) := by omega
  letI : IsIso (((canonicalFiltration D).toA (p.natAbs + 1)).f p) := by
    apply isIso_ιTruncLE_f_of_lt
    exact hp₀
  letI : IsIso (((canonicalFiltration D).toA m).f p) := by
    apply isIso_ιTruncLE_f_of_lt
    simpa using hpm
  change IsIso (((filtrationDiagram (canonicalFiltration D)).map f).f p)
  refine IsIso.of_isIso_fac_right
    (g := ((filtrationDiagram (canonicalFiltration D)).map f).f p)
    (f := ((canonicalFiltration D).toA m).f p)
    (h := ((canonicalFiltration D).toA (p.natAbs + 1)).f p) ?_
  have h := (filtrationToACocone (canonicalFiltration D)).w f
  have h' : (filtrationDiagram (canonicalFiltration D)).map f ≫
      (canonicalFiltration D).toA m = (canonicalFiltration D).toA (p.natAbs + 1) := by
    simpa only [filtrationToACocone, NatTrans.ofSequence_app,
      Functor.const_obj_map, Category.comp_id] using h
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.eval_map,
    Functor.comp_map] using congrArg (fun φ => φ.f p) h'


/-- The degree comparison from the colimit of the canonical truncation filtration
is an isomorphism, without any exactness assumption on sequential colimits. -/
lemma isIso_filtrationColimitToA_f [HasColimitsOfShape ℕ C]
    (A : CochainComplex C ℤ) (D : CanonicalTruncationData A) (p : ℤ) :
    IsIso ((filtrationColimitToA (canonicalFiltration D)).f p) := by
  let F := canonicalFiltration D
  let E := HomologicalComplex.eval C (ComplexShape.up ℤ) p
  let c := filtrationToACocone F
  have hp : p < ((p.natAbs + 1 : ℕ) : ℤ) := by
    have := Int.le_natAbs (a := p)
    omega
  letI : IsIso ((E.mapCocone c).ι.app (p.natAbs + 1)) := by
    simp only [E, c, Functor.mapCocone_ι_app, HomologicalComplex.eval_map,
      filtrationToACocone, NatTrans.ofSequence_app]
    exact isIso_ιTruncLE_f_of_lt A _ _ hp
  have hc : IsColimit (E.mapCocone c) :=
    (isEventuallyConstantFrom_canonicalFiltration_eval A D p).isColimitOfIsIso
      (E.mapCocone c)
  have hdesc : IsIso ((colimit.isColimit (filtrationDiagram F ⋙ E)).desc
      (E.mapCocone c)) :=
    (IsColimit.nonempty_isColimit_iff_isIso_desc
      (colimit.isColimit (filtrationDiagram F ⋙ E))).1 ⟨hc⟩
  have hcomp : IsIso ((preservesColimitIso E (filtrationDiagram F)).inv ≫
      E.map (filtrationColimitToA F)) := by
    rw [show filtrationColimitToA F = colimit.desc (filtrationDiagram F) c from rfl]
    rw [preservesColimitIso_inv_comp_desc]
    exact hdesc
  exact IsIso.of_isIso_comp_left
    (preservesColimitIso E (filtrationDiagram F)).inv
    (E.map (filtrationColimitToA F))

/-- The canonical truncation filtration of a complex has colimit quasi-isomorphic
to the complex. Exactness of sequential colimits is not needed for this field. -/
lemma quasiIso_colimitToA_canonical [HasColimitsOfShape ℕ C]
    (A : CochainComplex C ℤ) (D : CanonicalTruncationData A) :
    QuasiIso (filtrationColimitToA (canonicalFiltration D)) := by
  letI (p : ℤ) : IsIso ((filtrationColimitToA (canonicalFiltration D)).f p) :=
    isIso_filtrationColimitToA_f A D p
  letI : IsIso (filtrationColimitToA (canonicalFiltration D)) :=
    HomologicalComplex.Hom.isIso_of_components _
  infer_instance


/-- The exact-sequential-colimit field of `TheoremCInput`. -/
theorem sequentialColimitQuasiIsoInput : SequentialColimitQuasiIsoInput C where
  quasiIso_colim_map α := quasiIso_colim_map_of_exact α

/-- Once canonical-truncation successor maps are supplied, both colimit fields
of `TheoremCInput` are automatic. -/
noncomputable def theoremCInputOfCanonicalTruncation
    (canonicalTruncation : ∀ A : CochainComplex C ℤ, CanonicalTruncationData A) :
    TheoremCInput C where
  exactSequentialColimit := sequentialColimitQuasiIsoInput
  canonicalTruncation := canonicalTruncation
  quasiIso_colimitToA A := quasiIso_colimitToA_canonical A (canonicalTruncation A)

#print axioms RelativeFM.Spaltenstein.quasiIso_colim_map_of_exact
#print axioms RelativeFM.Spaltenstein.quasiIso_colimitToA_canonical
#print axioms RelativeFM.Spaltenstein.theoremCInputOfCanonicalTruncation

end
end RelativeFM.Spaltenstein
