/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.AisleGenBounded
import FourierMukai.Scheme.SpaltensteinSequentialComparisons
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-! # Brutal filtration and sequential-colimit closure -/

@[expose] public section

namespace RelativeFM.AisleGeneration.Filtration

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeFM.AisleGeneration.Brutal
open RelativeFM.Spaltenstein

universe w v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The nested brutal truncations `brutalGE K (-n)` of a complex bounded above
by zero. -/
noncomputable def brutalFiltration (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    BoundedAboveFiltration K where
  B n := brutalGE K (-(n : ℤ))
  isStrictlyLE n :=
    (CochainComplex.isStrictlyLE_iff _ (n : ℤ)).2 (fun i hi =>
      (brutalGE K (-(n : ℤ))).isZero_of_isStrictlyLE 0 i (by omega))
  step n := brutalGEιOfLE K (by
    push_cast
    omega : -(((n + 1 : ℕ) : ℤ)) ≤ -(n : ℤ))
  toA n := brutalGEι K (-(n : ℤ))
  step_toA n := brutalGEιOfLE_comp_brutalGEι K _

/-- A degreewise retraction of the successor maps in `brutalFiltration`. -/
noncomputable def brutalFiltrationStepRetraction (K : CochainComplex C ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : ℤ) :
    (brutalGE K (-(((n + 1 : ℕ) : ℤ)))).X i ⟶ (brutalGE K (-(n : ℤ))).X i :=
  brutalGEιOfLERetractionHom K (by push_cast; omega : -(((n + 1 : ℕ) : ℤ)) ≤ -(n : ℤ)) i

lemma brutalFiltration_step_retraction (K : CochainComplex C ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : ℤ) :
    ((brutalFiltration K).step n).f i ≫ brutalFiltrationStepRetraction K n i = 𝟙 _ := by
  exact brutalGEιOfLE_retraction_f K _ i

section Derived

variable [HasDerivedCategory.{w} C] [HasCoproductsOfShape ℕ C] [HasColimitsOfShape ℕ C]

/-- The explicit coproduct complex of a sequence of K-projective complexes
maps to a derived coproduct. -/
theorem coprod_Q_complexCoproduct (S : ObjectProperty (DerivedCategory C))
    (P : ℕ ⥤ CochainComplex C ℤ) [∀ n, (P.obj n).IsKProjective]
    (hP : ∀ n, Coprod S (DerivedCategory.Q.obj (P.obj n))) :
    Coprod S (DerivedCategory.Q.obj (SpecialDirectLimits.complexCoproduct P)) := by
  let pres : ColimitPresentation (Discrete ℕ)
      (DerivedCategory.Q.obj
        (DerivedCoproducts.coproductComplexCocone (fun n => P.obj n)).pt) :=
    { diag := Discrete.functor (fun n => DerivedCategory.Q.obj (P.obj n))
      ι := (DerivedCoproducts.derivedCoproductCofan (fun n => P.obj n)).ι
      isColimit := DerivedCoproducts.derivedCoproductCofanIsColimit (fun n => P.obj n) }
  have h : Coprod S (DerivedCategory.Q.obj
      (DerivedCoproducts.coproductComplexCocone (fun n => P.obj n)).pt) :=
    Coprod.of_colimitPresentation (P := S)
      (pres.reindex (Discrete.equivalence Equiv.ulift).functor)
      (fun j => hP j.as.down)
  exact (Coprod S).prop_of_iso
    (DerivedCategory.Q.mapIso (SpecialDirectLimits.complexCoproductIso P)) h

/-- A sequential colimit with degreewise split successor maps lies in `Coprod S`
if its stages do, provided `Coprod S` is stable under positive shift. -/
theorem coprod_Q_pt_of_telescope (S : ObjectProperty (DerivedCategory C))
    (P : ℕ ⥤ CochainComplex C ℤ) (c : Cocone P) (hc : IsColimit c)
    [∀ n, (P.obj n).IsKProjective]
    (q : ∀ n i, (P.obj (n + 1)).X i ⟶ (P.obj n).X i)
    (hq : ∀ n i, (SpecialDirectLimits.step P n).f i ≫ q n i = 𝟙 _)
    (hP : ∀ n, Coprod S (DerivedCategory.Q.obj (P.obj n)))
    (hshift : ∀ {X : DerivedCategory C}, Coprod S X → Coprod S (X⟦(1 : ℤ)⟧)) :
    Coprod S (DerivedCategory.Q.obj c.pt) := by
  let σ := fun i => SpecialDirectLimits.complexTelescopeSplitting P c hc q hq i
  have hS : (SpecialDirectLimits.complexTelescopeShortComplex P c).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun i => (σ i).shortExact)
  let T := DerivedCategory.triangleOfSES hS
  have hT : T ∈ distTriang (DerivedCategory C) := DerivedCategory.triangleOfSES_distinguished hS
  have hcop : Coprod S (DerivedCategory.Q.obj (SpecialDirectLimits.complexCoproduct P)) :=
    coprod_Q_complexCoproduct S P hP
  exact Coprod.of_extension T.rotate ((rotate_distinguished_triangle T).1 hT)
    hcop (hshift hcop)

end Derived

section EventuallyConstant

variable [HasColimitsOfShape ℕ C]

/-- The filtration-colimit comparison is an isomorphism in a degree where one
leg is an isomorphism and the evaluated diagram is eventually constant. -/
lemma isIso_filtrationColimitToA_f_of_eventually {A : CochainComplex C ℤ}
    (F : BoundedAboveFiltration A) (N : ℕ) (p : ℤ)
    (h : (filtrationDiagram F ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) p).IsEventuallyConstantFrom N)
    [IsIso ((F.toA N).f p)] :
    IsIso ((filtrationColimitToA F).f p) := by
  let E := HomologicalComplex.eval C (ComplexShape.up ℤ) p
  let c := filtrationToACocone F
  letI : IsIso ((E.mapCocone c).ι.app N) := by
    simp only [E, c, Functor.mapCocone_ι_app, HomologicalComplex.eval_map,
      filtrationToACocone, NatTrans.ofSequence_app]
    infer_instance
  have hc : IsColimit (E.mapCocone c) := h.isColimitOfIsIso (E.mapCocone c)
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

/-- The brutal filtration is degreewise eventually constant from `p.natAbs + 1`. -/
lemma isEventuallyConstantFrom_brutalFiltration_eval (K : CochainComplex C ℤ)
    [K.IsStrictlyLE 0] (p : ℤ) :
    (filtrationDiagram (brutalFiltration K) ⋙
      HomologicalComplex.eval C (ComplexShape.up ℤ) p).IsEventuallyConstantFrom (p.natAbs + 1) := by
  intro m f
  have hm : p.natAbs + 1 ≤ m := leOfHom f
  have hN : -(((p.natAbs + 1 : ℕ) : ℤ)) ≤ p := by
    have := Int.le_natAbs (a := p)
    omega
  have hmz : ((p.natAbs + 1 : ℕ) : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hp : -((m : ℤ)) ≤ p := by omega
  letI : IsIso (((brutalFiltration K).toA (p.natAbs + 1)).f p) :=
    isIso_brutalGEι_f K _ _ hN
  letI : IsIso (((brutalFiltration K).toA m).f p) :=
    isIso_brutalGEι_f K _ _ hp
  change IsIso (((filtrationDiagram (brutalFiltration K)).map f).f p)
  refine IsIso.of_isIso_fac_right
    (g := ((filtrationDiagram (brutalFiltration K)).map f).f p)
    (f := ((brutalFiltration K).toA m).f p)
    (h := ((brutalFiltration K).toA (p.natAbs + 1)).f p) ?_
  have h := (filtrationToACocone (brutalFiltration K)).w f
  have h' : (filtrationDiagram (brutalFiltration K)).map f ≫
      (brutalFiltration K).toA m = (brutalFiltration K).toA (p.natAbs + 1) := by
    simpa only [filtrationToACocone, NatTrans.ofSequence_app,
      Functor.const_obj_map, Category.comp_id] using h
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.eval_map,
    Functor.comp_map] using congrArg (fun φ => φ.f p) h'

lemma quasiIso_colimitToA_brutal (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    QuasiIso (filtrationColimitToA (brutalFiltration K)) := by
  letI (p : ℤ) : IsIso ((filtrationColimitToA (brutalFiltration K)).f p) := by
    letI : IsIso (((brutalFiltration K).toA (p.natAbs + 1)).f p) :=
      isIso_brutalGEι_f K _ _ (by
        have := Int.le_natAbs (a := p)
        omega)
    exact isIso_filtrationColimitToA_f_of_eventually (brutalFiltration K) (p.natAbs + 1) p
      (isEventuallyConstantFrom_brutalFiltration_eval K p)
  letI : IsIso (filtrationColimitToA (brutalFiltration K)) :=
    HomologicalComplex.Hom.isIso_of_components _
  infer_instance

end EventuallyConstant

end

end RelativeFM.AisleGeneration.Filtration

#print axioms RelativeFM.AisleGeneration.Filtration.brutalFiltration
#print axioms RelativeFM.AisleGeneration.Filtration.coprod_Q_complexCoproduct
#print axioms RelativeFM.AisleGeneration.Filtration.coprod_Q_pt_of_telescope
#print axioms RelativeFM.AisleGeneration.Filtration.quasiIso_colimitToA_brutal
