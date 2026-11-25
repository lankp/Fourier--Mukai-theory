/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.AisleGenFiltration

/-! # Unbounded-below projective complexes in a coproduct/extension closure -/

@[expose] public section

namespace RelativeFM.AisleGeneration.Unbounded

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeFM.AisleGeneration.Brutal
open RelativeFM.AisleGeneration.Bounded
open RelativeFM.AisleGeneration.Filtration
open RelativeFM.Spaltenstein

universe w v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [HasCoproductsOfShape ℕ C] [HasColimitsOfShape ℕ C]

/-- A bounded-above complex of projectives is in `Coprod S` as soon as all
its degree-wise singles in nonpositive degrees are, and `Coprod S` is stable
under positive shift. -/
theorem coprod_Q_obj_projective_of_isStrictlyLE_zero
    (S : ObjectProperty (DerivedCategory C)) (K : CochainComplex C ℤ)
    [K.IsStrictlyLE 0] [∀ i, Projective (K.X i)]
    (hterm : ∀ i : ℤ, i ≤ 0 → Coprod S (DerivedCategory.Q.obj
      ((HomologicalComplex.single C (ComplexShape.up ℤ) i).obj (K.X i))))
    (hshift : ∀ {X : DerivedCategory C}, Coprod S X → Coprod S (X⟦(1 : ℤ)⟧)) :
    Coprod S (DerivedCategory.Q.obj K) := by
  let F := brutalFiltration K
  letI (n : ℕ) : ((filtrationDiagram F).obj n).IsKProjective := by
    letI : (brutalGE K (-(n : ℤ))).IsStrictlyLE (n : ℤ) :=
      (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi =>
        (brutalGE K (-(n : ℤ))).isZero_of_isStrictlyLE 0 i (by omega))
    letI (i : ℤ) : Projective ((brutalGE K (-(n : ℤ))).X i) := by
      by_cases hi : -(n : ℤ) ≤ i
      · exact Projective.of_iso (brutalGEXIso K (-(n : ℤ)) i hi).symm inferInstance
      · exact (isZero_brutalGE_X K (by omega)).projective
    change (brutalGE K (-(n : ℤ))).IsKProjective
    exact CochainComplex.isKProjective_of_projective _ (n : ℤ)
  have hstage (n : ℕ) : Coprod S (DerivedCategory.Q.obj ((filtrationDiagram F).obj n)) := by
    letI : (brutalGE K (-(n : ℤ))).IsStrictlyLE (-(n : ℤ) + (n : ℤ)) :=
      (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi =>
        (brutalGE K (-(n : ℤ))).isZero_of_isStrictlyLE 0 i (by omega))
    apply Bounded.coprod_Q_obj_of_support S n (brutalGE K (-(n : ℤ))) (-(n : ℤ))
    intro i hai hib
    let e := (HomologicalComplex.single C (ComplexShape.up ℤ) i).mapIso
      (brutalGEXIso K (-(n : ℤ)) i hai)
    exact (Coprod S).prop_of_iso (DerivedCategory.Q.mapIso e).symm
      (hterm i (by omega))
  have hcolim : Coprod S (DerivedCategory.Q.obj (colimit (filtrationDiagram F))) := by
    apply Filtration.coprod_Q_pt_of_telescope S (filtrationDiagram F)
      (colimit.cocone _) (colimit.isColimit _)
      (fun n i => brutalFiltrationStepRetraction K n i) _ hstage hshift
    intro n i
    simpa only [SpecialDirectLimits.step, filtrationDiagram,
      Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_obj] using
        brutalFiltration_step_retraction K n i
  letI : QuasiIso (filtrationColimitToA F) := quasiIso_colimitToA_brutal K
  letI : IsIso (DerivedCategory.Q.map (filtrationColimitToA F)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact (Coprod S).prop_of_iso
    (asIso (DerivedCategory.Q.map (filtrationColimitToA F))) hcolim

end

end RelativeFM.AisleGeneration.Unbounded

#print axioms RelativeFM.AisleGeneration.Unbounded.coprod_Q_obj_projective_of_isStrictlyLE_zero
