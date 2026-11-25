import FourierMukai.Scheme.SpaltensteinReplacement

@[expose] public section

namespace RelativeFM.Spaltenstein

open CategoryTheory CategoryTheory.Limits CochainComplex
open ComplexShape

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- The non-boundary components of a canonical `truncLE` inclusion are
isomorphisms. -/
lemma isIso_ιTruncLE_f_of_not_boundary (K : HomologicalComplex C c')
    [∀ i', K.HasHomology i'] (e : c.Embedding c') [e.IsTruncLE]
    (i : ι) (hi : ¬ e.BoundaryLE i) :
    IsIso ((K.ιTruncLE e).f (e.f i)) := by
  have h : IsIso ((K.op.πTruncGE e.op).f (e.f i)) := by
    apply (e.op.isIso_liftExtend_f_iff (K.op.restrictionToTruncGE' e.op)
      (K.op.restrictionToTruncGE'_hasLift e.op) rfl).2
    exact K.op.isIso_restrictionToTruncGE' e.op i (by simpa)
  exact inferInstanceAs (IsIso (((K.op.πTruncGE e.op).f (e.f i)).unop))

variable {K L : HomologicalComplex C c'} (φ : K ⟶ L)

/-- A morphism of the small truncated complexes is an isomorphism if its
ordinary and boundary components are isomorphisms. -/
lemma isIso_truncGEM' (e : c.Embedding c') [e.IsTruncGE]
    [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']
    (h : ∀ i, ¬ e.BoundaryGE i → IsIso (φ.f (e.f i)))
    (hb : ∀ i, e.BoundaryGE i → IsIso (HomologicalComplex.opcyclesMap φ (e.f i))) :
    IsIso (HomologicalComplex.truncGE'Map φ e) := by
  suffices ∀ i, IsIso ((HomologicalComplex.truncGE'Map φ e).f i) by
    apply HomologicalComplex.Hom.isIso_of_components
  intro i
  by_cases hi : e.BoundaryGE i
  · letI := hb i hi
    rw [HomologicalComplex.truncGE'Map_f_eq_opcyclesMap φ e hi rfl]
    infer_instance
  · letI := h i hi
    rw [HomologicalComplex.truncGE'Map_f_eq φ e hi rfl]
    infer_instance

/-- The induced map between canonical lower truncations is an isomorphism
when its ordinary and cycle components are isomorphisms. -/
lemma isIso_truncLEMap (e : c.Embedding c') [e.IsTruncLE]
    [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']
    (h : ∀ i, ¬ e.BoundaryLE i → IsIso (φ.f (e.f i)))
    (hb : ∀ i, e.BoundaryLE i → IsIso (HomologicalComplex.cyclesMap φ (e.f i))) :
    IsIso (HomologicalComplex.truncLEMap φ e) := by
  let φop := (HomologicalComplex.opFunctor C c').map φ.op
  have hop : ∀ i, ¬ e.op.BoundaryGE i → IsIso (φop.f (e.op.f i)) := by
    intro i hi
    change IsIso ((φ.f (e.f i)).op)
    letI := h i (by simpa using hi)
    infer_instance
  have hbop : ∀ i, e.op.BoundaryGE i → IsIso (HomologicalComplex.opcyclesMap φop (e.op.f i)) := by
    intro i hi
    have hc := hb i (by simpa using hi)
    haveI : IsIso ((HomologicalComplex.cyclesMap φ (e.f i)).op) :=
      (isIso_op_iff _).2 hc
    letI : IsIso (K.opcyclesOpIso (e.f i)).hom :=
      (K.opcyclesOpIso (e.f i)).isIso_hom
    have hn : IsIso (HomologicalComplex.opcyclesMap φop (e.f i) ≫
        (K.opcyclesOpIso (e.f i)).hom) := by
      rw [show HomologicalComplex.opcyclesMap φop (e.f i) ≫ (K.opcyclesOpIso (e.f i)).hom =
        (L.opcyclesOpIso (e.f i)).hom ≫ (HomologicalComplex.cyclesMap φ (e.f i)).op from
          HomologicalComplex.opcyclesOpIso_hom_naturality φ (e.f i)]
      exact IsIso.comp_isIso' (L.opcyclesOpIso (e.f i)).isIso_hom
        ((isIso_op_iff _).2 hc)
    exact @IsIso.of_isIso_comp_right _ _ _ _ _
      (HomologicalComplex.opcyclesMap φop (e.f i))
      (K.opcyclesOpIso (e.f i)).hom
      (K.opcyclesOpIso (e.f i)).isIso_hom hn
  letI : IsIso (HomologicalComplex.truncGE'Map φop e.op) := HomologicalComplex.isIso_truncGEM' φop e.op hop hbop
  haveI : IsIso (HomologicalComplex.truncGEMap φop e.op) := by
    change IsIso ((e.op.extendFunctor Cᵒᵖ).map
      (HomologicalComplex.truncGE'Map φop e.op))
    apply Functor.map_isIso
  exact inferInstanceAs (IsIso ((HomologicalComplex.unopFunctor C c'.symm).map
    (HomologicalComplex.truncGEMap φop e.op).op))

end HomologicalComplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Retruncating the next canonical truncation at `n` gives an isomorphic
complex. -/
lemma isIso_truncLEMap_ιTruncLE_succ (A : CochainComplex C ℤ) (n : ℕ) :
    IsIso (CochainComplex.truncLEMap
      (A.ιTruncLE ((n + 1 : ℕ) : ℤ)) (n : ℤ)) := by
  apply HomologicalComplex.isIso_truncLEMap
  · intro i hi
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff] at hi
    have heq : (ComplexShape.embeddingUpIntLE ((n + 1 : ℕ) : ℤ)).f (i + 1) =
        (ComplexShape.embeddingUpIntLE (n : ℤ)).f i := by
      change (((n + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ)) = (n : ℤ) - (i : ℤ)
      push_cast
      omega
    rw [← heq]
    exact HomologicalComplex.isIso_ιTruncLE_f_of_not_boundary A
      (ComplexShape.embeddingUpIntLE ((n + 1 : ℕ) : ℤ)) (i + 1)
      (by simp [ComplexShape.boundaryLE_embeddingUpIntLE_iff])
  · intro i hi
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff] at hi
    subst i
    apply ShortComplex.isIso_cyclesMap_of_isIso_of_mono'
    · change IsIso ((A.ιTruncLE ((n + 1 : ℕ) : ℤ)).f (n : ℤ))
      have heq : (ComplexShape.embeddingUpIntLE ((n + 1 : ℕ) : ℤ)).f 1 = (n : ℤ) := by
        change (((n + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) = (n : ℤ)
        push_cast
        omega
      rw [← heq]
      exact HomologicalComplex.isIso_ιTruncLE_f_of_not_boundary A
        (ComplexShape.embeddingUpIntLE ((n + 1 : ℕ) : ℤ)) 1
        (by simp [ComplexShape.boundaryLE_embeddingUpIntLE_iff])
    · rw [HomologicalComplex.shortComplexFunctor_map_τ₃]
      have heq0 : (ComplexShape.embeddingUpIntLE (n : ℤ)).f 0 = (n : ℤ) := by
        simp
      rw [heq0]
      exact HomologicalComplex.instMonoFιTruncLE A
        (ComplexShape.embeddingUpIntLE ((n + 1 : ℕ) : ℤ))
        ((ComplexShape.up ℤ).next (n : ℤ))

/-- The successor inclusion between successive canonical truncations. -/
noncomputable def truncLESucc (A : CochainComplex C ℤ) (n : ℕ) :
    A.truncLE (n : ℤ) ⟶ A.truncLE ((n + 1 : ℕ) : ℤ) := by
  letI := isIso_truncLEMap_ιTruncLE_succ A n
  exact inv (CochainComplex.truncLEMap
    (A.ιTruncLE ((n + 1 : ℕ) : ℤ)) (n : ℤ)) ≫
      (A.truncLE ((n + 1 : ℕ) : ℤ)).ιTruncLE (n : ℤ)

@[simp] lemma truncLESucc_comp_ιTruncLE (A : CochainComplex C ℤ) (n : ℕ) :
    truncLESucc A n ≫ A.ιTruncLE ((n + 1 : ℕ) : ℤ) = A.ιTruncLE (n : ℤ) := by
  letI := isIso_truncLEMap_ιTruncLE_succ A n
  rw [truncLESucc, Category.assoc, ← CochainComplex.ιTruncLE_naturality]
  simp

/-- The canonical filtration by lower truncations, with no additional
hypotheses on the abelian category. -/
noncomputable def canonicalTruncation (A : CochainComplex C ℤ) :
    CanonicalTruncationData A where
  step := truncLESucc A
  step_ι := truncLESucc_comp_ιTruncLE A

example (A : CochainComplex C ℤ) : BoundedAboveFiltration A :=
  canonicalFiltration (canonicalTruncation A)

#print axioms RelativeFM.Spaltenstein.HomologicalComplex.isIso_ιTruncLE_f_of_not_boundary
#print axioms RelativeFM.Spaltenstein.HomologicalComplex.isIso_truncGEM'
#print axioms RelativeFM.Spaltenstein.HomologicalComplex.isIso_truncLEMap
#print axioms RelativeFM.Spaltenstein.isIso_truncLEMap_ιTruncLE_succ
#print axioms RelativeFM.Spaltenstein.truncLESucc
#print axioms RelativeFM.Spaltenstein.truncLESucc_comp_ιTruncLE
#print axioms RelativeFM.Spaltenstein.canonicalTruncation

end
end RelativeFM.Spaltenstein
