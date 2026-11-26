/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.PerfectModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Bounded finite-projective models: the formal part of the converse

This module proves the elementary triangulated closure operations for objects of
`D(A-Mod)` having a bounded complex of finitely generated projective modules as
representative.  In particular, maps between two such representatives lift to
cochain maps by K-projectivity, and their mapping cone is another such model.
No Noetherian or compactness hypothesis is used.
-/

@[expose] public section
namespace RelativeFM.AffinePerfect

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open scoped ZeroObject Classical

universe u
noncomputable section
attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- Finitely generated modules are preserved by zero objects. -/
lemma moduleFinite_of_isZero {M : ModuleCat.{u} A} (hM : IsZero M) : Module.Finite A M := by
  letI : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
  rw [Module.finite_def, show (⊤ : Submodule A M) = ⊥ from
    (Submodule.eq_bot_iff _).2 (fun x _ ↦ Subsingleton.elim x 0)]
  exact Submodule.fg_bot

/-- A zero module is projective. -/
lemma moduleProjective_of_isZero {M : ModuleCat.{u} A} (hM : IsZero M) :
    Module.Projective A M := by
  letI : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
  infer_instance

/-- The object property whose reversal of `boundedFiniteProjectiveModel_mem_perf`
we wish to prove. -/
def HasBoundedFiniteProjectiveModel : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
  fun X ↦ Nonempty (BoundedFiniteProjectiveModel A X)

noncomputable def hasBoundedFiniteProjectiveModel_of_iso {X Y : DerivedCategory (ModuleCat.{u} A)}
    (e : X ≅ Y) (H : BoundedFiniteProjectiveModel A X) :
    BoundedFiniteProjectiveModel A Y where
  complex := H.complex
  lower := H.lower
  upper := H.upper
  isStrictlyGE := H.isStrictlyGE
  isStrictlyLE := H.isStrictlyLE
  finite := H.finite
  projective := H.projective
  iso := e.symm ≪≫ H.iso

/-- A finitely generated projective module in a single degree has the expected
strictly bounded model. -/
noncomputable def singleModel (M : ModuleCat.{u} A) [Module.Finite A M]
    [Module.Projective A M] (n : ℤ) :
    BoundedFiniteProjectiveModel A
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M) where
  complex := (CochainComplex.singleFunctor (ModuleCat.{u} A) n).obj M
  lower := n
  upper := n
  isStrictlyGE := inferInstance
  isStrictlyLE := inferInstance
  finite i := by
    by_cases hi : i = n
    · subst i
      exact Module.Finite.equiv (HomologicalComplex.singleObjXSelf (.up ℤ) n M).symm.toLinearEquiv
    · exact moduleFinite_of_isZero A (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
  projective i := by
    by_cases hi : i = n
    · subst i
      exact Module.Projective.of_equiv'
        (HomologicalComplex.singleObjXSelf (.up ℤ) n M).symm.toLinearEquiv
    · exact moduleProjective_of_isZero A (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
  iso := Iso.refl _

/-- The regular module has a bounded finite-projective model. -/
noncomputable def ringObjectModel :
    BoundedFiniteProjectiveModel A (ringObject A) := singleModel A (ModuleCat.of A A) 0

/-- The zero derived object has a bounded finite-projective model. -/
noncomputable def zeroModel : BoundedFiniteProjectiveModel A
    (0 : DerivedCategory (ModuleCat.{u} A)) where
  complex := 0
  lower := 0
  upper := 0
  isStrictlyGE := inferInstance
  isStrictlyLE := inferInstance
  finite n := moduleFinite_of_isZero A
    ((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n).map_isZero (isZero_zero _))
  projective n := moduleProjective_of_isZero A
    ((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n).map_isZero (isZero_zero _))
  iso := DerivedCategory.Q.mapZeroObject.symm

/-- Shift a bounded finite-projective representative. -/
noncomputable def shiftModel {X : DerivedCategory (ModuleCat.{u} A)}
    (H : BoundedFiniteProjectiveModel A X) (a : ℤ) :
    BoundedFiniteProjectiveModel A (X⟦a⟧) := by
  letI := H.isStrictlyGE
  letI := H.isStrictlyLE
  exact
    { complex := H.complex⟦a⟧
      lower := H.lower - a
      upper := H.upper - a
      isStrictlyGE := H.complex.isStrictlyGE_shift H.lower a _ (by omega)
      isStrictlyLE := H.complex.isStrictlyLE_shift H.upper a _ (by omega)
      finite n := by
        letI := H.finite (n + a)
        exact Module.Finite.equiv
          (H.complex.shiftFunctorObjXIso a n (n + a) rfl).symm.toLinearEquiv
      projective n := by
        letI := H.projective (n + a)
        exact Module.Projective.of_equiv'
          (H.complex.shiftFunctorObjXIso a n (n + a) rfl).symm.toLinearEquiv
      iso := (shiftFunctor _ a).mapIso H.iso ≪≫
        (DerivedCategory.Q.commShiftIso a).symm.app H.complex }

lemma moduleFinite_biprod (M N : ModuleCat.{u} A) [Module.Finite A M]
    [Module.Finite A N] : Module.Finite A (M ⊞ N : ModuleCat.{u} A) :=
  Module.Finite.equiv (ModuleCat.biprodIsoProd M N).symm.toLinearEquiv

lemma moduleProjective_biprod (M N : ModuleCat.{u} A) [Module.Projective A M]
    [Module.Projective A N] : Module.Projective A (M ⊞ N : ModuleCat.{u} A) :=
  Module.Projective.of_equiv' (ModuleCat.biprodIsoProd M N).symm.toLinearEquiv

/-- Every bounded finite-projective complex is K-projective, since it is in
particular bounded above. -/
lemma isKProjective_model_complex {X : DerivedCategory (ModuleCat.{u} A)}
    (H : BoundedFiniteProjectiveModel A X) : H.complex.IsKProjective := by
  letI := H.isStrictlyLE
  letI : ∀ n, CategoryTheory.Projective (H.complex.X n) := fun n ↦ by
    letI := H.projective n
    infer_instance
  exact CochainComplex.isKProjective_of_projective H.complex H.upper

/-- Morphisms out of a K-projective representative lift from the derived
category to genuine cochain maps.  This uses only bounded-above K-projectivity,
not an unbounded replacement theorem. -/
lemma exists_cochain_map_of_isKProjective {P L : CochainComplex (ModuleCat.{u} A) ℤ}
    [P.IsKProjective] (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) :
    ∃ φ : P ⟶ L, DerivedCategory.Q.map φ = f := by
  let q := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P (q.obj L)).surjective
    (e.hom.app P ≫ f ≫ e.inv.app L)
  obtain ⟨φ, rfl⟩ := q.map_surjective g
  refine ⟨φ, ?_⟩
  rw [← cancel_mono (e.inv.app L)]
  rw [DerivedCategory.quotientCompQhIso_inv_naturality, hg]
  simp [e]

/-- The mapping cone of a cochain map between bounded finite-projective
complexes is again bounded finite-projective. -/
noncomputable def mappingConeModel {X Y : DerivedCategory (ModuleCat.{u} A)}
    (H : BoundedFiniteProjectiveModel A X) (K : BoundedFiniteProjectiveModel A Y)
    (f : H.complex ⟶ K.complex) :
    BoundedFiniteProjectiveModel A
      (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) := by
  letI := H.isStrictlyGE
  letI := H.isStrictlyLE
  letI := K.isStrictlyGE
  letI := K.isStrictlyLE
  exact
    { complex := CochainComplex.mappingCone f
      lower := min (H.lower - 1) K.lower
      upper := max (H.upper - 1) K.upper
      isStrictlyGE := CochainComplex.isStrictlyGE_mappingCone f H.lower K.lower _
        (by omega) (by omega)
      isStrictlyLE := by
        rw [CochainComplex.isStrictlyLE_iff]
        intro n hn
        rw [CochainComplex.mappingCone.isZero_X_iff]
        exact ⟨H.complex.isZero_of_isStrictlyLE H.upper _ (by omega),
          K.complex.isZero_of_isStrictlyLE K.upper _ (by omega)⟩
      finite n := by
        letI := H.finite (n + 1)
        letI := K.finite n
        exact Module.Finite.equiv
          ((HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl ≪≫
            ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv)
      projective n := by
        letI := H.projective (n + 1)
        letI := K.projective n
        exact Module.Projective.of_equiv'
          ((HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl ≪≫
            ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv)
      iso := Iso.refl _ }

/-- Lift a derived morphism between bounded finite-projective models to a
cochain map, with its defining compatibility. -/
noncomputable def modelMapLift {X Y : DerivedCategory (ModuleCat.{u} A)}
    (H : BoundedFiniteProjectiveModel A X) (K : BoundedFiniteProjectiveModel A Y)
    (f : X ⟶ Y) : H.complex ⟶ K.complex := by
  letI := isKProjective_model_complex A H
  exact (exists_cochain_map_of_isKProjective A
    (H.iso.inv ≫ f ≫ K.iso.hom)).choose

lemma Q_map_modelMapLift {X Y : DerivedCategory (ModuleCat.{u} A)}
    (H : BoundedFiniteProjectiveModel A X) (K : BoundedFiniteProjectiveModel A Y)
    (f : X ⟶ Y) : DerivedCategory.Q.map (modelMapLift A H K f) =
      H.iso.inv ≫ f ≫ K.iso.hom := by
  letI := isKProjective_model_complex A H
  exact (exists_cochain_map_of_isKProjective A
    (H.iso.inv ≫ f ≫ K.iso.hom)).choose_spec

instance hasModel_isClosedUnderIsomorphisms :
    (HasBoundedFiniteProjectiveModel A).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    obtain ⟨H⟩ := hX
    exact ⟨hasBoundedFiniteProjectiveModel_of_iso A e H⟩

instance hasModel_isStableUnderShift :
    (HasBoundedFiniteProjectiveModel A).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ObjectProperty.IsStableUnderShiftBy.mk fun X hX ↦ by
    obtain ⟨H⟩ := hX
    exact ⟨shiftModel A H a⟩

instance hasModel_isTriangulatedClosed₃ :
    (HasBoundedFiniteProjectiveModel A).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (fun T hT h₁ h₂ ↦ by
    obtain ⟨H₁⟩ := h₁
    obtain ⟨H₂⟩ := h₂
    let φ := modelMapLift A H₁ H₂ T.mor₁
    let e := isoTriangleOfIso₁₂ T
      (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle φ)) hT
      (DerivedCategory.mappingCone_triangle_distinguished φ) H₁.iso H₂.iso (by
        change T.mor₁ ≫ H₂.iso.hom = H₁.iso.hom ≫ DerivedCategory.Q.map φ
        rw [Q_map_modelMapLift]
        simp)
    exact ⟨hasBoundedFiniteProjectiveModel_of_iso A (Triangle.π₃.mapIso e).symm
      (mappingConeModel A H₁ H₂ φ)⟩)

instance hasModel_isTriangulatedClosed₂ :
    (HasBoundedFiniteProjectiveModel A).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance hasModel_isTriangulated :
    (HasBoundedFiniteProjectiveModel A).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, ⟨zeroModel A⟩⟩

lemma ringObject_hasModel : HasBoundedFiniteProjectiveModel A (ringObject A) :=
  ⟨ringObjectModel A⟩

/-- The converse is proved as soon as bounded finite-projective models are
closed under derived retracts.  This isolates the idempotent-completion step;
zero, shifts and mapping cones are already proved above. -/
theorem perf_le_hasModel_of_stableUnderRetracts
    (hR : (HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts) :
    Perf A ≤ HasBoundedFiniteProjectiveModel A := by
  letI := hR
  change (ObjectProperty.singleton (ringObject A)).triangEnvelope ≤
    HasBoundedFiniteProjectiveModel A
  exact (@ObjectProperty.triangEnvelope_le_iff
    (DerivedCategory (ModuleCat.{u} A)) _ _ _ _ _ _
    (ObjectProperty.singleton (ringObject A))
    (HasBoundedFiniteProjectiveModel A) hR inferInstance).2
      ((ObjectProperty.singleton_le_iff).2 (ringObject_hasModel A))

/-- Consequently, under the same single residual condition, every perfect
object has a bounded finite-projective representative. -/
theorem model_of_perf_of_stableUnderRetracts
    (hR : (HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts)
    (X : DerivedCategory (ModuleCat.{u} A)) (hX : Perf A X) :
    Nonempty (BoundedFiniteProjectiveModel A X) := by
  letI := hR
  exact perf_le_hasModel_of_stableUnderRetracts A hR X hX

lemma hasModel_le_perf : HasBoundedFiniteProjectiveModel A ≤ Perf A := by
  rintro X ⟨H⟩
  exact model_mem_perf A X ⟨H⟩

/-- **Exact reduction of the converse.**  The thick envelope is contained in
bounded finite-projective models exactly when the latter are closed under
retracts.  All the other closure conditions have been proved unconditionally.
The remaining mathematical theorem is the direct-summand assertion Stacks Tag
066S (Lemma 15.76.5), equivalently idempotent completion of the bounded
projective model. -/
theorem perf_le_hasModel_iff_stableUnderRetracts :
    (Perf A ≤ HasBoundedFiniteProjectiveModel A) ↔
      (HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts := by
  constructor
  · intro h
    exact ⟨fun {X Y} r hY ↦ h X ((Perf A).prop_of_retract r
      (hasModel_le_perf A Y hY))⟩
  · exact perf_le_hasModel_of_stableUnderRetracts A

#print axioms RelativeFM.AffinePerfect.mappingConeModel
#print axioms RelativeFM.AffinePerfect.hasModel_isTriangulated
#print axioms RelativeFM.AffinePerfect.perf_le_hasModel_iff_stableUnderRetracts

end
end RelativeFM.AffinePerfect
