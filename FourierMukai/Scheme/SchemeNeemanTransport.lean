import WeakApprox.EquivalenceInvariance
import WeakApprox.GeneratorBridge
import FourierMukai.Scheme.AffineQCoh
import FourierMukai.Scheme.QCohSerreExtension01IE
import FourierMukai.Scheme.NeemanApproximation
import FourierMukai.Scheme.NeemanPreferred
import FourierMukai.Scheme.NeemanGeneratorBoundsM5

/-!
# Coproduct-free transport of weak-approximation ingredients

The transport lemmas in `WeakApprox.EquivalenceInvariance` ask both categories
to have all small coproducts.  For an equivalence this is unnecessary: the
inductive `Coprod` closure can be mapped directly through its colimit
presentations.  This file records that sharper transport, including Neeman's
zero-detection generation predicate.
-/

@[expose] public section

namespace RelativeWeakApprox.SchemeNeemanTransportM5

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type w} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Map `Coprod` through a triangulated equivalence without choosing any
coproducts in either category. -/
lemma map_coprod_of_equivalence (F : C ⥤ D) [F.IsEquivalence]
    [F.CommShift ℤ] [F.IsTriangulated]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    (h : ∀ Y, P Y → Coprod Q (F.obj Y)) {X : C} (hX : Coprod P X) :
    Coprod Q (F.obj X) := by
  induction hX with
  | of_mem X hX => exact h X hX
  | of_isoClosure e _ ih => exact .of_isoClosure (F.mapIso e) ih
  | of_colimitPresentation pres _ ih =>
      exact .of_colimitPresentation (pres.map F) ih
  | of_extension T hT _ _ ih₁ ih₃ =>
      exact .of_extension _ (F.map_distinguished T hT) ih₁ ih₃

/-- Transport a generator's approximation envelope along a triangulated,
shift-compatible equivalence.  No `HasCoproducts` hypothesis is needed. -/
lemma map_envelope_of_equivalence (F : C ⥤ D) [F.IsEquivalence]
    [F.CommShift ℤ] [F.IsTriangulated] (G : C) (a b : ℤ)
    {X : C} (hX : envelope G a b X) :
    envelope (F.obj G) a b (F.obj X) := by
  obtain ⟨Y, hY, ⟨r⟩⟩ := hX
  refine ⟨F.obj Y, map_coprod_of_equivalence F (Q := shiftInterval (F.obj G) a b)
    (fun Z hZ => ?_) hY, ⟨r.map F⟩⟩
  obtain ⟨k, hak, hkb, ⟨e⟩⟩ := hZ
  exact .of_mem _ ⟨k, hak, hkb,
    ⟨F.mapIso e ≪≫ (F.commShiftIso (-k)).app G⟩⟩

/-- A compactly generated zero aisle transports to the compactly generated
zero aisle, again without global coproduct hypotheses. -/
theorem transport_le_zero_eq_coprod (F : C ⥤ D) [F.IsEquivalence]
    [F.CommShift ℤ] [F.IsTriangulated] (G : C) (t : TStructure C)
    (hgen : t.le 0 = Coprod (shiftTail G 0)) :
    (transportTStructure F t).le 0 = Coprod (shiftTail (F.obj G) 0) := by
  letI : F.asEquivalence.functor.CommShift ℤ := by
    change F.CommShift ℤ
    infer_instance
  letI : F.asEquivalence.functor.IsTriangulated := by
    change F.IsTriangulated
    infer_instance
  letI : F.inv.CommShift ℤ := F.asEquivalence.commShiftInverse ℤ
  letI : F.asEquivalence.inverse.CommShift ℤ := by
    change F.inv.CommShift ℤ
    infer_instance
  letI : F.asEquivalence.CommShift ℤ := F.asEquivalence.commShift_of_functor ℤ
  apply le_antisymm
  · intro Y hY
    have hsource : Coprod (shiftTail G 0) (F.inv.obj Y) := by
      rw [← hgen]
      exact hY
    have hmap : Coprod (shiftTail (F.obj G) 0) (F.obj (F.inv.obj Y)) :=
      map_coprod_of_equivalence F (fun Z hZ => by
        obtain ⟨n, hn, ⟨e⟩⟩ := hZ
        exact .of_mem _ ⟨n, hn, ⟨F.mapIso e ≪≫ (F.commShiftIso n).app G⟩⟩) hsource
    exact (Coprod (shiftTail (F.obj G) 0)).prop_of_iso
      (F.objObjPreimageIso Y) hmap
  · letI (J : Type v) : ((transportTStructure F t).le 0).IsClosedUnderColimitsOfShape
        (Discrete J) := TStructure.le_isClosedUnderColimitsOfShape _ _ _
    letI : ((transportTStructure F t).le 0).IsTriangulatedClosed₂ :=
      TStructure.le_isTriangulatedClosed₂ _ _
    apply Coprod.le
    rintro X ⟨n, hn, ⟨e⟩⟩
    apply ((transportTStructure F t).le 0).prop_of_iso e.symm
    change t.le 0 (F.inv.obj ((F.obj G)⟦n⟧))
    let e' : F.inv.obj ((F.obj G)⟦n⟧) ≅ G⟦n⟧ :=
      (F.inv.commShiftIso n).app (F.obj G) ≪≫
        (shiftFunctor C n).mapIso (F.asEquivalence.unitIso.app G).symm
    apply (t.le 0).prop_of_iso e'.symm
    rw [hgen]
    exact .of_mem _ ⟨n, hn, ⟨Iso.refl _⟩⟩

/-- Neeman's zero-detection generation is invariant under equivalence. -/
lemma isPaperGenerator_of_equivalence (F : C ⥤ D) [F.IsEquivalence]
    [F.CommShift ℤ] [F.Additive] {G : C}
    (hG : IsPaperGenerator G) : IsPaperGenerator (F.obj G) := by
  intro E hE
  have hz : IsZero (F.inv.obj E) := hG (fun n f => by
    apply F.map_injective
    rw [F.map_zero]
    have h := hE n ((F.commShiftIso n).inv.app G ≫ F.map f ≫
      (F.objObjPreimageIso E).hom)
    have h' : F.map f ≫ (F.objObjPreimageIso E).hom = 0 := by
      rw [← cancel_epi ((F.commShiftIso n).inv.app G)]
      simpa only [Limits.zero_comp, Limits.comp_zero] using h
    exact (cancel_mono (F.objObjPreimageIso E).hom).mp
      (by simpa only [Limits.zero_comp] using h'))
  exact (F.map_isZero hz).of_iso (F.objObjPreimageIso E).symm

/-- Compactness transports along an equivalence, with no ambient coproduct
existence assumptions. -/
lemma isCompactAb_of_equivalence (F : C ⥤ D) [F.IsEquivalence] [F.Additive]
    {G : C} (hG : IsCompactAb G) : IsCompactAb (F.obj G) := by
  letI : F.asEquivalence.functor.Additive := by
    change F.Additive
    infer_instance
  exact isCompactAb_leftAdjoint_obj' F.asEquivalence.toAdjunction hG
    (fun _ => inferInstance)

/-- The preferred-class assertion transports along a triangulated equivalence,
without coproduct-existence hypotheses. -/
theorem inPreferredClass_transportTStructure
    (F : C ⥤ D) [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (G : C) (t : TStructure C) (hGc : IsCompactAb G) (hGg : IsPaperGenerator G)
    (hgen : t.le 0 = Coprod (shiftTail G 0)) :
    RelativeFM.NeemanPreferredM6.InPreferredClass (transportTStructure F t) :=
  RelativeFM.NeemanPreferredM6.inPreferredClass_of_compactlyGenerated _ _
    (isCompactAb_of_equivalence F hGc) (isPaperGenerator_of_equivalence F hGg)
    (transport_le_zero_eq_coprod F G t hgen)

/-- Transport all fields of weak approximation, with Neeman's zero-detection
condition instead of the repository's stronger morphism-separation condition.
The conclusion is left unbundled so it can be used without choosing a competing
replacement for `WeakApproximationData`. -/
theorem exists_paper_weakApproximation_of_equivalence
    (F : C ⥤ D) [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (G : C) (t : TStructure C) (N : ℤ) (hN : 0 < N)
    (hGc : IsCompactAb G) (hGg : IsPaperGenerator G)
    (hGmem : t.le N G)
    (hvan : ∀ {Y : C}, t.le (-N) Y → ∀ f : G ⟶ Y, f = 0)
    (htri : ∀ X : C, t.le 0 X →
      ∃ (E D : C) (f : E ⟶ X) (g : X ⟶ D) (h : D ⟶ E⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C ∧ envelope G (-N) N E ∧ t.le (-1) D) :
    ∃ N : ℤ, 0 < N ∧
      IsCompactAb (F.obj G) ∧ IsPaperGenerator (F.obj G) ∧
      (transportTStructure F t).le N (F.obj G) ∧
      (∀ {Y : D}, (transportTStructure F t).le (-N) Y →
        ∀ f : F.obj G ⟶ Y, f = 0) ∧
      ∀ Y : D, (transportTStructure F t).le 0 Y →
        ∃ (E Z : D) (f : E ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ E⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang D ∧
          envelope (F.obj G) (-N) N E ∧
          (transportTStructure F t).le (-1) Z := by
  letI : F.asEquivalence.functor.CommShift ℤ := by
    change F.CommShift ℤ
    infer_instance
  letI : F.asEquivalence.functor.Additive := by
    change F.Additive
    infer_instance
  letI : F.asEquivalence.functor.IsTriangulated := by
    change F.IsTriangulated
    infer_instance
  letI : F.inv.CommShift ℤ := F.asEquivalence.commShiftInverse ℤ
  letI : F.asEquivalence.inverse.CommShift ℤ := by
    change F.inv.CommShift ℤ
    infer_instance
  letI : F.asEquivalence.CommShift ℤ := F.asEquivalence.commShift_of_functor ℤ
  letI : F.inv.IsTriangulated := F.asEquivalence.toAdjunction.isTriangulated_rightAdjoint
  refine ⟨N, hN, isCompactAb_of_equivalence F hGc,
    isPaperGenerator_of_equivalence F hGg, ?_, ?_, ?_⟩
  · exact (t.le N).prop_of_iso (F.asEquivalence.unitIso.app G) hGmem
  · intro Y hY f
    apply (F.asEquivalence.toAdjunction.homEquiv G Y).injective
    rw [hvan hY (F.asEquivalence.toAdjunction.homEquiv G Y f)]
    exact (F.asEquivalence.toAdjunction.homAddEquiv_zero G Y).symm
  · intro Y hY
    obtain ⟨E, Z, f, g, h, hT, hE, hZ⟩ := htri (F.inv.obj Y) hY
    refine ⟨F.obj E, F.obj Z,
      F.map f ≫ (F.objObjPreimageIso Y).hom,
      (F.objObjPreimageIso Y).inv ≫ F.map g,
      F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app E, ?_, ?_, ?_⟩
    · exact isomorphic_distinguished _ (F.map_distinguished _ hT) _
        (Triangle.isoMk _ _ (Iso.refl _) (F.objObjPreimageIso Y).symm (Iso.refl _)
          (by
            simp only [Triangle.mk, Functor.mapTriangle, Iso.refl_hom, Category.id_comp,
              Iso.symm_hom]
            rw [Category.assoc, Iso.hom_inv_id, Category.comp_id])
          (by simp [Triangle.mk, Functor.mapTriangle])
          (by simp [Triangle.mk, Functor.mapTriangle]))
    · exact map_envelope_of_equivalence F G (-N) N hE
    · exact (t.le (-1)).prop_of_iso (F.asEquivalence.unitIso.app Z) hZ

end RelativeWeakApprox.SchemeNeemanTransportM5

#print axioms RelativeWeakApprox.SchemeNeemanTransportM5.exists_paper_weakApproximation_of_equivalence
#print axioms RelativeWeakApprox.SchemeNeemanTransportM5.map_coprod_of_equivalence
#print axioms RelativeWeakApprox.SchemeNeemanTransportM5.map_envelope_of_equivalence
#print axioms RelativeWeakApprox.SchemeNeemanTransportM5.isPaperGenerator_of_equivalence
#print axioms RelativeWeakApprox.SchemeNeemanTransportM5.isCompactAb_of_equivalence

/-!
## Affine Neeman weak approximation in the cohomological `D_qc` model

The ring-side regular-module approximation package is transported across the
affine comparison `D(A-Mod) ≌ D_qc(Spec A)`.  The target uses the transported
standard `t`-structure and Neeman's zero-detection generation condition, not
the false stronger `IsGenerator` condition.

There are exactly two mathematical inputs: compactness of `A[0]` and the
explicit `AffineDerivedGammaInput` comparison data (Stacks 06Z0/079W/08D4/01XB).
In particular, no global coproduct existence on `D_qc`, no scheme recollement,
and no morphism-separation hypothesis is assumed.  The triangulated structure
comes from the repository's proved Stacks-01IE extension argument.
-/

namespace RelativeFM.SchemeNeemanAffineM5

open RelativeWeakApprox
open RelativeWeakApprox.SchemeNeemanTransportM5
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The triangulated structure on quasicoherent-cohomology complexes, proved by
the repository's Stacks-01IE development. -/
noncomputable instance isDQCohTriangulated01IE (X : Scheme.{u}) :
    (IsDQCoh X).IsTriangulated :=
  AffineExtension.isDQCohTriangulated_01IE X

/-- Additivity of the affine comparison, in its `D_qc` spelling. -/
noncomputable instance affineRingDqcEquivalence_additive
    (A : CommRingCat.{u}) (I : AffineDerivedGammaInput A) :
    (affineRingDqcEquivalence A I).functor.Additive := by
  change (affineRingCohomologyEquivalence A I).functor.Additive
  infer_instance

/-- Shift compatibility of the affine comparison, in its `D_qc` spelling. -/
noncomputable instance affineRingDqcEquivalence_commShift
    (A : CommRingCat.{u}) (I : AffineDerivedGammaInput A) :
    (affineRingDqcEquivalence A I).functor.CommShift ℤ := by
  change (affineRingCohomologyEquivalence A I).functor.CommShift ℤ
  infer_instance

/-- The affine ring/`D_qc` comparison is triangulated, using the same proved
extension-closure input rather than adding a Serre-class hypothesis. -/
noncomputable instance affineRingDqcEquivalence_isTriangulated01IE
    (A : CommRingCat.{u}) (I : AffineDerivedGammaInput A) :
    (affineRingDqcEquivalence A I).functor.IsTriangulated := by
  letI := I.tildeExact
  letI : (QuasicoherentCohomology A).IsTriangulated := by
    rw [quasicoherentCohomology_eq_isDQCoh]
    infer_instance
  dsimp only [affineRingDqcEquivalence, affineRingCohomologyEquivalence]
  apply ObjectProperty.isTriangulated_lift

/-- The standard `t`-structure transported from `D(A-Mod)` to the
quasicoherent-cohomology model on `Spec A`. -/
noncomputable def transportedStandardTStructure (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) : TStructure (Dqc (Spec A)) :=
  transportTStructure (affineRingDqcEquivalence A I).functor
    (AffineD.standardTStructure A)

/-- Neeman 3.2(iv), affine unsupported (`Z = X`) form in the all-sheaves
quasicoherent-cohomology model.  The generator is the image of `A[0]`, and the
generation field is zero detection. -/
def RegularModuleDqcWeakApproximation (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) : Prop :=
  ∃ N : ℤ, 0 < N ∧
    IsCompactAb ((affineRingDqcEquivalence A I).functor.obj (ringObject A)) ∧
    IsPaperGenerator ((affineRingDqcEquivalence A I).functor.obj (ringObject A)) ∧
    (transportedStandardTStructure A I).le N
      ((affineRingDqcEquivalence A I).functor.obj (ringObject A)) ∧
    (∀ {Y : Dqc (Spec A)}, (transportedStandardTStructure A I).le (-N) Y →
      ∀ f : (affineRingDqcEquivalence A I).functor.obj (ringObject A) ⟶ Y, f = 0) ∧
    ∀ Y : Dqc (Spec A), (transportedStandardTStructure A I).le 0 Y →
      ∃ (E Z : Dqc (Spec A)) (f : E ⟶ Y) (g : Y ⟶ Z)
        (h : Z ⟶ E⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang (Dqc (Spec A)) ∧
        envelope ((affineRingDqcEquivalence A I).functor.obj (ringObject A)) (-N) N E ∧
        (transportedStandardTStructure A I).le (-1) Z

/-- Affine Neeman 3.2(iv) in the cohomological `D_qc` model.  Only compactness
of the regular module and the explicitly named affine derived-Γ comparison are
inputs; the bound is one and the other fields are proved in the ring model. -/
theorem regularModule_dqcSpec_weakApproximation (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) (hAc : IsCompactAb (ringObject A)) :
    RegularModuleDqcWeakApproximation A I := by
  unfold RegularModuleDqcWeakApproximation transportedStandardTStructure
  exact exists_paper_weakApproximation_of_equivalence
    (affineRingDqcEquivalence A I).functor (ringObject A)
    (AffineD.standardTStructure A) 1 (by omega) hAc
    (NeemanPreferredM6.ringObject_isPaperGenerator A)
    (NeemanGeneratorM5.ringObject_mem_standard_le_of_nonneg A (by omega))
    (fun hY f => NeemanGeneratorM5.ringObject_hom_zero_of_standard_le_neg_of_pos A
      (by omega) hY f)
    (NeemanApproximation.M3.exists_approximation_triangle A)

end

end RelativeFM.SchemeNeemanAffineM5

#print axioms RelativeFM.SchemeNeemanAffineM5.regularModule_dqcSpec_weakApproximation

namespace RelativeFM.SchemeNeemanAffineM5

open RelativeWeakApprox
open RelativeWeakApprox.SchemeNeemanTransportM5
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Affine Neeman 3.2(iii) for the transported standard `t`-structure, with
exactly the same two inputs. -/
theorem regularModule_dqcSpec_preferred (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) (hAc : IsCompactAb (ringObject A)) :
    NeemanPreferredM6.InPreferredClass (transportedStandardTStructure A I) := by
  unfold transportedStandardTStructure
  exact inPreferredClass_transportTStructure
    (affineRingDqcEquivalence A I).functor (ringObject A)
    (AffineD.standardTStructure A) hAc
    (NeemanPreferredM6.ringObject_isPaperGenerator A)
    (AisleGeneration.Ring.standard_le_zero_eq_coprod A)

/-- The unsupported affine 3.2(iii)--(iv) package, without the compact/perfect
comparison, which is a separate part of the theorem. -/
theorem regularModule_dqcSpec_neemanPackage (A : CommRingCat.{u})
    (I : AffineDerivedGammaInput A) (hAc : IsCompactAb (ringObject A)) :
    RegularModuleDqcWeakApproximation A I ∧
      NeemanPreferredM6.InPreferredClass (transportedStandardTStructure A I) :=
  ⟨regularModule_dqcSpec_weakApproximation A I hAc,
    regularModule_dqcSpec_preferred A I hAc⟩

end

end RelativeFM.SchemeNeemanAffineM5

#print axioms RelativeWeakApprox.SchemeNeemanTransportM5.transport_le_zero_eq_coprod
#print axioms RelativeWeakApprox.SchemeNeemanTransportM5.inPreferredClass_transportTStructure
#print axioms RelativeFM.SchemeNeemanAffineM5.regularModule_dqcSpec_preferred
#print axioms RelativeFM.SchemeNeemanAffineM5.regularModule_dqcSpec_neemanPackage
