/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.Derived
import FourierMukai.Scheme.Perfect
import FourierMukai.Scheme.PerfectRing
import FourierMukai.Scheme.AffineDictionary
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Perfect objects: the thick-envelope model and bounded projective models

Three things are proved here, and one cited input is left.

* Thick envelopes transport along triangulated equivalences and along fully
  faithful thick inclusions (`perf_iff_qcThickGenerated`, unconditional in the
  QC model).
* Finite projective single objects are perfect, and complementary stupid
  truncations form a short exact sequence, which yields `mem_Q_of_bounded`: a
  bounded complex whose cohomology lies in a class closed under the relevant
  operations is in the thick envelope.
* `boundedFiniteProjectiveModel_mem_perf`: every bounded complex of finitely
  generated projective `A`-modules is perfect, for **every** commutative ring —
  no compactness, Noetherian hypothesis or resolution input (Stacks 066T).
* `perf_iff_affineThickGenerated`: on `Spec A` the thick envelope of the
  structure sheaf is the image of `Perf A`, under the derived affine dictionary,
  from the explicit 06Z0 comparison together with shift, exactness and generator
  coherence.  The bare comparison alone was insufficient.

`BoundedProjectiveModelConverseInput` is the remaining input — the direction
`Perf A → bounded finite projective model` — and `boundedProjectiveModelInput_of_converse`
assembles `BoundedProjectiveModelInput` from it.  That direction is Stacks 07LT;
it is not asserted proved.

Found by a member of the Ultramath run `smwv1bkrk` (direction AF4).
-/
@[expose] public section
namespace RelativeFM
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry
open scoped ZeroObject Classical
universe vC vD uC uD u w₁ w₂ w₃
namespace AffinePerfect
section Transport
variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [CategoryTheory.IsTriangulated C]
  {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [CategoryTheory.IsTriangulated D]
/-- A triangulated functor maps the thick envelope of `G` into the thick
envelope of its image. -/
theorem mem_triangEnvelope_singleton_map (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] (G : C) {X : C}
    (hX : (ObjectProperty.singleton G).triangEnvelope X) :
    (ObjectProperty.singleton (F.obj G)).triangEnvelope (F.obj X) := by
  let Q := (ObjectProperty.singleton (F.obj G)).triangEnvelope
  let P := Q.inverseImage F
  letI : P.IsStableUnderRetracts :=
    ⟨fun r hr ↦ Q.prop_of_retract (r.map F) hr⟩
  letI : P.IsTriangulated := inferInstance
  have hle : ObjectProperty.singleton G ≤ P := by
    rw [ObjectProperty.singleton_le_iff]
    exact ObjectProperty.le_triangEnvelope _ _
      (ObjectProperty.ofObj_apply _ Unit.unit)
  exact ((ObjectProperty.triangEnvelope_le_iff
    (ObjectProperty.singleton G)).2 hle) X hX
/-- Thick-envelope transport by a triangulated equivalence; proved. -/
theorem mem_triangEnvelope_singleton_map_iff (F : C ⥤ D) [F.IsEquivalence]
    [F.CommShift ℤ] [F.IsTriangulated] (G X : C) :
    (ObjectProperty.singleton (F.obj G)).triangEnvelope (F.obj X) ↔
      (ObjectProperty.singleton G).triangEnvelope X := by
  constructor
  · intro h
    let E := F.asEquivalence
    letI : E.functor.CommShift ℤ := by change F.CommShift ℤ; infer_instance
    letI : E.functor.IsTriangulated := by change F.IsTriangulated; infer_instance
    letI : F.inv.CommShift ℤ := E.commShiftInverse ℤ
    letI : E.inverse.CommShift ℤ := by change F.inv.CommShift ℤ; infer_instance
    letI : E.CommShift ℤ := E.commShift_of_functor ℤ
    letI : F.inv.IsTriangulated := E.toAdjunction.isTriangulated_rightAdjoint
    have h' := mem_triangEnvelope_singleton_map F.inv (F.obj G) h
    have hbase : (ObjectProperty.singleton G).triangEnvelope G :=
      ObjectProperty.le_triangEnvelope _ _ (ObjectProperty.ofObj_apply _ Unit.unit)
    have hgen : (ObjectProperty.singleton G).triangEnvelope (F.inv.obj (F.obj G)) :=
      (ObjectProperty.singleton G).triangEnvelope.prop_of_iso (E.unitIso.app G) hbase
    have hle : (ObjectProperty.singleton (F.inv.obj (F.obj G))).triangEnvelope ≤
        (ObjectProperty.singleton G).triangEnvelope := by
      rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
      exact hgen
    exact (ObjectProperty.singleton G).triangEnvelope.prop_of_iso
      (E.unitIso.app X).symm (hle _ h')
  · exact mem_triangEnvelope_singleton_map F G
/-- Isomorphic generators have the same finite thick envelope. -/
theorem triangEnvelope_singleton_eq_of_iso {G H : C} (e : G ≅ H) :
    (ObjectProperty.singleton G).triangEnvelope =
      (ObjectProperty.singleton H).triangEnvelope := by
  apply le_antisymm <;>
    rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
  · exact (ObjectProperty.singleton H).triangEnvelope.prop_of_iso e.symm
      (ObjectProperty.le_triangEnvelope _ _ (ObjectProperty.ofObj_apply _ Unit.unit))
  · exact (ObjectProperty.singleton G).triangEnvelope.prop_of_iso e
      (ObjectProperty.le_triangEnvelope _ _ (ObjectProperty.ofObj_apply _ Unit.unit))
/-- The essential image in `D` of the thick envelope inside a triangulated,
retract-closed full subcategory is the ambient thick envelope. -/
theorem triangEnvelope_map_ι {D : Type uD} [Category.{vD} D] [HasZeroObject D]
    [Preadditive D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [CategoryTheory.IsTriangulated D]
    (P : ObjectProperty D) [P.IsTriangulated] [P.IsStableUnderRetracts]
    (G : P.FullSubcategory) :
    ((ObjectProperty.singleton G).triangEnvelope).map P.ι =
      (ObjectProperty.singleton (P.ι.obj G)).triangEnvelope := by
  let T := (ObjectProperty.singleton G).triangEnvelope
  let Q := T.map P.ι
  letI : Q.IsTriangulated := inferInstance
  letI : Q.IsStableUnderRetracts := ⟨by
    intro Y Z r hZ
    obtain ⟨X, hX, ⟨e⟩⟩ := hZ
    have hPZ : P Z := P.prop_of_iso e X.property
    have hPY : P Y := P.prop_of_retract r hPZ
    let Y' : P.FullSubcategory := ⟨Y, hPY⟩
    let r' : Retract Y' X :=
      { i := InducedCategory.homMk (r.i ≫ e.inv)
        r := InducedCategory.homMk (e.hom ≫ r.r)
        retract := by
          apply ObjectProperty.hom_ext
          simp }
    exact ⟨Y', T.prop_of_retract r' hX, ⟨Iso.refl _⟩⟩⟩
  apply le_antisymm
  · rintro Y ⟨X, hX, ⟨e⟩⟩
    exact (ObjectProperty.singleton (P.ι.obj G)).triangEnvelope.prop_of_iso e
      (mem_triangEnvelope_singleton_map P.ι G hX)
  · rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
    exact ⟨G, ObjectProperty.le_triangEnvelope _ _
      (ObjectProperty.ofObj_apply _ Unit.unit), ⟨Iso.refl _⟩⟩

/-- Membership in a thick envelope is detected inside or outside a
triangulated, retract-closed full subcategory. -/
theorem mem_triangEnvelope_ι_iff {D : Type uD} [Category.{vD} D]
    [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (P : ObjectProperty D) [P.IsTriangulated] [P.IsStableUnderRetracts]
    (G X : P.FullSubcategory) :
    (ObjectProperty.singleton (P.ι.obj G)).triangEnvelope (P.ι.obj X) ↔
      (ObjectProperty.singleton G).triangEnvelope X := by
  constructor
  · intro h
    rw [← triangEnvelope_map_ι P G] at h
    obtain ⟨Y, hY, ⟨e⟩⟩ := h
    exact (ObjectProperty.singleton G).triangEnvelope.prop_of_iso
      (P.fullyFaithfulι.preimageIso e) hY
  · exact mem_triangEnvelope_singleton_map P.ι G

/-- An iso-closed singleton and its iso-closure generate the same thick
subcategory. -/
theorem triangEnvelope_isoClosure_singleton {C : Type uC} [Category.{vC} C]
    [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C] (G : C) :
    (ObjectProperty.singleton G).isoClosure.triangEnvelope =
      (ObjectProperty.singleton G).triangEnvelope := by
  apply le_antisymm
  · rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.isoClosure_le_iff,
      ObjectProperty.singleton_le_iff]
    exact ObjectProperty.le_triangEnvelope _ _ (ObjectProperty.ofObj_apply _ Unit.unit)
  · exact ObjectProperty.monotone_triangEnvelope (ObjectProperty.le_isoClosure _)

end Transport

section CohomologyGenerator

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{w₁} C] (P : ObjectProperty C)
  [P.IsClosedUnderIsomorphisms] [P.ContainsZero]

/-- A degree-zero object with property `P` has cohomology in `P`. -/
theorem cohomologyWithin_single_zero (M : C) (hM : P M) :
    cohomologyWithin P ((DerivedCategory.singleFunctor C 0).obj M) := by
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact P.prop_of_isZero
      (DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor C 0).obj M)
        0 n hn)
  · exact P.prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M).symm hM
  · exact P.prop_of_isZero
      (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor C 0).obj M)
        0 n hn)

end CohomologyGenerator

section AffineDictionary

attribute [local instance] HasDerivedCategory.standard

variable (A : CommRingCat.{u})

/-- The regular module viewed in the affine abelian category of
quasicoherent sheaves. -/
noncomputable def qcUnitObject : QCModules A :=
  (tildeEquiv (R := A)).functor.obj (ModuleCat.of A A)

/-- The structure-sheaf generator in `D(QCoh(Spec A))`. -/
noncomputable def qcRingObject : DerivedCategory (QCModules A) :=
  (DerivedCategory.singleFunctor (QCModules A) 0).obj (qcUnitObject A)

/-- The thick envelope of the structure-sheaf generator in the QC affine
model. -/
noncomputable def qcThickGenerated : ObjectProperty (DerivedCategory (QCModules A)) :=
  (ObjectProperty.singleton (qcRingObject A)).triangEnvelope

/-- The ordinary affine derived dictionary identifies the two regular-module
generators. -/
noncomputable def affineDerivedRingObjectIso :
    (affineDerivedEquivalence A).functor.obj (ringObject A) ≅ qcRingObject A :=
  (affineDerivedSingleFunctor A 0).app (ModuleCat.of A A)

/-- **Affine Perf bridge, QC model (proved).**  Unlike the all-sheaves version,
this needs no Stacks 06Z0 comparison. -/
theorem perf_iff_qcThickGenerated (X : DerivedCategory (ModuleCat A)) :
    Perf A X ↔ qcThickGenerated A ((affineDerivedEquivalence A).functor.obj X) := by
  rw [qcThickGenerated, ← triangEnvelope_singleton_eq_of_iso
    (affineDerivedRingObjectIso A)]
  exact (mem_triangEnvelope_singleton_map_iff
    (affineDerivedEquivalence A).functor (ringObject A) X).symm

end AffineDictionary

section AllSheavesBridge

attribute [local instance] HasDerivedCategory.standard

variable (A : CommRingCat.{u})

/-- The structure sheaf in degree zero, in the derived category of all module
sheaves. -/
noncomputable def affineUnitDerived : DerivedCategory (Spec A).Modules :=
  (DerivedCategory.singleFunctor (Spec A).Modules 0).obj
    (SheafOfModules.unit (Spec A).ringCatSheaf)

/-- The structure-sheaf generator as an object with quasicoherent cohomology. -/
noncomputable def affineUnitDerivedQC : (QuasicoherentCohomology A).FullSubcategory where
  obj := affineUnitDerived A
  property := cohomologyWithin_single_zero (quasiCoherent (Spec A))
    (SheafOfModules.unit (Spec A).ringCatSheaf) (by
      change (SheafOfModules.unit (Spec A).ringCatSheaf).IsQuasicoherent
      letI : IsFiniteLocallyFree (SheafOfModules.unit (Spec A).ringCatSheaf) := inferInstance
      exact IsFiniteLocallyFree.toIsQuasicoherent)

/-- Existing `affineUnitGenerators` is precisely the iso-closure of the
singleton of `affineUnitDerived`. -/
theorem affineUnitGenerators_eq_isoClosure :
    affineUnitGenerators A = (ObjectProperty.singleton (affineUnitDerived A)).isoClosure := by
  ext E
  constructor
  · rintro ⟨e⟩
    exact ⟨affineUnitDerived A, (ObjectProperty.singleton_iff _ _).2 rfl, ⟨e⟩⟩
  · rintro ⟨Y, hY, ⟨e⟩⟩
    have h : affineUnitDerived A = Y := (ObjectProperty.singleton_iff _ _).1 hY
    subst Y
    exact ⟨e⟩

/-- The original all-sheaves affine envelope equals the envelope of the literal
structure-sheaf object. -/
theorem affineThickGenerated_eq :
    affineThickGenerated A = (ObjectProperty.singleton (affineUnitDerived A)).triangEnvelope := by
  rw [affineThickGenerated, affineUnitGenerators_eq_isoClosure,
    triangEnvelope_isoClosure_singleton]

/-- **Exact residual input for the all-sheaves Perf bridge.**  The canonical
Stacks 06Z0 comparison must be triangulated and compatible with integer shifts
and with the regular-module generator.  The first field is the existing
ordinary comparison; these further coherence fields are not asserted by that
old interface. -/
structure AffineAllSheavesBridgeInput
    [(QuasicoherentCohomology A).IsTriangulated]
    [(QuasicoherentCohomology A).IsStableUnderRetracts] where
  /-- The ordinary comparison supplied by Stacks Lemma 36.3.5 (Tag 06Z0). -/
  comparison : AffineCohomologyComparison A
  /-- Shift compatibility of the canonical comparison. -/
  commShift : (affineDerivedCohomologyEquivalence A comparison).functor.CommShift ℤ
  /-- Exactness of the canonical comparison. -/
  isTriangulated : (affineDerivedCohomologyEquivalence A comparison).functor.IsTriangulated
  /-- Naturality at the regular module, again part of the canonical Stacks 06Z0
  comparison rather than a new perfectness theorem. -/
  ringObject : Nonempty ((affineDerivedCohomologyEquivalence A comparison).functor.obj
    (ringObject A) ≅ affineUnitDerivedQC A)

/-- **All-sheaves affine Perf bridge, modulo precisely the named 06Z0
coherence input.**  Under `AffineAllSheavesBridgeInput`, `Perf A` is exactly
the preimage of `affineThickGenerated A`. -/
theorem perf_iff_affineThickGenerated
    [(QuasicoherentCohomology A).IsTriangulated]
    [(QuasicoherentCohomology A).IsStableUnderRetracts]
    (H : AffineAllSheavesBridgeInput A) (X : DerivedCategory (ModuleCat A)) :
    Perf A X ↔ affineThickGenerated A
      (((affineDerivedCohomologyEquivalence A H.comparison).functor.obj X).obj) := by
  let F := (affineDerivedCohomologyEquivalence A H.comparison).functor
  letI : F.CommShift ℤ := H.commShift
  letI : F.IsTriangulated := H.isTriangulated
  obtain ⟨eG⟩ := H.ringObject
  have hInternal : Perf A X ↔
      (ObjectProperty.singleton (affineUnitDerivedQC A)).triangEnvelope (F.obj X) := by
    rw [← triangEnvelope_singleton_eq_of_iso eG]
    exact (mem_triangEnvelope_singleton_map_iff F (ringObject A) X).symm
  rw [affineThickGenerated_eq]
  exact hInternal.trans (mem_triangEnvelope_ι_iff
    (QuasicoherentCohomology A) (affineUnitDerivedQC A) (F.obj X)).symm

end AllSheavesBridge

section FiniteProjective

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- A finite free module in degree zero lies in `Perf A`.  The proof uses
finite biproduct closure of the thick envelope. -/
theorem finiteFree_zero_mem_perf (n : ℕ) :
    Perf A ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
      (ModuleCat.of A (Fin n → A))) := by
  let f : Fin n → ModuleCat A := fun _ ↦ ModuleCat.of A A
  let g : Fin n → DerivedCategory (ModuleCat A) := fun _ ↦ ringObject A
  have hg : Perf A (⨁ g) := by
    apply (Perf A).prop_of_isLimit (biproduct.isLimit g)
    intro j
    exact ringObject_mem_perf A
  have hleft : Perf A ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj (⨁ f)) := by
    apply (Perf A).prop_of_iso
      ((DerivedCategory.singleFunctor (ModuleCat A) 0).mapBiproduct f).symm
    simpa [f, g, Function.comp_def, ringObject] using hg
  exact (Perf A).prop_of_iso
    ((DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso
      (ModuleCat.biproductIsoPi f)) (by simpa [f] using hleft)

/-- **Finite projectives are perfect (proved).**  Mathlib supplies a splitting
of a finite free cover; applying the derived single-object functor turns it
into the required categorical retract. -/
theorem finiteProjective_zero_mem_perf (M : ModuleCat A) [Module.Finite A M]
    [Module.Projective A M] :
    Perf A ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M) := by
  obtain ⟨n, f, g, hf, hg, hcomp⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective A M
  let r : Retract M (ModuleCat.of A (Fin n → A)) :=
    { i := ModuleCat.ofHom g
      r := ModuleCat.ofHom f
      retract := by
        ext x
        exact LinearMap.congr_fun hcomp x }
  exact perf_of_retract A (r.map (DerivedCategory.singleFunctor (ModuleCat A) 0))
    (finiteFree_zero_mem_perf A n)

/-- A finite projective module in any single degree is perfect. -/
theorem finiteProjective_single_mem_perf (M : ModuleCat A) [Module.Finite A M]
    [Module.Projective A M] (n : ℤ) :
    Perf A ((DerivedCategory.singleFunctor (ModuleCat A) n).obj M) := by
  exact (Perf A).prop_of_iso
    (((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
      (-n) n 0 (by simp)).app M)
    (perf_shift A (finiteProjective_zero_mem_perf A M) (-n))

end FiniteProjective

section BrutalFiltration

variable {C : Type u} [Category.{vC} C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

noncomputable section

/-- Proved differential formula on a supported stupid-truncation index. -/
lemma stupidTrunc_d_of_mem (K : HomologicalComplex C c')
    (e : c.Embedding c') [e.IsRelIff] {i j : ι} {i' j' : ι'}
    (hi : e.f i = i') (hj : e.f j = j') :
    (K.stupidTrunc e).d i' j' = (K.stupidTruncXIso e hi).hom ≫ K.d i' j' ≫
      (K.stupidTruncXIso e hj).inv := by
  subst i'
  subst j'
  change ((K.restriction e).extend e).d _ _ =
    (((K.restriction e).extendXIso e rfl ≪≫ eqToIso rfl).hom ≫ K.d _ _ ≫
      ((K.restriction e).extendXIso e rfl ≪≫ eqToIso rfl).inv)
  rw [(K.restriction e).extend_d_eq e rfl rfl, K.restriction_d_eq e rfl rfl]
  simp [HomologicalComplex.stupidTrunc, HomologicalComplex.stupidTruncXIso,
    HomologicalComplex.restrictionXIso, HomologicalComplex.restriction, Category.assoc]

/-- The components of the inclusion of a stupid truncation bounded below. -/
noncomputable def stupidTruncιGEF (K : HomologicalComplex C c')
    (e : c.Embedding c') [e.IsRelIff] (i' : ι') : (K.stupidTrunc e).X i' ⟶ K.X i' :=
  if hi : ∃ i, e.f i = i' then (K.stupidTruncXIso e hi.choose_spec).hom else 0

/-- On the support, the inclusion is the canonical component isomorphism; proved directly from the definition. -/
lemma stupidTruncιGEF_of_mem (K : HomologicalComplex C c')
    (e : c.Embedding c') [e.IsRelIff] {i : ι} {i' : ι'} (hi : e.f i = i') :
    stupidTruncιGEF K e i' = (K.stupidTruncXIso e hi).hom := by
  let h : ∃ j, e.f j = i' := ⟨i, hi⟩
  have hh : h.choose = i := e.injective_f (h.choose_spec.trans hi.symm)
  simp only [stupidTruncιGEF, dif_pos h]
  simp [hh]

/-- Off the support, the inclusion vanishes; proved directly from the definition. -/
lemma stupidTruncιGEF_of_not_mem (K : HomologicalComplex C c')
    (e : c.Embedding c') [e.IsRelIff] (i' : ι') (hi : ∀ i, e.f i ≠ i') :
    stupidTruncιGEF K e i' = 0 := by
  simp only [stupidTruncιGEF, dif_neg (not_exists.mpr hi)]

/-- The inclusion of a stupid truncation bounded below. -/
noncomputable def stupidTruncιGE (K : HomologicalComplex C c')
    (e : c.Embedding c') [e.IsTruncGE] : K.stupidTrunc e ⟶ K where
  f := stupidTruncιGEF K e
  comm' i' j' hij := by
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi
      obtain ⟨j, rfl⟩ := e.mem_next hij
      rw [stupidTruncιGEF_of_mem K e rfl, stupidTruncιGEF_of_mem K e rfl,
        stupidTrunc_d_of_mem K e (i := i) (j := j) rfl rfl]
      simp
    · have hzi : IsZero ((K.stupidTrunc e).X i') :=
        K.isZero_stupidTrunc_X e i' (by simpa using hi)
      rw [stupidTruncιGEF_of_not_mem K e i' (by simpa using hi), zero_comp]
      by_cases hj : ∃ j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj
        rw [stupidTruncιGEF_of_mem K e rfl]
        exact hzi.eq_of_src _ _
      · rw [stupidTruncιGEF_of_not_mem K e j' (by simpa using hj), comp_zero]

/-- The components of the projection onto a stupid truncation bounded above. -/
noncomputable def stupidTruncπLEF (K : HomologicalComplex C c')
    (e : c.Embedding c') [e.IsRelIff] (i' : ι') : K.X i' ⟶ (K.stupidTrunc e).X i' :=
  if hi : ∃ i, e.f i = i' then (K.stupidTruncXIso e hi.choose_spec).inv else 0

/-- On the support, the projection is the inverse canonical component isomorphism; proved directly from the definition. -/
lemma stupidTruncπLEF_of_mem (K : HomologicalComplex C c')
    (e : c.Embedding c') [e.IsRelIff] {i : ι} {i' : ι'} (hi : e.f i = i') :
    stupidTruncπLEF K e i' = (K.stupidTruncXIso e hi).inv := by
  let h : ∃ j, e.f j = i' := ⟨i, hi⟩
  have hh : h.choose = i := e.injective_f (h.choose_spec.trans hi.symm)
  simp only [stupidTruncπLEF, dif_pos h]
  simp [hh]

/-- Off the support, the projection vanishes; proved directly from the definition. -/
lemma stupidTruncπLEF_of_not_mem (K : HomologicalComplex C c')
    (e : c.Embedding c') [e.IsRelIff] (i' : ι') (hi : ∀ i, e.f i ≠ i') :
    stupidTruncπLEF K e i' = 0 := by
  simp only [stupidTruncπLEF, dif_neg (not_exists.mpr hi)]

/-- The projection onto a stupid truncation bounded above. -/
noncomputable def stupidTruncπLE (K : HomologicalComplex C c')
    (e : c.Embedding c') [e.IsTruncLE] : K ⟶ K.stupidTrunc e where
  f := stupidTruncπLEF K e
  comm' i' j' hij := by
    by_cases hj : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj
      obtain ⟨i, rfl⟩ := e.mem_prev hij
      rw [stupidTruncπLEF_of_mem K e rfl, stupidTruncπLEF_of_mem K e rfl,
        stupidTrunc_d_of_mem K e (i := i) (j := j) rfl rfl]
      simp
    · have hzj : IsZero ((K.stupidTrunc e).X j') :=
        K.isZero_stupidTrunc_X e j' (by simpa using hj)
      rw [stupidTruncπLEF_of_not_mem K e j' (by simpa using hj), comp_zero]
      by_cases hi : ∃ i, e.f i = i'
      · obtain ⟨i, rfl⟩ := hi
        rw [stupidTruncπLEF_of_mem K e rfl]
        exact hzj.eq_of_tgt _ _
      · rw [stupidTruncπLEF_of_not_mem K e i' (by simpa using hi), zero_comp]

/-- The brutal-filtration short complex attached to complementary embeddings. -/
noncomputable def stupidTruncShortComplex (K : HomologicalComplex C c')
    {ι₁ ι₂ : Type*} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
    (e₁ : c₁.Embedding c') (e₂ : c₂.Embedding c')
    [e₁.IsTruncGE] [e₂.IsTruncLE] (ac : e₁.AreComplementary e₂) :
    ShortComplex (HomologicalComplex C c') :=
  ShortComplex.mk (stupidTruncιGE K e₁) (stupidTruncπLE K e₂) (by
    ext i
    change stupidTruncιGEF K e₁ i ≫ stupidTruncπLEF K e₂ i = 0
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
    · have h₂ : ∀ i₂, e₂.f i₂ ≠ e₁.f i₁ := by
        intro i₂ hi
        exact ac.disjoint i₁ i₂ hi.symm
      rw [stupidTruncιGEF_of_mem K e₁ rfl,
        stupidTruncπLEF_of_not_mem K e₂ _ h₂, comp_zero]
    · have h₁ : ∀ i₁, e₁.f i₁ ≠ e₂.f i₂ := by
        intro i₁ hi
        exact ac.disjoint i₁ i₂ hi
      rw [stupidTruncιGEF_of_not_mem K e₁ _ h₁, zero_comp])

/-- The brutal-filtration sequence is degreewise split exact, hence short exact. -/
theorem stupidTruncShortComplex_shortExact (K : HomologicalComplex C c')
    {ι₁ ι₂ : Type*} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
    (e₁ : c₁.Embedding c') (e₂ : c₂.Embedding c')
    [e₁.IsTruncGE] [e₂.IsTruncLE] (ac : e₁.AreComplementary e₂) :
    (stupidTruncShortComplex K e₁ e₂ ac).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · have h₂ : ∀ i₂, e₂.f i₂ ≠ e₁.f i₁ := by
      intro i₂ hi
      exact ac.disjoint i₁ i₂ hi.symm
    have hz : IsZero ((K.stupidTrunc e₂).X (e₁.f i₁)) :=
      K.isZero_stupidTrunc_X e₂ _ h₂
    have hg : (stupidTruncπLE K e₂).f (e₁.f i₁) = 0 :=
      stupidTruncπLEF_of_not_mem K e₂ _ h₂
    change (ShortComplex.mk ((stupidTruncιGE K e₁).f (e₁.f i₁))
      ((stupidTruncπLE K e₂).f (e₁.f i₁)) (by rw [hg, comp_zero])).ShortExact
    refine
      { exact := (ShortComplex.exact_iff_epi _ hg).2 (by
          change Epi (stupidTruncιGEF K e₁ (e₁.f i₁))
          rw [stupidTruncιGEF_of_mem K e₁ rfl]
          infer_instance)
        mono_f := by
          change Mono (stupidTruncιGEF K e₁ (e₁.f i₁))
          rw [stupidTruncιGEF_of_mem K e₁ rfl]
          infer_instance
        epi_g := hz.epi _ }
  · have h₁ : ∀ i₁, e₁.f i₁ ≠ e₂.f i₂ := by
      intro i₁ hi
      exact ac.disjoint i₁ i₂ hi
    have hz : IsZero ((K.stupidTrunc e₁).X (e₂.f i₂)) :=
      K.isZero_stupidTrunc_X e₁ _ h₁
    have hf : (stupidTruncιGE K e₁).f (e₂.f i₂) = 0 :=
      stupidTruncιGEF_of_not_mem K e₁ _ h₁
    change (ShortComplex.mk ((stupidTruncιGE K e₁).f (e₂.f i₂))
      ((stupidTruncπLE K e₂).f (e₂.f i₂)) (by rw [hf, zero_comp])).ShortExact
    refine
      { exact := (ShortComplex.exact_iff_mono _ hf).2 (by
          change Mono (stupidTruncπLEF K e₂ (e₂.f i₂))
          rw [stupidTruncπLEF_of_mem K e₂ rfl]
          infer_instance)
        mono_f := hz.mono _
        epi_g := by
          change Epi (stupidTruncπLEF K e₂ (e₂.f i₂))
          rw [stupidTruncπLEF_of_mem K e₂ rfl]
          infer_instance }

section DerivedFiltration

open ComplexShape
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

variable [HasDerivedCategory C]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  (T : ObjectProperty (DerivedCategory C)) [T.IsTriangulated]
  [T.IsClosedUnderIsomorphisms]

/-- Stupid truncation preserves any iso-closed property containing zero; support terms use their canonical isomorphisms and other terms are zero. -/
lemma prop_stupidTrunc_X (K : HomologicalComplex C c')
    (e : c.Embedding c') [e.IsRelIff] (hK : ∀ i, P (K.X i)) (i' : ι') :
    P ((K.stupidTrunc e).X i') := by
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi
    exact P.prop_of_iso (K.stupidTruncXIso e rfl).symm (hK _)
  · exact P.prop_of_isZero (K.isZero_stupidTrunc_X e i' (by simpa using hi))

/-- A complex supported in precisely one degree belongs to `T` when its term does; this is the base of the proved 066T induction. -/
lemma mem_Q_of_single (hsingle : ∀ (M : C) (n : ℤ), P M →
    T ((DerivedCategory.singleFunctor C n).obj M))
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] [K.IsStrictlyLE n]
    (hK : P (K.X n)) : T (DerivedCategory.Q.obj K) := by
  obtain ⟨M, ⟨e⟩⟩ := K.exists_iso_single n
  let eM : K.X n ≅ M := (HomologicalComplex.eval C (.up ℤ) n).mapIso e ≪≫
    HomologicalComplex.singleObjXSelf (.up ℤ) n M
  exact T.prop_of_iso (DerivedCategory.Q.mapIso e.symm) (hsingle M n (P.prop_of_iso eM hK))

/-- The stupid-truncation induction over a positive width. -/
theorem mem_Q_of_bounded_of_le
    (hsingle : ∀ (M : C) (n : ℤ), P M →
      T ((DerivedCategory.singleFunctor C n).obj M)) (a : ℤ) :
    ∀ (b : ℤ), a ≤ b → ∀ (K : CochainComplex C ℤ) [K.IsStrictlyGE a]
      [K.IsStrictlyLE b], (∀ n, P (K.X n)) → T (DerivedCategory.Q.obj K) := by
  intro b hab
  induction b, hab using Int.leInduction with
  | base =>
      intro K hGE hLE hK
      exact mem_Q_of_single P T hsingle K a (hK a)
  | succ b hab ih =>
      intro K hGE hLE hK
      let e₁ := ComplexShape.embeddingUpIntGE (b + 1)
      let e₂ := ComplexShape.embeddingUpIntLE b
      let ac : e₁.AreComplementary e₂ :=
        (ComplexShape.Embedding.embeddingUpInt_areComplementary b (b + 1) rfl).symm
      have hterms₁ : ∀ n, P ((K.stupidTrunc e₁).X n) :=
        fun n ↦ prop_stupidTrunc_X P K e₁ hK n
      have hterms₂ : ∀ n, P ((K.stupidTrunc e₂).X n) :=
        fun n ↦ prop_stupidTrunc_X P K e₂ hK n
      have h₁ : T (DerivedCategory.Q.obj (K.stupidTrunc e₁)) :=
        mem_Q_of_single P T hsingle (K.stupidTrunc e₁) (b + 1) (hterms₁ (b + 1))
      have h₂ : T (DerivedCategory.Q.obj (K.stupidTrunc e₂)) :=
        ih (K.stupidTrunc e₂) hterms₂
      exact T.ext_of_isTriangulatedClosed₂
        (DerivedCategory.triangleOfSES (stupidTruncShortComplex_shortExact K e₁ e₂ ac))
        (DerivedCategory.triangleOfSES_distinguished
          (stupidTruncShortComplex_shortExact K e₁ e₂ ac)) h₁ h₂

/-- A bounded complex belongs to `T` as soon as all its single terms do. -/
theorem mem_Q_of_bounded
    (hsingle : ∀ (M : C) (n : ℤ), P M →
      T ((DerivedCategory.singleFunctor C n).obj M))
    (K : CochainComplex C ℤ) (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ n, P (K.X n)) : T (DerivedCategory.Q.obj K) := by
  by_cases hab : a ≤ b
  · exact mem_Q_of_bounded_of_le P T hsingle a b hab K hK
  · have hzero : IsZero K := by
      rw [IsZero.iff_id_eq_zero]
      ext i
      by_cases hi : i < a
      · exact (K.isZero_of_isStrictlyGE a i hi).eq_of_src _ _
      · exact (K.isZero_of_isStrictlyLE b i (by omega)).eq_of_src _ _
    exact T.prop_of_isZero (DerivedCategory.Q.map_isZero hzero)

end DerivedFiltration

end

end BrutalFiltration

section BoundedProjectiveApplication

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- **Bounded finite-projective models are perfect (proved).**  The proof is
by stupid truncation.  No projective-resolution, compactness or Noetherian
input is used. -/
theorem boundedFiniteProjectiveModel_mem_perf
    (X : DerivedCategory (ModuleCat A)) (H : BoundedFiniteProjectiveModel A X) :
    Perf A X := by
  let P : ObjectProperty (ModuleCat A) := fun M ↦ Module.Finite A M ∧ Module.Projective A M
  letI : P.IsClosedUnderIsomorphisms :=
    { of_iso e h := by
        letI : Module.Finite A _ := h.1
        letI : Module.Projective A _ := h.2
        exact ⟨Module.Finite.equiv e.toLinearEquiv,
          Module.Projective.of_equiv' e.toLinearEquiv⟩ }
  letI : P.ContainsZero :=
    { exists_zero := ⟨0, isZero_zero _, by
      letI : Subsingleton (0 : ModuleCat A) :=
        ModuleCat.subsingleton_of_isZero (isZero_zero _)
      constructor
      · rw [Module.finite_def, show (⊤ : Submodule A (0 : ModuleCat A)) = ⊥ from
          (Submodule.eq_bot_iff _).2 (fun x _ ↦ Subsingleton.elim x 0)]
        exact Submodule.fg_bot
      · infer_instance⟩ }
  letI := H.isStrictlyGE
  letI := H.isStrictlyLE
  have hsingle : ∀ (M : ModuleCat A) (n : ℤ), P M →
      Perf A ((DerivedCategory.singleFunctor (ModuleCat A) n).obj M) := by
    intro M n h
    letI : Module.Finite A M := h.1
    letI : Module.Projective A M := h.2
    exact finiteProjective_single_mem_perf A M n
  have hQ : Perf A (DerivedCategory.Q.obj H.complex) :=
    mem_Q_of_bounded P (Perf A) hsingle H.complex H.lower H.upper
      (fun n ↦ ⟨H.finite n, H.projective n⟩)
  exact (Perf A).prop_of_iso H.iso.symm hQ

/-- Nonempty form of `boundedFiniteProjectiveModel_mem_perf`. -/
theorem model_mem_perf (X : DerivedCategory (ModuleCat A))
    (H : Nonempty (BoundedFiniteProjectiveModel A X)) : Perf A X := by
  obtain ⟨H⟩ := H
  exact boundedFiniteProjectiveModel_mem_perf A X H

/-- **Only the converse remains external.**  This is the `Perf ⇒ bounded
finite-projective model` part of Stacks 09M1, using the strict model of 0657
and the resolution/idempotent-completion arguments of 066R, 066S and 066T.
The opposite implication is proved above and is not duplicated as input. -/
structure BoundedProjectiveModelConverseInput (A : Type u) [CommRing A] where
  /-- Produce a bounded finite-projective representative of a perfect object. -/
  model_of_perf : ∀ X : DerivedCategory (ModuleCat A),
    Perf A X → Nonempty (BoundedFiniteProjectiveModel A X)

/-- The old `BoundedProjectiveModelInput` is now obtained from its converse
alone; the forward implication is filled by the proved filtration theorem. -/
theorem boundedProjectiveModelInput_of_converse (H : BoundedProjectiveModelConverseInput A) :
    BoundedProjectiveModelInput A where
  perf_iff_model X := ⟨H.model_of_perf X, model_mem_perf A X⟩

end BoundedProjectiveApplication

end AffinePerfect
end RelativeFM
