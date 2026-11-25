/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.AisleGenRingGeneration
import WeakApprox.CompactThick
import WeakApprox.GeneratorBridge
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The affine preferred `t`-structure and compact generation of its aisle

Neeman, *Bounded t-structures on the category of perfect complexes*, Acta
Math. 233 (2024), Definitions 2.6 and 2.9, Corollary 2.8 and Remark 2.11,
https://arxiv.org/html/2202.08861v4#S2 .

Two points are deliberately kept distinct:

* Neeman's generation is zero detection by shifts (`IsPaperGenerator` here).
  It is not the repository's stronger morphism-separation predicate
  `IsGenerator`.
* The preferred class consists of `t`-structures equivalent to one generated
  by a compact generator, where equivalence means bounded interposition of
  aisles.  It is not defined by a literal equality of aisles.

`ringObject_isPaperGenerator` proves ordinary generation for every commutative
ring, without compactness or Noetherian hypotheses.  The affine theorem
`standard_inPreferredClass` then has exactly one remaining input: compactness
of the regular module.  The independent theorem
`standard_le_zero_eq_coprod_compactInAisle` identifies the usual `Coprod`
presentation with the `Coprod`-closure of all compact objects in the standard
aisle, under that same compactness input.  Thus the two aisle formulations
agree; there is no counterexample.

The specialization is for `AffineD A`.  The general
`inPreferredClass_of_compactlyGenerated` applies verbatim to any other model
for which a standard-aisle identity is proved; this file does not assert such
an identity for `SmallAffineD`.
-/

@[expose] public section


namespace RelativeFM.NeemanPreferredM6

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe w v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A nonzero map from a projective object to a cohomology object gives a
nonzero morphism in the derived category from the corresponding single
complex. -/
lemma exists_nonzero_derivedHom_of_nonzero_homology_map
    {P : C} [Projective P] (K : CochainComplex C ℤ) (i : ℤ)
    (α : P ⟶ K.homology i) (hα : α ≠ 0) :
    ∃ f : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C i).obj P) ⟶
      DerivedCategory.Q.obj (K⟦(0 : ℤ)⟧), f ≠ 0 := by
  letI (n : ℤ) : Projective (((CochainComplex.singleFunctor C i).obj P).X n) := by
    change Projective (((HomologicalComplex.single C (ComplexShape.up ℤ) i).obj P).X n)
    infer_instance
  letI : ((CochainComplex.singleFunctor C i).obj P).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ i
  let z : P ⟶ K.cycles i := Projective.factorThru α (K.homologyπ i)
  let k : P ⟶ K.X i := z ≫ K.iCycles i
  have hk : k ≫ K.d i (i + 1) = 0 := by
    simp [k, Category.assoc]
  let c := CochainComplex.HomComplex.Cocycle.fromSingleMk k
    (show i + 0 = i by simp) (i + 1) rfl hk
  let x := CochainComplex.HomComplex.CohomologyClass.mk c
  refine ⟨DerivedCoproducts.derivedHomKProjectiveEquiv _ _ x.toHom, ?_⟩
  intro hf
  have hto : x.toHom = 0 := by
    apply (DerivedCoproducts.derivedHomKProjectiveEquiv
      ((CochainComplex.singleFunctor C i).obj P) (K⟦(0 : ℤ)⟧)).injective
    rw [hf]
    symm
    change DerivedCoproducts.derivedHomMap _ _ 0 = 0
    simp only [DerivedCoproducts.derivedHomMap, Functor.map_zero,
      Limits.zero_comp, Limits.comp_zero]
  have hx : x = 0 := by
    change CochainComplex.HomComplex.CohomologyClass.mk c = 0
    rw [CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff]
    exact (CochainComplex.HomComplex.CohomologyClass.toHom_mk_eq_zero_iff c).mp hto
  have hc : c ∈ CochainComplex.HomComplex.coboundaries _ _ _ :=
    (CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff c).mp hx
  dsimp only [c] at hc
  obtain ⟨g, hg⟩ :=
    (CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff
      (f := k) (p := i) (q := i) (n := 0) (h := by simp) (q' := i + 1)
      (hq' := rfl) (hf := hk) (q'' := i - 1) (by omega)).mp hc
  have hlift : K.liftCycles k (i + 1) (by simp) hk = z := by
    rw [← cancel_mono (K.iCycles i), K.liftCycles_i]
  have hlift0 : K.liftCycles k (i + 1) (by simp) hk ≫ K.homologyπ i = 0 :=
    K.liftCycles_homologyπ_eq_zero_of_boundary k (i + 1) (by simp) g hg.symm
  have hz : z ≫ K.homologyπ i = 0 := by
    rwa [← hlift]
  exact hα ((Projective.factorThru_comp α (K.homologyπ i)).symm.trans hz)

/-- Unshifted-target form of `exists_nonzero_derivedHom_of_nonzero_homology_map`. -/
lemma exists_nonzero_derivedHom_of_nonzero_homology_map'
    {P : C} [Projective P] (K : CochainComplex C ℤ) (i : ℤ)
    (α : P ⟶ K.homology i) (hα : α ≠ 0) :
    ∃ f : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C i).obj P) ⟶
      DerivedCategory.Q.obj K, f ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_nonzero_derivedHom_of_nonzero_homology_map K i α hα
  let e : DerivedCategory.Q.obj (K⟦(0 : ℤ)⟧) ≅ DerivedCategory.Q.obj K :=
    DerivedCategory.Q.mapIso ((shiftFunctorZero (CochainComplex C ℤ) ℤ).app K)
  refine ⟨f ≫ e.hom, ?_⟩
  intro h
  apply hf
  rw [← cancel_mono e.hom]
  simpa only [Limits.zero_comp] using h

end

section RingGenerator

variable (A : Type u) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- The regular module generates `D(A-Mod)` in Neeman's ordinary sense:
an object is zero as soon as every map into it from every shift of `A[0]`
vanishes. -/
theorem ringObject_isPaperGenerator : IsPaperGenerator (ringObject A) := by
  intro E hE
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hH : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj E) := by
    intro i
    rw [ModuleCat.isZero_iff_subsingleton]
    let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj E
    have hz : ∀ z : H, z = 0 := by
      intro z
      by_contra hnz
      let α : ModuleCat.of A A ⟶ H :=
        ModuleCat.ofHom (LinearMap.toSpanSingleton A H z)
      have hα : α ≠ 0 := by
        intro h
        have h1 := congrArg (fun φ : ModuleCat.of A A ⟶ H => φ.hom 1) h
        apply hnz
        simpa [α] using h1
      let eH : K.homology i ≅ H :=
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).symm.app K ≪≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eK
      obtain ⟨f, hf⟩ := exists_nonzero_derivedHom_of_nonzero_homology_map'
        K i (α ≫ eH.inv) (by
          intro hzero
          apply hα
          rw [← cancel_mono eH.inv]
          simpa using hzero)
      let s : ringObject A⟦-i⟧ ≅
          DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} A) i).obj
            (ModuleCat.of A A)) :=
        ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
          (-i) i 0 (by omega)).app (ModuleCat.of A A) ≪≫
          (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) i).app (ModuleCat.of A A)
      have hzero := hE (-i) (s.hom ≫ f ≫ eK.hom)
      have hzero' : s.hom ≫ f = 0 := by
        rw [← cancel_mono eK.hom]
        simpa only [Category.assoc, Limits.zero_comp] using hzero
      apply hf
      rw [← cancel_epi s.hom]
      simpa only [Limits.comp_zero] using hzero'
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  letI : E.IsLE 0 := (DerivedCategory.isLE_iff E 0).2 (fun i _ => hH i)
  letI : E.IsGE 1 := (DerivedCategory.isGE_iff E 1).2 (fun i _ => hH i)
  exact DerivedCategory.TStructure.t.isZero E 0 1 (by omega)

end RingGenerator

end RelativeFM.NeemanPreferredM6

#print axioms RelativeFM.NeemanPreferredM6.exists_nonzero_derivedHom_of_nonzero_homology_map
#print axioms RelativeFM.NeemanPreferredM6.exists_nonzero_derivedHom_of_nonzero_homology_map'
#print axioms RelativeFM.NeemanPreferredM6.ringObject_isPaperGenerator



namespace RelativeFM.NeemanPreferredM6

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Neeman, Definition 2.9: two `t`-structures are equivalent when their
aisles can be interposed with a uniform finite amplitude. -/
def TStructureEquivalent (t₁ t₂ : TStructure C) : Prop :=
  ∃ n : ℤ, 0 < n ∧ t₁.le (-n) ≤ t₂.le 0 ∧ t₂.le 0 ≤ t₁.le n

/-- Reflexivity of Neeman's equivalence of `t`-structures. -/
theorem tStructureEquivalent_refl (t : TStructure C) : TStructureEquivalent t t := by
  refine ⟨1, by omega, ?_, ?_⟩
  · simpa using (t.le_monotone (show (-1 : ℤ) ≤ 0 by omega))
  · simpa using (t.le_monotone (show (0 : ℤ) ≤ 1 by omega))

/-- Shift an inclusion of graded aisles. -/
lemma shift_aisle_inclusion {t₁ t₂ : TStructure C} {a b : ℤ}
    (h : t₁.le a ≤ t₂.le b) (s : ℤ) : t₁.le (a - s) ≤ t₂.le (b - s) := by
  intro X hX
  have hX' := t₁.le_shift (a - s) (-s) a (by omega) X hX
  have hY := h (X⟦-s⟧) hX'
  rwa [← t₂.shift_le (-s) b (b - s) (by omega)]

/-- Symmetry of Neeman's equivalence of `t`-structures. -/
theorem tStructureEquivalent_symm {t₁ t₂ : TStructure C}
    (h : TStructureEquivalent t₁ t₂) : TStructureEquivalent t₂ t₁ := by
  obtain ⟨n, hn, h₁, h₂⟩ := h
  refine ⟨n, hn, ?_, ?_⟩
  · simpa using shift_aisle_inclusion h₂ n
  · simpa using shift_aisle_inclusion h₁ (-n)

/-- Transitivity of Neeman's equivalence of `t`-structures. -/
theorem tStructureEquivalent_trans {t₁ t₂ t₃ : TStructure C}
    (h₁₂ : TStructureEquivalent t₁ t₂) (h₂₃ : TStructureEquivalent t₂ t₃) :
    TStructureEquivalent t₁ t₃ := by
  obtain ⟨n, hn, h₁₂₁, h₁₂₂⟩ := h₁₂
  obtain ⟨m, hm, h₂₃₁, h₂₃₂⟩ := h₂₃
  refine ⟨n + m, by omega, ?_, ?_⟩
  · have hshift := shift_aisle_inclusion h₁₂₁ m
    rw [zero_sub] at hshift
    simpa only [show (-(n + m) : ℤ) = -n - m by omega] using
      hshift.trans h₂₃₁
  have h₂₃₂' := h₂₃₂
  have h₁₂₂' := shift_aisle_inclusion h₁₂₂ (-m)
  rw [show 0 - -m = m by omega, show n - -m = n + m by omega] at h₁₂₂'
  exact h₂₃₂'.trans h₁₂₂'

/-- Membership in the preferred equivalence class.  The existential compact
generator is intentional: Neeman's Remark 2.11 subsequently proves that the
choice does not matter.  The generated `t`-structure is supplied explicitly,
so no separate Alonso--Jeremías--Souto existence theorem is assumed. -/
def InPreferredClass (t : TStructure C) : Prop :=
  ∃ (G : C) (tG : TStructure C), IsCompactAb G ∧ IsPaperGenerator G ∧
    tG.le 0 = Coprod (shiftTail G 0) ∧ TStructureEquivalent t tG

/-- A compactly generated `t`-structure is preferred as soon as its generator
is compact and detects zero in Neeman's sense. -/
theorem inPreferredClass_of_compactlyGenerated (t : TStructure C) (G : C)
    (hGc : IsCompactAb G) (hGg : IsPaperGenerator G)
    (hgen : t.le 0 = Coprod (shiftTail G 0)) : InPreferredClass t :=
  ⟨G, t, hGc, hGg, hgen, tStructureEquivalent_refl t⟩

/-- The compact objects lying in an aisle. -/
def compactInAisle (t : TStructure C) : ObjectProperty C :=
  compactObjectProperty C ⊓ t.le 0

/-- The single-generator and all-compact-generators descriptions of an aisle
agree.  No compact/perfect comparison and no classical-generation theorem is
needed: compactness of the displayed generator and its shifts suffices. -/
theorem le_zero_eq_coprod_compactInAisle (t : TStructure C) (G : C)
    (hGc : IsCompactAb G) (hgen : t.le 0 = Coprod (shiftTail G 0)) :
    t.le 0 = Coprod (compactInAisle t) := by
  letI (J : Type v) : (t.le 0).IsClosedUnderColimitsOfShape (Discrete J) :=
    TStructure.le_isClosedUnderColimitsOfShape t 0 (Discrete J)
  letI : (t.le 0).IsTriangulatedClosed₂ :=
    TStructure.le_isTriangulatedClosed₂ t 0
  apply le_antisymm
  · rw [hgen]
    apply Coprod_mono
    rintro X ⟨n, hn, ⟨e⟩⟩
    refine ⟨isCompactAb_of_iso e.symm (isCompactAb_shift G n hGc), ?_⟩
    rw [hgen]
    exact Coprod.of_mem X ⟨n, hn, ⟨e⟩⟩
  · apply Coprod.le
    exact fun _ hX => hX.2

/-- Retracts preserve an aisle bound. -/
lemma isLE_of_retract' (t : TStructure C) {X Y : C} (r : Retract X Y)
    (n : ℤ) (hY : t.IsLE Y n) : t.IsLE X n := by
  rw [t.isLE_iff_orthogonal n (n + 1) rfl]
  intro Z f hZ
  letI := hY
  letI := hZ
  calc
    f = 𝟙 X ≫ f := (Category.id_comp f).symm
    _ = (r.i ≫ r.r) ≫ f := by rw [r.retract]
    _ = r.i ≫ (r.r ≫ f) := Category.assoc _ _ _
    _ = 0 := by rw [t.zero (r.r ≫ f) n (n + 1) (by omega), comp_zero]

/-- The bounded-above objects of a `t`-structure are closed under retracts. -/
instance minus_isStableUnderRetracts (t : TStructure C) :
    t.minus.IsStableUnderRetracts where
  of_retract r hY := by
    obtain ⟨n, hn⟩ := hY
    exact ⟨n, isLE_of_retract' t r n hn⟩

/-- A generator of the degree-zero aisle is bounded above. -/
lemma generator_mem_minus (t : TStructure C) (G : C)
    (hgen : t.le 0 = Coprod (shiftTail G 0)) : t.minus G := by
  refine ⟨0, ⟨?_⟩⟩
  rw [hgen]
  exact Coprod.of_mem G ⟨0, le_rfl, ⟨(shiftFunctorZero C ℤ).symm.app G⟩⟩

/-- Every object in the finite thick envelope of the generator is bounded
above for its generated `t`-structure. -/
lemma triangEnvelope_singleton_le_minus (t : TStructure C) (G : C)
    (hgen : t.le 0 = Coprod (shiftTail G 0)) :
    (ObjectProperty.singleton G).triangEnvelope ≤ t.minus := by
  rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
  exact generator_mem_minus t G hgen

/-- Finite thick generation on compacts yields a positive aisle bound. -/
lemma exists_positive_le_of_isClassicalGeneratorOnCompacts
    (t : TStructure C) (G H : C) (hgen : t.le 0 = Coprod (shiftTail G 0))
    (hG : IsClassicalGeneratorOnCompacts G) (hH : IsCompactAb H) :
    ∃ n : ℤ, 0 < n ∧ t.le n H := by
  obtain ⟨n, hn⟩ := triangEnvelope_singleton_le_minus t G hgen _ (hG H hH)
  exact ⟨max n 1, lt_max_of_lt_right (by omega),
    t.le_monotone (le_max_left _ _) _ hn.le⟩

/-- If a compact generator has an upper bound, its whole generated aisle has
that same bound. -/
lemma coprod_shiftTail_le_le (t : TStructure C) (G : C) (n : ℤ)
    (hG : t.le n G) : Coprod (shiftTail G 0) ≤ t.le n := by
  letI (J : Type v) : (t.le n).IsClosedUnderColimitsOfShape (Discrete J) :=
    TStructure.le_isClosedUnderColimitsOfShape t n (Discrete J)
  letI : (t.le n).IsTriangulatedClosed₂ :=
    TStructure.le_isTriangulatedClosed₂ t n
  apply Coprod.le
  rintro X ⟨m, hm, ⟨e⟩⟩
  have hshift := t.le_shift n m (n - m) (by omega) G hG
  exact (t.le n).prop_of_iso e.symm (t.le_monotone (by omega) _ hshift)

/-- Neeman's Lemma 2.7 in generated-aisle form: finite thick generation of a
compact object gives a uniform bound for the other generated aisle. -/
lemma exists_positive_generated_aisle_bound
    (tG : TStructure C) (tH : TStructure C) (G H : C)
    (hgenG : tG.le 0 = Coprod (shiftTail G 0))
    (hgenH : tH.le 0 = Coprod (shiftTail H 0))
    (hG : IsClassicalGeneratorOnCompacts G) (hH : IsCompactAb H) :
    ∃ n : ℤ, 0 < n ∧ tH.le 0 ≤ tG.le n := by
  obtain ⟨n, hn, hbound⟩ :=
    exists_positive_le_of_isClassicalGeneratorOnCompacts tG G H hgenG hG hH
  exact ⟨n, hn, hgenH ▸ coprod_shiftTail_le_le tG H n hbound⟩

/-- Neeman's Corollary 2.8, with Ravenel--Neeman finite generation on compacts
kept as the explicit `IsClassicalGeneratorOnCompacts` input rather than
silently assumed. -/
theorem tStructureEquivalent_of_isClassicalGeneratorOnCompacts
    (tG tH : TStructure C) (G H : C)
    (hgenG : tG.le 0 = Coprod (shiftTail G 0))
    (hgenH : tH.le 0 = Coprod (shiftTail H 0))
    (hG : IsClassicalGeneratorOnCompacts G) (hHgen : IsClassicalGeneratorOnCompacts H)
    (hGc : IsCompactAb G) (hHc : IsCompactAb H) : TStructureEquivalent tG tH := by
  obtain ⟨n, hn, hH_bound⟩ :=
    exists_positive_generated_aisle_bound tG tH G H hgenG hgenH hG hHc
  obtain ⟨m, hm, hG_bound⟩ :=
    exists_positive_generated_aisle_bound tH tG H G hgenH hgenG hHgen hGc
  let N := max n m
  have hleft : tG.le (-m) ≤ tH.le 0 := by
    simpa using shift_aisle_inclusion hG_bound m
  refine ⟨N, by dsimp [N]; omega, ?_, hH_bound.trans
    (tG.le_monotone (by dsimp [N]; omega))⟩
  exact (tG.le_monotone (show -N ≤ -m by dsimp [N]; omega)).trans hleft

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Affine comparison of the two aisles: the standard aisle is both the
`Coprod`-closure of the regular module's tail and of every compact object it
contains. -/
theorem standard_le_zero_eq_coprod_compactInAisle (A : Type u) [CommRing A]
    (hA : IsCompactAb (ringObject A)) :
    (AffineD.standardTStructure A).le 0 =
      Coprod (compactInAisle (AffineD.standardTStructure A)) :=
  le_zero_eq_coprod_compactInAisle _ _ hA
    (AisleGeneration.Ring.standard_le_zero_eq_coprod A)

/-- Neeman 3.2(iii), affine form, modulo exactly compactness of `A[0]`.
Ordinary zero-detection generation is proved in this module. -/
theorem standard_inPreferredClass (A : Type u) [CommRing A]
    (hAc : IsCompactAb (ringObject A)) :
    InPreferredClass (AffineD.standardTStructure A) :=
  inPreferredClass_of_compactlyGenerated _ _ hAc (ringObject_isPaperGenerator A)
    (AisleGeneration.Ring.standard_le_zero_eq_coprod A)

end

end RelativeFM.NeemanPreferredM6

#print axioms RelativeFM.NeemanPreferredM6.tStructureEquivalent_refl
#print axioms RelativeFM.NeemanPreferredM6.inPreferredClass_of_compactlyGenerated
#print axioms RelativeFM.NeemanPreferredM6.le_zero_eq_coprod_compactInAisle
#print axioms RelativeFM.NeemanPreferredM6.standard_le_zero_eq_coprod_compactInAisle
#print axioms RelativeFM.NeemanPreferredM6.standard_inPreferredClass

#print axioms RelativeFM.NeemanPreferredM6.tStructureEquivalent_symm
#print axioms RelativeFM.NeemanPreferredM6.tStructureEquivalent_trans
#print axioms RelativeFM.NeemanPreferredM6.tStructureEquivalent_of_isClassicalGeneratorOnCompacts
