import FourierMukai.Scheme.CompactToPerfect
import FourierMukai.Scheme.AffineSpaltenstein
import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Compact objects are bounded above

This module supplies the exact-coproduct and canonical-truncation steps in the
first paragraph of Stacks 07LT. All declarations are in the member-specific
namespace `RelativeFM.Stacks07LT.BoundedAboveM1`.
-/

@[expose] public section

namespace RelativeFM.Stacks07LT.BoundedAboveM1

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeFM RelativeFM.DerivedCoproducts
open RelativeWeakApprox
open CochainComplex

universe w w' v u uA
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {J : Type w} [Category.{w'} J]

/-- Exact colimits preserve quasi-isomorphisms of short complexes. -/
lemma quasiIso_colim_mapShortComplex_of_exact
    {D : Type u} [Category.{v} D] [Abelian D]
    [HasColimitsOfShape J D] [HasExactColimitsOfShape J D]
    {S₁ S₂ : J ⥤ ShortComplex D} (φ : S₁ ⟶ S₂)
    [∀ j, ShortComplex.QuasiIso (φ.app j)] :
    ShortComplex.QuasiIso
      ((CategoryTheory.Functor.mapShortComplex (colim : (J ⥤ D) ⥤ D)).map
        ((ShortComplex.FunctorEquivalence.inverse J D).map φ)) := by
  let E := ShortComplex.FunctorEquivalence.inverse J D
  letI : ShortComplex.QuasiIso (E.map φ) :=
    (ShortComplex.quasiIso_iff_evaluation _).2 (fun j => by
      change ShortComplex.QuasiIso (φ.app j)
      infer_instance)
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology
    (colim : (J ⥤ D) ⥤ D) (E.map φ)

/-- Exact colimits of arbitrary shape preserve quasi-isomorphisms of cochain
complexes. This generalizes `Spaltenstein.quasiIso_colim_map_of_exact` from
sequential colimits to coproducts. -/
lemma quasiIso_colim_map_of_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    {F G : J ⥤ CochainComplex C ℤ} (α : F ⟶ G)
    [∀ j, QuasiIso (α.app j)] : QuasiIso (colim.map α) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff]
  letI (j : J) : ShortComplex.QuasiIso ((whiskerRight α
      (HomologicalComplex.shortComplexFunctor C _ i)).app j) := by
    change ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor C _ i).map (α.app j))
    rw [← quasiIsoAt_iff]
    infer_instance
  have hC := quasiIso_colim_mapShortComplex_of_exact (whiskerRight α
    (HomologicalComplex.shortComplexFunctor C _ i))
  let e (H : J ⥤ ShortComplex C) :
      ((ShortComplex.FunctorEquivalence.inverse J C).obj H).map
        (colim : (J ⥤ C) ⥤ C) ≅ colimit H :=
    ShortComplex.isoMk
      (preservesColimitIso ShortComplex.π₁ H).symm
      (preservesColimitIso ShortComplex.π₂ H).symm
      (preservesColimitIso ShortComplex.π₃ H).symm
      (by apply colimit.hom_ext; intro j
          simpa using (colimit.ι H j).comm₁₂)
      (by apply colimit.hom_ext; intro j
          simpa using (colimit.ι H j).comm₂₃)
  letI : ShortComplex.QuasiIso
      ((CategoryTheory.Functor.mapShortComplex
        (colim : (J ⥤ C) ⥤ C)).map
        ((ShortComplex.FunctorEquivalence.inverse J C).map
          (whiskerRight α (HomologicalComplex.shortComplexFunctor C _ i)))) := hC
  have hB : ShortComplex.QuasiIso (colim.map (whiskerRight α
      (HomologicalComplex.shortComplexFunctor C _ i))) := by
    apply ShortComplex.quasiIso_of_arrow_mk_iso
      ((CategoryTheory.Functor.mapShortComplex
        (colim : (J ⥤ C) ⥤ C)).map
        ((ShortComplex.FunctorEquivalence.inverse J C).map
          (whiskerRight α (HomologicalComplex.shortComplexFunctor C _ i))))
      (colim.map (whiskerRight α
        (HomologicalComplex.shortComplexFunctor C _ i)))
    exact Arrow.isoMk (e _) (e _) (by
      ext <;> apply colimit.hom_ext <;> intro j
      · simp [e]
        exact congrArg (fun k => k.τ₁) (colimit.ι_map
          (whiskerRight α (HomologicalComplex.shortComplexFunctor C _ i)) j)
      · simp [e]
        exact congrArg (fun k => k.τ₂) (colimit.ι_map
          (whiskerRight α (HomologicalComplex.shortComplexFunctor C _ i)) j)
      · simp [e]
        exact congrArg (fun k => k.τ₃) (colimit.ι_map
          (whiskerRight α (HomologicalComplex.shortComplexFunctor C _ i)) j))
  letI : ShortComplex.QuasiIso (colim.map (whiskerRight α
      (HomologicalComplex.shortComplexFunctor C _ i))) := hB
  apply ShortComplex.quasiIso_of_arrow_mk_iso
    (colim.map (whiskerRight α
      (HomologicalComplex.shortComplexFunctor C _ i)))
    ((HomologicalComplex.shortComplexFunctor C _ i).map (colim.map α))
  exact (Arrow.isoOfNatIso (preservesColimitNatIso
    (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i))
    (Arrow.mk α)).symm

/-- The degreewise coproduct cocone after applying the localization functor. -/
noncomputable abbrev qCoproductCofan
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    {ι : Type w} [HasCoproductsOfShape ι C]
    (F : ι → CochainComplex C ℤ) : Cofan (fun i => DerivedCategory.Q.obj (F i)) :=
  Cofan.mk (DerivedCategory.Q.obj (coproductComplexCocone F).pt)
    (fun i => DerivedCategory.Q.map ((coproductComplexCocone F).ι.app ⟨i⟩))

/-- The chain-level coproduct of a family of maps. -/
noncomputable def coproductComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [HasCoproductsOfShape ι C]
    {R F : ι → CochainComplex C ℤ} (f : ∀ i, R i ⟶ F i) :
    (coproductComplexCocone R).pt ⟶ (coproductComplexCocone F).pt :=
  (coproductComplexCoconeIsColimit R).desc
    (Cofan.mk (coproductComplexCocone F).pt
      (fun i => f i ≫ (coproductComplexCocone F).ι.app ⟨i⟩))

@[simp, reassoc]
lemma coproductComplexInj_comp_map
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [HasCoproductsOfShape ι C]
    {R F : ι → CochainComplex C ℤ} (f : ∀ i, R i ⟶ F i) (i : ι) :
    (coproductComplexCocone R).ι.app ⟨i⟩ ≫ coproductComplexMap f =
      f i ≫ (coproductComplexCocone F).ι.app ⟨i⟩ :=
  (coproductComplexCoconeIsColimit R).fac _ ⟨i⟩

/-- Exact coproducts preserve a family of quasi-isomorphisms. -/
lemma quasiIso_coproductComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [HasCoproductsOfShape ι C]
    [HasExactColimitsOfShape (Discrete ι) C]
    {R F : ι → CochainComplex C ℤ} (f : ∀ i, R i ⟶ F i)
    [∀ i, QuasiIso (f i)] : QuasiIso (coproductComplexMap f) := by
  let α : Discrete.functor R ⟶ Discrete.functor F :=
    Discrete.natTrans (fun i => f i.as)
  let eR := IsColimit.coconePointUniqueUpToIso
    (coproductComplexCoconeIsColimit R) (colimit.isColimit (Discrete.functor R))
  let eF := IsColimit.coconePointUniqueUpToIso
    (coproductComplexCoconeIsColimit F) (colimit.isColimit (Discrete.functor F))
  letI (j : Discrete ι) : QuasiIso (α.app j) := by
    dsimp [α]
    infer_instance
  letI : QuasiIso (colim.map α) := quasiIso_colim_map_of_exact α
  apply quasiIso_of_arrow_mk_iso (colim.map α) (coproductComplexMap f)
  exact (Arrow.isoMk eR eF (by
    apply (coproductComplexCoconeIsColimit R).hom_ext
    intro i
    calc
      (coproductComplexCocone R).ι.app i ≫ eR.hom ≫ colim.map α =
          colimit.ι (Discrete.functor R) i ≫ colim.map α := by
        rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]
        rfl
      _ = α.app i ≫ colimit.ι (Discrete.functor F) i := colimit.ι_map α i
      _ = f i.as ≫ (coproductComplexCocone F).ι.app i ≫ eF.hom := by
        rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
        rfl
      _ = (coproductComplexCocone R).ι.app i ≫ coproductComplexMap f ≫ eF.hom := by
        rw [coproductComplexInj_comp_map_assoc])).symm

/-- If arbitrary coproducts are exact, the degreewise coproduct of complexes
also computes their coproduct in the derived category. The proof transports
`derivedCoproductCofanIsColimit` along chosen K-projective quasi-isomorphic
resolutions. -/
noncomputable def qCoproductCofanIsColimit_of_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    {ι : Type w} [HasCoproductsOfShape ι C]
    [HasExactColimitsOfShape (Discrete ι) C]
    (R F : ι → CochainComplex C ℤ) (f : ∀ i, R i ⟶ F i)
    [∀ i, (R i).IsKProjective] [∀ i, QuasiIso (f i)] :
    IsColimit (qCoproductCofan F) := by
  letI : QuasiIso (coproductComplexMap f) := quasiIso_coproductComplexMap f
  let α : Discrete.functor (fun i => DerivedCategory.Q.obj (R i)) ≅
      Discrete.functor (fun i => DerivedCategory.Q.obj (F i)) :=
    Discrete.natIso (fun i => asIso (DerivedCategory.Q.map (f i.as)))
  let e : DerivedCategory.Q.obj (coproductComplexCocone R).pt ≅
      DerivedCategory.Q.obj (coproductComplexCocone F).pt :=
    asIso (DerivedCategory.Q.map (coproductComplexMap f))
  apply (IsColimit.equivOfNatIsoOfIso α (derivedCoproductCofan R)
    (qCoproductCofan F) ?_) (derivedCoproductCofanIsColimit R)
  exact Cocone.ext e (fun j => by
    dsimp [α, e, qCoproductCofan]
    rw [Category.assoc, ← DerivedCategory.Q.map_comp,
      coproductComplexInj_comp_map, DerivedCategory.Q.map_comp]
    simp)

section TruncationDiagonal

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical lower truncations indexed by the naturals. -/
noncomputable abbrev truncGEFamily (K : CochainComplex C ℤ) : ℕ → CochainComplex C ℤ :=
  fun n => K.truncGE (n : ℤ)

/-- One matrix entry of the canonical-truncation diagonal. -/
noncomputable def truncationDiagonalEntry [HasCoproductsOfShape ℕ C]
    (K : CochainComplex C ℤ) (n : ℕ) (i : ℤ) :
    K.X i ⟶ (coproductComplexCocone (truncGEFamily K)).pt.X i :=
  (K.πTruncGE (n : ℤ)).f i ≫
    ((coproductComplexCocone (truncGEFamily K)).ι.app ⟨n⟩).f i

lemma truncationDiagonalEntry_eq_zero_of_lt [HasCoproductsOfShape ℕ C]
    (K : CochainComplex C ℤ) {n : ℕ} {i : ℤ} (hin : i < (n : ℤ)) :
    truncationDiagonalEntry K n i = 0 := by
  have hz : IsZero ((K.truncGE (n : ℤ)).X i) :=
    (K.truncGE (n : ℤ)).isZero_of_isStrictlyGE (n : ℤ) i hin
  rw [truncationDiagonalEntry, hz.eq_of_tgt ((K.πTruncGE (n : ℤ)).f i) 0, zero_comp]

lemma truncationDiagonalEntry_eq_zero_of_natAbs_lt [HasCoproductsOfShape ℕ C]
    (K : CochainComplex C ℤ) {n : ℕ} {i : ℤ} (hin : i.natAbs < n) :
    truncationDiagonalEntry K n i = 0 := by
  apply truncationDiagonalEntry_eq_zero_of_lt
  have hn : (i.natAbs : ℤ) < (n : ℤ) := by exact_mod_cast hin
  have hi := Int.le_natAbs (a := i)
  omega

lemma truncationDiagonal_sum_extend [HasCoproductsOfShape ℕ C]
    (K : CochainComplex C ℤ) (i : ℤ) (N : ℕ) (hN : i.natAbs < N) :
    (∑ n ∈ Finset.range (i.natAbs + 1), truncationDiagonalEntry K n i) =
      ∑ n ∈ Finset.range N, truncationDiagonalEntry K n i := by
  apply Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_of_lt hN))
  intro n hnN hn
  simp only [Finset.mem_range] at hnN hn
  exact truncationDiagonalEntry_eq_zero_of_natAbs_lt K (by omega)

/-- The projection from a coproduct of complexes onto one summand. -/
noncomputable def natCoproductProjection [HasCoproductsOfShape ℕ C]
    (F : ℕ → CochainComplex C ℤ) (n : ℕ) :
    (coproductComplexCocone F).pt ⟶ F n :=
  (coproductComplexCoconeIsColimit F).desc
    (Cofan.mk (F n) (fun k => if h : k = n then eqToHom (congrArg F h) else 0))

@[simp]
lemma natCoproductProjection_inj [HasCoproductsOfShape ℕ C]
    (F : ℕ → CochainComplex C ℤ) (n k : ℕ) :
    (coproductComplexCocone F).ι.app ⟨k⟩ ≫ natCoproductProjection F n =
      if h : k = n then eqToHom (congrArg F h) else 0 :=
  (coproductComplexCoconeIsColimit F).fac _ ⟨k⟩

lemma truncationDiagonalEntry_comm [HasCoproductsOfShape ℕ C]
    (K : CochainComplex C ℤ) (n : ℕ) (i j : ℤ) :
    truncationDiagonalEntry K n i ≫ (coproductComplexCocone (truncGEFamily K)).pt.d i j =
      K.d i j ≫ truncationDiagonalEntry K n j :=
  ((K.πTruncGE (n : ℤ)) ≫
    (coproductComplexCocone (truncGEFamily K)).ι.app ⟨n⟩).comm i j

/-- The map `K → ⊕ₙ τ_≥n K`. At each degree the sum is finite since
`τ_≥n K` is zero below `n`. -/
noncomputable def truncationDiagonal [HasCoproductsOfShape ℕ C]
    (K : CochainComplex C ℤ) :
    K ⟶ (coproductComplexCocone (truncGEFamily K)).pt where
  f i := ∑ n ∈ Finset.range (i.natAbs + 1), truncationDiagonalEntry K n i
  comm' i j _ := by
    let N := i.natAbs + j.natAbs + 1
    change (∑ n ∈ Finset.range (i.natAbs + 1), truncationDiagonalEntry K n i) ≫
      (coproductComplexCocone (truncGEFamily K)).pt.d i j =
        K.d i j ≫ ∑ n ∈ Finset.range (j.natAbs + 1), truncationDiagonalEntry K n j
    rw [truncationDiagonal_sum_extend K i N (by omega),
      truncationDiagonal_sum_extend K j N (by omega)]
    simp only [Preadditive.sum_comp, Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact truncationDiagonalEntry_comm K n i j


lemma truncationDiagonalEntry_comp_projection [HasCoproductsOfShape ℕ C]
    (K : CochainComplex C ℤ) (n k : ℕ) (i : ℤ) :
    truncationDiagonalEntry K k i ≫ (natCoproductProjection (truncGEFamily K) n).f i =
      if k = n then (K.πTruncGE (n : ℤ)).f i else 0 := by
  rw [truncationDiagonalEntry, Category.assoc, ← HomologicalComplex.comp_f,
    natCoproductProjection_inj]
  split_ifs with h
  · subst k
    simp
  · simp

/-- Every component of the truncation diagonal is the canonical truncation
map. -/
lemma truncationDiagonal_comp_projection [HasCoproductsOfShape ℕ C]
    (K : CochainComplex C ℤ) (n : ℕ) :
    truncationDiagonal K ≫ natCoproductProjection (truncGEFamily K) n =
      K.πTruncGE (n : ℤ) := by
  ext i
  change (∑ k ∈ Finset.range (i.natAbs + 1), truncationDiagonalEntry K k i) ≫
    (natCoproductProjection (truncGEFamily K) n).f i = (K.πTruncGE (n : ℤ)).f i
  simp only [Preadditive.sum_comp, truncationDiagonalEntry_comp_projection]
  rw [Finset.sum_ite_eq']
  by_cases hn : n ∈ Finset.range (i.natAbs + 1)
  · simp [hn]
  · have hn₀ : i.natAbs + 1 ≤ n := by
      simpa only [Finset.mem_range, not_lt] using hn
    have hn' : i.natAbs < n := by omega
    have hz : IsZero ((K.truncGE (n : ℤ)).X i) :=
      (K.truncGE (n : ℤ)).isZero_of_isStrictlyGE (n : ℤ) i
        (lt_of_le_of_lt Int.le_natAbs (by exact_mod_cast hn'))
    simp [hn, hz.eq_of_tgt ((K.πTruncGE (n : ℤ)).f i) 0]

end TruncationDiagonal

section SpaltensteinResolution

/-- A K-projective resolution with its chain-level quasi-isomorphism exposed. -/
structure QuasiIsoKProjectiveResolution
    {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℤ) where
  complex : CochainComplex C ℤ
  isKProjective : complex.IsKProjective
  π : complex ⟶ K
  quasiIso : QuasiIso π

open RelativeFM.Spaltenstein

/-- Spaltenstein's constructed resolution, retaining the comparison at chain
level rather than only its isomorphism after localization. -/
noncomputable def spaltensteinResolution
    {C : Type u} [Category.{v} C] [Abelian C]
    [EnoughProjectives C] [HasDerivedCategory C]
    [HasColimitsOfShape ℕ C] [HasCoproductsOfShape ℕ C]
    [HasExactColimitsOfShape ℕ C]
    (H : TheoremCInput C) (K : CochainComplex C ℤ) :
    QuasiIsoKProjectiveResolution K := by
  let F := canonicalFiltration (H.canonicalTruncation K)
  letI : QuasiIso (filteredColimitMap F) :=
    quasiIso_filteredColimitMap F H.exactSequentialColimit
  letI : QuasiIso (filtrationColimitToA F) := by
    dsimp [F]
    exact H.quasiIso_colimitToA K
  exact
    { complex := colimit (filteredResolutionDiagram F)
      isKProjective := isKProjective_filteredColimit F
      π := filteredColimitMap F ≫ filtrationColimitToA F
      quasiIso := inferInstance }

attribute [local instance] HasDerivedCategory.standard

/-- The unconditional affine form of `spaltensteinResolution`. -/
noncomputable def affineSpaltensteinResolution (A : Type uA) [CommRing A]
    (K : CochainComplex (ModuleCat.{uA} A) ℤ) :
    QuasiIsoKProjectiveResolution K := by
  letI : AB5OfSize.{0, 0} (ModuleCat.{uA} A) :=
    AB5OfSize_of_univLE (ModuleCat.{uA} A)
  exact spaltensteinResolution (theoremCInput (C := ModuleCat.{uA} A)) K

/-- A zero canonical lower-truncation map forces a complex to be bounded
above in the derived category. -/
lemma exists_isLE_Q_obj_of_piTruncGE_eq_zero
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (n : ℤ)
    (hzero : DerivedCategory.Q.map (K.πTruncGE n) = 0) :
    ∃ m : ℤ, DerivedCategory.IsLE (DerivedCategory.Q.obj K) m := by
  let c := K.shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega)
  let hS := K.shortComplexTruncLE_shortExact (n - 1)
  letI : IsIso (DerivedCategory.Q.map c) := by
    dsimp [c]
    infer_instance
  have hg : DerivedCategory.Q.map ((K.shortComplexTruncLE (n - 1)).g) = 0 := by
    rw [← cancel_mono (DerivedCategory.Q.map c), ← DerivedCategory.Q.map_comp,
      K.g_shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega), hzero]
    simp
  obtain ⟨r, hr⟩ := Triangle.coyoneda_exact₂
    (DerivedCategory.triangleOfSES hS)
    (DerivedCategory.triangleOfSES_distinguished hS)
    (𝟙 (DerivedCategory.Q.obj K)) (by
      change 𝟙 (DerivedCategory.Q.obj K) ≫
        DerivedCategory.Q.map ((K.shortComplexTruncLE (n - 1)).g) = 0
      rw [hg, comp_zero])
  let s : Retract (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj (K.truncLE (n - 1))) :=
    { i := r
      r := DerivedCategory.Q.map (K.ιTruncLE (n - 1))
      retract := hr.symm }
  exact ⟨n - 1, RelativeFM.Stacks07LT.isLE_of_retract DerivedCategory.TStructure.t
    s (n - 1) inferInstance⟩

/-- The canonical truncations of a module complex have their degreewise
coproduct as a derived coproduct, with no large module-coproduct hypothesis. -/
noncomputable def affineTruncationCoproductIsColimit (A : Type uA) [CommRing A]
    (K : CochainComplex (ModuleCat.{uA} A) ℤ) :
    IsColimit (qCoproductCofan (truncGEFamily K)) := by
  let R := fun n => (affineSpaltensteinResolution A (truncGEFamily K n)).complex
  let f := fun n => (affineSpaltensteinResolution A (truncGEFamily K n)).π
  letI (n : ℕ) : (R n).IsKProjective := by
    dsimp [R]
    exact (affineSpaltensteinResolution A (truncGEFamily K n)).isKProjective
  letI (n : ℕ) : QuasiIso (f n) := by
    dsimp [f]
    exact (affineSpaltensteinResolution A (truncGEFamily K n)).quasiIso
  exact qCoproductCofanIsColimit_of_quasiIso R (truncGEFamily K) f

end SpaltensteinResolution

section AffineCompact

attribute [local instance] HasDerivedCategory.standard

/-- Compactness makes some canonical lower-truncation map zero. -/
theorem exists_piTruncGE_eq_zero_of_isCompactAb (A : Type uA) [CommRing A]
    (K : CochainComplex (ModuleCat.{uA} A) ℤ)
    (hK : IsCompactAb (DerivedCategory.Q.obj K)) :
    ∃ n : ℕ, DerivedCategory.Q.map (K.πTruncGE (n : ℤ)) = 0 := by
  let S := coproductComplexCocone (truncGEFamily K)
  let pres : ColimitPresentation (Discrete ℕ) (DerivedCategory.Q.obj S.pt) :=
    { diag := Discrete.functor (fun n => DerivedCategory.Q.obj (truncGEFamily K n))
      ι := (qCoproductCofan (truncGEFamily K)).ι
      isColimit := affineTruncationCoproductIsColimit A K }
  let presU : ColimitPresentation (Discrete (ULift.{uA + 1} ℕ))
      (DerivedCategory.Q.obj S.pt) :=
    pres.reindex (Discrete.equivalence Equiv.ulift).functor
  let g : ∀ n : ULift.{uA + 1} ℕ,
      DerivedCategory.Q.obj (truncGEFamily K n.down) ⟶ DerivedCategory.Q.obj S.pt :=
    fun n => DerivedCategory.Q.map (S.ι.app ⟨n.down⟩)
  have hg : IsColimit (Cofan.mk (DerivedCategory.Q.obj S.pt) g) := by
    exact presU.isColimit
  obtain ⟨n, hn⟩ := RelativeFM.Stacks07LT.exists_comp_coproductProjection_eq_zero
    (J := ULift.{uA + 1} ℕ) hK
    (fun n : ULift.{uA + 1} ℕ => DerivedCategory.Q.obj (truncGEFamily K n.down))
    g hg (DerivedCategory.Q.map (truncationDiagonal K))
  have hp : RelativeWeakApprox.coproductProjection g hg n =
      DerivedCategory.Q.map (natCoproductProjection (truncGEFamily K) n.down) := by
    apply hg.hom_ext
    intro j
    change g j.as ≫ RelativeWeakApprox.coproductProjection g hg n =
      g j.as ≫ DerivedCategory.Q.map (natCoproductProjection (truncGEFamily K) n.down)
    rw [RelativeWeakApprox.coproductProjection_comp]
    dsimp [g]
    rw [← DerivedCategory.Q.map_comp, natCoproductProjection_inj]
    by_cases h : j.as = n
    · subst n
      simp
    · have hd : j.as.down ≠ n.down := by
        intro hd
        exact h (ULift.ext _ _ hd)
      simp [h, hd]
  rw [hp] at hn
  refine ⟨n.down, ?_⟩
  rw [← DerivedCategory.Q.map_comp, truncationDiagonal_comp_projection] at hn
  exact hn

/-- A compact `Q`-image is bounded above for the canonical `t`-structure. -/
theorem exists_isLE_Q_obj_of_isCompactAb (A : Type uA) [CommRing A]
    (K : CochainComplex (ModuleCat.{uA} A) ℤ)
    (hK : IsCompactAb (DerivedCategory.Q.obj K)) :
    ∃ n : ℤ, DerivedCategory.IsLE (DerivedCategory.Q.obj K) n := by
  obtain ⟨n, hn⟩ := exists_piTruncGE_eq_zero_of_isCompactAb A K hK
  exact exists_isLE_Q_obj_of_piTruncGE_eq_zero K (n : ℤ) hn

/-- **Stacks 07LT, first paragraph:** every compact object of the unbounded
derived category of a ring is bounded above. -/
theorem exists_isLE_of_isCompactAb (A : Type uA) [CommRing A]
    (X : AffineD A) (hX : IsCompactAb X) :
    ∃ n : ℤ, (AffineD.standardTStructure A).IsLE X n := by
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hpre : IsCompactAb (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X)) :=
    isCompactAb_of_iso e.symm hX
  obtain ⟨n, hn⟩ := exists_isLE_Q_obj_of_isCompactAb A
    (DerivedCategory.Q.objPreimage X) hpre
  letI : DerivedCategory.IsLE (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X)) n := hn
  exact ⟨n, DerivedCategory.TStructure.t.isLE_of_iso e n⟩

end AffineCompact

#print axioms RelativeFM.Stacks07LT.BoundedAboveM1.quasiIso_colim_map_of_exact
#print axioms RelativeFM.Stacks07LT.BoundedAboveM1.qCoproductCofanIsColimit_of_quasiIso
#print axioms RelativeFM.Stacks07LT.BoundedAboveM1.truncationDiagonal
#print axioms RelativeFM.Stacks07LT.BoundedAboveM1.truncationDiagonal_comp_projection
#print axioms RelativeFM.Stacks07LT.BoundedAboveM1.spaltensteinResolution
#print axioms RelativeFM.Stacks07LT.BoundedAboveM1.affineSpaltensteinResolution
#print axioms RelativeFM.Stacks07LT.BoundedAboveM1.exists_isLE_Q_obj_of_piTruncGE_eq_zero
#print axioms RelativeFM.Stacks07LT.BoundedAboveM1.affineTruncationCoproductIsColimit
#print axioms RelativeFM.Stacks07LT.BoundedAboveM1.exists_piTruncGE_eq_zero_of_isCompactAb
#print axioms RelativeFM.Stacks07LT.BoundedAboveM1.exists_isLE_Q_obj_of_isCompactAb
#print axioms RelativeFM.Stacks07LT.BoundedAboveM1.exists_isLE_of_isCompactAb

end
end RelativeFM.Stacks07LT.BoundedAboveM1
