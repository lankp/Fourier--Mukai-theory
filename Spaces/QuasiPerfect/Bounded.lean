/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.QuasiPerfect.Inputs
import Spaces.QuasiPerfect.Neeman53
import Spaces.RelativePerfect
import Spaces.LP26.HomVanishing

/-!
# GL26 Lemma 5.3 (`lem:quasi-perfect_bounded`), first two claims, over algebraic spaces

Guisado Villalgordo–Lank (GL26), §5 (`sec:quasi-perfect`), **Lemma 5.3**
(`lem:quasi-perfect_bounded`).  Let `f : Y ⟶ X` be a morphism of quasi-compact quasi-separated
algebraic spaces.

1. If `E` is `f`-quasi-perfect, so is `E ⊗^L Q` for every `Q ∈ Perf(Y)` (`lemma_5_3_tensor`).
2. If moreover `E` is pseudo-coherent, then `ℝ𝓗om(E, f^× 𝒪_X) ∈ D^b_qc(Y)` (`lemma_5_3_bounded`;
   `lemma_5_3_bounded_of_bounded` for `f^× P`, any `P ∈ D^b_qc(X)`).
3. If moreover `f^× 𝒪_X` has coherent cohomology and `Y` is Noetherian, `ℝ𝓗om(E, f^× 𝒪_X)` is
   pseudo-coherent.  **Not proved here** (see "Claim (3)" below).

`ℝ𝓗om` is the derived sheaf Hom of `D(𝒪_Y)` (`sheafHomObj`, blackboard in GL26) and `f^×` the right
adjoint of `Rf_* : D_qc(Y) ⥤ D_qc(X)` (`upperTimes`, Stacks 0E55).

## Proof of (2)

Put `L = f^× P` and `M = ℝ𝓗om(E, L)`.

* `f^×` lowers lower bounds by a fixed amount (`upperTimes_isGE`, Stacks 0E56, proved here from the
  uniform bound of Stacks 08FA (2) exactly as AxiomMath proves it for its own right adjoint), so
  `L ∈ D^+_qc(Y)`, and `M ∈ D_qc(Y)` by Stacks 0A8A (`E` pseudo-coherent).
* For `Q ∈ D_qc(Y)` and `n ∈ ℤ`, tensor/hom, `Rf_* ⊣ f^×` and the compatibility of `⊗^L` and `Rf_*`
  with shifts give `Hom(Q[n], M) ≃ Hom((Rf_*(Q ⊗^L E))[n], P)` (`homEquiv_shift`).
* For `Q` compact (= perfect, Stacks 09M8), `K = Rf_*(Q ⊗^L E) ≅ Rf_*(E ⊗^L Q)` is perfect because
  `E` is `f`-quasi-perfect.  Hence `Hom(K[-i], P) = 0` for `i ≫ 0` (Stacks 09MB, `P` bounded above)
  and for `i ≪ 0` (`K` bounded above, `P` bounded below).
* Stacks 0GFH and 0GFI, (7) ⇒ (1): `M` is bounded above and below.

This is GL26's argument (adjunction, then Stacks 0GFH), run with every compact object of `D_qc(Y)`
in place of one compact generator, and used for both bounds; GL26 obtains the lower bound from
Stacks 0A6H instead.  It does not use that pseudo-coherent objects are bounded above.

## Claim (3)

GL26 cites Stacks 0D0S (`ℝ𝓗om(D^-_coh, D^+_coh) ⊆ D^+_coh` on a locally Noetherian space).
AxiomMath proves 0D0S only for the internal Hom *complex* of chosen models, in a raised module
universe (`AlgebraicGeometry.Space.derivedCategoryBPlus_isCoherentOnSite_sheafHomComplex`); it does
not identify that complex with `smallEtaleDerivedSheafHom` (`ℝ𝓗om` here).  Claim (3) is therefore
left open (`results/COVERAGE.md`).

## Differences from GL26

* The hypothesis on `f` is `IsQcqsHom hZ f` (`Y` qcqs, `X` quasi-separated, `f` qcqs) together
  with `X` quasi-compact: exactly "morphism of qcqs algebraic spaces".
* `𝒪_X` is `𝒪_X[0] = (singleFunctor 0).obj (SheafOfModules.unit _)`, which lies in `D_qc(X)` by
  `StructureSheafQcohInput`.  Claim (2) is proved for every `P ∈ D^b_qc(X)`, which is stronger.
* GL26's first claim is stated for `E ∈ D_qc(Y)`; `IsQuasiPerfect` includes `E ∈ D_qc(Y)`.

## Assumptions

AxiomMath theorems only, as tagged inputs: `Tag08F5Input`, `Tag08FAInput`, `Tag0E55Input`,
`Tag0A8AInput`; from `Spaces/LP26/Inputs.lean` `PerfectQcohInput`, `Tag09M8Input`, `Tag09MBInput`,
`PerfectBoundedAboveInput`, `Tag08FABoundInput`; from `Spaces/QuasiPerfect/Inputs.lean`
`Tag09JBInput`, `Tag0GFHInput`, `Tag0GFIInput`, `QcohTruncLEInput`, `StructureSheafQcohInput`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space Opposite

namespace RelativeFM.Spaces.QuasiPerfect

open RelativeFM.Spaces RelativeFM.Spaces.Duality RelativeFM.Spaces.LP26

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Claim (1) -/

/-- The associator `(A ⊗ P) ⊗ M ≅ A ⊗ (P ⊗ M)` of `⊗^L` (AxiomMath's `associatorGeneral`). -/
abbrev tensorAssocIso {X : AlgebraicSpaces B S hS} (A P M : D B S hS X) :
    tensorObj (tensorObj A P) M ≅ tensorObj A (tensorObj P M) :=
  (smallEtaleDerivedTensorProduct B S hS X).associatorGeneral A P M

/-- **Lemma 5.3**, first claim (`lem:quasi-perfect_bounded`): if `E` is `f`-quasi-perfect, then
`E ⊗^L Q` is `f`-quasi-perfect for every `Q ∈ Perf(Y)`.  For any morphism `f`. -/
theorem lemma_5_3_tensor (h08F5 : Tag08F5Input B S hS) (hPq : PerfectQcohInput B S hS)
    (h09JB : Tag09JBInput B S hS) {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) {E Q : D B S hS Y}
    (hE : IsQuasiPerfect f E) (hQ : Perf Y Q) : IsQuasiPerfect f (tensorObj E Q) :=
  ⟨h08F5 Y E Q hE.1 (hPq Y Q hQ), fun P hP =>
    RingedSite.IsPerfect.of_iso _ (hE.2 _ (perf_tensorObj h09JB hQ hP))
      ((push f).mapIso (tensorAssocIso E Q P).symm)⟩

/-! ### `f^×` and lower bounds (Stacks 0E56) -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))
variable (h08FA : Tag08FAInput B S hS) (h0E55 : Tag0E55Input B S hS)

variable {hZ} in
/-- **Stacks 0E56** for `f^×`: for `f` as in Stacks 0E55 with quasi-compact target, there is `N`
such that `f^×` sends `D_qc(X) ∩ D^{≥ c}` into `D^{≥ c - N}`.  The proof is AxiomMath's
(`isGE_quasicoherentDerivedRightAdjoint_obj`, for its own right adjoint), run for `upperTimes`:
for `d = c - N - 1`, `Rf_*(τ_{≤ d} f^× K) ∈ D^{≤ c - 1}` (Stacks 08FA (2)), so the truncation map
`τ_{≤ d} f^× K ⟶ f^× K` is adjoint to a morphism into `K ∈ D^{≥ c}`, hence zero. -/
theorem upperTimes_isGE (h08FAb : Tag08FABoundInput B S hS) (htr : QcohTruncLEInput B S hS)
    {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsQcqsHom hZ f)
    (hXqc : IsQuasiCompactSpace B S hS X.1) :
    ∃ N : ℤ, ∀ (K : (Dqc X).FullSubcategory) (c : ℤ), K.obj.IsGE c →
      ((upperTimes h08FA h0E55 f hf).obj K).obj.IsGE (c - N) := by
  obtain ⟨N, hN⟩ := h08FAb f hf.qc hf.qs hXqc
  refine ⟨N, fun K c hK => ?_⟩
  let a := upperTimes h08FA h0E55 f hf
  let adj := upperTimesAdj h08FA h0E55 f hf
  obtain ⟨d, hd⟩ : ∃ d : ℤ, c - N = d + 1 := ⟨c - N - 1, by omega⟩
  let T : (Dqc Y).FullSubcategory :=
    ⟨(DerivedCategory.TStructure.t.truncLE d).obj (a.obj K).obj,
      htr (X := Y.1) (hX := Y.2) _ d (a.obj K).property⟩
  have hT : DerivedCategory.TStructure.t.IsLE T.obj d := by dsimp only [T]; infer_instance
  have hRLE : ((push f).obj T.obj).IsLE (d + N) := hN T.obj T.property d hT
  have hzero : ∀ g₁ g₂ : (pushQc h08FA f hf.qc hf.qs).obj T ⟶ K, g₁ = g₂ := by
    intro g₁ g₂
    refine ObjectProperty.hom_ext _ ?_
    rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g₁.hom (d + N) c (by omega) hRLE hK,
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g₂.hom (d + N) c (by omega) hRLE hK]
  have hsub : ∀ g₁ g₂ : T ⟶ a.obj K, g₁ = g₂ := fun g₁ g₂ =>
    (adj.homEquiv T K).symm.injective (hzero _ _)
  have hι : (DerivedCategory.TStructure.t.truncLTι (d + 1)).app (a.obj K).obj = 0 :=
    congrArg InducedCategory.Hom.hom
      (hsub (ObjectProperty.homMk
        ((DerivedCategory.TStructure.t.truncLEι d).app (a.obj K).obj))
        (ObjectProperty.homMk 0))
  rw [hd]
  refine (DerivedCategory.TStructure.t.isGE_iff_orthogonal d (d + 1) rfl _).2 fun Z g _ => ?_
  rw [← DerivedCategory.TStructure.t.liftTruncLT_ι g d (d + 1) rfl, hι, comp_zero]

/-! ### The Hom computation -/

section HomComputation

variable (h08F5 : Tag08F5Input B S hS)

variable {hZ} in
/-- `Hom(Q[n], ℝ𝓗om(E, f^× P)) ≃ Hom((Rf_*(Q ⊗^L E))[n], P)` for `Q, E ∈ D_qc(Y)`: tensor/hom
(Stacks 08J8), `Rf_* ⊣ f^×` on `D_qc`, and the compatibility of `- ⊗^L E` and of `Rf_*` with
shifts. -/
def homEquivShift {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsQcqsHom hZ f)
    {E : D B S hS Y} (hE : Dqc Y E) {Q : D B S hS Y} (hQ : Dqc Y Q) (n : ℤ)
    (P : (Dqc X).FullSubcategory) :
    (Q⟦n⟧ ⟶ sheafHomObj E ((upperTimes h08FA h0E55 f hf).obj P).obj) ≃
      (((push f).obj (tensorObj Q E))⟦n⟧ ⟶ P.obj) :=
  let T : (Dqc Y).FullSubcategory :=
    ⟨tensorObj (Q⟦n⟧) E, h08F5 Y _ _ (qcohDerived_shift Y hQ n) hE⟩
  letI : ((tensor Y).flip.obj E).CommShift ℤ :=
    (smallEtaleDerivedTensorProduct B S hS Y).commShift_left E
  letI : (push f).CommShift ℤ := (pullPushAdj f).rightAdjointCommShift ℤ
  ((tensorSheafHomAdj E).homEquiv (Q⟦n⟧) _).symm.trans <|
    ((Dqc Y).fullyFaithfulι.homEquiv (X := T)).symm.trans <|
      ((upperTimesAdj h08FA h0E55 f hf).homEquiv T P).symm.trans <|
        (Dqc X).fullyFaithfulι.homEquiv.trans <|
          Iso.homCongr
            ((push f).mapIso ((((tensor Y).flip.obj E).commShiftIso n).app Q) ≪≫
              ((push f).commShiftIso n).app (tensorObj Q E))
            (Iso.refl P.obj)

end HomComputation

/-! ### Claim (2) -/

variable (h08F5 : Tag08F5Input B S hS) (h0A8A : Tag0A8AInput B S hS)
  (h08FAb : Tag08FABoundInput B S hS) (htr : QcohTruncLEInput B S hS)
  (hPq : PerfectQcohInput B S hS) (h09M8 : Tag09M8Input B S hS) (h09MB : Tag09MBInput B S hS)
  (hbd : PerfectBoundedAboveInput B S hS) (h0GFH : Tag0GFHInput B S hS)
  (h0GFI : Tag0GFIInput B S hS)

variable {hZ} in
include h08F5 h0A8A h08FAb htr hPq h09M8 h09MB hbd h0GFH h0GFI in
/-- **Lemma 5.3**, second claim (`lem:quasi-perfect_bounded`), for `f^× P` with `P ∈ D^b_qc(X)`:
let `f : Y ⟶ X` be a morphism of qcqs algebraic spaces (`IsQcqsHom hZ f`, `X` quasi-compact),
`E` `f`-quasi-perfect and pseudo-coherent, and `P ∈ D_qc(X)` bounded.  Then
`ℝ𝓗om(E, f^× P) ∈ D^b_qc(Y)`.  GL26 states it for `P = 𝒪_X` (`lemma_5_3_bounded`). -/
theorem lemma_5_3_bounded_of_bounded {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsQcqsHom hZ f) (hXqc : IsQuasiCompactSpace B S hS X.1) {E : D B S hS Y}
    (hE : IsQuasiPerfect f E) (hpc : IsPseudoCoherent Y E) (P : (Dqc X).FullSubcategory)
    {a b : ℤ} (haP : P.obj.IsGE a) (hbP : P.obj.IsLE b) :
    Dbqc Y (sheafHomObj E ((upperTimes h08FA h0E55 f hf).obj P).obj) := by
  set L := ((upperTimes h08FA h0E55 f hf).obj P).obj with hL
  -- `L ∈ D^+_qc(Y)` (Stacks 0E56), so `M ∈ D_qc(Y)` (Stacks 0A8A).
  obtain ⟨N, hN⟩ := upperTimes_isGE h08FA h0E55 h08FAb htr f hf hXqc
  have hLge : L.IsGE (a - N) := hN P a haP
  have hLplus : DplusQc Y L :=
    ⟨⟨a - N, fun i hi => DerivedCategory.isZero_of_isGE L (a - N) i hi⟩,
      ((upperTimes h08FA h0E55 f hf).obj P).property⟩
  have hM : Dqc Y (sheafHomObj E L) := sheafHomObj_mem_Dqc_of_isPseudoCoherent h0A8A hpc hLplus
  let M : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 := ⟨sheafHomObj E L, hM⟩
  -- For a compact `Q ∈ D_qc(Y)`, `K = Rf_*(Q ⊗ E)` is perfect, compact and bounded above.
  have hK : ∀ Q : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2, IsCompactObject.{u} Q →
      Perf X ((push f).obj (tensorObj Q.obj E)) := fun Q hQ =>
    RingedSite.IsPerfect.of_iso _
      (hE.2 Q.obj ((h09M8 hZ Y hf.srcQc hf.srcQs Q).1 hQ))
      ((push f).mapIso (((tensorBraiding Y).app E).app Q.obj))
  -- `Hom(Q[-i], M) ≃ Hom(K[-i], P)`.
  have hsub : ∀ (Q : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) (i : ℤ),
      Subsingleton (((push f).obj (tensorObj Q.obj E))⟦-i⟧ ⟶ P.obj) →
        Subsingleton (Q.obj⟦-i⟧ ⟶ M.obj) := fun Q i h =>
    (homEquivShift h08FA h0E55 h08F5 f hf hE.1 Q.property (-i) P).subsingleton_congr.2 h
  refine ⟨⟨?_, ?_⟩, hM⟩
  · -- bounded below: Stacks 0GFI.
    obtain ⟨a', ha'⟩ := h0GFI hZ Y hf.srcQc hf.srcQs M fun Q hQ => by
      obtain ⟨m, hm⟩ := hbd hXqc _ (hK Q hQ)
      have : DerivedCategory.TStructure.t.IsLE ((push f).obj (tensorObj Q.obj E)) m := hm
      refine ⟨a - m - 1, fun i hi => hsub Q i ?_⟩
      refine ⟨fun g₁ g₂ => ?_⟩
      have : (((push f).obj (tensorObj Q.obj E))⟦-i⟧).IsLE (m + i) :=
        DerivedCategory.TStructure.t.isLE_shift _ m (-i) (m + i) (by omega)
      rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g₁ (m + i) a (by omega) this haP,
        DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g₂ (m + i) a (by omega) this haP]
    exact ⟨a', fun i hi => DerivedCategory.isZero_of_isGE _ a' i hi (hX := ha')⟩
  · -- bounded above: Stacks 0GFH.
    obtain ⟨a', ha'⟩ := h0GFH hZ Y hf.srcQc hf.srcQs M fun Q hQ => by
      let K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
        ⟨(push f).obj (tensorObj Q.obj E), hPq X _ (hK Q hQ)⟩
      have hKc : IsCompactObject.{u} K := (h09M8 hZ X hXqc hf.tgtQs K).2 (hK Q hQ)
      obtain ⟨N₀, hN₀⟩ := h09MB hZ X hXqc hf.tgtQs K hKc
      refine ⟨b + N₀, fun i hi => hsub Q i ?_⟩
      refine ((shiftEquiv' (D B S hS X) (-i) i (by omega)).toAdjunction.homEquiv
        K.obj P.obj).subsingleton_congr.2 ⟨fun g₁ g₂ => ?_⟩
      have := hbP
      have : (P.obj⟦i⟧).IsLE (b - i) :=
        DerivedCategory.TStructure.t.isLE_shift _ b i (b - i) (by omega)
      have hle : (P.obj⟦i⟧).IsLE (-N₀) :=
        DerivedCategory.TStructure.t.isLE_of_le _ (b - i) (-N₀) (by omega)
      rw [hN₀ _ (qcohDerived_shift X P.property i) hle g₁,
        hN₀ _ (qcohDerived_shift X P.property i) hle g₂]
    exact ⟨a', fun i hi => DerivedCategory.isZero_of_isLE _ a' i hi (hX := ha')⟩

/-- **`𝒪_X` as an object of `D_qc(X)`**: `𝒪_X[0]`, from `StructureSheafQcohInput`. -/
def structureSheafQc (hO : StructureSheafQcohInput B S hS) (X : AlgebraicSpaces B S hS) :
    (Dqc X).FullSubcategory :=
  ⟨(DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)),
    hO (X := X.1) (hX := X.2)⟩

variable {hZ} in
include h08F5 h0A8A h08FAb htr hPq h09M8 h09MB hbd h0GFH h0GFI in
/-- **Lemma 5.3**, second claim (`lem:quasi-perfect_bounded`): let `f : Y ⟶ X` be a morphism of
quasi-compact quasi-separated algebraic spaces (`IsQcqsHom hZ f`, `X` quasi-compact).  If `E` is
`f`-quasi-perfect and pseudo-coherent, then `ℝ𝓗om(E, f^× 𝒪_X) ∈ D^b_qc(Y)`. -/
theorem lemma_5_3_bounded (hO : StructureSheafQcohInput B S hS) {Y X : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : IsQcqsHom hZ f) (hXqc : IsQuasiCompactSpace B S hS X.1) {E : D B S hS Y}
    (hE : IsQuasiPerfect f E) (hpc : IsPseudoCoherent Y E) :
    Dbqc Y (sheafHomObj E ((upperTimes h08FA h0E55 f hf).obj (structureSheafQc hO X)).obj) :=
  lemma_5_3_bounded_of_bounded h08FA h0E55 h08F5 h0A8A h08FAb htr hPq h09M8 h09MB hbd h0GFH h0GFI
    f hf hXqc hE hpc (structureSheafQc hO X) (a := 0) (b := 0)
    (DerivedCategory.instIsGEObjSingleFunctor _ _) (DerivedCategory.instIsLEObjSingleFunctor _ _)

end RelativeFM.Spaces.QuasiPerfect
