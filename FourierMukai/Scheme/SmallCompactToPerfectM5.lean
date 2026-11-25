import FourierMukai.Scheme.SmallAffineBridgeM5
import FourierMukai.Scheme.CompactToPerfect

@[expose] public section

namespace RelativeFM.SmallHomM5

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox

universe u

noncomputable section

/-- A bounded model whose terms are free, with no finite-generation
assumption. -/
structure SmallBoundedFreeModel (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (Y : SmallAffineD A H) where
  complex : CochainComplex (ModuleCat.{u} A) ℤ
  lower : ℤ
  upper : ℤ
  isStrictlyGE : complex.IsStrictlyGE lower
  isStrictlyLE : complex.IsStrictlyLE upper
  bounds : lower ≤ upper + 1
  free : ∀ n, Module.Free A (complex.X n)
  iso : Y ≅ (smallAffineQ A H).obj complex

/-- An identity factorization through a bounded complex of free modules. -/
structure SmallBoundedFreeFactorization (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (X : SmallAffineD A H) where
  compact : IsCompactAb X
  Y : SmallAffineD A H
  model : SmallBoundedFreeModel A H Y
  φ : X ⟶ Y
  ψ : Y ⟶ X
  factor : φ ≫ ψ = 𝟙 X

/-- A model by an arbitrary complex of free modules. -/
structure SmallFreeComplexModel (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) (X : SmallAffineD A H) where
  complex : CochainComplex (ModuleCat.{u} A) ℤ
  free : ∀ n, Module.Free A (complex.X n)
  iso : X ≅ (smallAffineQ A H).obj complex

/-- Bounded-free stages whose maps into the full free model are jointly
Hom-surjective. -/
structure SmallBoundedFreeFiltration (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X : SmallAffineD A H}
    (M : SmallFreeComplexModel A H X) where
  indices : Type u
  stage : indices → Stacks07LT.BoundedFreeStage A M.complex
  surjective : ∀ δ : X ⟶ (smallAffineQ A H).obj M.complex,
    ∃ i, ∃ f : X ⟶ (smallAffineQ A H).obj (stage i).complex,
      f ≫ (smallAffineQ A H).map (stage i).ι = δ

/-- Joint Hom-surjectivity gives an identity factorization through a finite
stage of the filtration. -/
theorem nonempty_smallBoundedFreeFactorization_of_filtration
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    {X : SmallAffineD A H} (M : SmallFreeComplexModel A H X)
    (F : SmallBoundedFreeFiltration A H M) (hX : IsCompactAb X) :
    Nonempty (SmallBoundedFreeFactorization A H X) := by
  obtain ⟨i, f, hf⟩ := F.surjective M.iso.hom
  let S := F.stage i
  refine ⟨
    { compact := hX
      Y := (smallAffineQ A H).obj S.complex
      model :=
        { complex := S.complex
          lower := S.lower
          upper := S.upper
          isStrictlyGE := S.isStrictlyGE
          isStrictlyLE := S.isStrictlyLE
          bounds := S.bounds
          free := S.free
          iso := Iso.refl _ }
      φ := f
      ψ := (smallAffineQ A H).map S.ι ≫ M.iso.inv
      factor := ?_ }⟩
  change f ≫ ((smallAffineQ A H).map S.ι ≫ M.iso.inv) = 𝟙 X
  rw [← Category.assoc, hf, M.iso.hom_inv_id]

/-- Terms in degrees strictly below `c` are finitely generated. -/
def SmallFiniteBelow (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X : SmallAffineD A H}
    (F : SmallBoundedFreeFactorization A H X) (c : ℤ) : Prop :=
  ∀ n, n < c → Module.Finite A (F.model.complex.X n)

lemma smallFiniteBelow_lower (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X : SmallAffineD A H}
    (F : SmallBoundedFreeFactorization A H X) :
    SmallFiniteBelow A H F F.model.lower := by
  intro n hn
  letI := F.model.isStrictlyGE
  exact AffinePerfect.moduleFinite_of_isZero A
    (F.model.complex.isZero_of_isStrictlyGE F.model.lower n hn)

/-- The single-degree finite-generation improvement used by 07LT. -/
structure SmallFiniteFreeImprovementInput (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) where
  improve : ∀ {X : SmallAffineD A H} (F : SmallBoundedFreeFactorization A H X)
    (c : ℤ), SmallFiniteBelow A H F c → c ≤ F.model.upper →
    ∃ F' : SmallBoundedFreeFactorization A H X,
      F'.model.lower = F.model.lower ∧ F'.model.upper = F.model.upper ∧
      SmallFiniteBelow A H F' (c + 1)

/-- Explicit triangle data for one finite-generation improvement. -/
structure SmallDegreeImprovementTriangleDatum (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) {X : SmallAffineD A H}
    (F : SmallBoundedFreeFactorization A H X) (c : ℤ) where
  Y' : SmallAffineD A H
  model' : SmallBoundedFreeModel A H Y'
  ι : Y' ⟶ F.Y
  Z : SmallAffineD A H
  π : F.Y ⟶ Z
  δ : Z ⟶ Y'⟦(1 : ℤ)⟧
  distinguished : Triangle.mk ι π δ ∈ distTriang (SmallAffineD A H)
  vanish : F.φ ≫ π = 0
  lower : model'.lower = F.model.lower
  upper : model'.upper = F.model.upper
  finite : ∀ n, n < c + 1 → Module.Finite A (model'.complex.X n)

/-- Exactness on the improvement triangle lifts the identity factorization. -/
theorem exists_smallImprovedFactorization_of_triangleDatum
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    {X : SmallAffineD A H} (F : SmallBoundedFreeFactorization A H X) (c : ℤ)
    (D : SmallDegreeImprovementTriangleDatum A H F c) :
    ∃ F' : SmallBoundedFreeFactorization A H X,
      F'.model.lower = F.model.lower ∧ F'.model.upper = F.model.upper ∧
      SmallFiniteBelow A H F' (c + 1) := by
  let T := Triangle.mk D.ι D.π D.δ
  obtain ⟨φ', hφ'⟩ := Triangle.coyoneda_exact₂ T D.distinguished F.φ D.vanish
  refine ⟨
    { compact := F.compact
      Y := D.Y'
      model := D.model'
      φ := φ'
      ψ := T.mor₁ ≫ F.ψ
      factor := ?_ },
    D.lower, D.upper, D.finite⟩
  change X ⟶ D.Y' at φ'
  change F.φ = φ' ≫ D.ι at hφ'
  change φ' ≫ D.ι ≫ F.ψ = 𝟙 X
  rw [← Category.assoc, ← hφ', F.factor]

/-- Assemble the one-degree improvement operation from triangle data. -/
theorem smallFiniteFreeImprovementInput_of_triangleData
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (datum : ∀ {X : SmallAffineD A H} (F : SmallBoundedFreeFactorization A H X)
      (c : ℤ), SmallFiniteBelow A H F c → c ≤ F.model.upper →
      Nonempty (SmallDegreeImprovementTriangleDatum A H F c)) :
    SmallFiniteFreeImprovementInput A H where
  improve F c hfin hc :=
    exists_smallImprovedFactorization_of_triangleDatum A H F c
      (datum F c hfin hc).some

/-- The 07LT induction turns a bounded-free identity factorization into a
bounded finite-projective identity factorization. -/
theorem exists_smallFiniteProjectiveFactorization
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (I : SmallFiniteFreeImprovementInput A H) {X : SmallAffineD A H}
    (F : SmallBoundedFreeFactorization A H X) :
    ∃ Y : SmallAffineD A H, Nonempty (SmallBoundedFiniteProjectiveModel A H Y) ∧
      ∃ φ : X ⟶ Y, ∃ ψ : Y ⟶ X, φ ≫ ψ = 𝟙 X := by
  let motive := fun c (_ : F.model.lower ≤ c) => c ≤ F.model.upper + 1 →
    ∃ F' : SmallBoundedFreeFactorization A H X,
      F'.model.lower = F.model.lower ∧ F'.model.upper = F.model.upper ∧
      SmallFiniteBelow A H F' c
  have hex : motive (F.model.upper + 1) F.model.bounds := by
    refine Int.leInduction (motive := motive) (fun _ => ⟨F, rfl, rfl,
      smallFiniteBelow_lower A H F⟩) ?_ (F.model.upper + 1) F.model.bounds
    intro c hc ih hcb
    obtain ⟨G, hGl, hGu, hGfin⟩ := ih (by omega)
    obtain ⟨G', hG'l, hG'u, hG'fin⟩ := I.improve G c hGfin (by omega)
    exact ⟨G', hG'l.trans hGl, hG'u.trans hGu, hG'fin⟩
  obtain ⟨G, hGl, hGu, hGfin⟩ := hex (le_refl _)
  have hfinite : ∀ n, Module.Finite A (G.model.complex.X n) := by
    intro n
    by_cases hn : n < G.model.upper + 1
    · rw [hGu] at hn
      exact hGfin n hn
    · have hn' : G.model.upper < n := by omega
      letI := G.model.isStrictlyLE
      exact AffinePerfect.moduleFinite_of_isZero A
        (G.model.complex.isZero_of_isStrictlyLE G.model.upper n hn')
  refine ⟨G.Y, ⟨?_⟩, G.φ, G.ψ, G.factor⟩
  exact
    { complex := G.model.complex
      lower := G.model.lower
      upper := G.model.upper
      isStrictlyGE := G.model.isStrictlyGE
      isStrictlyLE := G.model.isStrictlyLE
      finite := hfinite
      projective n := by
        letI := G.model.free n
        infer_instance
      iso := G.model.iso }

/-- The constructive output needed from bounded-above resolutions and the
finite-free induction. -/
structure SmallStacks07LTBoundedFactorizationInput (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) where
  factorization : ∀ X : SmallAffineD A H, IsCompactAb X →
    ∃ Y : SmallAffineD A H, Nonempty (SmallBoundedFiniteProjectiveModel A H Y) ∧
      ∃ φ : X ⟶ Y, ∃ ψ : Y ⟶ X, φ ≫ ψ = 𝟙 X

/-- The two inputs preceding the induction: an initial bounded-free
factorization and the one-degree improvement operation. -/
structure SmallBoundedFreeInductionInput (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) where
  initial : ∀ X : SmallAffineD A H, IsCompactAb X →
    Nonempty (SmallBoundedFreeFactorization A H X)
  improve : SmallFiniteFreeImprovementInput A H

/-- Ring data for the initial 07LR stage: a free complex model and a
bounded-free filtration with jointly surjective Hom maps. -/
structure SmallFilteredFreeModelInput (A : Type u) [CommRing A]
    (H : AffineSpaltensteinInput A) where
  models : ∀ X : SmallAffineD A H, IsCompactAb X →
    ∃ M : SmallFreeComplexModel A H X, Nonempty (SmallBoundedFreeFiltration A H M)

/-- Assemble the initial and improvement inputs for the induction. -/
theorem smallBoundedFreeInductionInput_of_filteredFreeModels
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (F : SmallFilteredFreeModelInput A H) (I : SmallFiniteFreeImprovementInput A H) :
    SmallBoundedFreeInductionInput A H where
  initial X hX := by
    obtain ⟨M, hM⟩ := F.models X hX
    exact nonempty_smallBoundedFreeFactorization_of_filtration A H M hM.some hX
  improve := I

/-- Obtain bounded finite-projective factorizations from the two induction
inputs. -/
theorem smallStacks07LTBoundedFactorizationInput_of_freeInduction
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (I : SmallBoundedFreeInductionInput A H) :
    SmallStacks07LTBoundedFactorizationInput A H where
  factorization X hX := by
    let F := (I.initial X hX).some
    exact exists_smallFiniteProjectiveFactorization A H I.improve F

/-- The same conclusion from filtered free models and explicit one-degree
improvements. -/
theorem smallStacks07LTBoundedFactorizationInput_of_filteredFreeModels
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (F : SmallFilteredFreeModelInput A H) (I : SmallFiniteFreeImprovementInput A H) :
    SmallStacks07LTBoundedFactorizationInput A H :=
  smallStacks07LTBoundedFactorizationInput_of_freeInduction A H
    (smallBoundedFreeInductionInput_of_filteredFreeModels A H F I)

/-- Neeman's compact-to-perfect interface follows from the constructive 07LT
factorization: a bounded finite-projective object is perfect, and the original
compact object is a retract of it. -/
theorem smallNeemanCompactToPerfectInput_of_boundedFactorization
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (I : SmallStacks07LTBoundedFactorizationInput A H) :
    SmallNeemanCompactToPerfectInput A H where
  perfect_of_compact X hX := by
    obtain ⟨Y, hY, φ, ψ, hφψ⟩ := I.factorization X hX
    let r : Retract X Y := { i := φ, r := ψ, retract := hφψ }
    letI : (SmallPerf A H).IsStableUnderRetracts := by
      unfold SmallPerf
      infer_instance
    exact (SmallPerf A H).prop_of_retract r
      (smallPerf_of_nonempty_smallBoundedFiniteProjectiveModel A H hY)

/-- The small compact/perfect characterization from the same constructive
input, using the already proved perfect-to-compact direction. -/
theorem isCompactAb_iff_smallPerf_of_boundedFactorization
    (A : Type u) [CommRing A] (H : AffineSpaltensteinInput A)
    (I : SmallStacks07LTBoundedFactorizationInput A H)
    (X : SmallAffineD A H) : IsCompactAb X ↔ SmallPerf A H X :=
  NeemanM1.isCompactAb_iff_smallPerf_of_neeman A H
    (smallNeemanCompactToPerfectInput_of_boundedFactorization A H I) X

end

end RelativeFM.SmallHomM5

#print axioms RelativeFM.SmallHomM5.nonempty_smallBoundedFreeFactorization_of_filtration
#print axioms RelativeFM.SmallHomM5.exists_smallImprovedFactorization_of_triangleDatum
#print axioms RelativeFM.SmallHomM5.exists_smallFiniteProjectiveFactorization
#print axioms RelativeFM.SmallHomM5.smallNeemanCompactToPerfectInput_of_boundedFactorization
#print axioms RelativeFM.SmallHomM5.isCompactAb_iff_smallPerf_of_boundedFactorization
