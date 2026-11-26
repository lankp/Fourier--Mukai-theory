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

end

end RelativeFM.SmallHomM5

#print axioms RelativeFM.SmallHomM5.nonempty_smallBoundedFreeFactorization_of_filtration
#print axioms RelativeFM.SmallHomM5.exists_smallImprovedFactorization_of_triangleDatum
