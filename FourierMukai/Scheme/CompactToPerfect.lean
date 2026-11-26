/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0
license as described in the file LICENSE.
-/
import FourierMukai.Scheme.PerfectRingStacks
import FourierMukai.Scheme.PerfectModelConverse
import WeakApprox.CompactAb

/-!
# Categorical steps in the compact-to-perfect direction of Stacks 07LT

This file proves the categorical and inductive steps in the proof that a
compact object of `D(R)` is perfect.

* A map from an `Ab`-compact object to a coproduct has an explicit `DFinsupp`
  finite-support decomposition.  A zero-projection consequence and the
  truncation triangle therefore prove bounded-above cohomology from the
  explicit coproduct of canonical truncations.
* The algebraic `1 - transition` map on a sequence has zero kernel, and the
  rotated-triangle argument reduces Hom-surjectivity in Stacks 07LR to its
  categorical coproduct analogue.
* Joint Hom-surjectivity for bounded-free stages produces the initial identity
  factorization.  A distinguished improvement triangle and a zero composite
  produce the next identity factorization.  `Int.leInduction` then carries
  finite generation from the lower bound to `upper + 1`.
* The final identity factorization is a retract of a bounded finite-projective
  model, hence perfect.  Consequently `compact ⇒ Perf` does not need Stacks
  066S, although the full compact-to-model statement does.

`FiniteFreeImprovementInput` is a residual input; it is not asserted for a ring.
(`FilteredFreeModelInput` and the affine gluing endpoint built on it were deleted
in wave 6, `results/OPEN_INPUTS.md` row 3.5.)  The
more explicit `DegreeImprovementTriangleDatum` refines the latter, while
`TruncationCoproductDatum` belongs only to the optional bounded-above argument.
No global coproduct existence, free resolution, filtration, or compactness
theorem is silently assumed.
-/

@[expose] public section

namespace RelativeFM.Stacks07LT

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox
open scoped ZeroObject

universe w v u

noncomputable section

section CompactCoproduct

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **The finite-support decomposition of a compact map to a coproduct.**
The coefficients are morphisms into the summands; only finitely many are
nonzero.  This is the full form needed for the free-basis induction in Stacks
07LT, where a finite set is enlarged to contain the entire support. -/
lemma exists_dfinsupp_coproduct_decomposition
    {J : Type v} [DecidableEq J] {X : C} (hX : IsCompactAb X)
    (f : J → C) {P : C} (g : ∀ j, f j ⟶ P)
    (hc : IsColimit (Cofan.mk P g)) (δ : X ⟶ P) :
    ∃ z : DFinsupp (fun j => X ⟶ f j),
      (DFinsupp.sumAddHom (fun j =>
        ((RelativeWeakApprox.abCoyoneda X).map (g j)).hom)) z = δ := by
  classical
  letI : PreservesColimitsOfShape (Discrete J)
      (preadditiveCoyoneda.obj (.op X)) := hX.preserves J
  letI : PreservesColimitsOfShape (Discrete J)
      (RelativeWeakApprox.abCoyoneda X) :=
    preservesColimitsOfShape_of_natIso
      (RelativeWeakApprox.abCoyonedaIsoPreadditive X).symm
  let c : Cofan (fun j => (RelativeWeakApprox.abCoyoneda X).obj (f j)) :=
    Cofan.mk ((RelativeWeakApprox.abCoyoneda X).obj P)
      (fun j => (RelativeWeakApprox.abCoyoneda X).map (g j))
  have hmap : IsColimit c :=
    (Cofan.isColimitMapCoconeEquiv (RelativeWeakApprox.abCoyoneda X) f
      (Cofan.mk P g)) (isColimitOfPreserves (RelativeWeakApprox.abCoyoneda X) hc)
  obtain ⟨z, hz⟩ :=
    (RelativeWeakApprox.bijective_abCofanSum_of_isColimit hmap).2 δ
  exact ⟨z, hz⟩

/-- **A zero-projection consequence of finite support.**  When the index type
is infinite, some index lies outside the support, so the corresponding
coproduct projection kills the map.  This is the form used for the canonical
truncations in Stacks 07LT. -/
lemma exists_comp_coproductProjection_eq_zero
    {J : Type v} [DecidableEq J] [Infinite J] {X : C} (hX : IsCompactAb X)
    (f : J → C) {P : C} (g : ∀ j, f j ⟶ P)
    (hc : IsColimit (Cofan.mk P g)) (δ : X ⟶ P) :
    ∃ j : J, δ ≫ RelativeWeakApprox.coproductProjection (C := C) (J := J) g hc j = 0 := by
  classical
  let c : Cofan (fun j => (RelativeWeakApprox.abCoyoneda X).obj (f j)) :=
    Cofan.mk ((RelativeWeakApprox.abCoyoneda X).obj P)
      (fun j => (RelativeWeakApprox.abCoyoneda X).map (g j))
  obtain ⟨z, hz⟩ := exists_dfinsupp_coproduct_decomposition hX f g hc δ
  change RelativeWeakApprox.abCofanSum c z = δ at hz
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset z.support
  refine ⟨j, ?_⟩
  have hzj : z j = 0 := DFinsupp.notMem_support_iff.mp hj
  let p := RelativeWeakApprox.coproductProjection g hc j
  let post := ((RelativeWeakApprox.abCoyoneda X).map p).hom
  have eval (w : DFinsupp (fun j => X ⟶ f j)) :
      (RelativeWeakApprox.abCofanSum c w) ≫ p = w j := by
    have hw := post.map_dfinsuppSumAddHom w (fun k => (c.inj k).hom)
    calc
      (RelativeWeakApprox.abCofanSum c w) ≫ p =
          post ((DFinsupp.sumAddHom fun k => (c.inj k).hom) w) := rfl
      _ = (DFinsupp.sumAddHom fun k => post.comp (c.inj k).hom) w := hw
      _ = w j := by
        have hfun : (fun k => post.comp (c.inj k).hom) =
            Pi.single j (AddMonoidHom.id (X ⟶ f j)) := by
          funext k
          by_cases h : k = j
          · subst k
            ext q
            simp [post, p, c]
          · ext q
            simp [post, p, c, h]
        rw [hfun, DFinsupp.sumAddHom_piSingle]
        rfl
  change δ ≫ p = 0
  rw [← hz, eval z, hzj]

/-- The predecessor part of the `1 - transition` map on a sequence of
abelian groups. -/
def sequenceTransitionTail {A : ℕ → Type w} [∀ n, AddCommGroup (A n)]
    (t : ∀ n, A n →+ A (n + 1)) (z : ∀ n, A n) : ∀ n, A n
  | 0 => 0
  | n + 1 => t n (z n)

/-- **Injectivity of `1 - transition`.**  No finiteness of support is needed:
the zero coordinate forces `z 0 = 0`, and each successor equation then forces
the next coordinate to vanish. -/
theorem sequence_eq_zero_of_sub_transitionTail
    {A : ℕ → Type w} [∀ n, AddCommGroup (A n)]
    (t : ∀ n, A n →+ A (n + 1)) (z : ∀ n, A n)
    (h : ∀ n, z n - sequenceTransitionTail t z n = 0) : z = 0 := by
  funext n
  induction n with
  | zero =>
      have hz := sub_eq_zero.mp (h 0)
      change z 0 = 0 at hz
      exact hz
  | succ n ih =>
      have hn := sub_eq_zero.mp (h (n + 1))
      change z (n + 1) = t n (z n) at hn
      rw [ih] at hn
      simpa only [Pi.zero_apply, map_zero] using hn

end CompactCoproduct

section TriangleHom

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- In a distinguished triangle `T`, injectivity after the shift of `T.mor₁`
makes every map to `T.obj₃` lift to `T.obj₂`.  For the termwise-colimit triangle
in Stacks 07LR this reduces Hom-surjectivity to the explicit injectivity of the
coproduct map `1 - transition`. -/
theorem exists_lift_triangle_of_injective_shift
    {X : C} (T : Triangle C) (hT : T ∈ distTriang C)
    (hinj : Function.Injective (fun f : X ⟶ T.obj₁⟦(1 : ℤ)⟧ =>
      f ≫ T.mor₁⟦(1 : ℤ)⟧')) (δ : X ⟶ T.obj₃) :
    ∃ γ : X ⟶ T.obj₂, δ = γ ≫ T.mor₂ := by
  have hzero : δ ≫ T.mor₃ = 0 := by
    apply hinj
    dsimp only
    rw [Category.assoc, comp_distTriang_mor_zero₃₁ T hT, comp_zero, zero_comp]
  obtain ⟨γ, hγ⟩ := Triangle.coyoneda_exact₂ T.rotate (rot_of_distTriang _ hT) δ (by
    change δ ≫ T.mor₃ = 0
    exact hzero)
  exact ⟨γ, hγ⟩

end TriangleHom

section Truncations

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- An aisle of a `t`-structure is closed under retracts. -/
lemma isLE_of_retract (t : TStructure C) {X Y : C} (r : Retract X Y)
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

/-- The special coproduct used on the first page of the converse direction of
Stacks 07LT.

For `D(R)`, the point `P` is the degreewise direct sum of the complexes
`τ_{≥n}K`, which is legitimate because only finitely many terms contribute in
a fixed degree; `diagonal` is induced degreewise by the canonical truncation
maps.  The field `diagonal_projection` says precisely that its components are
those maps.  No such datum is constructed in this module. -/
structure TruncationCoproductDatum (t : TStructure C) (X : C) where
  P : C
  ι : ∀ n : ULift.{v} ℕ, (t.truncGE (n.down : ℤ)).obj X ⟶ P
  isColimit : IsColimit (Cofan.mk P ι)
  diagonal : X ⟶ P
  diagonal_projection (n : ULift.{v} ℕ) :
    diagonal ≫ RelativeWeakApprox.coproductProjection (C := C)
        (J := ULift.{v} ℕ) ι isColimit n =
      (t.truncGEπ (n.down : ℤ)).app X

/-- Compactness and the special truncation coproduct imply bounded-above
cohomology.  The argument after finite-support extraction is only the exactness
of `Hom` on a distinguished triangle and orthogonality for a `t`-structure. -/
theorem exists_isLE_of_truncationCoproductDatum
    (t : TStructure C) {X : C} (hX : IsCompactAb X)
    (D : TruncationCoproductDatum t X) : ∃ n : ℤ, t.IsLE X n := by
  obtain ⟨n, hn⟩ := exists_comp_coproductProjection_eq_zero (J := ULift.{v} ℕ) hX
    (fun n : ULift.{v} ℕ => (t.truncGE (n.down : ℤ)).obj X)
    D.ι D.isColimit D.diagonal
  have hzero : (t.truncGEπ (n.down : ℤ)).app X = 0 := by
    rw [← D.diagonal_projection n]
    exact hn
  obtain ⟨r, hr⟩ := Triangle.coyoneda_exact₂ ((t.triangleLTGE (n.down : ℤ)).obj X)
    (t.triangleLTGE_distinguished (n.down : ℤ) X) (𝟙 X) (by
      change 𝟙 X ≫ (t.truncGEπ (n.down : ℤ)).app X = 0
      rw [hzero, comp_zero])
  let s : Retract X ((t.truncLT (n.down : ℤ)).obj X) :=
    { i := r
      r := (t.truncLTι (n.down : ℤ)).app X
      retract := hr.symm }
  exact ⟨(n.down : ℤ) - 1,
    isLE_of_retract t s ((n.down : ℤ) - 1) inferInstance⟩

end Truncations

section RingConclusion

universe uA

open RelativeFM
open RelativeFM.AffinePerfect

attribute [local instance] HasDerivedCategory.standard

/-- A bounded model whose terms are free, but not assumed finitely generated.
This is the intermediate object in the induction in Stacks 07LT. -/
structure BoundedFreeModel (A : Type uA) [CommRing A] (Y : AffineD A) where
  complex : CochainComplex (ModuleCat A) ℤ
  lower : ℤ
  upper : ℤ
  isStrictlyGE : complex.IsStrictlyGE lower
  isStrictlyLE : complex.IsStrictlyLE upper
  bounds : lower ≤ upper + 1
  free : ∀ n, Module.Free A (complex.X n)
  iso : Y ≅ DerivedCategory.Q.obj complex

/-- An identity factorization through a bounded complex of free modules. -/
structure BoundedFreeFactorization (A : Type uA) [CommRing A] (X : AffineD A) where
  compact : IsCompactAb X
  Y : AffineD A
  model : BoundedFreeModel A Y
  φ : X ⟶ Y
  ψ : Y ⟶ X
  factor : φ ≫ ψ = 𝟙 X

/-- A (not necessarily bounded) model by a complex of free modules. -/
structure FreeComplexModel (A : Type uA) [CommRing A] (X : AffineD A) where
  complex : CochainComplex (ModuleCat A) ℤ
  free : ∀ n, Module.Free A (complex.X n)
  iso : X ≅ DerivedCategory.Q.obj complex

/-- A bounded-free subcomplex stage of a free complex model. -/
structure BoundedFreeStage (A : Type uA) [CommRing A]
    (P : CochainComplex (ModuleCat A) ℤ) where
  complex : CochainComplex (ModuleCat A) ℤ
  lower : ℤ
  upper : ℤ
  isStrictlyGE : complex.IsStrictlyGE lower
  isStrictlyLE : complex.IsStrictlyLE upper
  bounds : lower ≤ upper + 1
  free : ∀ n, Module.Free A (complex.X n)
  ι : complex ⟶ P

/-- Bounded-free stages whose induced maps on derived Homs into `Q M.complex`
are jointly surjective.  For an exhaustive termwise filtered system, this is
precisely the surjectivity conclusion of Stacks 07LR; no filtered-colimit
construction is smuggled into this definition. -/
structure BoundedFreeFiltration (A : Type uA) [CommRing A] {X : AffineD A}
    (M : FreeComplexModel A X) where
  indices : Type uA
  stage : indices → BoundedFreeStage A M.complex
  surjective : ∀ δ : X ⟶ DerivedCategory.Q.obj M.complex,
    ∃ i, ∃ f : X ⟶ DerivedCategory.Q.obj (stage i).complex,
      f ≫ DerivedCategory.Q.map (stage i).ι = δ

/-- Joint Hom-surjectivity applied to the forward component of the model iso
produces an identity factorization through one bounded-free stage. -/
theorem nonempty_boundedFreeFactorization_of_filtration
    (A : Type uA) [CommRing A] {X : AffineD A}
    (M : FreeComplexModel A X) (F : BoundedFreeFiltration A M)
    (hX : IsCompactAb X) :
    Nonempty (BoundedFreeFactorization A X) := by
  obtain ⟨i, f, hf⟩ := F.surjective M.iso.hom
  let S := F.stage i
  refine ⟨
    { compact := hX
      Y := DerivedCategory.Q.obj S.complex
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
      ψ := DerivedCategory.Q.map S.ι ≫ M.iso.inv
      factor := ?_ }⟩
  change f ≫ (DerivedCategory.Q.map S.ι ≫ M.iso.inv) = 𝟙 X
  rw [← Category.assoc, hf, M.iso.hom_inv_id]

/-- Terms in degrees strictly below `c` are finitely generated. -/
def FiniteBelow (A : Type uA) [CommRing A] {X : AffineD A}
    (F : BoundedFreeFactorization A X) (c : ℤ) : Prop :=
  ∀ n, n < c → Module.Finite A (F.model.complex.X n)

/-- Terms strictly below the lower strict bound are zero, hence finitely
generated. -/
lemma finiteBelow_lower (A : Type uA) [CommRing A] {X : AffineD A}
    (F : BoundedFreeFactorization A X) : FiniteBelow A F F.model.lower := by
  intro n hn
  letI := F.model.isStrictlyGE
  exact moduleFinite_of_isZero A
    (F.model.complex.isZero_of_isStrictlyGE F.model.lower n hn)

/-- The single-degree finiteness improvement used in Stacks 07LT.  In the
published argument it is obtained by projecting to infinitely many free basis
vectors, using compactness to make the composite vanish, and replacing the old
model by the kernel of this projection.  Bounds are required to be preserved. -/
structure FiniteFreeImprovementInput (A : Type uA) [CommRing A] where
  improve : ∀ {X : AffineD A} (F : BoundedFreeFactorization A X) (c : ℤ),
    FiniteBelow A F c → c ≤ F.model.upper →
    ∃ F' : BoundedFreeFactorization A X,
      F'.model.lower = F.model.lower ∧ F'.model.upper = F.model.upper ∧
      FiniteBelow A F' (c + 1)

/-- The ring-specific data in one step of the finite-free induction.  The new
model is the left term of a distinguished triangle over the old model.  The
projected composite is zero; finiteness is required only through degree `c`.
No lifting map is included: it is constructed from exactness below. -/
structure DegreeImprovementTriangleDatum (A : Type uA) [CommRing A]
    {X : AffineD A} (F : BoundedFreeFactorization A X) (c : ℤ) where
  Y' : AffineD A
  model' : BoundedFreeModel A Y'
  ι : Y' ⟶ F.Y
  Z : AffineD A
  π : F.Y ⟶ Z
  δ : Z ⟶ Y'⟦(1 : ℤ)⟧
  distinguished : Triangle.mk ι π δ ∈ distTriang (AffineD A)
  vanish : F.φ ≫ π = 0
  lower : model'.lower = F.model.lower
  upper : model'.upper = F.model.upper
  finite : ∀ n, n < c + 1 → Module.Finite A (model'.complex.X n)

/-- Exactness of `Hom(X, -)` on the improvement triangle produces the lifted
identity factorization.  This is the purely categorical part of the displayed
`φ'`/`ψ'` construction in Stacks 07LT. -/
theorem exists_improved_factorization_of_triangleDatum
    (A : Type uA) [CommRing A] {X : AffineD A}
    (F : BoundedFreeFactorization A X) (c : ℤ)
    (D : DegreeImprovementTriangleDatum A F c) :
    ∃ F' : BoundedFreeFactorization A X,
      F'.model.lower = F.model.lower ∧ F'.model.upper = F.model.upper ∧
      FiniteBelow A F' (c + 1) := by
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

/-- Construct the one-degree improvement operation from the explicit triangle
models.  All Hom-exactness and factorization bookkeeping is thereby proved. -/
theorem finiteFreeImprovementInput_of_triangleData
    (A : Type uA) [CommRing A]
    (datum : ∀ {X : AffineD A} (F : BoundedFreeFactorization A X) (c : ℤ),
      FiniteBelow A F c → c ≤ F.model.upper →
      Nonempty (DegreeImprovementTriangleDatum A F c)) :
    FiniteFreeImprovementInput A where
  improve F c hfin hc :=
    exists_improved_factorization_of_triangleDatum A F c (datum F c hfin hc).some

/-- **The finite-free induction in Stacks 07LT.**  Repeatedly apply the
one-degree improvement from the lower bound to `upper + 1`.  All remaining
terms vanish strictly above the upper bound, so the result is a bounded complex
of finitely generated projectives. -/
theorem exists_finite_projective_factorization
    (A : Type uA) [CommRing A] (I : FiniteFreeImprovementInput A)
    {X : AffineD A} (F : BoundedFreeFactorization A X) :
    ∃ Y : AffineD A, Nonempty (BoundedFiniteProjectiveModel A Y) ∧
      ∃ φ : X ⟶ Y, ∃ ψ : Y ⟶ X, φ ≫ ψ = 𝟙 X := by
  let motive := fun c (_ : F.model.lower ≤ c) => c ≤ F.model.upper + 1 →
    ∃ F' : BoundedFreeFactorization A X,
      F'.model.lower = F.model.lower ∧ F'.model.upper = F.model.upper ∧
      FiniteBelow A F' c
  have hex : motive (F.model.upper + 1) F.model.bounds := by
    refine Int.leInduction (motive := motive) (fun _ => ⟨F, rfl, rfl,
      finiteBelow_lower A F⟩) ?_ (F.model.upper + 1) F.model.bounds
    intro c hc ih hcb
    obtain ⟨H, hHl, hHu, hHfin⟩ := ih (by omega)
    obtain ⟨H', hH'l, hH'u, hH'fin⟩ := I.improve H c hHfin (by omega)
    exact ⟨H', hH'l.trans hHl, hH'u.trans hHu, hH'fin⟩
  obtain ⟨G, hGl, hGu, hGfin⟩ := hex (le_refl _)
  have hfinite : ∀ n, Module.Finite A (G.model.complex.X n) := by
    intro n
    by_cases hn : n < G.model.upper + 1
    · rw [hGu] at hn
      exact hGfin n hn
    · have hn' : G.model.upper < n := by omega
      letI := G.model.isStrictlyLE
      exact moduleFinite_of_isZero A
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

/-- The output of the bounded-free factorization and finiteness induction in
Stacks 07LT.  Notice that this is not the assertion `compact ⇒ perfect`: it
retains the stronger retract-of-a-bounded-projective-model information. -/
structure Stacks07LTBoundedFactorizationInput (A : Type uA) [CommRing A] where
  factorization : ∀ X : AffineD A, IsCompactAb X →
    ∃ Y : AffineD A, Nonempty (BoundedFiniteProjectiveModel A Y) ∧
      ∃ φ : X ⟶ Y, ∃ ψ : Y ⟶ X, φ ≫ ψ = 𝟙 X

/-- Two residual constructions before the induction: an initial bounded-free
identity factorization, and the one-degree improvement. -/
structure BoundedFreeInductionInput (A : Type uA) [CommRing A] where
  initial : ∀ X : AffineD A, IsCompactAb X →
    Nonempty (BoundedFreeFactorization A X)
  improve : FiniteFreeImprovementInput A

/-- The induction turns arbitrary bounded-free identity factorizations into
bounded finite-projective ones, preserving the identity factorization. -/
theorem stacks07LTBoundedFactorizationInput_of_freeInduction
    (A : Type uA) [CommRing A] (I : BoundedFreeInductionInput A) :
    Stacks07LTBoundedFactorizationInput A where
  factorization X hX := by
    let F := (I.initial X hX).some
    exact exists_finite_projective_factorization A I.improve F

/-- The final retract step of Stacks 07LT gives the implication actually used
by the affine gluing theorem.  Stacks 066S is not needed for this implication. -/
theorem compactToPerfectInput_of_boundedFactorization
    (A : Type uA) [CommRing A] (I : Stacks07LTBoundedFactorizationInput A) :
    CompactToPerfectInput A where
  perfect_of_compact X hX := by
    obtain ⟨Y, hY, φ, ψ, hφψ⟩ := I.factorization X hX
    let r : Retract X Y := { i := φ, r := ψ, retract := hφψ }
    exact (Perf A).prop_of_retract r (AffinePerfect.model_mem_perf A Y hY)

/-- `compact ⇒ Perf`, with only the initial bounded-free factorization and the
explicit one-degree improvement data left as inputs. -/
theorem compactToPerfectInput_of_freeInduction
    (A : Type uA) [CommRing A] (I : BoundedFreeInductionInput A) :
    CompactToPerfectInput A :=
  compactToPerfectInput_of_boundedFactorization A
    (stacks07LTBoundedFactorizationInput_of_freeInduction A I)

/-- With the direct-summand theorem for bounded finite-projective models
(Stacks 066S), the same factorization input also gives the full compact-to-model
statement.  Before applying 066S, compactness is used only to obtain `Perf A`. -/
theorem stacks07LTCompactModelInput_of_boundedFactorization
    (A : Type uA) [CommRing A] (I : Stacks07LTBoundedFactorizationInput A)
    (hR : (HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts) :
    Stacks07LTCompactModelInput A where
  model_of_compact X hX := by
    have J := compactToPerfectInput_of_boundedFactorization A I
    exact AffinePerfect.model_of_perf_of_stableUnderRetracts A hR X
      (J.perfect_of_compact X hX)

/-- Full `Stacks07LTCompactModelInput` from the two bounded-free induction inputs
and the separate Stacks 066S retract-closure theorem. -/
theorem stacks07LTCompactModelInput_of_freeInduction
    (A : Type uA) [CommRing A] (I : BoundedFreeInductionInput A)
    (hR : (HasBoundedFiniteProjectiveModel A).IsStableUnderRetracts) :
    Stacks07LTCompactModelInput A :=
  stacks07LTCompactModelInput_of_boundedFactorization A
    (stacks07LTBoundedFactorizationInput_of_freeInduction A I) hR

end RingConclusion

end
end RelativeFM.Stacks07LT

#print axioms RelativeFM.Stacks07LT.exists_dfinsupp_coproduct_decomposition
#print axioms RelativeFM.Stacks07LT.exists_comp_coproductProjection_eq_zero
#print axioms RelativeFM.Stacks07LT.sequence_eq_zero_of_sub_transitionTail
#print axioms RelativeFM.Stacks07LT.exists_lift_triangle_of_injective_shift
#print axioms RelativeFM.Stacks07LT.isLE_of_retract
#print axioms RelativeFM.Stacks07LT.exists_isLE_of_truncationCoproductDatum
#print axioms RelativeFM.Stacks07LT.nonempty_boundedFreeFactorization_of_filtration
#print axioms RelativeFM.Stacks07LT.exists_improved_factorization_of_triangleDatum
#print axioms RelativeFM.Stacks07LT.finiteFreeImprovementInput_of_triangleData
#print axioms RelativeFM.Stacks07LT.exists_finite_projective_factorization
#print axioms RelativeFM.Stacks07LT.stacks07LTBoundedFactorizationInput_of_freeInduction
#print axioms RelativeFM.Stacks07LT.compactToPerfectInput_of_boundedFactorization
#print axioms RelativeFM.Stacks07LT.compactToPerfectInput_of_freeInduction
#print axioms RelativeFM.Stacks07LT.stacks07LTCompactModelInput_of_boundedFactorization
#print axioms RelativeFM.Stacks07LT.stacks07LTCompactModelInput_of_freeInduction
