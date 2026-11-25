import FourierMukai.Scheme.CompactToPerfect
import FourierMukai.Scheme.AisleGenFiltration
import Mathlib.Algebra.Category.ModuleCat.Biproducts

import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Category.ModuleCat.LeftResolution
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# The bounded above resolution engine

Let `A` be an abelian category, let `R` be a weak Serre class in `A` and let `G` be a class of
objects of `A` which contains the zero object, is closed under binary biproducts and under
isomorphism, and covers epimorphisms onto objects of `R` (`CoversEpis`). Then every cochain
complex `X` with `X^i = 0` for `i > a` whose cohomology objects all lie in `R` receives a
quasi-isomorphism from a cochain complex `Y` with `Y^i = 0` for `i > a` and every term in `G`
(`exists_quasiIso_isStrictlyLE_of_coversEpis`).

## Main definitions

* `Stacks.Homology.BoundedAboveResolution.CoversEpis` - the hypothesis that a class `G` of
  objects of an abelian category epimorphically covers, after refinement, every epimorphism onto
  an object of an ambient class `R`.
* `CategoryTheory.descExtend` - a morphism out of a complex extended along
  `ComplexShape.embeddingUpIntLE`, built from a morphism to the restriction.

## Main results

* `Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis` - the
  engine described above.

## Implementation notes

`Y` is built degree by degree downwards from `a`, as a `ℕ`-indexed chain complex of layers
(`resolution`) which is extended back to a `ℤ`-indexed cochain complex along
`ComplexShape.embeddingUpIntLE`. In each degree the new term is the biproduct of an object of `G`
covering the cohomology of `X` in that degree, which makes the map surjective on cohomology, and
an object of `G` covering, up to refinement, those cocycles of the previously built term whose
image in `X` is a boundary, which makes the map injective on cohomology; that these two
properties in every degree suffice is `quasiIso_of_epi_of_cover`. A `Layer` in degree `i` carries
an object of `G`, its map to `X^i`, its differential and the preceding degree with its own map to
`X`, so consecutive layers compose without transport.

Morphisms *out of* an extended complex are not provided by Mathlib -
`ComplexShape.Embedding.homEquiv` constructs only morphisms *into* one - so they are built here
as `descExtend`, the boundary case `i ≤ a < i + 1` being handled by
`X.d i (i + 1) = 0`.

The intermediate layers are chosen, not canonical: `CoversEpis` asserts that a cover exists and
the recursion picks one at each degree with `Nonempty.some`, which is why `Classical.choice`
appears in the axioms of every declaration of the construction. Nothing in the public interface
extracts data from an existence statement: the engine's conclusion is existential, and every
definition which does make such a choice is private to this module.

Two classes are separated here because the consumers need them separated: for [Stacks, Tag 0FCL]
the terms of the resolution are asked to lie in the very Serre class `P` whose objects the
cohomology lies in, which is the case `G = P`, while for [Stacks, Tag 0960] the terms must be
finite affine shriek sums whereas the cohomology is merely constructible.

## References

* [Stacks project, Tag 0FCL](https://stacks.math.columbia.edu/tag/0FCL)
* [Stacks project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
-/

universe v u

namespace RelativeFM.Stacks07LT.M2.Resolution

open CategoryTheory CategoryTheory.Limits ZeroObject ComplexShape

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Any morphism into the target of an epimorphism factors through it after an epimorphism of its
source: the refinement of `τ` by `σ` is the pullback of the two. -/
lemma exists_epi_fac_of_epi {T V W : A} (τ : T ⟶ W) (σ : V ⟶ W) [Epi σ] :
    ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p) (v : T' ⟶ V), p ≫ τ = v ≫ σ :=
  ⟨pullback τ σ, pullback.fst τ σ, inferInstance, pullback.snd τ σ, pullback.condition⟩

private lemma isZero_extend_X_of_not_le (K : ChainComplex A ℕ) (a i : ℤ) (hi : ¬ i ≤ a) :
    IsZero ((K.extend (embeddingUpIntLE a)).X i) :=
  HomologicalComplex.isZero_extend_X K (embeddingUpIntLE a) i
    (fun n => by rw [embeddingUpIntLE_f]; omega)

private lemma embeddingUpIntLE_f_toNat {a i : ℤ} (hi : i ≤ a) :
    (embeddingUpIntLE a).f (a - i).toNat = i := by
  rw [embeddingUpIntLE_f]; omega
section Desc

variable (X : CochainComplex A ℤ) (K : ChainComplex A ℕ) (a : ℤ)
  (φ : K ⟶ X.restriction (embeddingUpIntLE a))

/-- Auxiliary definition for `descExtend`. -/
noncomputable def descF (i : ℤ) : (K.extend (embeddingUpIntLE a)).X i ⟶ X.X i :=
  if hi : i ≤ a then
    (K.extendXIso _ (embeddingUpIntLE_f_toNat hi)).hom ≫ φ.f (a - i).toNat ≫
      (X.restrictionXIso _ (embeddingUpIntLE_f_toNat hi)).hom
  else 0

/-- In a degree `i = (embeddingUpIntLE a).f n` coming from `n : ℕ`, the component `descF X K a φ i`
is `φ.f n`, transported along the identifications of the degree-`i` objects of the extension of `K`
and of `X` with the degree-`n` objects of `K` and of the restriction of `X`. -/
lemma descF_eq {n : ℕ} {i : ℤ} (h : (embeddingUpIntLE a).f n = i) :
    descF X K a φ i =
      (K.extendXIso _ h).hom ≫ φ.f n ≫ (X.restrictionXIso _ h).hom := by
  have hi : i ≤ a := by rw [embeddingUpIntLE_f] at h; omega
  have h1 : descF X K a φ i = (K.extendXIso _ (embeddingUpIntLE_f_toNat hi)).hom ≫
      φ.f (a - i).toNat ≫ (X.restrictionXIso _ (embeddingUpIntLE_f_toNat hi)).hom := by
    simp [descF, hi]
  obtain rfl : (a - i).toNat = n :=
    (embeddingUpIntLE a).injective_f ((embeddingUpIntLE_f_toNat hi).trans h.symm)
  rw [h1]

private lemma descF_eq_zero {i : ℤ} (hi : ¬ i ≤ a) : descF X K a φ i = 0 := by
  simp [descF, hi]

/-- The maps `descF X K a φ i` commute with the differentials of the extension of `K` and of `X`,
when `X` is strictly `≤ a`. -/
lemma descF_comm [X.IsStrictlyLE a] (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    descF X K a φ i ≫ X.d i j = (K.extend (embeddingUpIntLE a)).d i j ≫ descF X K a φ j := by
  change i + 1 = j at hij
  by_cases hi : i ≤ a
  · have hn := embeddingUpIntLE_f_toNat (a := a) hi
    by_cases hj : j ≤ a
    · have hm := embeddingUpIntLE_f_toNat (a := a) hj
      obtain ⟨m, hm2⟩ : ∃ m : ℕ, (a - j).toNat = m := ⟨_, rfl⟩
      rw [hm2] at hm
      rw [show (a - i).toNat = m + 1 by omega] at hn
      rw [descF_eq X K a φ hn, descF_eq X K a φ hm,
        HomologicalComplex.extend_d_eq K (embeddingUpIntLE a) hn hm]
      have hc := φ.comm (m + 1) m
      rw [HomologicalComplex.restriction_d_eq X (embeddingUpIntLE a) hn hm] at hc
      have hc' : φ.f (m + 1) ≫ (X.restrictionXIso (embeddingUpIntLE a) hn).hom ≫ X.d i j =
          K.d (m + 1) m ≫ φ.f m ≫ (X.restrictionXIso (embeddingUpIntLE a) hm).hom := by
        rw [← Category.assoc (K.d (m + 1) m), ← hc]; simp
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hc']
    · rw [(X.isZero_of_isStrictlyLE a j (by omega)).eq_of_tgt (X.d i j) 0, comp_zero,
        descF_eq_zero X K a φ hj, comp_zero]
  · rw [descF_eq_zero X K a φ hi, zero_comp,
      (isZero_extend_X_of_not_le K a i hi).eq_of_src
          ((K.extend (embeddingUpIntLE a)).d i j) 0, zero_comp]

/-- A morphism out of an extended complex, from a morphism to the restriction. -/
@[expose] noncomputable def descExtend [X.IsStrictlyLE a] :
    K.extend (embeddingUpIntLE a) ⟶ X where
  f i := descF X K a φ i
  comm' i j hij := descF_comm X K a φ i j hij

/-- The degree-`i` component of `descExtend X K a φ` is `descF X K a φ i`. -/
lemma descExtend_f [X.IsStrictlyLE a] (i : ℤ) :
    (descExtend X K a φ).f i = descF X K a φ i := rfl
end Desc

end RelativeFM.Stacks07LT.M2.Resolution

@[expose] noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace RelativeFM.Stacks07LT.M2.Resolution

open Limits ZeroObject

variable {A : Type*} [Category A] [Abelian A]

class IsWeakSerreClass (P : ObjectProperty A) : Prop where
  prop_kernel {X Y : A} (f : X ⟶ Y) : P X → P Y → P (kernel f)
  prop_biprod {X Y : A} : P X → P Y → P (X ⊞ Y)
  prop_zero : P 0

instance : RelativeFM.Stacks07LT.M2.Resolution.IsWeakSerreClass (fun _ => True : ObjectProperty A) where
  prop_kernel _ _ _ := trivial
  prop_biprod _ _ := trivial
  prop_zero := trivial

end RelativeFM.Stacks07LT.M2.Resolution

namespace RelativeFM.Stacks07LT.M2.Resolution

open ZeroObject ComplexShape

variable {A : Type*} [Category A] [Abelian A]

/-- A class `G` of objects of an abelian category **covers epimorphisms** onto a class `R` when
every epimorphism `f : V ⟶ W` with `W` in `R` can be refined by an object of `G`: there are an
object `V'` of `G`, which is moreover in `R`, and a map `g : V' ⟶ V` with `g ≫ f` epimorphic.

The ambient class `R` is only ever asked to be a weak Serre class; it is what the kernels and
pullbacks occurring in the construction are tested against, while `G` controls the terms of the
resolution which comes out. -/
def CoversEpis (R : ObjectProperty A) (G : A → Prop) : Prop :=
  ∀ ⦃V W : A⦄ (f : V ⟶ W), Epi f → R W →
    ∃ (V' : A) (g : V' ⟶ V), G V' ∧ R V' ∧ Epi (g ≫ f)

/-- The sequence `X^(i-1) ⟶ Z^i ⟶ H^i` is exact. -/
private lemma exact_toCycles_homologyπ (X : CochainComplex A ℤ) (i : ℤ) :
    (ShortComplex.mk (X.toCycles (i - 1) i) (X.homologyπ i)
      (X.toCycles_comp_homologyπ _ _)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (X.homologyIsCokernel (i - 1) i (by simp))

/-- A map of cochain complexes which is surjective on cohomology, and injective on cohomology up
to refinements, is a quasi-isomorphism.

Surjectivity in degree `i` is witnessed by an object `C` mapping to the degree-`i` cocycles of
`Y` and onto the degree-`i` cohomology of `X`; injectivity is witnessed by the ability to refine
any cocycle of `Y` whose image in `X` is a boundary to a boundary of `Y`. -/
private lemma quasiIso_of_epi_of_cover {X Y : CochainComplex A ℤ} (φ : Y ⟶ X)
    (hepi : ∀ i : ℤ, ∃ (C : A) (γ : C ⟶ Y.X i) (c : C ⟶ X.cycles i), γ ≫ Y.d i (i + 1) = 0 ∧
      c ≫ X.iCycles i = γ ≫ φ.f i ∧ Epi (c ≫ X.homologyπ i))
    (hcov : ∀ (i : ℤ) ⦃T : A⦄ (t : T ⟶ Y.X i), t ≫ Y.d i (i + 1) = 0 →
      (∃ u : T ⟶ X.X (i - 1), t ≫ φ.f i = u ≫ X.d (i - 1) i) →
      ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p) (s : T' ⟶ Y.X (i - 1)),
        p ≫ t = s ≫ Y.d (i - 1) i) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hnext : (ComplexShape.up ℤ).next i = i + 1 := by simp
  have hE : Epi (HomologicalComplex.homologyMap φ i) := by
    obtain ⟨C, γ, c, hγd, hγc, hce⟩ := hepi i
    have hlift : Y.liftCycles γ (i + 1) hnext hγd ≫ HomologicalComplex.cyclesMap φ i = c := by
      rw [← cancel_mono (X.iCycles i)]
      simp [hγc]
    have : (Y.liftCycles γ (i + 1) hnext hγd ≫ Y.homologyπ i) ≫
        HomologicalComplex.homologyMap φ i = c ≫ X.homologyπ i := by
      rw [Category.assoc, HomologicalComplex.homologyπ_naturality, reassoc_of% hlift]
    exact epi_of_epi_fac this
  have hM : Mono (HomologicalComplex.homologyMap φ i) := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro T t ht
    obtain ⟨T₀, π, hπ, q, hq⟩ := exists_epi_fac_of_epi t (Y.homologyπ i)
    have hz : (q ≫ HomologicalComplex.cyclesMap φ i) ≫ X.homologyπ i = 0 := by
      rw [Category.assoc, ← HomologicalComplex.homologyπ_naturality, ← reassoc_of% hq, ht,
        comp_zero]
    obtain ⟨W, e, he, u, hu⟩ := (ShortComplex.exact_iff_exact_up_to_refinements _).1
      (exact_toCycles_homologyπ X i)
      (q ≫ HomologicalComplex.cyclesMap φ i) hz
    obtain ⟨T', p, hp, s, hs⟩ := hcov i ((e ≫ q) ≫ Y.iCycles i) (by simp)
      ⟨u, by
        dsimp at hu
        simp only [Category.assoc]
        rw [← HomologicalComplex.cyclesMap_i, reassoc_of% hu]
        simp⟩
    have key : (p ≫ e ≫ q) ≫ Y.homologyπ i = 0 := by
      have h1 : p ≫ e ≫ q = s ≫ Y.toCycles (i - 1) i := by
        rw [← cancel_mono (Y.iCycles i)]
        simpa using hs
      rw [h1, Category.assoc, Y.toCycles_comp_homologyπ, comp_zero]
    have : Epi (p ≫ e ≫ π) := by have := hp; have := he; have := hπ; infer_instance
    rw [← cancel_epi (p ≫ e ≫ π), comp_zero, Category.assoc, Category.assoc, hq]
    simpa using key
  exact isIso_of_mono_of_epi _

section Resolution

variable (R : ObjectProperty A) [RelativeFM.Stacks07LT.M2.Resolution.IsWeakSerreClass R] (G : A → Prop) (X : CochainComplex A ℤ)

/-- The data produced by one step of the descending induction: an object `Y₀` of the ambient
class, a differential `d₀` into the previous layer, a map `f₀` to the degree-`i` term of `X`
commuting with the differentials, a witness that `Y₀` covers the degree-`i` cohomology of `X`,
and the property that every cocycle of the previous layer whose image in `X` is a boundary is,
up to refinement, a boundary of `d₀`. -/
private structure StepData (i j : ℤ) {Y₁ Y₂ : A} (d₁ : Y₁ ⟶ Y₂) (f₁ : Y₁ ⟶ X.X j) where
  /-- The new layer. -/
  Y₀ : A
  /-- The new layer lies in the ambient class. -/
  hY₀ : R Y₀
  /-- The differential into the previous layer. -/
  d₀ : Y₀ ⟶ Y₁
  /-- The map to the degree-`i` term of `X`. -/
  f₀ : Y₀ ⟶ X.X i
  /-- The composite of two consecutive differentials vanishes. -/
  zero : d₀ ≫ d₁ = 0
  /-- The maps to `X` commute with the differentials. -/
  comm : f₀ ≫ X.d i j = d₀ ≫ f₁
  /-- The new layer covers the degree-`i` cohomology of `X`. -/
  epiH : ∃ (C : A) (γ : C ⟶ Y₀) (c : C ⟶ X.cycles i), γ ≫ d₀ = 0 ∧
    c ≫ X.iCycles i = γ ≫ f₀ ∧ Epi (c ≫ X.homologyπ i)
  /-- Cocycles of the previous layer which become boundaries in `X` are, up to refinement,
  boundaries of `d₀`. -/
  cover : ∀ ⦃T : A⦄ (t : T ⟶ Y₁), t ≫ d₁ = 0 → (∃ u : T ⟶ X.X i, t ≫ f₁ = u ≫ X.d i j) →
    ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p) (s : T' ⟶ Y₀), p ≫ t = s ≫ d₀

/-- The second summand of a step: an object of `G` inside the ambient class which covers, up to
refinement, every cocycle of the previous layer whose image in `X` is a boundary. -/
private lemma exists_prop_boundary_cover (hP : CoversEpis R G)
    (hX : ∀ k, R (X.homology k)) (i j : ℤ) (hij : i + 1 = j)
    {Y₁ Y₂ : A} (hY₁ : R Y₁) (hY₂ : R Y₂) (d₁ : Y₁ ⟶ Y₂)
    (f₁ : Y₁ ⟶ X.X j) (f₂ : Y₂ ⟶ X.X (j + 1))
    (hcomm : f₁ ≫ X.d j (j + 1) = d₁ ≫ f₂) :
    ∃ (E : A) (_ : G E) (_ : R E) (dE : E ⟶ Y₁) (fE : E ⟶ X.X i),
      dE ≫ d₁ = 0 ∧ fE ≫ X.d i j = dE ≫ f₁ ∧
      ∀ ⦃T : A⦄ (t : T ⟶ Y₁), t ≫ d₁ = 0 →
        (∃ u : T ⟶ X.X i, t ≫ f₁ = u ≫ X.d i j) →
        ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p) (s : T' ⟶ E), p ≫ t = s ≫ dE := by
  have hK : R (kernel d₁) := RelativeFM.Stacks07LT.M2.Resolution.IsWeakSerreClass.prop_kernel d₁ hY₁ hY₂
  have hcycle : (kernel.ι d₁ ≫ f₁) ≫ X.d j (j + 1) = 0 := by
    calc
      (kernel.ι d₁ ≫ f₁) ≫ X.d j (j + 1) =
          kernel.ι d₁ ≫ (f₁ ≫ X.d j (j + 1)) := by rw [Category.assoc]
      _ = kernel.ι d₁ ≫ (d₁ ≫ f₂) := by rw [hcomm]
      _ = 0 := by simp
  let c := X.liftCycles (kernel.ι d₁ ≫ f₁) (j + 1) (by simp) hcycle
  let m := c ≫ X.homologyπ j
  let W := kernel m
  have hW : R W := RelativeFM.Stacks07LT.M2.Resolution.IsWeakSerreClass.prop_kernel m hK (hX j)
  have hz : (kernel.ι m ≫ c) ≫ X.homologyπ j = 0 := by
    calc
      (kernel.ι m ≫ c) ≫ X.homologyπ j = kernel.ι m ≫ (c ≫ X.homologyπ j) := by
        simp only [Category.assoc]
      _ = kernel.ι m ≫ m := by rfl
      _ = 0 := kernel.condition m
  obtain ⟨W', e, he, u, hu⟩ :=
    (ShortComplex.exact_iff_exact_up_to_refinements _).1
      (exact_toCycles_homologyπ X j) (kernel.ι m ≫ c) hz
  obtain ⟨E, σ, hQE, hE, hepi⟩ := hP e inferInstance hW
  have hi : i = j - 1 := by omega
  subst i
  let dE := σ ≫ e ≫ kernel.ι m ≫ kernel.ι d₁
  let fE := σ ≫ u
  have hc : c ≫ X.iCycles j = kernel.ι d₁ ≫ f₁ := by
    dsimp [c]
    exact X.liftCycles_i (kernel.ι d₁ ≫ f₁) (j + 1) (by simp) hcycle
  refine ⟨E, hQE, hE, dE, fE, ?_, ?_, ?_⟩
  · simp [dE, Category.assoc]
  · have huc : σ ≫ e ≫ kernel.ι m ≫ c ≫ X.iCycles j =
        σ ≫ u ≫ X.d (j - 1) j := by
      have h := congrArg (fun z => σ ≫ z ≫ X.iCycles j) hu
      simpa only [Category.assoc, X.toCycles_i] using h
    calc
      fE ≫ X.d (j - 1) j = σ ≫ u ≫ X.d (j - 1) j := by simp [fE, Category.assoc]
      _ = σ ≫ e ≫ kernel.ι m ≫ c ≫ X.iCycles j := huc.symm
      _ = dE ≫ f₁ := by simp [dE, Category.assoc, hc]
  · rintro T t ht ⟨v, hv⟩
    let k := kernel.lift d₁ t ht
    have hcycles : k ≫ c ≫ X.iCycles j = t ≫ f₁ := by
      calc
        k ≫ c ≫ X.iCycles j = k ≫ (c ≫ X.iCycles j) := rfl
        _ = k ≫ (kernel.ι d₁ ≫ f₁) := by rw [hc]
        _ = t ≫ f₁ := by rw [← Category.assoc, kernel.lift_ι]
    have hcyclev : (v ≫ X.toCycles (j - 1) j) ≫ X.iCycles j = t ≫ f₁ := by
      calc
        (v ≫ X.toCycles (j - 1) j) ≫ X.iCycles j = v ≫ X.d (j - 1) j := by
          rw [Category.assoc, X.toCycles_i]
        _ = t ≫ f₁ := hv.symm
    have hk : k ≫ c = v ≫ X.toCycles (j - 1) j := by
      apply (cancel_mono (X.iCycles j)).1
      simpa using hcycles.trans hcyclev.symm
    have hzT : k ≫ m = 0 := by
      calc
        k ≫ m = k ≫ (c ≫ X.homologyπ j) := by rfl
        _ = (k ≫ c) ≫ X.homologyπ j := by
          simp only [Category.assoc]
        _ = (v ≫ X.toCycles (j - 1) j) ≫ X.homologyπ j := by rw [hk]
        _ = 0 := by rw [Category.assoc, X.toCycles_comp_homologyπ, comp_zero]
    let w := kernel.lift m k hzT
    obtain ⟨T', p, hp, s, hs⟩ := exists_epi_fac_of_epi w (σ ≫ e)
    refine ⟨T', p, hp, s, ?_⟩
    have hkι : k ≫ kernel.ι d₁ = t := kernel.lift_ι d₁ t ht
    have hwι : w ≫ kernel.ι m = k := kernel.lift_ι m k hzT
    calc
      p ≫ t = p ≫ (k ≫ kernel.ι d₁) := by rw [hkι]
      _ = p ≫ (w ≫ kernel.ι m) ≫ kernel.ι d₁ := by rw [hwι]
      _ = (p ≫ w) ≫ kernel.ι m ≫ kernel.ι d₁ := by simp [Category.assoc]
      _ = (s ≫ σ ≫ e) ≫ kernel.ι m ≫ kernel.ι d₁ := by rw [hs]
      _ = s ≫ dE := by simp [dE, Category.assoc]

/-- One step of the descending induction exists: the new layer is the biproduct of a cover of the
degree-`i` cohomology of `X` and a cover of the boundaries, both taken in `G`. -/
private lemma nonempty_stepData (hP : CoversEpis R G)
    (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E))
    (hX : ∀ i, R (X.homology i)) (i j : ℤ) (hij : i + 1 = j)
    {Y₁ Y₂ : A} (hY₁ : R Y₁) (hY₂ : R Y₂) (d₁ : Y₁ ⟶ Y₂)
    (f₁ : Y₁ ⟶ X.X j) (f₂ : Y₂ ⟶ X.X (j + 1))
    (hcomm : f₁ ≫ X.d j (j + 1) = d₁ ≫ f₂) :
    Nonempty {s : StepData R X i j d₁ f₁ // G s.Y₀} := by
  obtain ⟨C, γ, hQC, hC, hγ⟩ := hP (X.homologyπ i) inferInstance (hX i)
  obtain ⟨E, hQE, hE, dE, fE, hdE, hfE, hcov⟩ :=
    exists_prop_boundary_cover R G X hP hX i j hij hY₁ hY₂ d₁ f₁ f₂ hcomm
  let s : StepData R X i j d₁ f₁ :=
    { Y₀ := C ⊞ E
      hY₀ := RelativeFM.Stacks07LT.M2.Resolution.IsWeakSerreClass.prop_biprod hC hE
      d₀ := biprod.desc 0 dE
      f₀ := biprod.desc (γ ≫ X.iCycles i) fE
      zero := by apply biprod.hom_ext' <;> simp [hdE]
      comm := by apply biprod.hom_ext' <;> simp [hfE]
      epiH := ⟨C, biprod.inl, γ, by simp, by simp, hγ⟩
      cover := by
        intro T t ht hu
        obtain ⟨T', p, hp, s, hs⟩ := hcov t ht hu
        exact ⟨T', p, hp, s ≫ biprod.inr, by simpa using hs⟩ }
  exact ⟨⟨s, hQbiprod hQC hQE⟩⟩

/-- The state carried by the descending induction at degree `i`: the layer `Y` in degree `i`,
its map `f` to `X`, and the previous layer `Z` with its own map to `X`. -/
private structure Layer (i : ℤ) where
  /-- The layer in degree `i`. -/
  Y : A
  /-- The layer lies in the ambient class. -/
  hY : R Y
  /-- The layer lies in `G`. -/
  hQ : G Y
  /-- Its map to the degree-`i` term of `X`. -/
  f : Y ⟶ X.X i
  /-- The layer in degree `i + 1`. -/
  Z : A
  /-- It lies in the ambient class. -/
  hZ : R Z
  /-- Its map to the degree-`i + 1` term of `X`. -/
  Zf : Z ⟶ X.X (i + 1)
  /-- The differential. -/
  d : Y ⟶ Z
  /-- The maps to `X` commute with the differentials. -/
  comm : f ≫ X.d i (i + 1) = d ≫ Zf

/-- The layer which starts the induction, in the degree just above the bound. -/
private def Layer.zero (i : ℤ) (hQzero : G (0 : A)) : Layer R G X i where
  Y := 0
  hY := RelativeFM.Stacks07LT.M2.Resolution.IsWeakSerreClass.prop_zero
  hQ := hQzero
  f := 0
  Z := 0
  hZ := RelativeFM.Stacks07LT.M2.Resolution.IsWeakSerreClass.prop_zero
  Zf := 0
  d := 0
  comm := by simp

/-- The step data chosen at a layer. -/
private def Layer.step {i j : ℤ}
    (s : Layer R G X j) (hij : i + 1 = j) (hP : CoversEpis R G)
    (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E))
    (hX : ∀ k, R (X.homology k)) :
    {d : StepData R X i j s.d s.f // G d.Y₀} :=
  (nonempty_stepData R G X hP hQbiprod hX i j hij s.hY s.hZ s.d s.f s.Zf s.comm).some

/-- The layer one degree lower. -/
private def Layer.next {i j : ℤ}
    (s : Layer R G X j) (hij : i + 1 = j) (hP : CoversEpis R G)
    (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E))
    (hX : ∀ k, R (X.homology k)) : Layer R G X i := by
  let d := Layer.step R G X s hij hP hQbiprod hX
  let e := X.XIsoOfEq hij.symm
  exact
    { Y := d.val.Y₀
      hY := d.val.hY₀
      hQ := d.property
      f := d.val.f₀
      Z := s.Y
      hZ := s.hY
      Zf := s.f ≫ e.hom
      d := d.val.d₀
      comm := by
        calc
          d.val.f₀ ≫ X.d i (i + 1) = d.val.f₀ ≫ (X.d i j ≫ e.hom) := by
            rw [← X.d_comp_XIsoOfEq_hom hij.symm i]
          _ = d.val.d₀ ≫ s.f ≫ e.hom := by
            rw [← Category.assoc, d.val.comm]
            simp [Category.assoc] }

/-- The degree of the layer preceding the `n`-th one. -/
private def prevDeg (a : ℤ) : ℕ → ℤ
  | 0 => a - ((0 : ℕ) : ℤ) + 1
  | n + 1 => a - (n : ℤ)

private lemma layerAdjacency (a : ℤ) (n : ℕ) :
    a - ((n + 1 : ℕ) : ℤ) + 1 = prevDeg a (n + 1) := by
  simp [prevDeg]
  omega

section

variable (hP : CoversEpis R G) (hQzero : G (0 : A))
  (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E)) (hX : ∀ i, R (X.homology i)) (a : ℤ)

/-- The `n`-th layer of the resolution, in degree `a - n`. -/
private def layer : (n : ℕ) → Layer R G X (a - (n : ℤ))
  | 0 => Layer.next R G X (Layer.zero R G X (prevDeg a 0) hQzero)
      (by simp [prevDeg]) hP hQbiprod hX
  | n + 1 => Layer.next R G X (layer n) (layerAdjacency a n) hP hQbiprod hX

/-- The layer preceding the `n`-th one. -/
private def prevLayer : (n : ℕ) → Layer R G X (prevDeg a n)
  | 0 => Layer.zero R G X (prevDeg a 0) hQzero
  | n + 1 => layer R G X hP hQzero hQbiprod hX a n

/-- The step data used to build the `n`-th layer. -/
private def layerStep (n : ℕ) :
    {d : StepData R X (a - (n : ℤ)) (prevDeg a n)
      (prevLayer R G X hP hQzero hQbiprod hX a n).d
      (prevLayer R G X hP hQzero hQbiprod hX a n).f // G d.Y₀} :=
  match n with
  | 0 => Layer.step R G X (Layer.zero R G X (prevDeg a 0) hQzero)
      (by simp [prevDeg]) hP hQbiprod hX
  | n + 1 => Layer.step R G X (layer R G X hP hQzero hQbiprod hX a n)
      (layerAdjacency a n) hP hQbiprod hX

/-- The differential of the resolution, from the `n + 1`-st to the `n`-th layer. -/
private def layerD (n : ℕ) :
    (layer R G X hP hQzero hQbiprod hX a (n + 1)).Y ⟶
      (layer R G X hP hQzero hQbiprod hX a n).Y :=
  (layer R G X hP hQzero hQbiprod hX a (n + 1)).d

/-- The resolution, as a `ℕ`-indexed chain complex of layers. -/
private def resolution : ChainComplex A ℕ :=
  ChainComplex.of (fun n => (layer R G X hP hQzero hQbiprod hX a n).Y)
    (layerD R G X hP hQzero hQbiprod hX a)
    (by
      intro n
      change (layerStep R G X hP hQzero hQbiprod hX a (n + 2)).val.d₀ ≫
        (layerStep R G X hP hQzero hQbiprod hX a (n + 1)).val.d₀ = 0
      exact (layerStep R G X hP hQzero hQbiprod hX a (n + 2)).val.zero)

private lemma resolution_d (n : ℕ) :
    (resolution R G X hP hQzero hQbiprod hX a).d (n + 1) n =
      layerD R G X hP hQzero hQbiprod hX a n := by
  unfold resolution
  exact ChainComplex.of_d
    (fun n => (layer R G X hP hQzero hQbiprod hX a n).Y)
    (layerD R G X hP hQzero hQbiprod hX a) n

/-- The map from the resolution to the restriction of `X`. -/
private def resolutionHom :
    resolution R G X hP hQzero hQbiprod hX a ⟶ X.restriction (embeddingUpIntLE a) where
  f n := (layer R G X hP hQzero hQbiprod hX a n).f
  comm' n m hnm := by
    obtain rfl : n = m + 1 := hnm.symm
    rw [resolution_d]
    change (layer R G X hP hQzero hQbiprod hX a (m + 1)).f ≫
      X.d (a - ((m + 1 : ℕ) : ℤ)) (a - (m : ℤ)) =
        layerD R G X hP hQzero hQbiprod hX a m ≫
          (layer R G X hP hQzero hQbiprod hX a m).f
    simpa [embeddingUpIntLE_f, prevDeg, layerD, layerStep, prevLayer, layer, Layer.next] using
      (layerStep R G X hP hQzero hQbiprod hX a (m + 1)).val.comm

/-- The identification of a term of the extended resolution with a layer. -/
private def layerExtendXIso {n : ℕ} {i : ℤ} (h : (embeddingUpIntLE a).f n = i) :
    ((resolution R G X hP hQzero hQbiprod hX a).extend (embeddingUpIntLE a)).X i ≅
      (layer R G X hP hQzero hQbiprod hX a n).Y :=
  (resolution R G X hP hQzero hQbiprod hX a).extendXIso (embeddingUpIntLE a) h

private lemma resolution_extend_d_eq (n : ℕ) {i j : ℤ}
    (hi : (embeddingUpIntLE a).f (n + 1) = i) (hj : (embeddingUpIntLE a).f n = j) :
    ((resolution R G X hP hQzero hQbiprod hX a).extend (embeddingUpIntLE a)).d i j =
      (layerExtendXIso R G X hP hQzero hQbiprod hX a hi).hom ≫
        layerD R G X hP hQzero hQbiprod hX a n ≫
        (layerExtendXIso R G X hP hQzero hQbiprod hX a hj).inv := by
  rw [← resolution_d]
  exact HomologicalComplex.extend_d_eq _ _ hi hj

private lemma descExtend_resolution_f [X.IsStrictlyLE a] (n : ℕ) :
    (descExtend X (resolution R G X hP hQzero hQbiprod hX a) a
      (resolutionHom R G X hP hQzero hQbiprod hX a)).f (a - (n : ℤ)) =
      (layerExtendXIso R G X hP hQzero hQbiprod hX a (embeddingUpIntLE_f a n)).hom ≫
        (layer R G X hP hQzero hQbiprod hX a n).f := by
  have h : (resolutionHom R G X hP hQzero hQbiprod hX a).f n ≫
      (X.restrictionXIso (embeddingUpIntLE a) (embeddingUpIntLE_f a n)).hom =
      (layer R G X hP hQzero hQbiprod hX a n).f := Category.comp_id _
  rw [descExtend_f,
    descF_eq X (resolution R G X hP hQzero hQbiprod hX a) a
      (resolutionHom R G X hP hQzero hQbiprod hX a) (embeddingUpIntLE_f a n), h]
  rfl

private lemma layer_epiH (n : ℕ) :
    ∃ (C : A) (γ : C ⟶ (layer R G X hP hQzero hQbiprod hX a n).Y)
      (c : C ⟶ X.cycles (a - (n : ℤ))),
      γ ≫ (layer R G X hP hQzero hQbiprod hX a n).d = 0 ∧
      c ≫ X.iCycles (a - (n : ℤ)) = γ ≫ (layer R G X hP hQzero hQbiprod hX a n).f ∧
      Epi (c ≫ X.homologyπ (a - (n : ℤ))) := by
  cases n with
  | zero => exact (layerStep R G X hP hQzero hQbiprod hX a 0).val.epiH
  | succ n => exact (layerStep R G X hP hQzero hQbiprod hX a (n + 1)).val.epiH

private lemma layer_cover (n : ℕ) ⦃T : A⦄
    (t : T ⟶ (layer R G X hP hQzero hQbiprod hX a n).Y)
    (ht : t ≫ (layer R G X hP hQzero hQbiprod hX a n).d = 0)
    (hu : ∃ u : T ⟶ X.X (a - ((n + 1 : ℕ) : ℤ)),
      t ≫ (layer R G X hP hQzero hQbiprod hX a n).f =
        u ≫ X.d (a - ((n + 1 : ℕ) : ℤ)) (a - (n : ℤ))) :
    ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p)
      (s : T' ⟶ (layer R G X hP hQzero hQbiprod hX a (n + 1)).Y),
      p ≫ t = s ≫ layerD R G X hP hQzero hQbiprod hX a n := by
  obtain ⟨T', p, hp, s, hs⟩ :=
    (layerStep R G X hP hQzero hQbiprod hX a (n + 1)).val.cover t ht hu
  refine ⟨T', p, hp, s, ?_⟩
  simpa [layerD, layerStep, prevLayer, layer, Layer.next] using hs

private lemma comp_extend_d_eq_zero (n : ℕ) {C : A}
    (γ : C ⟶ (layer R G X hP hQzero hQbiprod hX a n).Y)
    (hγd : γ ≫ (layer R G X hP hQzero hQbiprod hX a n).d = 0) :
    (γ ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a (embeddingUpIntLE_f a n)).inv) ≫
      ((resolution R G X hP hQzero hQbiprod hX a).extend (embeddingUpIntLE a)).d
        (a - (n : ℤ)) (a - (n : ℤ) + 1) = 0 := by
  cases n with
  | zero =>
      exact (isZero_extend_X_of_not_le
        (resolution R G X hP hQzero hQbiprod hX a) a _ (by omega)).eq_of_tgt _ 0
  | succ m =>
      have h2 : (embeddingUpIntLE a).f m = a - ((m + 1 : ℕ) : ℤ) + 1 := by
        rw [embeddingUpIntLE_f]; omega
      have hγd' : γ ≫ layerD R G X hP hQzero hQbiprod hX a m = 0 := by
        change γ ≫ (layer R G X hP hQzero hQbiprod hX a (m + 1)).d = 0
        exact hγd
      rw [resolution_extend_d_eq R G X hP hQzero hQbiprod hX a m
        (embeddingUpIntLE_f a (m + 1)) h2]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hγd', zero_comp]

private lemma comp_layer_d_eq_zero (n : ℕ) ⦃T : A⦄
    (t : T ⟶ ((resolution R G X hP hQzero hQbiprod hX a).extend
      (embeddingUpIntLE a)).X (a - (n : ℤ)))
    (ht : t ≫ ((resolution R G X hP hQzero hQbiprod hX a).extend
      (embeddingUpIntLE a)).d (a - (n : ℤ)) (a - (n : ℤ) + 1) = 0) :
    (t ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a (embeddingUpIntLE_f a n)).hom) ≫
      (layer R G X hP hQzero hQbiprod hX a n).d = 0 := by
  cases n with
  | zero =>
      exact (isZero_zero A).eq_of_tgt _ 0
  | succ m =>
      have h2 : (embeddingUpIntLE a).f m = a - ((m + 1 : ℕ) : ℤ) + 1 := by
        rw [embeddingUpIntLE_f]; omega
      change _ ≫ layerD R G X hP hQzero hQbiprod hX a m = 0
      rw [resolution_extend_d_eq R G X hP hQzero hQbiprod hX a m
        (embeddingUpIntLE_f a (m + 1)) h2] at ht
      rw [← cancel_mono (layerExtendXIso R G X hP hQzero hQbiprod hX a h2).inv, zero_comp]
      simp only [Category.assoc] at ht ⊢
      exact ht

end

/-- The complex of layers, extended to a `ℤ`-indexed cochain complex, together with its map to
`X` and the two conditions which make that map a quasi-isomorphism. -/
private lemma exists_complex_of_coversEpis (hP : CoversEpis R G) (hQzero : G (0 : A))
    (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E))
    (hQiso : ∀ ⦃V W : A⦄ (e : V ⟶ W), IsIso e → G V → G W)
    (hX : ∀ i, R (X.homology i)) (a : ℤ) [X.IsStrictlyLE a] :
    ∃ (Y : CochainComplex A ℤ) (_ : Y.IsStrictlyLE a) (φ : Y ⟶ X),
      (∀ i, G (Y.X i)) ∧
      (∀ i : ℤ, ∃ (C : A) (γ : C ⟶ Y.X i) (c : C ⟶ X.cycles i),
        γ ≫ Y.d i (i + 1) = 0 ∧ c ≫ X.iCycles i = γ ≫ φ.f i ∧
          Epi (c ≫ X.homologyπ i)) ∧
      (∀ (i : ℤ) ⦃T : A⦄ (t : T ⟶ Y.X i), t ≫ Y.d i (i + 1) = 0 →
        (∃ u : T ⟶ X.X (i - 1), t ≫ φ.f i = u ≫ X.d (i - 1) i) →
        ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p) (s : T' ⟶ Y.X (i - 1)),
          p ≫ t = s ≫ Y.d (i - 1) i) := by
  refine ⟨(resolution R G X hP hQzero hQbiprod hX a).extend (embeddingUpIntLE a),
    inferInstance,
    descExtend X (resolution R G X hP hQzero hQbiprod hX a) a
      (resolutionHom R G X hP hQzero hQbiprod hX a), ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ≤ a
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, i = a - (n : ℤ) := ⟨(a - i).toNat, by omega⟩
      subst i
      let e := (layerExtendXIso R G X hP hQzero hQbiprod hX a
        (embeddingUpIntLE_f a n)).symm
      exact hQiso e.hom inferInstance (layer R G X hP hQzero hQbiprod hX a n).hQ
    · have hzero := isZero_extend_X_of_not_le
        (resolution R G X hP hQzero hQbiprod hX a) a i hi
      exact hQiso (IsZero.iso (isZero_zero _) hzero).hom inferInstance hQzero
  · intro i
    by_cases hi : i ≤ a
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = a - (n : ℤ) := ⟨(a - i).toNat, by omega⟩
      obtain ⟨C, γ, c, hγd, hγc, hce⟩ := layer_epiH R G X hP hQzero hQbiprod hX a n
      refine ⟨C, γ ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a
        (embeddingUpIntLE_f a n)).inv, c,
        comp_extend_d_eq_zero R G X hP hQzero hQbiprod hX a n γ hγd, ?_, hce⟩
      rw [descExtend_resolution_f]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact hγc
    · exact ⟨0, 0, 0, by simp, by simp, (X.isZero_of_isLE a i (by omega)).epi _⟩
  · intro i T t ht hu
    by_cases hi : i ≤ a
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = a - (n : ℤ) := ⟨(a - i).toNat, by omega⟩
      have h1 : (embeddingUpIntLE a).f (n + 1) = a - (n : ℤ) - 1 := by
        rw [embeddingUpIntLE_f]; omega
      have hbdry : ∃ u : T ⟶ X.X (a - ((n + 1 : ℕ) : ℤ)),
          (t ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a
            (embeddingUpIntLE_f a n)).hom) ≫
              (layer R G X hP hQzero hQbiprod hX a n).f =
            u ≫ X.d (a - ((n + 1 : ℕ) : ℤ)) (a - (n : ℤ)) := by
        obtain ⟨u, hu⟩ := hu
        refine ⟨u ≫ (X.XIsoOfEq (show a - (n : ℤ) - 1 =
          a - ((n + 1 : ℕ) : ℤ) by omega)).hom, ?_⟩
        rw [descExtend_resolution_f] at hu
        simp only [Category.assoc] at hu ⊢
        rw [HomologicalComplex.XIsoOfEq_hom_comp_d]
        exact hu
      obtain ⟨T', p, hp, s, hs⟩ := layer_cover R G X hP hQzero hQbiprod hX a n
        (t ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a
          (embeddingUpIntLE_f a n)).hom)
        (comp_layer_d_eq_zero R G X hP hQzero hQbiprod hX a n t ht) hbdry
      refine ⟨T', p, hp, s ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a h1).inv, ?_⟩
      rw [resolution_extend_d_eq R G X hP hQzero hQbiprod hX a n h1 (embeddingUpIntLE_f a n)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, ← hs]
      simp
    · refine ⟨T, 𝟙 T, inferInstance, 0, ?_⟩
      rw [Category.id_comp, zero_comp]
      exact (isZero_extend_X_of_not_le
        (resolution R G X hP hQzero hQbiprod hX a) a i hi).eq_of_tgt t 0

/-- **The bounded above resolution engine.** Let `A` be an abelian category, let `R` be a weak
Serre class in `A` and let `G` be a class of objects of `A` which contains the zero object, is
closed under binary biproducts and under isomorphism, and covers epimorphisms onto objects of
`R`. Then every cochain complex `X` with `X^i = 0` for `i > a` whose cohomology objects all lie
in `R` receives a quasi-isomorphism from a cochain complex `Y` with `Y^i = 0` for `i > a` and
every term in `G`.

The complex `Y` is built degree by degree downwards from `a`: in each degree the new term is the
biproduct of an object of `G` covering the cohomology of `X` in that degree, which makes the map
surjective on cohomology, and an object of `G` covering, up to refinement, those cocycles of the
previously built term whose image in `X` is a boundary, which makes the map injective on
cohomology. -/
theorem exists_quasiIso_isStrictlyLE_of_coversEpis
    (hP : CoversEpis R G) (hQzero : G (0 : A))
    (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E))
    (hQiso : ∀ ⦃V W : A⦄ (e : V ⟶ W), IsIso e → G V → G W)
    (a : ℤ) [X.IsStrictlyLE a] (hX : ∀ i, R (X.homology i)) :
    ∃ (Y : CochainComplex A ℤ) (_ : Y.IsStrictlyLE a) (f : Y ⟶ X) (_ : QuasiIso f),
      ∀ i, G (Y.X i) := by
  obtain ⟨Y, hY, f, hGY, hepi, hcov⟩ :=
    exists_complex_of_coversEpis R G X hP hQzero hQbiprod hQiso hX a
  exact ⟨Y, hY, f, quasiIso_of_epi_of_cover f hepi hcov, hGY⟩

end Resolution


section FreeModules

open CategoryTheory.Abelian

variable {R : Type u} [CommRing R]

/-- Every module is covered by a free module, in the refinement form used by
the bounded-above resolution engine. -/
lemma coversEpis_freeModules :
    CoversEpis (fun _ => True : ObjectProperty (ModuleCat.{u} R))
      (fun M => Module.Free R M) := by
  intro V W f hf _
  let g := (ModuleCat.projectiveResolution R).π.app V
  letI : Epi f := hf
  have hg : Epi g := by
    dsimp [g]
    infer_instance
  exact ⟨(ModuleCat.free R).obj V, g, Module.Free.finsupp R _ _, trivial,
    show Epi (g ≫ f) by dsimp [g]; infer_instance⟩

lemma freeModules_zero : Module.Free R (0 : ModuleCat.{u} R) := by
  letI : Subsingleton (0 : ModuleCat.{u} R) :=
    ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
  exact Module.Free.of_subsingleton R _

lemma freeModules_biprod {M N : ModuleCat.{u} R}
    (hM : Module.Free R M) (hN : Module.Free R N) : Module.Free R (↥(M ⊞ N)) := by
  let eLin : ModuleCat.of R (M × N) ≃ₗ[R] (↥(M ⊞ N)) :=
    (ModuleCat.biprodIsoProd M N).symm.toLinearEquiv
  exact Module.Free.of_equiv eLin

lemma freeModules_iso {M N : ModuleCat.{u} R} (e : M ⟶ N) (_ : IsIso e)
    (hM : Module.Free R M) : Module.Free R N :=
  Module.Free.of_equiv (asIso e).toLinearEquiv

/-- The unconditional bounded-above free resolution, obtained from the
05T7(1) descending-induction engine specialized to free modules and to the
ambient class of all modules. -/
theorem exists_free_resolution_isStrictlyLE (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a : ℤ) [K.IsStrictlyLE a] :
    ∃ (Y : CochainComplex (ModuleCat.{u} R) ℤ) (_ : Y.IsStrictlyLE a)
      (f : Y ⟶ K), QuasiIso f ∧ ∀ i, Module.Free R (Y.X i) := by
  obtain ⟨Y, hY, f, hf, hfree⟩ := exists_quasiIso_isStrictlyLE_of_coversEpis
    (fun _ => True : ObjectProperty (ModuleCat.{u} R))
    (fun M => Module.Free R M) K coversEpis_freeModules freeModules_zero
    (fun _ _ hM hN => freeModules_biprod hM hN)
    (fun _ _ e he hM => freeModules_iso e he hM) a (fun _ => trivial)
  exact ⟨Y, hY, f, hf, hfree⟩

end FreeModules

#print axioms RelativeFM.Stacks07LT.M2.Resolution.exists_quasiIso_isStrictlyLE_of_coversEpis
#print axioms RelativeFM.Stacks07LT.M2.Resolution.exists_free_resolution_isStrictlyLE

end RelativeFM.Stacks07LT.M2.Resolution

end



@[expose] public section

namespace RelativeFM.Stacks07LT.M2

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox
open scoped ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts

universe w
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Preadditive C]

lemma biproduct_lift_eq_univ {J : Type w} [Fintype J] {B : J → C}
    [HasBiproduct B] {T : C} (g : ∀ j, T ⟶ B j) :
    biproduct.lift g = ∑ j, g j ≫ biproduct.ι B j := by
  classical
  apply biproduct.hom_ext
  intro j
  rw [biproduct.lift_π]
  simp [Preadditive.sum_comp, biproduct.ι_π, comp_dite]

lemma biproduct_desc_eq_univ {J : Type w} [Fintype J] {B : J → C}
    [HasBiproduct B] {T : C} (g : ∀ j, B j ⟶ T) :
    biproduct.desc g = ∑ j, biproduct.π B j ≫ g j := by
  classical
  apply biproduct.hom_ext'
  intro j
  rw [biproduct.ι_desc]
  simp [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp]

lemma biproduct_lift_desc_univ {J : Type w} [Fintype J] {B : J → C}
    [HasBiproduct B] {T U : C} (g : ∀ j, T ⟶ B j) (h : ∀ j, B j ⟶ U) :
    biproduct.lift g ≫ biproduct.desc h = ∑ j, g j ≫ h j := by
  classical
  rw [biproduct_lift_eq_univ, biproduct_desc_eq_univ]
  simp [Preadditive.comp_sum, Preadditive.sum_comp, biproduct.ι_π_assoc,
    comp_dite, dite_comp]

lemma abCofanSum_comp_coproductProjection
    {J : Type v} [DecidableEq J] {X : C} {A : J → C} {P : C}
    (ι : ∀ j, A j ⟶ P) (hc : IsColimit (Cofan.mk P ι))
    (z : DFinsupp (fun j => X ⟶ A j)) (j : J) :
    (DFinsupp.sumAddHom (fun k =>
      ((RelativeWeakApprox.abCoyoneda X).map (ι k)).hom)) z ≫
        RelativeWeakApprox.coproductProjection ι hc j = z j := by
  classical
  let c : Cofan (fun j => (RelativeWeakApprox.abCoyoneda X).obj (A j)) :=
    Cofan.mk ((RelativeWeakApprox.abCoyoneda X).obj P)
      (fun j => (RelativeWeakApprox.abCoyoneda X).map (ι j))
  let p := RelativeWeakApprox.coproductProjection ι hc j
  let post := ((RelativeWeakApprox.abCoyoneda X).map p).hom
  have hz := post.map_dfinsuppSumAddHom z (fun k => (c.inj k).hom)
  calc
    (DFinsupp.sumAddHom (fun k =>
      ((RelativeWeakApprox.abCoyoneda X).map (ι k)).hom)) z ≫ p =
        post ((DFinsupp.sumAddHom fun k => (c.inj k).hom) z) := rfl
    _ = (DFinsupp.sumAddHom fun k => post.comp (c.inj k).hom) z := hz
    _ = z j := by
      have hfun : (fun k => post.comp (c.inj k).hom) =
          Pi.single j (AddMonoidHom.id (X ⟶ A j)) := by
        funext k
        by_cases h : k = j
        · subst k
          ext q
          simp [post, p, c]
        · ext q
          simp [post, p, c, h]
      rw [hfun, DFinsupp.sumAddHom_piSingle]
      rfl

/-- A countable coproduct with its shift endomorphism, in the morphism universe
of the ambient category.  `diff` is the telescope differential `1-shift`. -/
structure SequentialCoproduct (C : Type u) [Category.{v} C] [Preadditive C] where
  A : ULift.{v} ℕ → C
  P : C
  ι : ∀ n, A n ⟶ P
  isColimit : IsColimit (Cofan.mk P ι)
  step : ∀ n, A n ⟶ A (ULift.up (n.down + 1))
  diff : P ⟶ P
  inj_diff : ∀ n, ι n ≫ diff =
    ι n - step n ≫ ι (ULift.up (n.down + 1))

namespace SequentialCoproduct

variable (D : SequentialCoproduct C)

lemma diff_projection_zero :
    D.diff ≫ RelativeWeakApprox.coproductProjection D.ι D.isColimit (ULift.up 0) =
      RelativeWeakApprox.coproductProjection D.ι D.isColimit (ULift.up 0) := by
  apply Cofan.IsColimit.hom_ext D.isColimit
  intro n
  change D.ι n ≫ (D.diff ≫ RelativeWeakApprox.coproductProjection D.ι D.isColimit
    (ULift.up 0)) = _
  rw [← Category.assoc, D.inj_diff]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, ← Category.assoc,
    RelativeWeakApprox.coproductProjection_comp]
  by_cases hn : n = ULift.up 0
  · subst n
    simp
  · have hnext : (ULift.up (n.down + 1) : ULift.{v} ℕ) ≠ ULift.up (0 : ℕ) := by
      intro h
      have hh := congrArg ULift.down h
      dsimp at hh
      omega
    simp [hn, hnext]

lemma diff_projection_succ (n : ULift.{v} ℕ) :
    D.diff ≫ RelativeWeakApprox.coproductProjection D.ι D.isColimit
        (ULift.up (n.down + 1)) =
      RelativeWeakApprox.coproductProjection D.ι D.isColimit
        (ULift.up (n.down + 1)) -
      RelativeWeakApprox.coproductProjection D.ι D.isColimit n ≫ D.step n := by
  apply Cofan.IsColimit.hom_ext D.isColimit
  intro k
  change D.ι k ≫ (D.diff ≫ RelativeWeakApprox.coproductProjection D.ι D.isColimit
    (ULift.up (n.down + 1))) = _
  rw [← Category.assoc, D.inj_diff]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, ← Category.assoc,
    RelativeWeakApprox.coproductProjection_comp]
  by_cases hk : k = ULift.up (n.down + 1)
  · subst k
    have hkn : (ULift.up (n.down + 1) : ULift.{v} ℕ) ≠ n := by
      intro h
      have hh := congrArg ULift.down h
      dsimp at hh
      omega
    have hnext : (ULift.up ((ULift.up (n.down + 1) : ULift.{v} ℕ).down + 1) :
        ULift.{v} ℕ) ≠ ULift.up (n.down + 1) := by
      intro h
      have hh := congrArg ULift.down h
      dsimp at hh
      omega
    simp [hkn, hnext]
  · by_cases hkn : k = n
    · subst k
      have hne : n ≠ ULift.up (n.down + 1) := by
        intro h
        have hh := congrArg ULift.down h
        dsimp at hh
        omega
      simp [hne]
    · have hnext : (ULift.up (k.down + 1) : ULift.{v} ℕ) ≠ ULift.up (n.down + 1) := by
        intro h
        apply hkn
        ext
        have hh := congrArg ULift.down h
        dsimp at hh
        omega
      simp [hk, hkn, hnext]

/-- Apply an integer shift to a sequential coproduct and its telescope. -/
noncomputable def shift [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    (D : SequentialCoproduct C) (a : ℤ) : SequentialCoproduct C where
  A n := D.A n⟦a⟧
  P := D.P⟦a⟧
  ι n := D.ι n⟦a⟧'
  isColimit := (Cofan.isColimitMapCoconeEquiv (shiftFunctor C a) D.A
    (Cofan.mk D.P D.ι)) (isColimitOfPreserves (shiftFunctor C a) D.isColimit)
  step n := D.step n⟦a⟧'
  diff := D.diff⟦a⟧'
  inj_diff n := by
    rw [← Functor.map_comp, D.inj_diff, Functor.map_sub, Functor.map_comp]

/-- Hom out of a compact object is injective on the telescope differential.
This is the categorical content of Stacks 07LR for a sequential homotopy colimit. -/
theorem eq_zero_of_comp_diff {X : C} (hX : IsCompactAb X)
    (f : X ⟶ D.P) (hf : f ≫ D.diff = 0) : f = 0 := by
  classical
  obtain ⟨z, hz⟩ := Stacks07LT.exists_dfinsupp_coproduct_decomposition
    hX D.A D.ι D.isColimit f
  let t : ∀ n : ℕ, (X ⟶ D.A (ULift.up n)) →+
      (X ⟶ D.A (ULift.up (n + 1))) := fun n =>
    ((RelativeWeakApprox.abCoyoneda X).map (D.step (ULift.up n))).hom
  have hcoord : ∀ n : ℕ,
      z (ULift.up n) - Stacks07LT.sequenceTransitionTail t
        (fun k => z (ULift.up k)) n = 0 := by
    intro n
    cases n with
    | zero =>
        have hzero := congrArg (fun q : X ⟶ D.P =>
          q ≫ RelativeWeakApprox.coproductProjection D.ι D.isColimit (ULift.up 0)) hf
        rw [Category.assoc, D.diff_projection_zero, zero_comp] at hzero
        rw [← hz] at hzero
        rw [abCofanSum_comp_coproductProjection] at hzero
        simpa [Stacks07LT.sequenceTransitionTail, t] using hzero
    | succ n =>
        have hzero := congrArg (fun q : X ⟶ D.P =>
          q ≫ RelativeWeakApprox.coproductProjection D.ι D.isColimit
            (ULift.up (n + 1))) hf
        rw [Category.assoc, D.diff_projection_succ, Preadditive.comp_sub,
          ← Category.assoc, zero_comp] at hzero
        rw [← hz] at hzero
        rw [abCofanSum_comp_coproductProjection,
          abCofanSum_comp_coproductProjection] at hzero
        change z (ULift.up (n + 1)) - z (ULift.up n) ≫ D.step (ULift.up n) = 0 at hzero
        simpa [Stacks07LT.sequenceTransitionTail, t] using hzero
  have hz0 : (fun n : ℕ => z (ULift.up n)) = 0 :=
    Stacks07LT.sequence_eq_zero_of_sub_transitionTail _ _ hcoord
  have hz' : z = 0 := by
    ext n
    obtain ⟨n⟩ := n
    have := congrFun hz0 n
    simpa using this
  rw [← hz, hz']
  simp

end SequentialCoproduct



section ModuleBiproducts

open RelativeFM.AisleGeneration.Brutal
open RelativeFM.AisleGeneration.Filtration
open RelativeFM.Spaltenstein

universe uA
variable {A : Type uA} [CommRing A]

/-- Every finite module biproduct is isomorphic to a product indexed by `Fin n`.
This universe-polymorphic wrapper is needed because `biproductIsoPi` itself is
stated only for `Type 0` indices. -/
lemma exists_biproduct_module_iso_pi {J : Type w} [Finite J]
    (B : J → ModuleCat.{uA} A) :
    ∃ n : ℕ, ∃ e : J ≃ Fin n,
      Nonempty ((⨁ B) ≅ ModuleCat.of A (∀ i : Fin n, B (e.symm i))) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  let G : Fin n → ModuleCat.{uA} A := fun i => B (e.symm i)
  let r : (⨁ B) ≅ ⨁ G := biproduct.whiskerEquiv (f := B) (g := G) e
    (fun j => eqToIso (by simp only [G, Equiv.symm_apply_apply]))
  exact ⟨n, e, ⟨r ≪≫ ModuleCat.biproductIsoPi G⟩⟩

lemma exists_eval_biproduct_complex_iso_pi {J : Type w} [Finite J]
    (B : J → CochainComplex (ModuleCat.{uA} A) ℤ) (i : ℤ) :
    ∃ n : ℕ, ∃ e : J ≃ Fin n, Nonempty (((⨁ B).X i) ≅
      ModuleCat.of A (∀ j : Fin n, (B (e.symm j)).X i)) := by
  obtain ⟨n, e, ⟨r⟩⟩ := exists_biproduct_module_iso_pi (fun j => (B j).X i)
  letI : PreservesBiproduct B (HomologicalComplex.eval (ModuleCat.{uA} A) (.up ℤ) i) :=
    preservesBiproduct_of_preservesProduct _
  exact ⟨n, e, ⟨((HomologicalComplex.eval (ModuleCat.{uA} A) (.up ℤ) i).mapBiproduct B) ≪≫ r⟩⟩

lemma isZero_biproduct_module {J : Type w} [Finite J]
    (B : J → ModuleCat.{uA} A) (hB : ∀ j, IsZero (B j)) : IsZero (⨁ B) := by
  obtain ⟨n, e, ⟨r⟩⟩ := exists_biproduct_module_iso_pi B
  have heq (j : Fin n) (x y : B (e.symm j)) : x = y :=
    @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.mp (hB (e.symm j))) x y
  letI : Subsingleton (∀ j, B (e.symm j)) :=
    ⟨fun x y => funext fun j => heq j (x j) (y j)⟩
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) r

lemma free_biproduct_module {J : Type w} [Finite J]
    (B : J → ModuleCat.{uA} A) [∀ j, Module.Free A (B j)] : Module.Free A (↥(⨁ B)) := by
  obtain ⟨n, e, ⟨r⟩⟩ := exists_biproduct_module_iso_pi B
  let eLin : ModuleCat.of A (∀ i : Fin n, B (e.symm i)) ≃ₗ[A] (↥(⨁ B)) :=
    r.symm.toLinearEquiv
  exact Module.Free.of_equiv eLin

lemma isZero_eval_biproduct_complex {J : Type w} [Finite J]
    (B : J → CochainComplex (ModuleCat.{uA} A) ℤ) (i : ℤ)
    (hB : ∀ j, IsZero ((B j).X i)) : IsZero ((⨁ B).X i) := by
  obtain ⟨n, e, ⟨r⟩⟩ := exists_eval_biproduct_complex_iso_pi B i
  have heq (j : Fin n) (x y : (B (e.symm j)).X i) : x = y :=
    @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.mp (hB (e.symm j))) x y
  letI : Subsingleton (∀ j, (B (e.symm j)).X i) :=
    ⟨fun x y => funext fun j => heq j (x j) (y j)⟩
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) r

lemma free_eval_biproduct_complex {J : Type w} [Finite J]
    (B : J → CochainComplex (ModuleCat.{uA} A) ℤ) (i : ℤ)
    [∀ j, Module.Free A ((B j).X i)] : Module.Free A ((⨁ B).X i) := by
  obtain ⟨n, e, ⟨r⟩⟩ := exists_eval_biproduct_complex_iso_pi B i
  let eLin : ModuleCat.of A (∀ j : Fin n, (B (e.symm j)).X i) ≃ₗ[A] ((⨁ B).X i) :=
    r.symm.toLinearEquiv
  exact Module.Free.of_equiv eLin

lemma free_brutalGE (K : CochainComplex (ModuleCat.{uA} A) ℤ)
    [∀ i, Module.Free A (K.X i)] (a i : ℤ) : Module.Free A ((brutalGE K a).X i) := by
  by_cases hi : a ≤ i
  · exact Module.Free.of_equiv (brutalGEXIso K a i hi).symm.toLinearEquiv
  · letI : Subsingleton ((brutalGE K a).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_brutalGE_X K (by omega))
    infer_instance

/-- The finite biproduct of brutal stages indexed by a finite set. -/
def brutalFiniteStageComplex (K : CochainComplex (ModuleCat.{uA} A) ℤ) [K.IsStrictlyLE 0]
    (s : Finset (ULift.{uA + 1} ℕ)) : CochainComplex (ModuleCat.{uA} A) ℤ :=
  ⨁ (fun n : ↥s => (filtrationDiagram (brutalFiltration K)).obj n.val.down)

/-- A common lower bound for all the stages in `brutalFiniteStageComplex`. -/
def brutalFiniteStageLower (s : Finset (ULift.{uA + 1} ℕ)) : ℤ :=
  -((∑ n ∈ s, n.down : ℕ) : ℤ)

lemma brutalFiniteStage_isStrictlyGE (K : CochainComplex (ModuleCat.{uA} A) ℤ)
    [K.IsStrictlyLE 0] (s : Finset (ULift.{uA + 1} ℕ)) :
    (brutalFiniteStageComplex K s).IsStrictlyGE (brutalFiniteStageLower s) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  apply isZero_eval_biproduct_complex
  intro n
  change IsZero ((brutalGE K (-(n.val.down : ℤ))).X i)
  apply isZero_brutalGE_X K
  have hn : n.val.down ≤ ∑ m ∈ s, m.down :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) n.property
  have hnz : (n.val.down : ℤ) ≤ ((∑ m ∈ s, m.down : ℕ) : ℤ) := by
    exact_mod_cast hn
  dsimp [brutalFiniteStageLower] at hi
  omega

lemma brutalFiniteStage_isStrictlyLE (K : CochainComplex (ModuleCat.{uA} A) ℤ)
    [K.IsStrictlyLE 0] (s : Finset (ULift.{uA + 1} ℕ)) :
    (brutalFiniteStageComplex K s).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  apply isZero_eval_biproduct_complex
  intro n
  change IsZero ((brutalGE K (-(n.val.down : ℤ))).X i)
  exact (brutalGE K (-(n.val.down : ℤ))).isZero_of_isStrictlyLE 0 i hi

lemma brutalFiniteStage_free (K : CochainComplex (ModuleCat.{uA} A) ℤ)
    [K.IsStrictlyLE 0] [∀ i, Module.Free A (K.X i)]
    (s : Finset (ULift.{uA + 1} ℕ)) (i : ℤ) :
    Module.Free A ((brutalFiniteStageComplex K s).X i) := by
  letI (n : ↥s) : Module.Free A
      (((filtrationDiagram (brutalFiltration K)).obj n.val.down).X i) := by
    change Module.Free A ((brutalGE K (-(n.val.down : ℤ))).X i)
    exact free_brutalGE K _ _
  exact free_eval_biproduct_complex _ _

lemma brutalFiniteStage_lower_bounds (s : Finset (ULift.{uA + 1} ℕ)) :
    brutalFiniteStageLower s ≤ 0 + 1 := by
  have h : 0 ≤ ((∑ n ∈ s, n.down : ℕ) : ℤ) := by positivity
  dsimp [brutalFiniteStageLower]
  omega

end ModuleBiproducts

section DerivedTelescope

open RelativeFM
open RelativeFM.SpecialDirectLimits
open RelativeFM.DerivedCoproducts

universe vE uE
variable {E : Type uE} [Category.{vE} E] [Abelian E]
variable [HasDerivedCategory.{w} E] [HasCoproductsOfShape ℕ E]

lemma complexCoproductInj_complexTelescopeShift (P : ℕ ⥤ CochainComplex E ℤ) (n : ℕ) :
    complexCoproductInj P n ≫ complexTelescopeShift P =
      step P n ≫ complexCoproductInj P (n + 1) := by
  apply HomologicalComplex.hom_ext
  intro i
  exact inj_telescopeShift (stages P i) n

lemma complexCoproductInj_complexTelescopeDifference (P : ℕ ⥤ CochainComplex E ℤ)
    (n : ℕ) :
    complexCoproductInj P n ≫ complexTelescopeDifference P =
      complexCoproductInj P n - step P n ≫ complexCoproductInj P (n + 1) := by
  change complexCoproductInj P n ≫ (𝟙 _ - complexTelescopeShift P) = _
  rw [Preadditive.comp_sub, Category.comp_id,
    complexCoproductInj_complexTelescopeShift]

lemma derivedCoproductInj_comp_complexCoproductIso (P : ℕ ⥤ CochainComplex E ℤ)
    [∀ n, (P.obj n).IsKProjective] (n : ℕ) :
    (derivedCoproductCofan (fun n => P.obj n)).inj n ≫
        DerivedCategory.Q.map (complexCoproductIso P).hom =
      DerivedCategory.Q.map (complexCoproductInj P n) := by
  change DerivedCategory.Q.map ((coproductComplexCocone (fun n => P.obj n)).ι.app ⟨n⟩) ≫
    DerivedCategory.Q.map (complexCoproductIso P).hom = _
  rw [← Functor.map_comp]
  congr 1
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coproductComplexCoconeIsColimit (fun n => P.obj n))
    (complexCoproductCofanIsColimit P) ⟨n⟩

/-- The derived coproduct of the stages of a K-projective sequential system,
indexed in the morphism universe of the derived category. -/
noncomputable def derivedSequentialCoproduct (P : ℕ ⥤ CochainComplex E ℤ)
    [∀ n, (P.obj n).IsKProjective] :
    SequentialCoproduct (DerivedCategory E) where
  A n := DerivedCategory.Q.obj (P.obj n.down)
  P := DerivedCategory.Q.obj (coproductComplexCocone (fun n => P.obj n)).pt
  ι n := DerivedCategory.Q.map
    ((coproductComplexCocone (fun n => P.obj n)).ι.app ⟨n.down⟩)
  isColimit := by
    let c : Cofan (fun n : ℕ => DerivedCategory.Q.obj (P.obj n)) :=
      derivedCoproductCofan (fun n => P.obj n)
    let hc := derivedCoproductCofanIsColimit (fun n => P.obj n)
    exact Cofan.IsColimit.mk _
      (fun t => hc.desc (Cofan.mk t.pt (fun n => t.inj (ULift.up n))))
      (fun t n => hc.fac _ ⟨n.down⟩)
      (fun t m hm => hc.uniq (Cofan.mk t.pt (fun n => t.inj (ULift.up n))) m
        (fun n => hm (ULift.up n.as)))
  step n := DerivedCategory.Q.map (step P n.down)
  diff := DerivedCategory.Q.map (complexCoproductIso P).hom ≫
    DerivedCategory.Q.map (complexTelescopeDifference P) ≫
    DerivedCategory.Q.map (complexCoproductIso P).inv
  inj_diff n := by
    let j₀ : DerivedCategory.Q.obj (P.obj n.down) ⟶
        DerivedCategory.Q.obj (coproductComplexCocone (fun n => P.obj n)).pt :=
      DerivedCategory.Q.map
        ((coproductComplexCocone (fun n => P.obj n)).ι.app ⟨n.down⟩)
    let j₁ : DerivedCategory.Q.obj (P.obj (n.down + 1)) ⟶
        DerivedCategory.Q.obj (coproductComplexCocone (fun n => P.obj n)).pt :=
      DerivedCategory.Q.map
        ((coproductComplexCocone (fun n => P.obj n)).ι.app ⟨n.down + 1⟩)
    have hι : j₀ ≫ DerivedCategory.Q.map (complexCoproductIso P).hom =
        DerivedCategory.Q.map (complexCoproductInj P n.down) := by
      simpa [j₀] using derivedCoproductInj_comp_complexCoproductIso P n.down
    have hιnext : j₁ ≫ DerivedCategory.Q.map (complexCoproductIso P).hom =
        DerivedCategory.Q.map (complexCoproductInj P (n.down + 1)) := by
      simpa [j₁] using derivedCoproductInj_comp_complexCoproductIso P (n.down + 1)
    have hd := complexCoproductInj_complexTelescopeDifference P n.down
    change j₀ ≫ (DerivedCategory.Q.map (complexCoproductIso P).hom ≫
      DerivedCategory.Q.map (complexTelescopeDifference P) ≫
      DerivedCategory.Q.map (complexCoproductIso P).inv) =
        j₀ - DerivedCategory.Q.map (step P n.down) ≫ j₁
    calc
      _ = (j₀ ≫ DerivedCategory.Q.map (complexCoproductIso P).hom) ≫
          DerivedCategory.Q.map (complexTelescopeDifference P) ≫
          DerivedCategory.Q.map (complexCoproductIso P).inv := by
            simp only [Category.assoc]
      _ = DerivedCategory.Q.map (complexCoproductInj P n.down) ≫
          DerivedCategory.Q.map (complexTelescopeDifference P) ≫
          DerivedCategory.Q.map (complexCoproductIso P).inv := by rw [hι]
      _ = DerivedCategory.Q.map
          (complexCoproductInj P n.down ≫ complexTelescopeDifference P) ≫
          DerivedCategory.Q.map (complexCoproductIso P).inv := by
            simp only [Functor.map_comp, Category.assoc]
      _ = DerivedCategory.Q.map
          (complexCoproductInj P n.down - step P n.down ≫
            complexCoproductInj P (n.down + 1)) ≫
          DerivedCategory.Q.map (complexCoproductIso P).inv := by rw [hd]
      _ = (DerivedCategory.Q.map (complexCoproductInj P n.down) -
          DerivedCategory.Q.map (step P n.down) ≫
            DerivedCategory.Q.map (complexCoproductInj P (n.down + 1))) ≫
          DerivedCategory.Q.map (complexCoproductIso P).inv := by
            rw [Functor.map_sub, Functor.map_comp]
      _ = (j₀ ≫ DerivedCategory.Q.map (complexCoproductIso P).hom -
          DerivedCategory.Q.map (step P n.down) ≫
          (j₁ ≫ DerivedCategory.Q.map (complexCoproductIso P).hom)) ≫
          DerivedCategory.Q.map (complexCoproductIso P).inv := by
            rw [← hι, ← hιnext]
      _ = _ := by
        simp only [Preadditive.sub_comp, Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
        rw [← Functor.map_comp, ← Functor.map_comp]
        simp only [Iso.hom_inv_id, Functor.map_id, Category.comp_id, Category.assoc,
          Iso.hom_inv_id_assoc]
        simp [j₀, j₁]


lemma complexTelescopeShortExact (P : ℕ ⥤ CochainComplex E ℤ) (c : Cocone P)
    (hc : IsColimit c) [HasColimitsOfShape ℕ E]
    (q : ∀ n i, (P.obj (n + 1)).X i ⟶ (P.obj n).X i)
    (hq : ∀ n i, (step P n).f i ≫ q n i = 𝟙 _) :
    (complexTelescopeShortComplex P c).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i => (complexTelescopeSplitting P c hc q hq i).shortExact)

/-- **Hom-compatibility for a compact source and a special sequential colimit.**
A map to the derived image of the colimit lifts to the countable derived coproduct
of the stages.  This is the surjectivity step in Stacks 07LR. -/
theorem exists_lift_derivedTelescope
    (P : ℕ ⥤ CochainComplex E ℤ) [∀ n, (P.obj n).IsKProjective]
    (c : Cocone P) (hc : IsColimit c) [HasColimitsOfShape ℕ E]
    (q : ∀ n i, (P.obj (n + 1)).X i ⟶ (P.obj n).X i)
    (hq : ∀ n i, (step P n).f i ≫ q n i = 𝟙 _)
    {X : DerivedCategory E} (hX : IsCompactAb X)
    (δ : X ⟶ DerivedCategory.Q.obj c.pt) :
    ∃ γ : X ⟶ (derivedSequentialCoproduct P).P,
      δ = γ ≫ DerivedCategory.Q.map (complexCoproductIso P).hom ≫
        DerivedCategory.Q.map (complexTelescopeToCocone P c) := by
  let e : DerivedCategory.Q.obj (coproductComplexCocone (fun n => P.obj n)).pt ≅
      DerivedCategory.Q.obj (complexTelescopeShortComplex P c).X₁ :=
    DerivedCategory.Q.mapIso (complexCoproductIso P)
  let d : DerivedCategory.Q.obj (complexTelescopeShortComplex P c).X₁ ⟶
      DerivedCategory.Q.obj (complexTelescopeShortComplex P c).X₁ :=
    DerivedCategory.Q.map (complexTelescopeDifference P)
  let hS := complexTelescopeShortExact P c hc q hq
  let T := DerivedCategory.triangleOfSES hS
  let T' : Triangle (DerivedCategory E) := Triangle.mk
    (e.hom ≫ d ≫ e.inv)
    (e.hom ≫ DerivedCategory.Q.map (complexTelescopeToCocone P c))
    (T.mor₃ ≫ e.inv⟦(1 : ℤ)⟧')
  have hT : T ∈ distTriang (DerivedCategory E) :=
    DerivedCategory.triangleOfSES_distinguished hS
  have iso : T' ≅ T := by
    refine Pretriangulated.Triangle.isoMk T' T e e (Iso.refl _) ?_ ?_ ?_
    · change (e.hom ≫ d ≫ e.inv) ≫
        e.hom = e.hom ≫ d
      calc
        _ = e.hom ≫ d ≫
            (e.inv ≫ e.hom) := by simp only [Category.assoc]
        _ = _ := by rw [e.inv_hom_id, Category.comp_id]
    · change (e.hom ≫ DerivedCategory.Q.map (complexTelescopeToCocone P c)) ≫ 𝟙 _ =
        e.hom ≫ DerivedCategory.Q.map (complexTelescopeToCocone P c)
      simp
    · dsimp [T']
      change (T.mor₃ ≫ e.inv⟦(1 : ℤ)⟧') ≫ e.hom⟦(1 : ℤ)⟧' =
        𝟙 T.obj₃ ≫ T.mor₃
      dsimp [T, DerivedCategory.triangleOfSES]
      change (DerivedCategory.triangleOfSESδ hS ≫ e.inv⟦(1 : ℤ)⟧') ≫
          e.hom⟦(1 : ℤ)⟧' =
        𝟙 (DerivedCategory.Q.obj (complexTelescopeShortComplex P c).X₃) ≫
          DerivedCategory.triangleOfSESδ hS
      rw [Category.id_comp, Category.assoc, ← Functor.map_comp, e.inv_hom_id]
      simp
  have hT' : T' ∈ distTriang (DerivedCategory E) :=
    isomorphic_distinguished T hT T' iso
  have hinj : Function.Injective (fun f : X ⟶ T'.obj₁⟦(1 : ℤ)⟧ =>
      f ≫ T'.mor₁⟦(1 : ℤ)⟧') := by
    intro f g hfg
    apply sub_eq_zero.mp
    apply ((derivedSequentialCoproduct P).shift 1).eq_zero_of_comp_diff hX
    change (f - g) ≫ T'.mor₁⟦(1 : ℤ)⟧' = 0
    dsimp at hfg
    rw [Preadditive.sub_comp, hfg, sub_self]
  obtain ⟨γ, hγ⟩ := Stacks07LT.exists_lift_triangle_of_injective_shift T' hT' hinj δ
  exact ⟨γ, hγ⟩


namespace SequentialCoproduct

variable [HasFiniteBiproducts C]

/-- A morphism from a compact object to a sequential coproduct factors through
the finite biproduct indexed by the support of its finite-support decomposition. -/
theorem exists_finite_biproduct_factor (D : SequentialCoproduct C)
    {X : C} (hX : IsCompactAb X) (γ : X ⟶ D.P) :
    ∃ s : Finset (ULift.{v} ℕ),
      ∃ φ : X ⟶ ⨁ (fun n : ↥s => D.A n.val),
      ∃ χ : (⨁ (fun n : ↥s => D.A n.val)) ⟶ D.P,
        γ = φ ≫ χ := by
  classical
  obtain ⟨z, hz⟩ := Stacks07LT.exists_dfinsupp_coproduct_decomposition
    hX D.A D.ι D.isColimit γ
  let s := z.support
  let φ : X ⟶ ⨁ (fun n : ↥s => D.A n.val) :=
    biproduct.lift (fun n => z n.val)
  let χ : (⨁ (fun n : ↥s => D.A n.val)) ⟶ D.P :=
    biproduct.desc (fun n => D.ι n.val)
  refine ⟨s, φ, χ, ?_⟩
  calc
    γ = (DFinsupp.sumAddHom (fun n =>
        ((RelativeWeakApprox.abCoyoneda X).map (D.ι n)).hom)) z := hz.symm
    _ = z.sum (fun n w => w ≫ D.ι n) :=
      DFinsupp.sumAddHom_apply _ _
    _ = ∑ n ∈ s, z n ≫ D.ι n := rfl
    _ = ∑ n : ↥s, z n.val ≫ D.ι n.val := by
      simpa using (Finset.sum_attach s (fun n => z n ≫ D.ι n)).symm
    _ = φ ≫ χ := by
      symm
      exact biproduct_lift_desc_univ (fun n : ↥s => z n.val)
        (fun n : ↥s => D.ι n.val)

end SequentialCoproduct

end DerivedTelescope

section BrutalFactorization

open RelativeFM.AisleGeneration.Brutal
open RelativeFM.AisleGeneration.Filtration
open RelativeFM.Spaltenstein
open RelativeFM.SpecialDirectLimits
open RelativeFM.DerivedCoproducts

universe uA
variable (A : Type uA) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- **The bounded-free factorization step of Stacks 07LT.**  For a free complex
strictly bounded above by zero, compactness of its derived image forces the
identity to factor through a bounded free complex.  The intermediate object is
a finite biproduct of brutal filtration stages. -/
theorem nonempty_boundedFreeFactorization_Q_obj
    (K : CochainComplex (ModuleCat.{uA} A) ℤ) [K.IsStrictlyLE 0]
    [∀ i, Module.Free A (K.X i)]
    (hX : IsCompactAb (DerivedCategory.Q.obj K)) :
    Nonempty (Stacks07LT.BoundedFreeFactorization A (DerivedCategory.Q.obj K)) := by
  let F := brutalFiltration K
  let P := filtrationDiagram F
  letI (n : ℕ) : (P.obj n).IsKProjective := by
    change (brutalGE K (-(n : ℤ))).IsKProjective
    letI (i : ℤ) : Module.Free A ((brutalGE K (-(n : ℤ))).X i) :=
      free_brutalGE K _ _
    exact CochainComplex.isKProjective_of_projective _ 0
  let c := colimit.cocone P
  let hc := colimit.isColimit P
  let q : ∀ n i, (P.obj (n + 1)).X i ⟶ (P.obj n).X i :=
    fun n i => brutalFiltrationStepRetraction K n i
  have hq : ∀ n i, (step P n).f i ≫ q n i = 𝟙 _ := by
    intro n i
    simpa only [SpecialDirectLimits.step, P, F, filtrationDiagram, brutalFiltration,
      Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_obj, q] using
      (brutalFiltration_step_retraction K n i)
  letI : QuasiIso (filtrationColimitToA F) := quasiIso_colimitToA_brutal K
  let e := asIso (DerivedCategory.Q.map (filtrationColimitToA F))
  obtain ⟨γ, hγ⟩ := exists_lift_derivedTelescope P c hc q hq hX e.inv
  obtain ⟨s, φ, χ, hφχ⟩ :=
    (derivedSequentialCoproduct P).exists_finite_biproduct_factor hX γ
  let ψ : (⨁ (fun n : ↥s => DerivedCategory.Q.obj (P.obj n.val.down))) ⟶
      DerivedCategory.Q.obj K :=
    (χ ≫ (DerivedCategory.Q.map (complexCoproductIso P).hom ≫
      DerivedCategory.Q.map (complexTelescopeToCocone P c))) ≫ e.hom
  have he : e.inv = φ ≫ (χ ≫ DerivedCategory.Q.map (complexCoproductIso P).hom ≫
      DerivedCategory.Q.map (complexTelescopeToCocone P c)) := by
    calc
      e.inv = γ ≫ DerivedCategory.Q.map (complexCoproductIso P).hom ≫
          DerivedCategory.Q.map (complexTelescopeToCocone P c) := hγ
      _ = (φ ≫ χ) ≫ DerivedCategory.Q.map (complexCoproductIso P).hom ≫
          DerivedCategory.Q.map (complexTelescopeToCocone P c) := by rw [hφχ]
      _ = _ := by simp only [Category.assoc]
  have hfactor : φ ≫ ψ = 𝟙 (DerivedCategory.Q.obj K) := by
    calc
      φ ≫ ψ = (φ ≫ (χ ≫ (DerivedCategory.Q.map (complexCoproductIso P).hom ≫
          DerivedCategory.Q.map (complexTelescopeToCocone P c)))) ≫ e.hom := by
            simp only [ψ, Category.assoc]
      _ = e.inv ≫ e.hom := by rw [← he]
      _ = 𝟙 _ := e.inv_hom_id
  letI : PreservesBiproduct (fun n : ↥s => P.obj n.val.down) DerivedCategory.Q :=
    preservesBiproduct_of_preservesCoproduct _
  refine ⟨
    { compact := hX
      Y := ⨁ (fun n : ↥s => DerivedCategory.Q.obj (P.obj n.val.down))
      model :=
        { complex := brutalFiniteStageComplex K s
          lower := brutalFiniteStageLower s
          upper := 0
          isStrictlyGE := brutalFiniteStage_isStrictlyGE K s
          isStrictlyLE := brutalFiniteStage_isStrictlyLE K s
          bounds := brutalFiniteStage_lower_bounds s
          free := brutalFiniteStage_free K s
          iso := (DerivedCategory.Q.mapBiproduct
            (fun n : ↥s => P.obj n.val.down)).symm }
      φ := φ
      ψ := ψ
      factor := hfactor }⟩

end BrutalFactorization

section FactorizationTransport

open RelativeFM

universe uA
variable (A : Type uA) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- Transport a bounded-free identity factorization along an isomorphism. -/
def BoundedFreeFactorization.ofIso {X X' : AffineD A}
    (F : Stacks07LT.BoundedFreeFactorization A X) (e : X ≅ X') :
    Stacks07LT.BoundedFreeFactorization A X' where
  compact := isCompactAb_of_iso e F.compact
  Y := F.Y
  model := F.model
  φ := e.inv ≫ F.φ
  ψ := F.ψ ≫ e.hom
  factor := by
    calc
      (e.inv ≫ F.φ) ≫ (F.ψ ≫ e.hom) = e.inv ≫ (F.φ ≫ F.ψ) ≫ e.hom := by
        simp only [Category.assoc]
      _ = e.inv ≫ e.hom := by rw [F.factor, Category.id_comp]
      _ = 𝟙 _ := e.inv_hom_id

/-- Shift a bounded-free model, with both bounds translated by `-a`. -/
noncomputable def shiftBoundedFreeModel {Y : AffineD A}
    (M : Stacks07LT.BoundedFreeModel A Y) (a : ℤ) :
    Stacks07LT.BoundedFreeModel A (Y⟦a⟧) where
  complex := M.complex⟦a⟧
  lower := M.lower - a
  upper := M.upper - a
  isStrictlyGE := by
    letI := M.isStrictlyGE
    exact M.complex.isStrictlyGE_shift M.lower a (M.lower - a) (by omega)
  isStrictlyLE := by
    letI := M.isStrictlyLE
    exact M.complex.isStrictlyLE_shift M.upper a (M.upper - a) (by omega)
  bounds := by have h := M.bounds; omega
  free i := by
    letI := M.free (i + a)
    exact Module.Free.of_equiv
      (M.complex.shiftFunctorObjXIso a i (i + a) rfl).symm.toLinearEquiv
  iso := (shiftFunctor (AffineD A) a).mapIso M.iso ≪≫
    (DerivedCategory.Q.commShiftIso a).symm.app M.complex

/-- Shift a bounded-free identity factorization. -/
noncomputable def shiftBoundedFreeFactorization {X : AffineD A}
    (F : Stacks07LT.BoundedFreeFactorization A X) (a : ℤ) :
    Stacks07LT.BoundedFreeFactorization A (X⟦a⟧) where
  compact := isCompactAb_shift X a F.compact
  Y := F.Y⟦a⟧
  model := shiftBoundedFreeModel A F.model a
  φ := F.φ⟦a⟧'
  ψ := F.ψ⟦a⟧'
  factor := by
    rw [← Functor.map_comp, F.factor]
    simp

/-- **Bounded-free factorization with an arbitrary strict upper bound.**
Shifting by the bound reduces to `nonempty_boundedFreeFactorization_Q_obj`. -/
theorem nonempty_boundedFreeFactorization_Q_obj_of_isStrictlyLE
    (K : CochainComplex (ModuleCat.{uA} A) ℤ) (d : ℤ) [K.IsStrictlyLE d]
    [∀ i, Module.Free A (K.X i)]
    (hX : IsCompactAb (DerivedCategory.Q.obj K)) :
    Nonempty (Stacks07LT.BoundedFreeFactorization A (DerivedCategory.Q.obj K)) := by
  let K₀ := K⟦d⟧
  letI : K₀.IsStrictlyLE 0 := K.isStrictlyLE_shift d d 0 (by simp)
  letI (i : ℤ) : Module.Free A (K₀.X i) := Module.Free.of_equiv
    (K.shiftFunctorObjXIso d i (i + d) rfl).symm.toLinearEquiv
  have hshift : IsCompactAb ((DerivedCategory.Q.obj K)⟦d⟧) :=
    isCompactAb_shift _ _ hX
  have h₀ : IsCompactAb (DerivedCategory.Q.obj K₀) :=
    isCompactAb_of_iso ((DerivedCategory.Q.commShiftIso d).symm.app K) hshift
  let F₀ := (nonempty_boundedFreeFactorization_Q_obj A K₀ h₀).some
  let F₁ := shiftBoundedFreeFactorization A F₀ (-d)
  let e₀ := (shiftFunctor (AffineD A) (-d)).mapIso
    ((DerivedCategory.Q.commShiftIso d).app K)
  let e : (DerivedCategory.Q.obj K₀)⟦(-d : ℤ)⟧ ≅ DerivedCategory.Q.obj K :=
    e₀ ≪≫ shiftShiftNeg (DerivedCategory.Q.obj K) d
  exact ⟨BoundedFreeFactorization.ofIso A F₁ e⟩

end FactorizationTransport

section FreeResolutionInput

open RelativeFM

universe uA
variable (A : Type uA) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- The bounded-above free-resolution input used in Stacks 07LT.

This is precisely Stacks 05T7(1), specialized to the class of free modules:
for a complex with zero terms above `d`, there is a quasi-isomorphism from a
complex of free modules with the same strict upper bound.  Stacks also gives
termwise surjectivity, which is not needed by the factorization argument. -/
structure BoundedAboveFreeResolutionInput (A : Type uA) [CommRing A] where
  resolve (K : CochainComplex (ModuleCat.{uA} A) ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    ∃ (P : CochainComplex (ModuleCat.{uA} A) ℤ) (π : P ⟶ K),
      QuasiIso π ∧ P.IsStrictlyLE d ∧ ∀ n, Module.Free A (P.X n)

/-- Bounded-free factorization for any derived object with a strict
cohomological upper bound, using only Stacks 05T7(1) and the formal 07LR step. -/
theorem nonempty_boundedFreeFactorization_of_isLE
    (R : BoundedAboveFreeResolutionInput A) {X : AffineD A}
    (hX : IsCompactAb X) (d : ℤ) [X.IsLE d] :
    Nonempty (Stacks07LT.BoundedFreeFactorization A X) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X d
  obtain ⟨P, π, hπ, hP, hfree⟩ := R.resolve K d
  letI : QuasiIso π := hπ
  letI : P.IsStrictlyLE d := hP
  letI (n : ℤ) : Module.Free A (P.X n) := hfree n
  let qπ := asIso (DerivedCategory.Q.map π)
  have hPcompact : IsCompactAb (DerivedCategory.Q.obj P) :=
    isCompactAb_of_iso (e ≪≫ qπ.symm) hX
  let F := (nonempty_boundedFreeFactorization_Q_obj_of_isStrictlyLE A P d hPcompact).some
  exact ⟨BoundedFreeFactorization.ofIso A F (qπ ≪≫ e.symm)⟩

/-- The initial half of `BoundedFreeInductionInput`, from Stacks 05T7(1)
and a bounded-above proof. -/
theorem boundedFreeInductionInput_of_freeResolution
    (R : BoundedAboveFreeResolutionInput A)
    (bounded : ∀ X : AffineD A, IsCompactAb X → ∃ d : ℤ, X.IsLE d)
    (I : Stacks07LT.FiniteFreeImprovementInput A) :
    Stacks07LT.BoundedFreeInductionInput A where
  initial X hX := by
    obtain ⟨d, hd⟩ := bounded X hX
    letI := hd
    exact nonempty_boundedFreeFactorization_of_isLE A R hX d
  improve := I

/-- Conditional compact-to-perfect assembly.  The only input not covered by
this module's formal factorization proof is Stacks 05T7(1), here kept explicit.
The bounded-above and finite-free improvement inputs are exactly dA and dC. -/
def compactToPerfectInput_of_freeResolution
    (R : BoundedAboveFreeResolutionInput A)
    (bounded : ∀ X : AffineD A, IsCompactAb X → ∃ d : ℤ, X.IsLE d)
    (I : Stacks07LT.FiniteFreeImprovementInput A) :
    CompactToPerfectInput A :=
  Stacks07LT.compactToPerfectInput_of_freeInduction A
    (boundedFreeInductionInput_of_freeResolution A R bounded I)

end FreeResolutionInput

#print axioms RelativeFM.Stacks07LT.M2.SequentialCoproduct.eq_zero_of_comp_diff
#print axioms RelativeFM.Stacks07LT.M2.SequentialCoproduct.exists_finite_biproduct_factor
#print axioms RelativeFM.Stacks07LT.M2.exists_lift_derivedTelescope
#print axioms RelativeFM.Stacks07LT.M2.nonempty_boundedFreeFactorization_Q_obj
#print axioms RelativeFM.Stacks07LT.M2.nonempty_boundedFreeFactorization_Q_obj_of_isStrictlyLE
#print axioms RelativeFM.Stacks07LT.M2.nonempty_boundedFreeFactorization_of_isLE
#print axioms RelativeFM.Stacks07LT.M2.compactToPerfectInput_of_freeResolution




end
end RelativeFM.Stacks07LT.M2


namespace RelativeFM.Stacks07LT.M2

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox

section UnconditionalFreeResolution

open RelativeFM

universe uA
variable (A : Type uA) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- The unconditional free-resolution input, proved by the 05T7(1)
descending-induction engine in `M2.Resolution`. -/
def boundedAboveFreeResolutionInput : BoundedAboveFreeResolutionInput A where
  resolve K d := by
    intro _
    obtain ⟨Y, hY, f, hf, hfree⟩ :=
      Resolution.exists_free_resolution_isStrictlyLE K d
    exact ⟨Y, f, hf, hY, hfree⟩

/-- The full bounded-free initial induction input, with no external
resolution assumption. -/
def boundedFreeInductionInput_of_boundedAbove
    (bounded : ∀ X : AffineD A, IsCompactAb X → ∃ d : ℤ, X.IsLE d)
    (I : Stacks07LT.FiniteFreeImprovementInput A) :
    Stacks07LT.BoundedFreeInductionInput A :=
  boundedFreeInductionInput_of_freeResolution A
    (boundedAboveFreeResolutionInput A) bounded I

/-- The full bounded finite-projective retract factorization from dA and dC,
with the free-resolution and 07LR steps proved internally and no 066S input. -/
def stacks07LTBoundedFactorizationInput_of_boundedAbove
    (bounded : ∀ X : AffineD A, IsCompactAb X → ∃ d : ℤ, X.IsLE d)
    (I : Stacks07LT.FiniteFreeImprovementInput A) :
    Stacks07LT.Stacks07LTBoundedFactorizationInput A :=
  Stacks07LT.stacks07LTBoundedFactorizationInput_of_freeInduction A
    (boundedFreeInductionInput_of_boundedAbove A bounded I)

/-- Compact-to-perfect from dA (bounded above) and dC (finite-free
improvement), with 05T7(1) and the 07LR factorization proved internally. -/
theorem compactToPerfectInput_of_boundedAbove
    (bounded : ∀ X : AffineD A, IsCompactAb X → ∃ d : ℤ, X.IsLE d)
    (I : Stacks07LT.FiniteFreeImprovementInput A) :
    CompactToPerfectInput A :=
  compactToPerfectInput_of_freeResolution A
    (boundedAboveFreeResolutionInput A) bounded I

end UnconditionalFreeResolution

#print axioms RelativeFM.Stacks07LT.M2.boundedAboveFreeResolutionInput
#print axioms RelativeFM.Stacks07LT.M2.boundedFreeInductionInput_of_boundedAbove
#print axioms RelativeFM.Stacks07LT.M2.stacks07LTBoundedFactorizationInput_of_boundedAbove
#print axioms RelativeFM.Stacks07LT.M2.compactToPerfectInput_of_boundedAbove

end RelativeFM.Stacks07LT.M2
