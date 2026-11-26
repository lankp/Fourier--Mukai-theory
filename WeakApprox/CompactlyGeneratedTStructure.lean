/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.CoprodRetract
import WeakApprox.HomVanishing
import WeakApprox.CompactAb
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Compactly generated `t`-structures (Alonso--Jeremías--Souto)

Source: Lank--Pauwels, *Gluing weak approximability along recollements* (LP26),
§2.1.3 (`sec:prelim_t-structures_t_structures`): for a compact object `G` of a
triangulated category with small coproducts,
`Coprod({G[n] : n ≥ 0}) = ⟨G⟩^{(-∞,0]}` is an aisle.  LP26 cites Neeman 2021b,
Theorem 2.3 and Canonaco--Haesemeyer--Neeman--Stellari 2024, Theorem 2.3.3
(generalizing Alonso--Jeremías--Souto 2003, Theorem A.1).  This is not a Stacks
Project result; it is proved here.

## What is proved

* `exists_finset_sum_of_isCompactAb`: a morphism from an `Ab`-compact object
  into a small coproduct is a finite sum of morphisms through the coprojections.
* `milnor_inj`: for the Milnor (homotopy) colimit triangle
  `∐ Aₖ --(1 - σ)--> ∐ Aₖ → hocolim Aₖ`, postcomposition with `1 - σ` is
  injective on maps out of a compact object.
* `exists_aisle_triangle`: for every `E` there is a distinguished triangle
  `X → E → Y → X[1]` with `X ∈ Coprod(shiftTail G 0)` and `Hom(G[n], Y) = 0`
  for all `n ≥ 0`.  The construction is the classical one: `X` is the Milnor
  colimit of objects `Aₖ ∈ Coprod(shiftTail G 0)`, where `A₀` is the coproduct
  of all `G[n] → E` (`n ≥ 0`) and `Aₖ₊₁` kills every `G[m] → Aₖ` (`m ≥ -1`)
  that vanishes in `E`.
* `compactTStructure G hG : TStructure C` with
  `(compactTStructure G hG).le n = Coprod (shiftTail G (-n))`, in particular
  `compactTStructure_le_zero : (compactTStructure G hG).le 0 = Coprod (shiftTail G 0)`,
  and the coaisle `ge n` is `{Y | Hom(G[k], Y) = 0 for all k ≥ 1 - n}`.

## Hypotheses

`C` is pretriangulated with `HasCoproducts.{v} C` (coproducts indexed by types
of the Hom universe, the coproducts used by `Coprod`), and `G` is compact in the
sense `IsCompactAb` (the project's compactness, `Hom(G, -)` to abelian groups
preserves small coproducts).  No octahedral axiom is used.  Nothing is assumed.
-/

@[expose] public section

namespace RelativeWeakApprox.CompactTStructureW6

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeWeakApprox

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Finite support for maps out of compact objects -/

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- A morphism from an `Ab`-compact object into a small coproduct factors
through finitely many coprojections. -/
theorem exists_finset_sum_of_isCompactAb {H : C} (hH : IsCompactAb H)
    {J : Type v} [DecidableEq J] (X : J → C) [HasCoproduct X] (v : H ⟶ ∐ X) :
    ∃ (S : Finset J) (y : ∀ j, H ⟶ X j), v = ∑ j ∈ S, y j ≫ Sigma.ι X j := by
  classical
  let F := preadditiveCoyoneda.obj (Opposite.op H)
  let c0 : Cofan X := Cofan.mk (∐ X) (Sigma.ι X)
  have hc0 : IsColimit c0 := coproductIsCoproduct X
  have hF : IsColimit (F.mapCocone c0) := isColimitOfPreserves F hc0
  let hAb := (Cofan.isColimitMapCoconeEquiv F X c0) hF
  obtain ⟨z, hz⟩ := (bijective_abCofanSum_of_isColimit hAb).2 v
  refine ⟨z.support, fun j => z j, ?_⟩
  rw [← hz]
  change (DFinsupp.sumAddHom fun j => _) z = _
  erw [DFinsupp.sumAddHom_apply]
  rfl

/-! ### Sequences and the Milnor colimit -/

section Milnor

variable [HasCoproducts.{v} C]

/-- The coproduct `∐ₖ Aₖ` of a sequence, indexed by `ULift ℕ`. -/
abbrev seqCoprod (A : ℕ → C) : C := ∐ fun k : ULift.{v} ℕ => A k.down

/-- The coprojection `Aₖ ⟶ ∐ Aₖ`. -/
abbrev seqι (A : ℕ → C) (k : ℕ) : A k ⟶ seqCoprod A :=
  Sigma.ι (fun k : ULift.{v} ℕ => A k.down) ⟨k⟩

/-- The shift map `σ : ∐ Aₖ ⟶ ∐ Aₖ`, which is `sₖ` followed by the `k+1`st
coprojection on the `k`th summand. -/
def seqShift (A : ℕ → C) (s : ∀ k, A k ⟶ A (k + 1)) : seqCoprod A ⟶ seqCoprod A :=
  Sigma.desc fun k => s k.down ≫ seqι A (k.down + 1)

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
@[reassoc (attr := simp)]
lemma ι_seqShift (A : ℕ → C) (s : ∀ k, A k ⟶ A (k + 1)) (k : ℕ) :
    seqι A k ≫ seqShift A s = s k ≫ seqι A (k + 1) := by
  simp [seqShift, seqι]

/-- The projection `∐ Aₖ ⟶ Aⱼ`. -/
def seqProj (A : ℕ → C) (j : ℕ) : seqCoprod A ⟶ A j :=
  Sigma.desc fun k => if h : k.down = j then eqToHom (by rw [h]) else 0

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma ι_seqProj (A : ℕ → C) (k j : ℕ) :
    seqι A k ≫ seqProj A j = if h : k = j then eqToHom (by rw [h]) else 0 := by
  simp [seqProj, seqι]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
@[reassoc (attr := simp)]
lemma ι_seqProj_self (A : ℕ → C) (j : ℕ) : seqι A j ≫ seqProj A j = 𝟙 _ := by
  rw [ι_seqProj]; simp

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma ι_seqProj_of_ne (A : ℕ → C) {k j : ℕ} (h : k ≠ j) : seqι A k ≫ seqProj A j = 0 := by
  rw [ι_seqProj]; simp [h]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma seqShift_seqProj_zero (A : ℕ → C) (s : ∀ k, A k ⟶ A (k + 1)) :
    seqShift A s ≫ seqProj A 0 = 0 := by
  apply Sigma.hom_ext
  rintro ⟨k⟩
  rw [comp_zero, ι_seqShift_assoc, ι_seqProj_of_ne A (by omega), comp_zero]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma seqShift_seqProj_succ (A : ℕ → C) (s : ∀ k, A k ⟶ A (k + 1)) (j : ℕ) :
    seqShift A s ≫ seqProj A (j + 1) = seqProj A j ≫ s j := by
  apply Sigma.hom_ext
  rintro ⟨k⟩
  change seqι A k ≫ _ = seqι A k ≫ _
  rw [ι_seqShift_assoc]
  by_cases h : k = j
  · subst h
    simp
  · rw [ι_seqProj_of_ne A (by omega : k + 1 ≠ j + 1), comp_zero,
      ← Category.assoc, ι_seqProj_of_ne A h, zero_comp]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- **Injectivity of `1 - σ` on compact sources.**  If `H` is compact and
`v : H ⟶ ∐ Aₖ` satisfies `v ≫ (1 - σ) = 0`, then `v = 0`.  The finite support
of `v` (compactness) and the projections reduce this to the recursion
`v_0 = 0`, `v_{j+1} = v_j ≫ s_j`. -/
theorem milnor_inj (A : ℕ → C) (s : ∀ k, A k ⟶ A (k + 1)) {H : C}
    (hH : IsCompactAb H) (v : H ⟶ seqCoprod A)
    (hv : v ≫ (𝟙 _ - seqShift A s) = 0) : v = 0 := by
  classical
  have hσ : v = v ≫ seqShift A s := by
    rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hv
    exact hv
  have hproj : ∀ j, v ≫ seqProj A j = 0 := by
    intro j
    induction j with
    | zero => rw [hσ, Category.assoc, seqShift_seqProj_zero, comp_zero]
    | succ j ih => rw [hσ, Category.assoc, seqShift_seqProj_succ, ← Category.assoc, ih,
        zero_comp]
  obtain ⟨S, y, hy⟩ := exists_finset_sum_of_isCompactAb hH
    (fun k : ULift.{v} ℕ => A k.down) v
  have hcoef : ∀ j ∈ S, y j = 0 := by
    intro j hj
    have h := hproj j.down
    rw [hy, Preadditive.sum_comp] at h
    rw [Finset.sum_eq_single_of_mem j hj] at h
    · rw [Category.assoc] at h
      change y j ≫ seqι A j.down ≫ seqProj A j.down = 0 at h
      simpa using h
    · intro i _ hij
      rw [Category.assoc]
      change y i ≫ seqι A i.down ≫ seqProj A j.down = 0
      rw [ι_seqProj_of_ne A (fun h => hij (ULift.ext h)), comp_zero]
  rw [hy]
  exact Finset.sum_eq_zero fun j hj => by rw [hcoef j hj, zero_comp]

end Milnor

/-! ### The killing step -/

section Kill

variable [HasCoproducts.{v} C] (G : C)

/-- The index type of the maps to be killed: `G[m] ⟶ A`, `m ≥ -1`, vanishing
after `a : A ⟶ E`. -/
abbrev KillIndex {A E : C} (a : A ⟶ E) : Type v :=
  Σ m : {m : ℤ // -1 ≤ m}, {u : G⟦(m : ℤ)⟧ ⟶ A // u ≫ a = 0}

/-- One killing step.  From `a : A ⟶ E` with `A` in the aisle, produce
`s : A ⟶ A'` and `a' : A' ⟶ E` with `s ≫ a' = a`, `A'` in the aisle, and every
`u : G[m] ⟶ A` (`m ≥ -1`) with `u ≫ a = 0` killed by `s`. -/
structure KillStep {A E : C} (a : A ⟶ E) where
  /-- The new object. -/
  obj : C
  /-- The transition map. -/
  s : A ⟶ obj
  /-- The new map to `E`. -/
  a' : obj ⟶ E
  fac : s ≫ a' = a
  kill : ∀ (m : ℤ), -1 ≤ m → ∀ u : G⟦m⟧ ⟶ A, u ≫ a = 0 → u ≫ s = 0
  mem : Coprod (shiftTail G 0) A → Coprod (shiftTail G 0) obj

omit [HasCoproducts.{v} C] in
lemma coprod_shiftTail_shift_one {X : C} (hX : Coprod (shiftTail G (-1)) X) :
    Coprod (shiftTail G 0) (X⟦(1 : ℤ)⟧) := by
  have h := map_shift_Coprod (shiftTail G (-1)) (1 : ℤ) hX
  rw [shiftImage_shiftTail] at h
  simpa using h

theorem nonempty_killStep {A E : C} (a : A ⟶ E) : Nonempty (KillStep G a) := by
  let X : KillIndex G a → C := fun x => G⟦(x.1 : ℤ)⟧
  let κ : ∐ X ⟶ A := Sigma.desc fun x => x.2.1
  have hκ : κ ≫ a = 0 := by
    apply Sigma.hom_ext
    intro x
    simp [κ, x.2.2]
  obtain ⟨A', s, d, hT⟩ := distinguished_cocone_triangle κ
  obtain ⟨a', ha'⟩ := Triangle.yoneda_exact₂ _ hT a hκ
  have hK : Coprod (shiftTail G (-1)) (∐ X) :=
    Coprod.of_sigma X fun x => Coprod.of_mem _ ⟨x.1.1, x.1.2, ⟨Iso.refl _⟩⟩
  refine ⟨{ obj := A', s := s, a' := a', fac := ha'.symm, kill := ?_, mem := ?_ }⟩
  · intro m hm u hu
    have hu' : u = Sigma.ι X ⟨⟨m, hm⟩, ⟨u, hu⟩⟩ ≫ κ := by simp [κ]
    rw [hu', Category.assoc]
    have := comp_distTriang_mor_zero₁₂ _ hT
    dsimp at this
    rw [this, comp_zero]
  · intro hA
    exact Coprod.of_extension _ (rot_of_distTriang _ hT) hA (coprod_shiftTail_shift_one G hK)

/-- A chosen killing step. -/
def killStep {A E : C} (a : A ⟶ E) : KillStep G a :=
  Classical.choice (nonempty_killStep G a)

/-- The coproduct of all `G[n] ⟶ E`, `n ≥ 0`, with its canonical map to `E`. -/
abbrev startIndex (E : C) : Type v := Σ n : {n : ℤ // 0 ≤ n}, (G⟦(n : ℤ)⟧ ⟶ E)

/-- The sequence `(Aₖ, aₖ : Aₖ ⟶ E)`. -/
def killSeq (E : C) : ℕ → Σ A : C, (A ⟶ E)
  | 0 => ⟨∐ fun x : startIndex G E => G⟦(x.1 : ℤ)⟧, Sigma.desc fun x => x.2⟩
  | k + 1 => ⟨(killStep G (killSeq E k).2).obj, (killStep G (killSeq E k).2).a'⟩

end Kill

/-! ### Existence of the aisle triangle -/

section Existence

variable [HasCoproducts.{v} C] (G : C)

lemma killSeq_mem (E : C) (k : ℕ) : Coprod (shiftTail G 0) (killSeq G E k).1 := by
  induction k with
  | zero =>
    exact Coprod.of_sigma _ fun x => Coprod.of_mem _ ⟨x.1.1, x.1.2, ⟨Iso.refl _⟩⟩
  | succ k ih => exact (killStep G (killSeq G E k).2).mem ih

/-- **Alonso--Jeremías--Souto, existence of the truncation triangle.**  For a
compact `G` and any `E` there is a distinguished triangle `X → E → Y → X[1]`
with `X ∈ Coprod(shiftTail G 0)` and `Hom(G[n], Y) = 0` for every `n ≥ 0`. -/
theorem exists_aisle_triangle (hG : IsCompactAb G) (E : C) :
    ∃ (X Y : C) (_ : Coprod (shiftTail G 0) X)
      (_ : ∀ n : ℤ, 0 ≤ n → ∀ f : G⟦n⟧ ⟶ Y, f = 0)
      (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  classical
  let A : ℕ → C := fun k => (killSeq G E k).1
  let a : ∀ k, A k ⟶ E := fun k => (killSeq G E k).2
  let s : ∀ k, A k ⟶ A (k + 1) := fun k => (killStep G (killSeq G E k).2).s
  have hfac : ∀ k, s k ≫ a (k + 1) = a k := fun k => (killStep G (killSeq G E k).2).fac
  have hkill : ∀ k (m : ℤ), -1 ≤ m → ∀ u : G⟦m⟧ ⟶ A k, u ≫ a k = 0 → u ≫ s k = 0 :=
    fun k => (killStep G (killSeq G E k).2).kill
  -- the Milnor triangle
  obtain ⟨Ainf, π, δ, hM⟩ := distinguished_cocone_triangle (𝟙 (seqCoprod A) - seqShift A s)
  let c : ∀ k, A k ⟶ Ainf := fun k => seqι A k ≫ π
  have hπ : (𝟙 (seqCoprod A) - seqShift A s) ≫ π = 0 := comp_distTriang_mor_zero₁₂ _ hM
  have hc : ∀ k, c k = s k ≫ c (k + 1) := by
    intro k
    have h := seqι A k ≫= hπ
    rw [comp_zero, Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub,
      ι_seqShift_assoc, sub_eq_zero] at h
    simpa [c] using h
  -- the map to `E`
  let adesc : seqCoprod A ⟶ E := Sigma.desc fun k => a k.down
  have hadesc : (𝟙 (seqCoprod A) - seqShift A s) ≫ adesc = 0 := by
    apply Sigma.hom_ext
    rintro ⟨k⟩
    change seqι A k ≫ _ = seqι A k ≫ 0
    simp only [Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub,
      ι_seqShift_assoc, comp_zero, adesc, seqι, Sigma.ι_comp_desc]
    rw [hfac, sub_self]
  obtain ⟨ainf, hainf⟩ := Triangle.yoneda_exact₂ _ hM adesc hadesc
  have hca : ∀ k, c k ≫ ainf = a k := by
    intro k
    have h := seqι A k ≫= hainf
    simpa [c, adesc, seqι] using h.symm
  -- membership of the Milnor colimit
  have hAinf : Coprod (shiftTail G 0) Ainf := by
    have hsum : Coprod (shiftTail G 0) (seqCoprod A) :=
      Coprod.of_sigma _ fun k => killSeq_mem G E k.down
    exact Coprod.of_extension _ (rot_of_distTriang _ hM) hsum
      (CoprodRetractM3.shift_one hsum)
  -- transition maps
  have htrans : ∀ k K, k ≤ K → ∃ t : A k ⟶ A K, c k = t ≫ c K := by
    intro k K hkK
    induction K, hkK using Nat.le_induction with
    | base => exact ⟨𝟙 _, by simp⟩
    | succ K _ ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨t ≫ s K, by rw [ht, hc K, Category.assoc]⟩
  -- every finite sum through the coprojections factors through one stage
  have hfin : ∀ {H : C} (S : Finset (ULift.{v} ℕ)) (y : ∀ j : ULift.{v} ℕ, H ⟶ A j.down),
      ∃ (K : ℕ) (g : H ⟶ A K), (∑ j ∈ S, y j ≫ seqι A j.down) ≫ π = g ≫ c K := by
    intro H S y
    induction S using Finset.induction_on with
    | empty => exact ⟨0, 0, by simp⟩
    | insert j S hj ih =>
      obtain ⟨K, g, hg⟩ := ih
      obtain ⟨t₁, ht₁⟩ := htrans K (max K j.down) (le_max_left _ _)
      obtain ⟨t₂, ht₂⟩ := htrans j.down (max K j.down) (le_max_right _ _)
      refine ⟨max K j.down, y j ≫ t₂ + g ≫ t₁, ?_⟩
      rw [Finset.sum_insert hj, Preadditive.add_comp, hg, Category.assoc,
        Preadditive.add_comp, Category.assoc, Category.assoc, ← ht₁, ← ht₂]
  -- (β): maps from `G[m]`, `m ≥ -1`, into `Ainf` vanishing in `E` vanish
  have hβ : ∀ (m : ℤ), -1 ≤ m → ∀ u : G⟦m⟧ ⟶ Ainf, u ≫ ainf = 0 → u = 0 := by
    intro m hm u hu
    have hHc : IsCompactAb (G⟦m⟧⟦(-1 : ℤ)⟧) := isCompactAb_shift _ _ (isCompactAb_shift _ _ hG)
    -- `u ≫ δ = 0`
    have hδ : u ≫ δ = 0 := by
      let e : (G⟦m⟧⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ G⟦m⟧ := shiftNegShift (G⟦m⟧) (1 : ℤ)
      let w : G⟦m⟧⟦(-1 : ℤ)⟧ ⟶ seqCoprod A :=
        (shiftFunctor C (1 : ℤ)).preimage (e.hom ≫ u ≫ δ)
      have hw : w⟦(1 : ℤ)⟧' = e.hom ≫ u ≫ δ := (shiftFunctor C (1 : ℤ)).map_preimage _
      have hw0 : w ≫ (𝟙 _ - seqShift A s) = 0 := by
        apply (shiftFunctor C (1 : ℤ)).map_injective
        rw [Functor.map_comp, hw, Functor.map_zero]
        have h3 := comp_distTriang_mor_zero₃₁ _ hM
        dsimp at h3
        rw [Category.assoc, Category.assoc, h3, comp_zero, comp_zero]
      have hw' : w = 0 := milnor_inj A s hHc w hw0
      rw [hw', Functor.map_zero] at hw
      rw [← cancel_epi e.hom, comp_zero, ← hw]
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₃ _ hM u hδ
    dsimp at hy
    obtain ⟨S, z, hz⟩ := exists_finset_sum_of_isCompactAb (isCompactAb_shift _ _ hG)
      (fun k : ULift.{v} ℕ => A k.down) y
    obtain ⟨K, g, hg⟩ := hfin S z
    have hu' : u = g ≫ c K := by rw [hy, hz]; exact hg
    have hga : g ≫ a K = 0 := by rw [← hca K, ← Category.assoc, ← hu', hu]
    rw [hu', hc K, ← Category.assoc, hkill K m hm g hga, zero_comp]
  -- the final triangle
  obtain ⟨Y, gE, hY, hT⟩ := distinguished_cocone_triangle ainf
  refine ⟨Ainf, Y, hAinf, ?_, ainf, gE, hY, hT⟩
  intro n hn y
  -- `y ≫ hY = 0`
  have hyδ : y ≫ hY = 0 := by
    let e : (G⟦n - 1⟧)⟦(1 : ℤ)⟧ ≅ G⟦n⟧ :=
      (shiftFunctorAdd' C (n - 1) 1 n (by omega)).symm.app G
    let w : G⟦n - 1⟧ ⟶ Ainf := (shiftFunctor C (1 : ℤ)).preimage (e.hom ≫ y ≫ hY)
    have hw : w⟦(1 : ℤ)⟧' = e.hom ≫ y ≫ hY := (shiftFunctor C (1 : ℤ)).map_preimage _
    have hw0 : w ≫ ainf = 0 := by
      apply (shiftFunctor C (1 : ℤ)).map_injective
      rw [Functor.map_comp, hw, Functor.map_zero]
      have h3 := comp_distTriang_mor_zero₃₁ _ hT
      dsimp at h3
      rw [Category.assoc, Category.assoc, h3, comp_zero, comp_zero]
    have hw' : w = 0 := hβ (n - 1) (by omega) w hw0
    rw [hw', Functor.map_zero] at hw
    rw [← cancel_epi e.hom, comp_zero, ← hw]
  obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₃ _ hT y hyδ
  dsimp at hx
  -- (α): `x` factors through `ainf`
  let ι0 : G⟦n⟧ ⟶ A 0 := Sigma.ι (fun x : startIndex G E => G⟦(x.1 : ℤ)⟧) ⟨⟨n, hn⟩, x⟩
  have hxfac : x = (ι0 ≫ c 0) ≫ ainf := by
    rw [Category.assoc, hca 0]
    exact (Sigma.ι_comp_desc (fun x : startIndex G E => x.2) ⟨⟨n, hn⟩, x⟩).symm
  rw [hx, hxfac, Category.assoc]
  have h12 := comp_distTriang_mor_zero₁₂ _ hT
  dsimp at h12
  rw [h12, comp_zero]

/-! ### The `t`-structure -/

/-- The coaisle of the `t`-structure compactly generated by `G`:
`Y ∈ ge n` iff `Hom(G[k], Y) = 0` for all `k ≥ 1 - n`. -/
def coaisle (n : ℤ) : ObjectProperty C := fun Y =>
  ∀ k : ℤ, 1 - n ≤ k → ∀ f : G⟦k⟧ ⟶ Y, f = 0

instance (n : ℤ) : (coaisle G n).IsClosedUnderIsomorphisms where
  of_iso e h := by
    intro k hk f
    rw [← cancel_mono e.inv, zero_comp]
    exact h k hk _

omit [HasCoproducts.{v} C] in
lemma coprod_shiftTail_shift {n a n' : ℤ} (h : a + n' = n) {X : C}
    (hX : Coprod (shiftTail G (-n)) X) : Coprod (shiftTail G (-n')) (X⟦a⟧) := by
  have h' := map_shift_Coprod (shiftTail G (-n)) a hX
  rw [shiftImage_shiftTail] at h'
  rwa [show -n + a = -n' by omega] at h'

/-- **The `t`-structure compactly generated by a compact object** (Alonso--
Jeremías--Souto; LP26 §2.1.3).  Its aisle in degree `n` is
`Coprod(shiftTail G (-n))`, i.e. generated by the `G[k]`, `k ≥ -n`. -/
def compactTStructure (G : C) (hG : IsCompactAb G) : TStructure C where
  le n := Coprod (shiftTail G (-n))
  ge n := coaisle G n
  le_shift n a n' h X hX := coprod_shiftTail_shift G h hX
  ge_shift n a n' h Y hY := by
    intro k hk f
    let e : G⟦k - a⟧ ≅ G⟦k⟧⟦-a⟧ := (shiftFunctorAdd' C k (-a) (k - a) (by omega)).app G
    have h0 := hY (k - a) (by omega) (e.hom ≫ f⟦-a⟧' ≫ (shiftShiftNeg Y a).hom)
    have h1 : f⟦-a⟧' = 0 := by
      rw [← cancel_mono (shiftShiftNeg Y a).hom, zero_comp, ← cancel_epi e.hom, comp_zero]
      exact h0
    apply (shiftFunctor C (-a)).map_injective
    rw [h1, Functor.map_zero]
  zero' X Y f hX hY := by
    have hle : Coprod (shiftTail G (-0)) ≤ homZeroLeft Y := by
      apply Coprod.le
      rintro Z ⟨k, hk, ⟨e⟩⟩ g
      rw [← cancel_epi e.inv, comp_zero]
      exact hY k (by omega) _
    exact hle X hX f
  le_zero_le := by
    apply Coprod_mono
    rintro X ⟨k, hk, e⟩
    exact ⟨k, by omega, e⟩
  ge_one_le := fun Y hY k hk f => hY k (by omega) f
  exists_triangle_zero_one E := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ := exists_aisle_triangle G hG E
    exact ⟨X, Y, by simpa using hX, fun k hk => hY k (by omega), f, g, h, hT⟩

@[simp]
lemma compactTStructure_le (hG : IsCompactAb G) (n : ℤ) :
    (compactTStructure G hG).le n = Coprod (shiftTail G (-n)) := rfl

@[simp]
lemma compactTStructure_ge (hG : IsCompactAb G) (n : ℤ) :
    (compactTStructure G hG).ge n = coaisle G n := rfl

/-- The degree-zero aisle is exactly `Coprod(shiftTail G 0)`, the form used by
`PaperSetupMainMinimal`. -/
theorem compactTStructure_le_zero (hG : IsCompactAb G) :
    (compactTStructure G hG).le 0 = Coprod (shiftTail G 0) := by
  simp

/-- **Existence of the compactly generated `t`-structure** in the form used by
the tree: a `t`-structure whose degree-zero aisle is `Coprod(shiftTail G 0)`. -/
theorem exists_compactlyGenerated_tStructure (hG : IsCompactAb G) :
    ∃ t : TStructure C, t.le 0 = Coprod (shiftTail G 0) :=
  ⟨compactTStructure G hG, compactTStructure_le_zero G hG⟩

omit [HasCoproducts.{v} C] in
/-- The coaisle of any `t`-structure compactly generated by `G` is described
by vanishing of maps from the shifts of `G`. -/
theorem ge_one_iff_of_compactlyGenerated (t : TStructure C)
    (ht : t.le 0 = Coprod (shiftTail G 0)) (Y : C) :
    t.ge 1 Y ↔ ∀ n : ℤ, 0 ≤ n → ∀ f : G⟦n⟧ ⟶ Y, f = 0 := by
  constructor
  · intro hY n hn f
    have hGn : t.le 0 (G⟦n⟧) := by
      rw [ht]; exact Coprod.of_mem _ ⟨n, hn, ⟨Iso.refl _⟩⟩
    exact t.zero' f hGn hY
  · intro hY
    rw [TStructure.ge_iff_isGE, t.isGE_iff_orthogonal 0 1 (by omega)]
    intro X g hX'
    have hX : t.le 0 X := t.le_of_isLE X 0
    rw [ht] at hX
    have hle : Coprod (shiftTail G 0) ≤ homZeroLeft Y := by
      apply Coprod.le
      rintro Z ⟨k, hk, ⟨e⟩⟩ g
      rw [← cancel_epi e.inv, comp_zero]
      exact hY k hk _
    exact hle X hX g

end Existence

end

end RelativeWeakApprox.CompactTStructureW6

#print axioms RelativeWeakApprox.CompactTStructureW6.exists_aisle_triangle
#print axioms RelativeWeakApprox.CompactTStructureW6.compactTStructure_le_zero
#print axioms RelativeWeakApprox.CompactTStructureW6.ge_one_iff_of_compactlyGenerated
