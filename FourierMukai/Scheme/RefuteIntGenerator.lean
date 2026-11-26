/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.GeneratorCounterexampleM5
import FourierMukai.Scheme.M4Unconditional
import FourierMukai.Scheme.AffineUniverse
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic

/-!
# F2: no compact object of `D(ℤ)` is an `IsGenerator`

Refutation **F2** of `results/OPEN_INPUTS.md` §0 (task `wave6/vacuity-refutations`,
rule 3 of `CLAUDE.md`).

The repository's `RelativeWeakApprox.IsGenerator G` asks that the shifts of `G`
**separate morphisms** (`Basic.lean`), which is strictly stronger than the zero
detection of LP26/Neeman (`IsPaperGenerator`).  In `D(ℤ)` no compact object has this
property (`not_isGenerator_of_isCompactAb_int`).

## Argument

1. (generic, `FinHom`) Fix an object `T` of a pretriangulated category.  The objects
   `X` such that every `Hom(X⟦n⟧, T)` is a finitely generated `ℤ`-module and
   `Hom(X⟦n⟧, T) = 0` for `n` outside a bounded interval form a triangulated,
   retract-closed subcategory (`FinHom T`; closure under extensions is the
   exactness of `Hom(-, T)` on distinguished triangles plus `ℤ` Noetherian).
2. (generic, `not_isGenerator_of_finHom`) Suppose that for every prime `p` there is
   a distinguished triangle `R --p--> R → M_p --φ_p--> R⟦1⟧` with `φ_p ≠ 0`.  If
   `G ∈ FinHom (R⟦1⟧)`, the torsion of the finitely many nonzero groups
   `Hom(G⟦n⟧, R⟦1⟧)` is killed by one `N ≠ 0`; for a prime `p ∤ N`, every composite
   `G⟦n⟧ → M_p → R⟦1⟧` is killed by `p` (since `φ_p ≫ p = 0`) and by `N`, hence is
   zero.  So `φ_p` is a nonzero ghost for the shifts of `G`, and `G` is not an
   `IsGenerator` (`not_isGenerator_of_isGhostFromShifts`).
3. (`D(ℤ)`) For `R = ℤ[0]` the triangles are the single triangles of
   `0 → ℤ --p--> ℤ → ℤ/p → 0` (non-split, so `φ_p ≠ 0`); `R ∈ FinHom (R⟦1⟧)` since
   `Hom(R⟦n⟧, R⟦1⟧)` is `0` for `n ≠ 1` (projectivity) and `ℤ·𝟙` for `n = 1`.  A
   compact object is perfect, i.e. in the thick envelope of `R`
   (`Stacks07LT.M4.perf_of_compact_unconditional`, proved), and the envelope lies in
   `FinHom (R⟦1⟧)` by step 1.

This avoids the structure theorem for perfect complexes over `ℤ`.

## Consequences (in the large model `AffineD ℤ`)

* `isEmpty_weakApproximationData_int : IsEmpty (WeakApproximationData (AffineD ℤ))`;
* `not_satisfiesWA_int : ¬ SatisfiesWA (AffineD ℤ)` — although `D(ℤ)` *is* weakly
  approximable in the paper's sense (LP26), so the repository rendering of
  Definition 2.1 is false at `ℤ`;
* `isEmpty_setupMainMinimal_int : IsEmpty (SetupMainMinimal DZ (AffineD ℤ) DU)`, so
  the pinned `RelativeWeakApprox.SetupMainMinimal.theorem_1_1` is vacuous whenever
  the middle category is `AffineD ℤ`.

The same refutation in the small-Hom model `SmallAffineD ℤ H` (hence vacuity of the
pinned `RelativeFM.affine_theorem_1_1_small` at `ℤ`) is in
`Scheme/RefuteIntGeneratorSmall.lean`.

Nothing is assumed.  The negated propositions are the tree's own definitions
(`IsGenerator`, `IsCompactAb`, `WeakApproximationData`, `SatisfiesWA`,
`SetupMainMinimal`).
-/

@[expose] public section

namespace RelativeFM.VacuityF2

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open RelativeFM RelativeWeakApprox
open scoped ZeroObject

universe u v w uZ uU

noncomputable section

section Generic

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Precomposition with `f`, as a `ℤ`-linear map of Hom groups. -/
def precompLin {X Y : C} (f : X ⟶ Y) (T : C) : (Y ⟶ T) →ₗ[ℤ] (X ⟶ T) :=
  (Preadditive.leftComp T f).toIntLinearMap

@[simp] lemma precompLin_apply {X Y : C} (f : X ⟶ Y) (T : C) (g : Y ⟶ T) :
    precompLin f T g = f ≫ g := rfl

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- Objects `X` with `Hom(X⟦n⟧, T)` finitely generated over `ℤ` for every `n`, and
zero for `n` outside a bounded interval. -/
def FinHom (T : C) : ObjectProperty C := fun X =>
  (∀ n : ℤ, Module.Finite ℤ (X⟦n⟧ ⟶ T)) ∧
    ∃ a b : ℤ, ∀ n : ℤ, (n < a ∨ b < n) → ∀ f : X⟦n⟧ ⟶ T, f = 0

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma module_finite_of_retract {X Y : C} (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X)
    (T : C) [Module.Finite ℤ (Y ⟶ T)] : Module.Finite ℤ (X ⟶ T) :=
  Module.Finite.of_surjective (precompLin i T) (fun g => ⟨r ≫ g, by
    simp [← Category.assoc, h]⟩)

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma eq_zero_of_retract {X Y : C} (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X)
    {T : C} (hY : ∀ f : Y ⟶ T, f = 0) (f : X ⟶ T) : f = 0 := by
  have : f = i ≫ (r ≫ f) := by simp [← Category.assoc, h]
  rw [this, hY (r ≫ f), Limits.comp_zero]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma finHom_of_retract (T : C) {X Y : C} (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X)
    (hY : FinHom T Y) : FinHom T X := by
  obtain ⟨hfin, a, b, hvan⟩ := hY
  have h' : ∀ n : ℤ, i⟦n⟧' ≫ r⟦n⟧' = 𝟙 _ := fun n => by
    rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]
  refine ⟨fun n => ?_, a, b, fun n hn f => ?_⟩
  · have := hfin n
    exact module_finite_of_retract (i⟦n⟧') (r⟦n⟧') (h' n) T
  · exact eq_zero_of_retract (i⟦n⟧') (r⟦n⟧') (h' n) (hvan n hn) f

instance finHom_isStableUnderRetracts (T : C) : (FinHom T).IsStableUnderRetracts where
  of_retract h hY := finHom_of_retract T h.i h.r h.retract hY

instance finHom_isClosedUnderIsomorphisms (T : C) : (FinHom T).IsClosedUnderIsomorphisms where
  of_iso e hX := finHom_of_retract T e.inv e.hom e.inv_hom_id hX

instance finHom_containsZero (T : C) : (FinHom T).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero C, fun n => ?_, 0, 0, fun n _ f => ?_⟩
    · have hz : IsZero ((0 : C)⟦n⟧) := (shiftFunctor C n).map_isZero (isZero_zero C)
      exact Module.Finite.of_surjective (0 : ℤ →ₗ[ℤ] ((0 : C)⟦n⟧ ⟶ T))
        (fun f => ⟨0, hz.eq_of_src _ _⟩)
    · exact ((shiftFunctor C n).map_isZero (isZero_zero C)).eq_of_src _ _

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma finHom_shift (T : C) {X : C} (hX : FinHom T X) (k : ℤ) : FinHom T (X⟦k⟧) := by
  obtain ⟨hfin, a, b, hvan⟩ := hX
  let e : ∀ n : ℤ, X⟦k⟧⟦n⟧ ≅ X⟦k + n⟧ := fun n => ((shiftFunctorAdd C k n).app X).symm
  refine ⟨fun n => ?_, a - k, b - k, fun n hn f => ?_⟩
  · have := hfin (k + n)
    exact module_finite_of_retract (e n).hom (e n).inv (e n).hom_inv_id T
  · exact eq_zero_of_retract (e n).hom (e n).inv (e n).hom_inv_id
      (hvan (k + n) (by omega)) f

instance finHom_isStableUnderShift (T : C) : (FinHom T).IsStableUnderShift ℤ where
  isStableUnderShiftBy k := ⟨fun _ hX => finHom_shift T hX k⟩

/-- Two-out-of-three for `FinHom` along a distinguished triangle: the middle term. -/
lemma finHom_ext₂ (T : C) (Δ : Triangle C) (hΔ : Δ ∈ distTriang C)
    (h₁ : FinHom T Δ.obj₁) (h₃ : FinHom T Δ.obj₃) : FinHom T Δ.obj₂ := by
  obtain ⟨hfin₁, a₁, b₁, hvan₁⟩ := h₁
  obtain ⟨hfin₃, a₃, b₃, hvan₃⟩ := h₃
  refine ⟨fun n => ?_, min a₁ a₃, max b₁ b₃, fun n hn f => ?_⟩
  · let Δ' := (shiftFunctor (Triangle C) n).obj Δ
    have hΔ' : Δ' ∈ distTriang C := Triangle.shift_distinguished Δ hΔ n
    have : Module.Finite ℤ (Δ'.obj₁ ⟶ T) := hfin₁ n
    have : Module.Finite ℤ (Δ'.obj₃ ⟶ T) := hfin₃ n
    let φ₁ := precompLin Δ'.mor₁ T
    let φ₂ := precompLin Δ'.mor₂ T
    have hker : LinearMap.ker φ₁ = LinearMap.range φ₂ := by
      apply le_antisymm
      · intro f hf
        obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ Δ' hΔ' f hf
        exact ⟨g, hg.symm⟩
      · rintro _ ⟨g, rfl⟩
        change Δ'.mor₁ ≫ Δ'.mor₂ ≫ g = 0
        rw [← Category.assoc, comp_distTriang_mor_zero₁₂ _ hΔ', Limits.zero_comp]
    have hs1 : ((⊤ : Submodule ℤ (Δ'.obj₂ ⟶ T)).map φ₁).FG :=
      IsNoetherian.noetherian _
    have hs2 : ((⊤ : Submodule ℤ (Δ'.obj₂ ⟶ T)) ⊓ LinearMap.ker φ₁).FG := by
      rw [top_inf_eq, hker, LinearMap.range_eq_map]
      exact (Module.Finite.fg_top).map φ₂
    exact ⟨Submodule.fg_of_fg_map_of_fg_inf_ker φ₁ hs1 hs2⟩
  · let Δ' := (shiftFunctor (Triangle C) n).obj Δ
    have hΔ' : Δ' ∈ distTriang C := Triangle.shift_distinguished Δ hΔ n
    have h1 : Δ'.mor₁ ≫ f = 0 := hvan₁ n (by omega) _
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ Δ' hΔ' f h1
    have h3 : g = 0 := hvan₃ n (by omega) g
    change f = 0
    rw [hg, h3]
    exact Limits.comp_zero

instance finHom_isTriangulated (T : C) : (FinHom T).IsTriangulated where
  ext₂' Δ hΔ h₁ h₃ := (FinHom T).le_isoClosure _ (finHom_ext₂ T Δ hΔ h₁ h₃)

/-- The thick triangulated envelope of an object in `FinHom T` lies in `FinHom T`. -/
lemma triangEnvelope_singleton_le_finHom [IsTriangulated C] (T R : C) (hR : FinHom T R) :
    (ObjectProperty.singleton R).triangEnvelope ≤ FinHom T := by
  rw [ObjectProperty.triangEnvelope_le_iff]
  intro X hX
  obtain rfl : R = X := (ObjectProperty.singleton_iff _ _).1 hX
  exact hR

/-- A finitely generated `ℤ`-module has a nonzero integer killing all its torsion. -/
lemma exists_torsion_annihilator (M : Type*) [AddCommGroup M] [Module.Finite ℤ M] :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ x : M, (∃ k : ℤ, k ≠ 0 ∧ k • x = 0) → c • x = 0 := by
  have : Module.Finite ℤ (Submodule.torsion ℤ M) := Module.IsNoetherian.finite ℤ _
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (Submodule.torsion_isTorsion (R := ℤ) (M := M))
  refine ⟨c, nonZeroDivisors.ne_zero hc0, fun x ⟨k, hk, hkx⟩ => ?_⟩
  have hx : x ∈ Submodule.torsion ℤ M :=
    (Submodule.mem_torsion_iff x).2 ⟨⟨k, mem_nonZeroDivisors_of_ne_zero hk⟩, hkx⟩
  have := (Submodule.mem_annihilator.1 hc) ⟨x, hx⟩ Submodule.mem_top
  exact congrArg Subtype.val this

/-- **The ghost criterion.**  If every prime `p` gives a distinguished triangle
`R --p--> R → M → R⟦1⟧` whose third map is nonzero, then no object of
`FinHom (R⟦1⟧)` separates morphisms by its shifts. -/
theorem not_isGenerator_of_finHom (R : C)
    (htri : ∀ p : ℕ, p.Prime → ∃ (M : C) (g : R ⟶ M) (φ : M ⟶ R⟦(1 : ℤ)⟧),
      Triangle.mk ((p : ℤ) • 𝟙 R) g φ ∈ distTriang C ∧ φ ≠ 0)
    {G : C} (hG : FinHom (R⟦(1 : ℤ)⟧) G) : ¬ IsGenerator G := by
  obtain ⟨hfin, a, b, hvan⟩ := hG
  have hann : ∀ n : ℤ, ∃ c : ℤ, c ≠ 0 ∧ ∀ x : G⟦n⟧ ⟶ R⟦(1 : ℤ)⟧,
      (∃ k : ℤ, k ≠ 0 ∧ k • x = 0) → c • x = 0 := fun n => by
    have := hfin n
    exact exists_torsion_annihilator _
  choose c hc0 hc using hann
  let N : ℤ := ∏ n ∈ Finset.Icc a b, c n
  have hN : N ≠ 0 := Finset.prod_ne_zero_iff.2 (fun n _ => hc0 n)
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N.natAbs + 1)
  obtain ⟨M, g, φ, hΔ, hφ⟩ := htri p hp
  have hpφ : (p : ℤ) • φ = 0 := by
    have h0 := comp_distTriang_mor_zero₃₁ _ hΔ
    simpa only [Triangle.mk_mor₃, Triangle.mk_obj₁, Triangle.mk_mor₁,
      CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id, Preadditive.comp_zsmul,
      Category.comp_id] using h0
  have hcop : IsCoprime (p : ℤ) N := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
    have hnd : ¬ p ∣ N.natAbs := fun hd =>
      absurd (Nat.le_of_dvd (Int.natAbs_pos.2 hN) hd) (by omega)
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
  obtain ⟨s, t, hst⟩ := hcop
  refine not_isGenerator_of_isGhostFromShifts (f := φ) ⟨hφ, fun n x => ?_⟩
  set y := x ≫ φ with hy
  have hpy : (p : ℤ) • y = 0 := by
    rw [hy, ← Preadditive.comp_zsmul, hpφ, Limits.comp_zero]
  by_cases hn : n < a ∨ b < n
  · exact hvan n hn y
  · have hmem : n ∈ Finset.Icc a b := Finset.mem_Icc.2 (by omega)
    have hcy : c n • y = 0 :=
      hc n y ⟨p, by exact_mod_cast hp.ne_zero, hpy⟩
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem c hmem
    have hNy : N • y = 0 := by
      change (∏ n ∈ Finset.Icc a b, c n) • y = 0
      rw [hd, mul_comm, mul_smul, hcy, smul_zero]
    calc y = (1 : ℤ) • y := (one_smul ℤ y).symm
      _ = (s * p + t * N) • y := by rw [hst]
      _ = 0 := by rw [add_smul, mul_smul, mul_smul, hpy, hNy, smul_zero, smul_zero,
            add_zero]

end Generic

section IntModules

/-- Multiplication by an integer `k` on the regular `ℤ`-module. -/
def mulBy (k : ℤ) : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
  ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ k)

lemma mulBy_eq_zsmul (k : ℤ) : mulBy k = k • 𝟙 (ModuleCat.of ℤ ℤ) := by
  ext
  simp [mulBy]

lemma mulBy_injective {k : ℤ} (hk : k ≠ 0) : Function.Injective (mulBy k) := by
  intro x y h
  change k • x = k • y at h
  exact mul_left_cancel₀ hk (by simpa only [smul_eq_mul] using h)

/-- The short complex `ℤ --k--> ℤ → coker(k)`. -/
def mulByComplex (k : ℤ) : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk (mulBy k) (cokernel.π (mulBy k)) (cokernel.condition _)

lemma mulByComplex_shortExact {k : ℤ} (hk : k ≠ 0) : (mulByComplex k).ShortExact where
  exact := ShortComplex.exact_cokernel (mulBy k)
  mono_f := (ModuleCat.mono_iff_injective _).mpr (mulBy_injective hk)
  epi_g := by
    change Epi (cokernel.π (mulBy k))
    infer_instance

lemma mulBy_not_isSplitMono {p : ℕ} (hp : p.Prime) : ¬ IsSplitMono (mulBy (p : ℤ)) := by
  intro h
  obtain ⟨s⟩ := IsSplitMono.exists_splitMono (f := mulBy (p : ℤ))
  have heq := congrArg (fun k : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => k.hom (1 : ℤ)) s.id
  change s.retraction.hom ((p : ℤ) • (1 : ℤ)) = (1 : ℤ) at heq
  rw [map_smul, smul_eq_mul] at heq
  have h1 : (p : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg p) heq
  exact hp.one_lt.ne' (by exact_mod_cast h1)

end IntModules

section IntDerived

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

open DerivedCategory NeemanGeneratorM5.Counterexample

/-- `ℤ[0]`, the regular module in degree `0`, in a model `DerivedCategory (ModuleCat ℤ)`
(the standard one gives `ringObject ℤ`, the Spaltenstein one `smallRingObject ℤ H`). -/
abbrev intObj : DerivedCategory (ModuleCat.{0} ℤ) :=
  (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)

/-- For each prime `p`, the single triangle of `0 → ℤ --p--> ℤ → ℤ/p → 0` in
`D(ℤ)`; its connecting map is nonzero because the extension does not split. -/
lemma int_prime_triangle (p : ℕ) (hp : p.Prime) :
    ∃ (M : DerivedCategory (ModuleCat.{0} ℤ)) (g : intObj ⟶ M) (φ : M ⟶ intObj⟦(1 : ℤ)⟧),
      Triangle.mk ((p : ℤ) • 𝟙 intObj) g φ ∈ distTriang (DerivedCategory (ModuleCat.{0} ℤ)) ∧
        φ ≠ 0 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hS := mulByComplex_shortExact hp0
  refine ⟨_, (singleFunctor (ModuleCat.{0} ℤ) 0).map (mulByComplex (p : ℤ)).g, hS.singleδ,
    ?_, DerivedSingle.singleδ_ne_zero hS (mulBy_not_isSplitMono hp)⟩
  have hf : (singleFunctor (ModuleCat.{0} ℤ) 0).map (mulByComplex (p : ℤ)).f =
      (p : ℤ) • 𝟙 intObj := by
    change (singleFunctor (ModuleCat.{0} ℤ) 0).map (mulBy (p : ℤ)) = _
    rw [mulBy_eq_zsmul, CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]
  have h := hS.singleTriangle_distinguished
  rw [show hS.singleTriangle = Triangle.mk
      ((singleFunctor (ModuleCat.{0} ℤ) 0).map (mulByComplex (p : ℤ)).f)
      ((singleFunctor (ModuleCat.{0} ℤ) 0).map (mulByComplex (p : ℤ)).g) hS.singleδ from rfl,
    hf] at h
  exact h

/-- `Hom(ℤ[0]⟦n⟧, ℤ[0]⟦1⟧) = 0` for `n ≠ 1` (projectivity of `ℤ`). -/
lemma intObj_hom_shift_eq_zero {n : ℤ} (hn : n ≠ 1)
    (f : (intObj : DerivedCategory (ModuleCat.{0} ℤ))⟦n⟧ ⟶ intObj⟦(1 : ℤ)⟧) : f = 0 := by
  let eP := ((singleFunctors (ModuleCat.{0} ℤ)).shiftIso n (-n) 0 (by omega)).app
    (ModuleCat.of ℤ ℤ)
  let e1 := ((singleFunctors (ModuleCat.{0} ℤ)).shiftIso 1 (-1) 0 (by omega)).app
    (ModuleCat.of ℤ ℤ)
  have h : eP.inv ≫ f ≫ e1.hom = 0 :=
    DerivedSingle.hom_eq_zero_of_projective_of_ne (P := ModuleCat.of ℤ ℤ)
      (X := ModuleCat.of ℤ ℤ) (a := -n) (b := -1) (by omega) _
  rw [← cancel_epi eP.inv, ← cancel_mono e1.hom]
  simpa only [Category.assoc, Limits.zero_comp, Limits.comp_zero] using h

/-- Every endomorphism of `ℤ[0]⟦1⟧` is an integer multiple of the identity. -/
lemma intObj_shift_endo
    (f : (intObj : DerivedCategory (ModuleCat.{0} ℤ))⟦(1 : ℤ)⟧ ⟶ intObj⟦(1 : ℤ)⟧) :
    ∃ k : ℤ, f = k • 𝟙 _ := by
  obtain ⟨f', rfl⟩ := (shiftFunctor (DerivedCategory (ModuleCat.{0} ℤ)) (1 : ℤ)).map_surjective f
  obtain ⟨g, rfl⟩ := (singleFunctor (ModuleCat.{0} ℤ) 0).map_surjective f'
  have hg : g = g.hom (1 : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ) := by
    ext
    simp
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, g = k • 𝟙 (ModuleCat.of ℤ ℤ) := ⟨_, hg⟩
  refine ⟨k, ?_⟩
  rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]

/-- `ℤ[0]` lies in `FinHom (ℤ[0]⟦1⟧)`. -/
lemma intObj_finHom : FinHom ((intObj : DerivedCategory (ModuleCat.{0} ℤ))⟦(1 : ℤ)⟧) intObj := by
  refine ⟨fun n => ?_, 1, 1, fun n hn f => intObj_hom_shift_eq_zero (by omega) f⟩
  by_cases hn : n = 1
  · subst hn
    refine Module.Finite.of_surjective (LinearMap.toSpanSingleton ℤ _ (𝟙 _)) (fun f => ?_)
    obtain ⟨k, rfl⟩ := intObj_shift_endo f
    exact ⟨k, by simp [LinearMap.toSpanSingleton_apply]⟩
  · exact Module.Finite.of_surjective (0 : ℤ →ₗ[ℤ] _)
      (fun f => ⟨0, (intObj_hom_shift_eq_zero hn f).symm⟩)

/-- **F2, model-independent form.**  In any model of `D(ℤ)`, no object of the thick
triangulated envelope of `ℤ[0]` (i.e. no perfect complex) satisfies `IsGenerator`. -/
theorem not_isGenerator_of_mem_triangEnvelope_int {G : DerivedCategory (ModuleCat.{0} ℤ)}
    (hG : (ObjectProperty.singleton intObj).triangEnvelope G) : ¬ IsGenerator G :=
  not_isGenerator_of_finHom intObj int_prime_triangle
    (triangEnvelope_singleton_le_finHom _ intObj intObj_finHom G hG)

end IntDerived

section IntModel

attribute [local instance] HasDerivedCategory.standard

/-- **F2 (large model).**  No compact object of `D(ℤ) = AffineD ℤ` satisfies the
repository's `IsGenerator` (shifts separating morphisms).  Compact objects are
perfect (`Stacks07LT.M4.perf_of_compact_unconditional`), perfect objects lie in
`FinHom (ℤ[0]⟦1⟧)`, and `not_isGenerator_of_finHom` produces a nonzero ghost
`ℤ/p → ℤ[1]` for a prime `p` prime to the torsion of the relevant Hom groups. -/
theorem not_isGenerator_of_isCompactAb_int (G : AffineD ℤ) (hG : IsCompactAb G) :
    ¬ IsGenerator G :=
  not_isGenerator_of_mem_triangEnvelope_int (Stacks07LT.M4.perf_of_compact_unconditional ℤ hG)

/-- **F2, corollary.**  `WeakApproximationData (AffineD ℤ)` is empty: its field
`G_generates : IsGenerator G` is incompatible with `G_compact`. -/
theorem isEmpty_weakApproximationData_int : IsEmpty (WeakApproximationData (AffineD ℤ)) :=
  ⟨fun W => not_isGenerator_of_isCompactAb_int W.G W.G_compact W.G_generates⟩

/-- **F2, corollary.**  `SatisfiesWA (AffineD ℤ)` is false, although `D(ℤ)` is weakly
approximable in the sense of LP26 (with zero-detecting generators): the
repository's Definition 2.1 rendering is false at `ℤ`. -/
theorem not_satisfiesWA_int : ¬ SatisfiesWA (AffineD ℤ) :=
  fun ⟨W⟩ => isEmpty_weakApproximationData_int.false W

section Setup

variable (DZ : Type uZ) (DU : Type uU)
  [Category.{1} DZ] [Category.{1} DU]
  [Preadditive DZ] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DZ n).Additive]
  [∀ n : ℤ, (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DU]

/-- **F2, corollary.**  `SetupMainMinimal DZ (AffineD ℤ) DU` is empty, whatever the
end categories: its fields `G'_compact` and `G'_generates` contradict
`not_isGenerator_of_isCompactAb_int`.  Hence the pinned
`RelativeWeakApprox.SetupMainMinimal.theorem_1_1` (and every affine endpoint built
on it, e.g. the pinned `RelativeFM.affine_theorem_1_1_unconditional` and
`RelativeFM.StacksGluing.affine_theorem_1_1_stacks07LT`) is vacuous when the middle
category is `AffineD ℤ`. -/
theorem isEmpty_setupMainMinimal_int : IsEmpty (SetupMainMinimal DZ (AffineD ℤ) DU) :=
  ⟨fun S => not_isGenerator_of_isCompactAb_int S.G' S.G'_compact S.G'_generates⟩

end Setup

end IntModel

end

end RelativeFM.VacuityF2

#print axioms RelativeFM.VacuityF2.finHom_isTriangulated
#print axioms RelativeFM.VacuityF2.triangEnvelope_singleton_le_finHom
#print axioms RelativeFM.VacuityF2.not_isGenerator_of_finHom
#print axioms RelativeFM.VacuityF2.int_prime_triangle
#print axioms RelativeFM.VacuityF2.intObj_finHom
#print axioms RelativeFM.VacuityF2.not_isGenerator_of_mem_triangEnvelope_int
#print axioms RelativeFM.VacuityF2.not_isGenerator_of_isCompactAb_int
#print axioms RelativeFM.VacuityF2.isEmpty_weakApproximationData_int
#print axioms RelativeFM.VacuityF2.not_satisfiesWA_int
#print axioms RelativeFM.VacuityF2.isEmpty_setupMainMinimal_int
