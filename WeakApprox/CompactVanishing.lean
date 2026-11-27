/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.MainMinimal
import WeakApprox.Lemma433TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Tactic

/-!
# Boundedness cannot replace Stacks 09SR in Lemma 4.3

The paper's §4.3 proof of `lem:normalize` (Lemma 4.3) propagates positive
self-Hom vanishing from a compact generator to all compacts through the finite
thick envelope supplied by Stacks 09SR (§2.1.2).  The proposed alternative
was to replace this by two-sided boundedness for a `t`-structure.

## Exact verdict

The proposed statement

```
t.ge n X → t.le m Y → EventuallyHomZero X Y
```

is **false** for a general `t`-structure.  Orthogonality vanishes maps from
`t.le a` to `t.ge b` for `a < b`, not maps in the opposite direction.  In the
standard derived `t`-structure, two objects of the heart have both degree-zero
bounds, while `Hom(A, B⟦k⟧) = Extᵏ(A,B)` need not eventually vanish: for
example, over `k[ε]/(ε²)`, the residue field has nonzero self-Ext in every
nonnegative degree.  Thus compact boundedness does not imply the paper's
positive-shift condition, and no proof of that implication is claimed here.

What is true, and is proved below, is:

* `IsClassicalGeneratorOnCompacts G` plus `t.bounded G` implies
  `CompactsBounded t` (`compactsBounded_of_isClassicalGeneratorOnCompacts`).
* Boundedness gives Hom-vanishing at sufficiently **negative** shifts.  In
  particular, with the source/target order of the proposed theorem,
  `t.ge n X` and `t.le m Y` imply `EventuallyHomZeroNeg Y X`, not
  `EventuallyHomZero X Y` (`EventuallyHomZeroNeg.of_ge_le`).
* The exact replacement input for the paper's positive-shift applications is
  `CompactHomZeroAtTop`.  Stacks 09SR plus `EventuallyHomZero G G` implies it,
  and it suffices for the uses in Lemma 4.3(1), Lemma 4.3(4), and Setup 4.4(3).

Checked from the repository root with:

```
LEAN_PATH="$LEAN_PATH:." lean -o .ultramath/smwuug9t7/m4/Solution.olean \
  .ultramath/smwuug9t7/m4/Solution.lean
```

(exit status 0).
-/

/-!
# What the 09SR input is really used for: eventual vanishing between compacts

The §4 chain (`lemma_4_3_1`, `lemma_4_3_4`, Setup 4.4(3)) never uses thick
generation directly; it uses one consequence of it, namely that Homs between
compact objects vanish in large positive degrees.  This file isolates that
consequence:

* `CompactHomZeroAtTop C := ∀ X Y, IsCompactAb X → IsCompactAb Y → EventuallyHomZero X Y`;
* `compactHomZeroAtTop_of_isClassicalGeneratorOnCompacts`: Stacks 09SR together
  with self-vanishing of the generator implies it;
* `exists_nonneg_le_jShriek_GU_of_compactHomZeroAtTop`,
  `lemma_4_3_4_of_compactHomZeroAtTop` and
  `exists_setup_4_4_3_of_compactHomZeroAtTop`: Lemma 4.3(1), Lemma 4.3(4) and
  Setup 4.4(3) from `CompactHomZeroAtTop` alone — no thick envelope, no
  `IsClassicalGeneratorOnCompacts`.

So 09SR may be replaced by `CompactHomZeroAtTop`, which is precisely what the
paper's geometric `lem:compact_ext_vanishing` supplies for `D_qc`.

The negative side is recorded too: boundedness of compacts does *not* give
`CompactHomZeroAtTop`.  The orthogonality of a `t`-structure gives vanishing only
for negative shifts (`EventuallyHomZeroNeg`, and `eventuallyHomZeroNeg_of_compact`
under `CompactsBounded`), so the two directions are genuinely different; this is
why the shortcut `t.ge n X → t.le m Y → EventuallyHomZero X Y` is false (a heart
object of infinite projective dimension is a counterexample: it is bounded and
its self-`Ext` does not vanish).

Found by a member of the Ultramath run `smwuug9t7` (direction D4).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Antitonicity of the co-aisles, proved from right orthogonality. -/
theorem TStructure.ge_antitone_via_orthogonal (t : TStructure C) : Antitone t.ge := by
  intro a b hab X hX
  rw [TStructure.ge_iff_rightOrthogonal_le_pred] at hX ⊢
  intro Y f hY
  exact hX f (t.le_monotone (by omega) Y hY)

/-- The orthogonality consequence for bounded objects, with explicit morphism
and shift directions. -/
theorem hom_zero_of_le_of_ge_of_lt (t : TStructure C) {X Y : C} {m n k : ℤ}
    (hX : t.le m X) (hY : t.ge n Y) (hk : m < n - k) (f : X ⟶ Y⟦k⟧) : f = 0 := by
  have hY' : t.ge (n - k) (Y⟦k⟧) := t.ge_shift n k (n - k) (by omega) Y hY
  have hY'' : t.ge (m + 1) (Y⟦k⟧) :=
    TStructure.ge_antitone_via_orthogonal t (by omega) (Y⟦k⟧) hY'
  exact t.zero_of_isLE_of_isGE f m (m + 1) (by omega) ⟨hX⟩ ⟨hY''⟩

/-- Fixed aisles are closed under retracts, by the orthogonal description. -/
instance TStructure.le_isStableUnderRetracts (t : TStructure C) (n : ℤ) :
    (t.le n).IsStableUnderRetracts where
  of_retract {X Y} r hY := by
    apply (t.le_iff_isLE X n).2
    apply (t.isLE_iff_orthogonal n (n + 1) rfl X).2
    intro Z f hZ
    have h : r.r ≫ f = 0 := t.zero_of_isLE_of_isGE (r.r ≫ f) n (n + 1)
      (by omega) ((t.le_iff_isLE Y n).1 hY) hZ
    calc
      f = 𝟙 X ≫ f := (Category.id_comp f).symm
      _ = (r.i ≫ r.r) ≫ f := by rw [r.retract]
      _ = r.i ≫ (r.r ≫ f) := Category.assoc _ _ _
      _ = 0 := by rw [h, comp_zero]

/-- Fixed co-aisles are closed under retracts, by the orthogonal description. -/
instance TStructure.ge_isStableUnderRetracts (t : TStructure C) (n : ℤ) :
    (t.ge n).IsStableUnderRetracts where
  of_retract {X Y} r hY := by
    apply (t.ge_iff_isGE X n).2
    apply (t.isGE_iff_orthogonal (n - 1) n (by omega) X).2
    intro Z f hZ
    have h : f ≫ r.i = 0 := t.zero_of_isLE_of_isGE (f ≫ r.i) (n - 1) n
      (by omega) hZ ((t.ge_iff_isGE Y n).1 hY)
    calc
      f = f ≫ 𝟙 X := (Category.comp_id f).symm
      _ = f ≫ (r.i ≫ r.r) := by rw [r.retract]
      _ = (f ≫ r.i) ≫ r.r := (Category.assoc _ _ _).symm
      _ = 0 := by rw [h, zero_comp]

instance TStructure.minus_isStableUnderRetracts (t : TStructure C) :
    t.minus.IsStableUnderRetracts where
  of_retract r h := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, ⟨(t.le n).prop_of_retract r hn.le⟩⟩

instance TStructure.plus_isStableUnderRetracts (t : TStructure C) :
    t.plus.IsStableUnderRetracts where
  of_retract r h := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, ⟨(t.ge n).prop_of_retract r hn.ge⟩⟩

instance TStructure.bounded_isStableUnderRetracts (t : TStructure C) :
    t.bounded.IsStableUnderRetracts where
  of_retract r h := by
    exact ⟨t.plus.prop_of_retract r h.1, t.minus.prop_of_retract r h.2⟩

/-- The thick envelope of a bounded-above object stays bounded above. -/
theorem triangEnvelope_le_minus (t : TStructure C) {G : C} (hG : t.minus G) :
    (ObjectProperty.singleton G).triangEnvelope ≤ t.minus := by
  rw [ObjectProperty.triangEnvelope_le_iff]
  intro X hX
  obtain rfl : G = X := (ObjectProperty.singleton_iff _ _).1 hX
  exact hG

/-- The thick envelope of a bounded-below object stays bounded below. -/
theorem triangEnvelope_le_plus (t : TStructure C) {G : C} (hG : t.plus G) :
    (ObjectProperty.singleton G).triangEnvelope ≤ t.plus := by
  rw [ObjectProperty.triangEnvelope_le_iff]
  intro X hX
  obtain rfl : G = X := (ObjectProperty.singleton_iff _ _).1 hX
  exact hG

/-- The thick envelope of a two-sided bounded object stays two-sided bounded. -/
theorem triangEnvelope_le_bounded (t : TStructure C) {G : C} (hG : t.bounded G) :
    (ObjectProperty.singleton G).triangEnvelope ≤ t.bounded := by
  rw [ObjectProperty.triangEnvelope_le_iff]
  intro X hX
  obtain rfl : G = X := (ObjectProperty.singleton_iff _ _).1 hX
  exact hG

/-- Put an object with an explicit lower and upper bound in `t.bounded`. -/
theorem TStructure.bounded_of_ge_le (t : TStructure C) {X : C} {n m : ℤ}
    (hXge : t.ge n X) (hXle : t.le m X) : t.bounded X :=
  ⟨⟨n, (t.ge_iff_isGE X n).1 hXge⟩, ⟨m, (t.le_iff_isLE X m).1 hXle⟩⟩

/-- The proposed compact-boundedness replacement predicate. -/
def CompactsBounded (t : TStructure C) : Prop :=
  ∀ X : C, IsCompactAb X → t.bounded X

/-- Stacks 09SR and two-sided boundedness of `G` imply boundedness of every compact. -/
theorem compactsBounded_of_isClassicalGeneratorOnCompacts (t : TStructure C) {G : C}
    (hgen : IsClassicalGeneratorOnCompacts G) (hG : t.bounded G) : CompactsBounded t := by
  intro X hX
  exact triangEnvelope_le_bounded t hG X (hgen X hX)

/-- The same implication with the two bounds displayed separately. -/
theorem compactsBounded_of_ge_le (t : TStructure C) {G : C} {n m : ℤ}
    (hgen : IsClassicalGeneratorOnCompacts G) (hGge : t.ge n G) (hGle : t.le m G) :
    CompactsBounded t :=
  compactsBounded_of_isClassicalGeneratorOnCompacts t hgen
    (TStructure.bounded_of_ge_le t hGge hGle)

/-- Eventual vanishing at negative shifts, the direction supplied by t-structure
orthogonality. -/
def EventuallyHomZeroNeg (X Y : C) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n ≤ N → ∀ f : X ⟶ Y⟦n⟧, f = 0

/-- Correct boundedness/cutoff statement: aisle source, co-aisle target. -/
theorem EventuallyHomZeroNeg.of_le_ge (t : TStructure C) {X Y : C} {m n : ℤ}
    (hX : t.le m X) (hY : t.ge n Y) : EventuallyHomZeroNeg X Y := by
  refine ⟨n - m - 1, fun k hk f => ?_⟩
  exact hom_zero_of_le_of_ge_of_lt t hX hY (by omega) f

/-- With `X` bounded below and `Y` bounded above, orthogonality controls the
reverse morphisms `Y ⟶ X[k]`, again at negative shifts. -/
theorem EventuallyHomZeroNeg.of_ge_le (t : TStructure C) {X Y : C} {n m : ℤ}
    (hX : t.ge n X) (hY : t.le m Y) : EventuallyHomZeroNeg Y X :=
  EventuallyHomZeroNeg.of_le_ge t hY hX

/-- Existential bounds give eventual negative-shift vanishing. -/
theorem EventuallyHomZeroNeg.of_minus_plus (t : TStructure C) {X Y : C}
    (hX : t.minus X) (hY : t.plus Y) : EventuallyHomZeroNeg X Y := by
  obtain ⟨m, hm⟩ := hX
  obtain ⟨n, hn⟩ := hY
  exact EventuallyHomZeroNeg.of_le_ge t hm.le hn.ge

/-- Compact boundedness gives negative-shift, not positive-shift, vanishing. -/
theorem eventuallyHomZeroNeg_of_compact (t : TStructure C)
    (hb : CompactsBounded t) {X Y : C} (hX : IsCompactAb X) (hY : IsCompactAb Y) :
    EventuallyHomZeroNeg X Y :=
  EventuallyHomZeroNeg.of_minus_plus t (hb X hX).2 (hb Y hY).1

/-- The exact positive-vanishing input used in Lemma 4.3 and Setup 4.4. -/
def CompactHomZeroAtTop (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] : Prop :=
  ∀ X Y : C, IsCompactAb X → IsCompactAb Y → EventuallyHomZero X Y

/-- Stacks 09SR propagates self-vanishing of `G` to `CompactHomZeroAtTop`. -/
theorem compactHomZeroAtTop_of_isClassicalGeneratorOnCompacts {G : C}
    (hG : EventuallyHomZero G G) (hgen : IsClassicalGeneratorOnCompacts G) :
    CompactHomZeroAtTop C := by
  intro X Y hX hY
  exact eventuallyHomZero_of_compact hG hgen hX hY

section RecollementApplications

universe uZ uD uU

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} D] [Category.{v} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]

/-- Lemma 4.3(1) with only the precise positive compact-Hom input. -/
theorem exists_nonneg_le_jShriek_GU_of_compactHomZeroAtTop
    (R : Recollement DZ D DU) (tD : TStructure D) (G' : D) (GU : DU)
    (hG'0 : tD.le 0 G') (hG'gen : IsGenerator G')
    (hG'compact : IsCompactAb G') (hGUcompact : IsCompactAb GU)
    (hvan : CompactHomZeroAtTop D) :
    ∃ B : ℤ, 0 ≤ B ∧ tD.le B (R.jShriek.obj GU) := by
  apply exists_nonneg_le_of_eventuallyHomZero tD G' _ hG'gen hG'0
  exact hvan _ _ hG'compact (R.isCompactAb_jShriek_obj hGUcompact)

/-- Lemma 4.3(4) with only the precise positive compact-Hom input: neither
classical generation nor self-vanishing of `G'` is needed separately. -/
theorem lemma_4_3_4_of_compactHomZeroAtTop
    (R : Recollement DZ D DU) (G' : D) (GU : DU) (m : ℤ)
    [HasBinaryBiproduct (G'⟦m⟧) (R.jShriek.obj GU)]
    (hG'compact : IsCompactAb G') (hGUcompact : IsCompactAb GU)
    (hvan : CompactHomZeroAtTop D) :
    EventuallyHomZero (G'⟦m⟧ ⊞ R.jShriek.obj GU) (G'⟦m⟧ ⊞ R.jShriek.obj GU) := by
  letI : IsCompactAb (G'⟦m⟧ ⊞ R.jShriek.obj GU) :=
    isCompactAb_normalizedGenerator R G' GU m hG'compact hGUcompact
  exact hvan _ _ (by infer_instance) (by infer_instance)

/-- Setup 4.4(3) from the exact positive compact-Hom input. This is the
09SR-free statement; compact boundedness supplies only the negative-direction
analogue and cannot replace `hvan`. -/
theorem exists_setup_4_4_3_of_compactHomZeroAtTop
    (R : Recollement DZ D DU) (tD : TStructure D) (G' : D) (GU : DU) (m : ℤ)
    [HasBinaryBiproduct (G'⟦m⟧) (R.jShriek.obj GU)]
    (hG'compact : IsCompactAb G') (hGUcompact : IsCompactAb GU)
    (hvan : CompactHomZeroAtTop D)
    (haisle : tD.le 0 = Coprod (shiftTail (G'⟦m⟧ ⊞ R.jShriek.obj GU) 0)) :
    ∃ A : ℤ, 0 < A ∧
      EventuallyHomZero (G'⟦m⟧ ⊞ R.jShriek.obj GU) (G'⟦m⟧ ⊞ R.jShriek.obj GU) ∧
      (∀ {Y : D}, tD.le (-A) Y →
        ∀ f : (G'⟦m⟧ ⊞ R.jShriek.obj GU) ⟶ Y, f = 0) := by
  letI : IsCompactAb (G'⟦m⟧ ⊞ R.jShriek.obj GU) :=
    isCompactAb_normalizedGenerator R G' GU m hG'compact hGUcompact
  have hG : EventuallyHomZero (G'⟦m⟧ ⊞ R.jShriek.obj GU)
      (G'⟦m⟧ ⊞ R.jShriek.obj GU) :=
    lemma_4_3_4_of_compactHomZeroAtTop R G' GU m hG'compact hGUcompact hvan
  obtain ⟨N, hN⟩ := hG
  refine ⟨max N 1, lt_of_lt_of_le Int.zero_lt_one (le_max_right N 1), ⟨N, hN⟩, ?_⟩
  intro Y hY
  exact setup_4_4_3_vanishing_at tD _ (le_max_left N 1) haisle hN hY

end RecollementApplications

end RelativeWeakApprox