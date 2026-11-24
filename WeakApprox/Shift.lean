/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Basic

/-!
# Lemma 3.1(2): shifting and enlarging `⟨H⟩^[a,b]`

Lemma 3.1(2) of

  P. Lank, B. Pauwels, *Gluing weak approximability along recollements*:
`⟨H⟩^[a,b]⟦s⟧ = ⟨H⟩^[a-s,b-s]`, and `⟨H⟩^[a,b] ⊆ ⟨H⟩^[a',b']` when `a' ≤ a`,
`b ≤ b'`.

`shiftImage P s` is the paper's `P⟦s⟧` (the isomorphism-closed image of `P` under
the shift), as opposed to Mathlib's preimage operation `ObjectProperty.shift`.

Found by a member of the Ultramath run `smwufzlp4` (direction D2); the proof was
ported to the `Coprod`/`envelope` definitions of `WeakApprox/Basic.lean`.
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The isomorphism-closed image of an object property under the shift by `s`,
i.e. the paper's notation `P⟦s⟧`. -/
def shiftImage (P : ObjectProperty C) (s : ℤ) : ObjectProperty C := fun X =>
  ∃ Y : C, P Y ∧ Nonempty (X ≅ Y⟦s⟧)

instance (P : ObjectProperty C) (s : ℤ) : (shiftImage P s).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨Y, hY, ⟨e'⟩⟩
    exact ⟨Y, hY, ⟨e.symm.trans e'⟩⟩

lemma shiftImage_shiftInterval (H : C) (a b s : ℤ) :
    shiftImage (shiftInterval H a b) s = shiftInterval H (a - s) (b - s) := by
  ext X
  constructor
  · rintro ⟨Y, ⟨k, hak, hkb, ⟨eY⟩⟩, ⟨eX⟩⟩
    refine ⟨k - s, by omega, by omega, ⟨?_⟩⟩
    let e₁ : (H⟦-k⟧)⟦s⟧ ≅ H⟦-(k - s)⟧ :=
      (shiftFunctorAdd' C (-k) s (-(k - s)) (by omega)).symm.app H
    exact eX.trans (((shiftFunctor C s).mapIso eY).trans e₁)
  · rintro ⟨k, hak, hkb, ⟨eX⟩⟩
    refine ⟨H⟦-(k + s)⟧, ⟨k + s, by omega, by omega, ⟨Iso.refl _⟩⟩, ⟨?_⟩⟩
    exact eX.trans ((shiftFunctorAdd' C (-(k + s)) s (-k) (by omega)).app H)

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma shiftImage_shiftImage_neg_le (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (s : ℤ) : shiftImage (shiftImage P s) (-s) ≤ P := by
  rintro X ⟨Y, ⟨Z, hZ, ⟨eY⟩⟩, ⟨eX⟩⟩
  let e : X ≅ Z := eX.trans (((shiftFunctor C (-s)).mapIso eY).trans (shiftShiftNeg Z s))
  exact P.prop_of_iso e.symm hZ

instance (H : C) (a b : ℤ) : (envelope H a b).IsClosedUnderIsomorphisms := by
  unfold envelope
  infer_instance

/-- Monotonicity of the coproduct/extension closure. -/
lemma Coprod_mono {P Q : ObjectProperty C} (h : P ≤ Q) : Coprod P ≤ Coprod Q :=
  Coprod.le (P := P) (Q := Coprod Q) (fun X hX => Coprod.of_mem X (h X hX))

/-- Shifting a member of `Coprod P` gives a member of `Coprod (P⟦s⟧)`. -/
lemma map_shift_Coprod (P : ObjectProperty C) (s : ℤ) {X : C}
    (hX : Coprod P X) : Coprod (shiftImage P s) (X⟦s⟧) := by
  induction hX with
  | of_mem X hX => exact .of_mem _ ⟨X, hX, ⟨Iso.refl _⟩⟩
  | of_isoClosure e _ ih => exact .of_isoClosure ((shiftFunctor C s).mapIso e) ih
  | of_colimitPresentation pres _ ih =>
      exact .of_colimitPresentation (pres.map (shiftFunctor C s)) ih
  | of_extension T hT _ _ ih₁ ih₃ =>
      exact .of_extension _ (T.shift_distinguished hT s) ih₁ ih₃

/-- Shifting preserves the retract closure as well. -/
lemma map_shift_envelope (H : C) (a b s : ℤ) {X : C}
    (hX : envelope H a b X) : envelope H (a - s) (b - s) (X⟦s⟧) := by
  obtain ⟨Y, hY, ⟨r⟩⟩ := hX
  exact ⟨Y⟦s⟧, by
    have h := map_shift_Coprod (shiftInterval H a b) s hY
    rwa [shiftImage_shiftInterval] at h, ⟨r.map (shiftFunctor C s)⟩⟩

/-- **Lemma 3.1(2), shift formula.** -/
theorem lemma31_2_shift (H : C) (a b s : ℤ) :
    shiftImage (envelope H a b) s = envelope H (a - s) (b - s) := by
  ext X
  constructor
  · rintro ⟨Y, hY, ⟨e⟩⟩
    exact (envelope H (a - s) (b - s)).prop_of_iso e.symm (map_shift_envelope H a b s hY)
  · intro hX
    have h := map_shift_envelope H (a - s) (b - s) (-s) hX
    rw [show a - s - -s = a by omega, show b - s - -s = b by omega] at h
    exact ⟨X⟦-s⟧, h, ⟨(shiftNegShift X s).symm⟩⟩

/-- **Lemma 3.1(2), enlargement of the interval.** -/
theorem lemma31_2_mono (H : C) {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') :
    envelope H a b ≤ envelope H a' b' := by
  unfold envelope
  exact ObjectProperty.monotone_retractClosure
    (Coprod_mono (shiftInterval_mono H ha hb))

end RelativeWeakApprox
