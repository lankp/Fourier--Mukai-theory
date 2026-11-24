/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.Lemma4323
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Tactic

/-!
# Extensionality of `t`-structures, and the canonical form of Lemma 4.3(3)

A `t`-structure is determined by its degree-zero aisle: the shifted aisles come
from the shift axiom and the co-aisles are the right orthogonals of the
preceding aisles.  Two consequences are recorded here.

* `TStructure.ext_le_zero` is the extensionality principle itself.
* `lemma_4_3_3_tStructure` strengthens Lemma 4.3(3) of Lank--Pauwels from an
  equality of degree-zero aisles to a description of *every* aisle and co-aisle
  of `tD`, and `lemma_4_3_3_tStructure_eq` states that the compactly generated
  `t`-structure is literally the glued one.

Found by a member of the Ultramath run `smwur4wqg` (direction D6).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

section TStructureExtensionality

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The degree-zero aisle determines every shifted aisle.  This is the
shift-invariance step in the extensionality principle for `t`-structures. -/
theorem TStructure.le_eq_of_le_zero {t₁ t₂ : TStructure C}
    (h : t₁.le 0 = t₂.le 0) : t₁.le = t₂.le := by
  funext n
  ext X
  rw [le_iff_shift_zero t₁ n X, le_iff_shift_zero t₂ n X, h]

/-- The co-aisle in degree `n` is the right orthogonal of the aisle in degree
`n - 1`.  This is the object-property form of
`TStructure.isGE_iff_orthogonal`. -/
theorem TStructure.ge_iff_rightOrthogonal_le_pred (t : TStructure C)
    (n : ℤ) (X : C) :
    t.ge n X ↔ (t.le (n - 1)).rightOrthogonal X := by
  rw [t.ge_iff_isGE, t.isGE_iff_orthogonal (n - 1) n (by omega)]
  simp only [ObjectProperty.rightOrthogonal_iff, t.le_iff_isLE]

/-- Equal aisle functions determine equal co-aisle functions, by the
orthogonality characterization of the co-aisles of a `t`-structure. -/
theorem TStructure.ge_eq_of_le {t₁ t₂ : TStructure C}
    (h : t₁.le = t₂.le) : t₁.ge = t₂.ge := by
  funext n
  ext X
  rw [TStructure.ge_iff_rightOrthogonal_le_pred,
    TStructure.ge_iff_rightOrthogonal_le_pred, h]

/-- The degree-zero aisle determines every shifted co-aisle. -/
theorem TStructure.ge_eq_of_le_zero {t₁ t₂ : TStructure C}
    (h : t₁.le 0 = t₂.le 0) : t₁.ge = t₂.ge :=
  TStructure.ge_eq_of_le (TStructure.le_eq_of_le_zero h)

/-- **Extensionality of `t`-structures.**  Two `t`-structures with the same
degree-zero aisle are equal.  No separate hypothesis on co-aisles is needed:
orthogonality and the truncation axioms determine them. -/
theorem TStructure.ext_le_zero {t₁ t₂ : TStructure C}
    (h : t₁.le 0 = t₂.le 0) : t₁ = t₂ := by
  have hle := TStructure.le_eq_of_le_zero h
  have hge := TStructure.ge_eq_of_le_zero h
  cases t₁
  cases t₂
  simp_all

end TStructureExtensionality

section GluedTStructure

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

/-- The degree-`n` co-aisle associated with the glued aisles: maps into an
object vanish from every object of the glued aisle in degree `n - 1`.

Mathlib's orientation is important here: a co-aisle is a **right** orthogonal
of the preceding aisle, not a left orthogonal of the following aisle. -/
def gluedGe (iStar : D ⥤ DZ) (jStar : D ⥤ DU)
    (tZ : TStructure DZ) (tU : TStructure DU) (n : ℤ) : ObjectProperty D :=
  (gluedLe iStar jStar tZ tU (n - 1)).rightOrthogonal

omit [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [CategoryTheory.IsTriangulated DZ]
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated DU] in
/-- Membership in `gluedGe` is the expected orthogonality condition. -/
lemma gluedGe_iff (iStar : D ⥤ DZ) (jStar : D ⥤ DU)
    (tZ : TStructure DZ) (tU : TStructure DU) (n : ℤ) (X : D) :
    gluedGe iStar jStar tZ tU n X ↔
      ∀ ⦃Y : D⦄ (f : Y ⟶ X), gluedLe iStar jStar tZ tU (n - 1) Y → f = 0 :=
  Iff.rfl

omit [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU] in
/-- A `t`-structure whose degree-zero aisle is glued has the glued co-aisles
in every degree.  This supplies the `ge` counterpart of Lemma 4.2. -/
theorem ge_eq_gluedGe (iStar : D ⥤ DZ) (jStar : D ⥤ DU)
    [iStar.CommShift ℤ] [jStar.CommShift ℤ]
    (tD : TStructure D) (tZ : TStructure DZ) (tU : TStructure DU)
    (hzero : tD.le 0 = gluedLe iStar jStar tZ tU 0) :
    tD.ge = gluedGe iStar jStar tZ tU := by
  have hle : tD.le = gluedLe iStar jStar tZ tU :=
    funext (lemma_4_2 iStar jStar tD tZ tU hzero)
  funext n
  ext X
  rw [TStructure.ge_iff_rightOrthogonal_le_pred]
  rw [hle]
  rfl

variable (R : Recollement DZ D DU)

/-- **Lemma 4.3(3), canonical `t`-structure form.**  Under exactly the four
compact-generation hypotheses of `lemma_4_3_3`, every aisle of `tD` is the
corresponding glued aisle and every co-aisle is the right orthogonal of the
preceding glued aisle.  Thus all of `tD`, not merely `tD.le 0`, is determined
by the gluing data. -/
theorem lemma_4_3_3_tStructure (tD : TStructure D) (tZ : TStructure DZ)
    (tU : TStructure DU) (G' : D) (GU : DU) (m : ℤ)
    (hjG' : tU.le m (R.jStar.obj G'))
    (hgenD : tD.le 0 = Coprod (shiftTail (G'⟦m⟧ ⊞ R.jShriek.obj GU) 0))
    (hgenZ : tZ.le 0 = Coprod
      (shiftTail (R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)) 0))
    (hgenU : tU.le 0 = Coprod (shiftTail GU 0)) :
    tD.le = gluedLe R.iStar R.jStar tZ tU ∧
      tD.ge = gluedGe R.iStar R.jStar tZ tU := by
  have hzero := lemma_4_3_3 R tD tZ tU G' GU m hjG' hgenD hgenZ hgenU
  exact ⟨funext (lemma_4_2 R.iStar R.jStar tD tZ tU hzero),
    ge_eq_gluedGe R.iStar R.jStar tD tZ tU hzero⟩

/-- **Lemma 4.3(3), uniqueness of the glued `t`-structure.**  If `tGlued` has
the degree-zero glued aisle, then the compactly generated `t`-structure `tD`
from Lemma 4.3(3) is literally equal to `tGlued`. -/
theorem lemma_4_3_3_tStructure_eq (tD tGlued : TStructure D)
    (tZ : TStructure DZ) (tU : TStructure DU) (G' : D) (GU : DU) (m : ℤ)
    (hglued : tGlued.le 0 = gluedLe R.iStar R.jStar tZ tU 0)
    (hjG' : tU.le m (R.jStar.obj G'))
    (hgenD : tD.le 0 = Coprod (shiftTail (G'⟦m⟧ ⊞ R.jShriek.obj GU) 0))
    (hgenZ : tZ.le 0 = Coprod
      (shiftTail (R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)) 0))
    (hgenU : tU.le 0 = Coprod (shiftTail GU 0)) :
    tD = tGlued := by
  apply TStructure.ext_le_zero
  exact (lemma_4_3_3 R tD tZ tU G' GU m hjG' hgenD hgenZ hgenU).trans hglued.symm

end GluedTStructure

end RelativeWeakApprox
