/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.WeakApprox

/-!
# A standard-t form of open/closed gluing

This module refines `FourierMukai.Scheme.WeakApprox` in two ways.

* `satisfiesStandardWA_of_setup44` remembers the middle t-structure produced by
  LP's reverse gluing theorem, rather than discarding it in `SatisfiesWA`.
* `exists_standardData_of_compactHomZeroAtTop` produces weak approximation data
  on the middle category with the prescribed t-structure and normalized
  generator. This is the form needed when the result of one gluing step is used
  as an endpoint of the next.

The perfect-Ext variant (`PerfectHomZeroAtTop` and its three consumers) was
deleted in wave 6 together with the contentless `CompactsArePerfect`
(`results/OPEN_INPUTS.md` row 2.11, F4).

No `D_qc` construction is asserted here. In a qcqs scheme instantiation, the
remaining geometric inputs are the supported derived categories and their
coproducts, the open/closed recollement, the glued standard t-structures and
compact-generation identities, supported compact/perfect identifications, and
perfect Ext boundedness (Stacks 09MB together with 0BCJ). The compact/perfect
identification is Neeman 3.2(i); the generator and preferred-t inputs are the
geometric content of 3.2(ii)--(iii). This file does not prove preferredness of
an abstract `SetupMainMinimal.tD`.

For an induction on a finite affine open cover, one must also supply supported
excision: if `Z` is closed in `X` and contained in an open `U`, restriction
identifies `D_qc,Z(X)` with `D_qc,Z(U)`. LP Corollary 1.2 is not a substitute
for this scheme argument: its proof cites Neeman 3.2(iv) for schemes and uses
gluing only for the passage to algebraic spaces.
-/

@[expose] public section

namespace RelativeWeakApprox.SchemeGluingM2

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u uZ uD uU

section Setup44

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

/-- LP reverse gluing gives weak approximation relative to the middle
`t`-structure, not merely bare weak approximability. -/
theorem satisfiesStandardWA_of_setup44 (S : Setup44 DZ D DU)
    [HasCoproducts.{v} DZ] [HasCoproducts.{v} D] [HasCoproducts.{v} DU] :
    SatisfiesStandardWA D S.tD := by
  obtain ⟨W, ht, _, _⟩ := theorem_1_1_of_setup S
  exact ⟨W, ht⟩

end Setup44

section SchemeStep

variable {DZ : Type uZ} {DX : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} DX] [Category.{v} DU]
  [Preadditive DZ] [Preadditive DX] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DX] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DX ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor DX n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DX] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DX]
  [CategoryTheory.IsTriangulated DU]

/-- Reverse gluing from `SetupMainMinimal`, retaining both the middle
`t`-structure and the normalized generator. This version needs neither the
scheme geometry nor a compact/perfect comparison. -/
theorem exists_standardData_setupMainMinimal (S : SetupMainMinimal DZ DX DU)
    [HasCoproducts.{v} DZ] [HasCoproducts.{v} DX] [HasCoproducts.{v} DU]
    (hvan : CompactHomZeroAtTop DX) :
    ∃ W : WeakApproximationData DX,
      W.t = S.tD ∧ W.G = (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) := by
  let T : Setup44 DZ DX DU := S.toSetup44OfCompactHomZeroAtTop hvan
  obtain ⟨W, ht, hG, _⟩ := theorem_1_1_of_setup T
  refine ⟨W, ?_, ?_⟩
  · change W.t = T.tD
    exact ht
  · change W.G = T.G
    exact hG

/-- Bare standard weak approximability from the minimal setup. -/
theorem satisfiesStandardWA_setupMainMinimal (S : SetupMainMinimal DZ DX DU)
    [HasCoproducts.{v} DZ] [HasCoproducts.{v} DX] [HasCoproducts.{v} DU]
    (hvan : CompactHomZeroAtTop DX) : SatisfiesStandardWA DX S.tD := by
  obtain ⟨W, ht, _⟩ := exists_standardData_setupMainMinimal S hvan
  exact ⟨W, ht⟩

/-- The full output of one 09SR-free gluing step. In particular, the data use
`I.setup.tD` and their generator is the normalized LP generator.  (Before wave 6
the conclusion also had a conjunct `I.perfectX.Perf W.G`, read off the deleted
contentless field `CompactsArePerfect`; `results/OPEN_INPUTS.md` row 2.11.) -/
theorem exists_standardData_of_compactHomZeroAtTop
    (I : SchemeOpenClosedDerived DZ DX DU)
    [HasCoproducts.{v} DZ] [HasCoproducts.{v} DX] [HasCoproducts.{v} DU]
    (hvan : CompactHomZeroAtTop DX) :
    ∃ W : WeakApproximationData DX,
      W.t = I.setup.tD ∧
      W.G = (I.setup.G'⟦I.setup.m⟧ ⊞ I.setup.R.jShriek.obj I.setup.GU) :=
  exists_standardData_setupMainMinimal I.setup hvan

end SchemeStep

end RelativeWeakApprox.SchemeGluingM2

#print axioms RelativeWeakApprox.SchemeGluingM2.satisfiesStandardWA_of_setup44
#print axioms RelativeWeakApprox.SchemeGluingM2.exists_standardData_setupMainMinimal
#print axioms RelativeWeakApprox.SchemeGluingM2.satisfiesStandardWA_setupMainMinimal
#print axioms RelativeWeakApprox.SchemeGluingM2.exists_standardData_of_compactHomZeroAtTop
