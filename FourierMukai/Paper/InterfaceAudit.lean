/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Paper.DerivedSetup

/-!
# The abstract `FMContext` interface is too weak for Lemma 2.25

`FourierMukai/Paper/Statements.lean` formerly stated GL26's Lemma 2.25 as the
*bare* rendering `Nonempty (C.transform C.diagonalKernel ≅ 𝟭 D)` for an arbitrary
`FMContext C`.  In `FourierMukai.Paper.DerivedSetup`, `transform` is *defined*
as `push ∘ tensorRight K ∘ pull`, and the three functors `pull`, `push`,
`tensorRight` are free structure fields.  Nothing forces them to come from a
geometric morphism, so that rendering is **not a consequence of the interface**:
this file proves it by exhibiting a legal `FMContext` for which it is false.
The current `RelativeFM.lemma_2_25` is not that statement -- it also takes
`DiagonalIdentityData` and the kernel/functor comparison equalities, which is
where the paper's proof inputs live -- and it is proved.

The countermodel lives on `Type 0` with every subcategory predicate `True` and
`push` constant at `PUnit`.  Then `transform diagonalKernel` is constant at
`PUnit`, which cannot be isomorphic to `𝟭 (Type 0)`.

What this means for the formalization: Lemma 2.25 is true for the Fourier--Mukai
contexts that actually arise (`transform` really is `Rp_{2*}(K ⊗^L Lp_1^*)` with
the projection formula, the tensor unit, and `f'_1 ∘ Δ = f'_2 ∘ Δ = 𝟙`), but
those facts must be **data** of the interface — they cannot be derived from a
free choice of `pull`, `push`, `tensorRight`.  The scheme-level statement layer
must therefore carry the projection formula and the two diagonal identities as
fields, exactly as GL26's proof of Lemma 2.25 uses them (Stacks tag 08IN plus
pseudofunctoriality of the six functors).  It now does: the data are
`RelativeFM.DiagonalIdentityData` (`FourierMukai/Scheme/DiagonalIdentity.lean`),
and the lemma is proved from them in `FourierMukai/Scheme/Statements.lean`
(`lemma_2_25Statement_proved`) and in `FourierMukai/Paper/Statements.lean`
(`lemma_2_25`).  This file's countermodel is what shows that the *bare* rendering
is not the lemma.

Found by a member of the Ultramath run `smwuyellz` (direction D4).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory

universe u v

/-- Placeholder subcategories used only for the interface countermodel. -/
def allTypeSubcats : Subcats (Type 0) where
  DbQc := fun _ => True
  Dcoh := fun _ => True
  Perf := fun _ => True
  IsPseudocoherent := fun _ => True

/-- A legal `FMContext` whose putative identity transform is constant at `PUnit`.
This is a countermodel, not a model of derived categories of schemes. -/
def constantContext : FMContext (Type 0) (Type 0) (Type 0) where
  tensorRight _ := 𝟭 _
  pull := 𝟭 _
  push := (Functor.const (Type 0)).obj PUnit
  pull' := 𝟭 _
  push' := (Functor.const (Type 0)).obj PUnit
  diagonalKernel := PUnit
  S1 := allTypeSubcats
  S2 := allTypeSubcats
  SP := allTypeSubcats

/-- The abstract `FMContext` interface alone does not imply Lemma 2.25:
the projection formula and the diagonal identities are additional geometric
input. -/
theorem lemma_2_25_needs_geometric_input
    (h : Nonempty (constantContext.transform constantContext.diagonalKernel ≅
      𝟭 (Type 0))) : False := by
  obtain ⟨e⟩ := h
  exact PEmpty.elim ((e.app PEmpty).hom PUnit.unit)

end RelativeFM

#print axioms RelativeFM.lemma_2_25_needs_geometric_input
