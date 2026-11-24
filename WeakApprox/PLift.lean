/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox.Basic

/-!
# Definition 4.5: lifts through an object property

Found by a member of the Ultramath run `smwunmkmj` (direction D2).

This file formalizes Definition 4.5 of Lank--Pauwels, *Gluing weak
approximability along recollements*, and its elementary isomorphism API.

The functor written `iStar` below is arbitrary.  Instantiating it by the
`iStar` field of `RelativeWeakApprox.Recollement` gives the definition in the
paper; no property of the functor is needed for this definition or its API.
The commuting triangle is rendered by the equation
`iStar.map q = θ.hom ≫ f'`, where `θ : iStar.obj E ≅ E'`.

Besides transport along isomorphisms of `E'`, of `Y`, and along equality of
the morphism `f'`, we include transport of the source `E` along an
isomorphism.  Thus a source is not asserted to be unique: it can be replaced
by any isomorphic object belonging to `P`.  The version `isoSource` assumes
that `P` is closed under isomorphisms; `transportSource` instead takes the
membership of the new source as an explicit argument.
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory

universe vZ uZ vD uD

variable {DZ : Type uZ} {D : Type uD}
  [Category.{vZ} DZ] [Category.{vD} D]

/-- **Definition 4.5.** A `P`-lift of `f' : E' ⟶ iStar.obj Y` consists of an
object `source` in `P`, a morphism `q : source ⟶ Y`, and an isomorphism
`θ : iStar.obj source ≅ E'` such that `iStar.map q = θ.hom ≫ f'`. -/
structure PLift (iStar : D ⥤ DZ) (P : ObjectProperty D)
    {E' : DZ} {Y : D} (f' : E' ⟶ iStar.obj Y) where
  /-- The source of the lift. -/
  source : D
  /-- The lifted morphism. -/
  q : source ⟶ Y
  /-- The identification of `iStar` applied to the source with `E'`. -/
  θ : iStar.obj source ≅ E'
  /-- The source belongs to the prescribed object property. -/
  source_mem : P source
  /-- The lifting triangle commutes. -/
  comm : iStar.map q = θ.hom ≫ f'

namespace PLift

variable {iStar : D ⥤ DZ} {P : ObjectProperty D}
  {E' : DZ} {Y : D} {f' : E' ⟶ iStar.obj Y}

/-- The commuting condition with the isomorphism on the other side. -/
lemma comm' (ℓ : PLift iStar P f') :
    ℓ.θ.inv ≫ iStar.map ℓ.q = f' := by
  simp only [ℓ.comm, Iso.inv_hom_id_assoc]

/-- Transport a lift along equality of the morphism being lifted. -/
def transportHom {g' : E' ⟶ iStar.obj Y} (ℓ : PLift iStar P f')
    (h : f' = g') : PLift iStar P g' where
  source := ℓ.source
  q := ℓ.q
  θ := ℓ.θ
  source_mem := ℓ.source_mem
  comm := by
    rw [← h]
    exact ℓ.comm

/-- Transport a lift along an isomorphism `e : E' ≅ E''`.  The new morphism
is `e.inv ≫ f'`. -/
def transportDomain {E'' : DZ} (ℓ : PLift iStar P f') (e : E' ≅ E'') :
    PLift iStar P (e.inv ≫ f') where
  source := ℓ.source
  q := ℓ.q
  θ := ℓ.θ ≪≫ e
  source_mem := ℓ.source_mem
  comm := by
    dsimp
    rw [ℓ.comm]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Transport a lift along an isomorphism `e : Y ≅ Z`.  The new morphism is
`f' ≫ iStar.map e.hom`, and the lifted morphism is `ℓ.q ≫ e.hom`. -/
def transportTarget {Z : D} (ℓ : PLift iStar P f') (e : Y ≅ Z) :
    PLift iStar P (f' ≫ iStar.map e.hom) where
  source := ℓ.source
  q := ℓ.q ≫ e.hom
  θ := ℓ.θ
  source_mem := ℓ.source_mem
  comm := by
    rw [iStar.map_comp, ℓ.comm, Category.assoc]

/-- Replace the source by an isomorphic object `F`, with membership of `F` in
`P` supplied explicitly.  If `e : ℓ.source ≅ F`, the new lifted morphism is
`e.inv ≫ ℓ.q`. -/
def transportSource {F : D} (ℓ : PLift iStar P f')
    (e : ℓ.source ≅ F) (hF : P F) : PLift iStar P f' where
  source := F
  q := e.inv ≫ ℓ.q
  θ := (iStar.mapIso e).symm ≪≫ ℓ.θ
  source_mem := hF
  comm := by
    dsimp
    simp only [iStar.map_comp, ℓ.comm, Category.assoc]

/-- Replace the source by an isomorphic object, using closure of `P` under
isomorphisms.  This is the precise sense in which the source of a lift is
only determined up to isomorphism. -/
def isoSource [P.IsClosedUnderIsomorphisms] {F : D} (ℓ : PLift iStar P f')
    (e : ℓ.source ≅ F) : PLift iStar P f' :=
  ℓ.transportSource e (P.prop_of_iso e ℓ.source_mem)

end PLift
end RelativeWeakApprox
