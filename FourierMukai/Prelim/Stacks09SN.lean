/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Prelim.Lemma25
import WeakApprox.GeneratorBridge
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Stacks 09SN: objects of a compactly generated category are homotopy colimits of cells

This file carries Stacks Project Tag 09SN (`lemma-write-as-colimit`) as a tagged input,
in the form of AxiomMath/Stacks, and derives from it the generation statement used in
**Lemma 2.4** (`lem:localizing_iff_cpt_gen`) and **Lemma 2.5**
(`lem:equivalence_or_fully_faithful_via_compacts`) of

  E. Guisado Villalgordo, P. Lank, *Relative Fourier--Mukai theory for algebraic spaces*.

## Inputs (see `results/ASSUMPTIONS.md`)

* `StacksInterface.IsHomotopyColimit` (Stacks 090Z) is a *definition*, verbatim from
  AxiomMath/Stacks `StacksFrontier/CategoryTheory/Triangulated/HomotopyColimit.lean`.
* `StacksInterface.Tag09SN D` (Stacks 09SN) is a `Prop`-valued statement, verbatim from
  AxiomMath/Stacks
  `CategoryTheory.Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated`
  (`StacksFrontier/CategoryTheory/Triangulated/CompactObjects/CellStructure.lean`), except
  that AxiomMath's `IsCompactObject.{v}` is replaced by the repository's
  `RelativeWeakApprox.IsCompactAb`.  It is assumed as a hypothesis wherever it is used,
  never as an axiom.

## What is proved

* `isZero_of_rightOrthogonal_ofObj_punit_iff`: for the one-member family
  `fun _ : PUnit => G`, AxiomMath's right-orthogonality hypothesis of 09SN is exactly
  `RelativeWeakApprox.IsPaperGenerator G` (zero detection by the shifts of `G`).
* `isLocalizingGenerator_of_tag09SN`: from `Tag09SN D`, a compact `G` with
  `IsPaperGenerator G` lies in no proper localizing subcategory:
  `IsLocalizingGenerator.{v} (singleton G)`.  A localizing `Q ∋ G` contains every
  `Type v`-indexed sum of shifts of `G`, hence the first cell `F 0`, every `F (n+1)`
  (third vertex of a triangle `Y → F n → F (n+1) →` with `Y` such a sum), the
  `ℕ`-indexed sum `∐ F` (reindexed to `ULift ℕ : Type v`), and finally `X` (third
  vertex of the 090Z triangle `∐ F → ∐ F → X →`).

## On the compactness notion

AxiomMath's `IsCompactObject.{w} K` (Stacks 07LS) asks that, for every family
`E : I → D` (`I : Type w`) with a coproduct, the map `⨁ i, (K ⟶ E i) → (K ⟶ ∐ E)`
induced by the coprojections be bijective.  `IsCompactAb K` asks that the
`AddCommGrpCat`-valued `Hom(K, -)` preserve `Type v`-indexed coproducts.  Since the
coproduct in `AddCommGrpCat` is the direct sum, the two notions agree at `w = v`; the
repository has the two directions of this comparison for cofans
(`RelativeWeakApprox.bijective_abCofanSum_of_isColimit`,
`RelativeWeakApprox.isColimitCofan_of_bijective_abCofanSum`, `WeakApprox/CompactAb.lean`),
but AxiomMath's `IsCompactObject` is not defined here and the equivalence of the two
predicates is **not** proved in this file.
-/

@[expose] public section

namespace RelativeFM

namespace StacksInterface

open CategoryTheory Limits Pretriangulated RelativeWeakApprox

universe v u

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- `ℕ`-indexed coproducts exist when `Type v`-indexed ones do (`ℕ` is `v`-small).  This
instance makes `∐ F.obj` (for `F : ℕ ⥤ D`) available under `HasCoproducts.{v} D`, as in
the AxiomMath statement of 09SN below. -/
instance (priority := 100) hasCoproductsOfShape_nat [HasCoproducts.{v} D] :
    HasCoproductsOfShape ℕ D :=
  hasCoproductsOfShape_of_small.{v} D ℕ

/-- **Stacks Tag 090Z** (definition of a homotopy colimit), verbatim from AxiomMath/Stacks
`CategoryTheory.Pretriangulated.IsHomotopyColimit`: `K` is a homotopy colimit of the
sequence `F` if there is a distinguished triangle
`∐ F → ∐ F → K → (∐ F)⟦1⟧` whose first map is `1 - shift`. -/
def IsHomotopyColimit (F : ℕ ⥤ D) [HasCoproduct F.obj] (K : D) : Prop :=
  ∃ (p : ∐ F.obj ⟶ K) (q : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧),
    Triangle.mk (Sigma.desc fun n ↦ Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)) p q ∈ distTriang D

/-- **Stacks Tag 09SN** (`lemma-write-as-colimit`), as a named input.  Let `D` be a
triangulated category with direct sums and `E_i` a family of compact objects such that
`⊕ E_i` generates `D`.  Then every object `X` is a homotopy colimit `hocolim X_n`, where
`X_0` is a direct sum of shifts of the `E_i` and each transition morphism sits in a
distinguished triangle `Y_n → X_n → X_{n+1} → Y_n⟦1⟧` with `Y_n` a direct sum of shifts
of the `E_i`.

Verbatim from AxiomMath/Stacks
`CategoryTheory.Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated`
(`StacksFrontier/CategoryTheory/Triangulated/CompactObjects/CellStructure.lean`), with
AxiomMath's `IsCompactObject.{v}` replaced by `RelativeWeakApprox.IsCompactAb`; see the
module docstring for the comparison of the two compactness notions. -/
def Tag09SN (D : Type u) [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasCoproducts.{v} D] :
    Prop :=
  ∀ {ι : Type v} (E : ι → D) [∀ i, IsCompactAb (E i)],
    (∀ Y : D, ((ObjectProperty.ofObj E).shiftClosure ℤ).rightOrthogonal Y → IsZero Y) →
    ∀ (X : D), ∃ F : ℕ ⥤ D,
      IsHomotopyColimit F X ∧
      (⨆ J : Type v, ((ObjectProperty.ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J))
        (F.obj 0) ∧
      ∀ n : ℕ, ∃ Y : D,
        (⨆ J : Type v,
          ((ObjectProperty.ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) Y ∧
        ∃ (f : Y ⟶ F.obj n) (g : F.obj (n + 1) ⟶ Y⟦(1 : ℤ)⟧),
          Triangle.mk f (F.map (homOfLE (Nat.le_succ n))) g ∈ distTriang D

omit [Preadditive D] [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- For the one-member family `fun _ : PUnit => G`, the class of shifts of the family
is the class of shifts of `G`. -/
lemma ofObj_punit_shiftClosure (G : D) :
    (ObjectProperty.ofObj (fun _ : PUnit.{v + 1} => G)).shiftClosure ℤ =
      (ObjectProperty.singleton G).shiftClosure ℤ := by
  congr 1
  ext X
  simp [ObjectProperty.ofObj_iff]

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- The right-orthogonality hypothesis of 09SN for the one-member family
`fun _ : PUnit => G` is the paper's generation condition `IsPaperGenerator G` (zero
detection by the shifts of `G`, GL26 §2.1). -/
lemma isZero_of_rightOrthogonal_ofObj_punit_iff (G : D) :
    (∀ Y : D, ((ObjectProperty.ofObj (fun _ : PUnit.{v + 1} => G)).shiftClosure ℤ).rightOrthogonal
      Y → IsZero Y) ↔ IsPaperGenerator G := by
  rw [ofObj_punit_shiftClosure]
  constructor
  · intro h E hE
    exact h E ((rightOrthogonal_shiftClosure_singleton_iff G E).2 hE)
  · intro h Y hY
    exact h ((rightOrthogonal_shiftClosure_singleton_iff G Y).1 hY)

omit [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- A localizing property contains every `Type v`-indexed colimit of objects of a
subclass, uniformly in the index type. -/
lemma iSup_colimitsOfShape_le {P Q : ObjectProperty D}
    [∀ (J : Type v), Q.IsClosedUnderColimitsOfShape (Discrete J)] (hPQ : P ≤ Q) :
    (⨆ J : Type v, P.colimitsOfShape (Discrete J)) ≤ Q := by
  refine iSup_le fun J => ?_
  exact (ObjectProperty.colimitsOfShape_monotone (Discrete J) hPQ).trans
    (Q.colimitsOfShape_le (Discrete J))

omit [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- A property closed under `Type v`-indexed coproducts is closed under `ℕ`-indexed
coproducts (reindex along `ULift ℕ ≃ ℕ`). -/
lemma isClosedUnderColimitsOfShape_discrete_nat {Q : ObjectProperty D}
    [∀ (J : Type v), Q.IsClosedUnderColimitsOfShape (Discrete J)] :
    Q.IsClosedUnderColimitsOfShape (Discrete ℕ) :=
  ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
    (P := Q) (J := Discrete (ULift.{v} ℕ)) (Discrete.equivalence Equiv.ulift)

/-- **Consequence of Stacks 09SN.**  If `G` is compact and detects zero objects through
its shifts (`IsPaperGenerator G`, GL26 §2.1), then every object lies in every localizing
subcategory containing `G`: `IsLocalizingGenerator.{v} (singleton G)`, i.e. `⟨G⟩‾ = D`.
This is the proof of `(2) ⇒ (1)` in Stacks 09SR, which applies 09SN with `I = {1}`. -/
theorem isLocalizingGenerator_of_tag09SN [HasCoproducts.{v} D] (h09SN : Tag09SN D)
    {G : D} [IsCompactAb G] (hG : IsPaperGenerator G) :
    ObjectProperty.IsLocalizingGenerator.{v} (ObjectProperty.singleton G) := by
  intro Q hQ hQiso hQcolim hGQ X
  let E : PUnit.{v + 1} → D := fun _ => G
  have : ∀ i, IsCompactAb (E i) := fun _ => inferInstance
  have := hQiso
  have := hQ
  have : ∀ (J : Type v), Q.IsClosedUnderColimitsOfShape (Discrete J) := hQcolim
  obtain ⟨F, ⟨p, q, hT⟩, h₀, hstep⟩ :=
    h09SN E ((isZero_of_rightOrthogonal_ofObj_punit_iff G).2 hG) X
  -- the shifts of the family lie in `Q`
  have hshift : (ObjectProperty.ofObj E).shiftClosure ℤ ≤ Q := by
    rw [ObjectProperty.shiftClosure_le_iff]
    rintro _ ⟨i⟩
    exact hGQ _ (ObjectProperty.singleton_iff _ _ |>.2 rfl)
  have hsum := iSup_colimitsOfShape_le hshift
  -- every cell lies in `Q`
  have hF : ∀ n, Q (F.obj n) := by
    intro n
    induction n with
    | zero => exact hsum _ h₀
    | succ n ih =>
      obtain ⟨Y, hY, f, g, hfg⟩ := hstep n
      exact Q.ext_of_isTriangulatedClosed₃ _ hfg (hsum _ hY) ih
  -- the sum of the cells lies in `Q`
  have : Q.IsClosedUnderColimitsOfShape (Discrete ℕ) :=
    isClosedUnderColimitsOfShape_discrete_nat
  have hsumF : Q (∐ F.obj) :=
    Q.prop_of_isColimit (coproductIsCoproduct F.obj) (fun j => hF j.as)
  -- `X` is the third vertex of the homotopy-colimit triangle
  exact Q.ext_of_isTriangulatedClosed₃ _ hT hsumF hsumF

end StacksInterface

end RelativeFM
