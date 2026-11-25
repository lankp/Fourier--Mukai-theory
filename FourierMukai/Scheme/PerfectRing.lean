/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Perfect complexes for a ring

`Perf A` for a commutative ring `A` is the thick triangulated envelope of the
ring object `A` in `D(A-Mod)`; `Db A` and `Dbcoh A` are the bounded complexes and
those with bounded, degreewise finitely generated cohomology.  Proved: `Perf A`
contains `0` and `A`, and is closed under shifts, binary biproducts, cones,
retracts and direct summands; `Perf A ≤ Db A`; and `Perf A ≤ Dbcoh A` for
Noetherian `A` (via the generic fact that the bounded complexes with cohomology
in a Serre class form a thick triangulated subcategory, `DerivedCohomology.Bounded`).

Two external inputs are named rather than assumed: `BoundedProjectiveModelInput`
identifies `Perf A` with bounded complexes of finitely generated projectives, and
`CompactPerfectInput` states that the compact objects of `D(A-Mod)` are exactly
`Perf A` (Stacks Tag 0AED for schemes, Tag 09M8 for the easy direction; the same
statement is Neeman, Acta Math. 233 (2024), Theorem 3.2(i)).  Neither is
used by the proved inclusions, and no compactness claim is made for a field or a
PID, so the file does not overstate what is known.

Found by a member of the Ultramath run `smwuz1thx` (direction B2).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open RelativeWeakApprox
open scoped ZeroObject

universe w v u

namespace DerivedCohomology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Objects of the derived category which are bounded and whose cohomology
objects belong to `P`.  For `P` the class of finitely generated modules over a
Noetherian ring, this is `D^b_coh`. -/
def Bounded (P : ObjectProperty C) : ObjectProperty (DerivedCategory C) :=
  fun X => DerivedCategory.TStructure.t.bounded X ∧
    ∀ n : ℤ, P ((DerivedCategory.homologyFunctor C n).obj X)

/-- The bounded part of the canonical `t`-structure is closed under retracts.
Mathlib records its triangulated closure but does not yet package this thickness
instance globally. -/
lemma bounded_of_retract {X Y : DerivedCategory C} (r : Retract X Y)
    (hY : DerivedCategory.TStructure.t.bounded Y) :
    DerivedCategory.TStructure.t.bounded X := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hY
  constructor
  · refine ⟨a, (DerivedCategory.isGE_iff X a).2 fun i hi => ?_⟩
    exact IsZero.of_mono ((DerivedCategory.homologyFunctor C i).map r.i)
      ((DerivedCategory.isGE_iff Y a).1 ha i hi)
  · refine ⟨b, (DerivedCategory.isLE_iff X b).2 fun i hi => ?_⟩
    exact IsZero.of_mono ((DerivedCategory.homologyFunctor C i).map r.i)
      ((DerivedCategory.isLE_iff Y b).1 hb i hi)

/-- A Serre class of cohomology objects gives a thick subcategory of the
bounded derived category. -/
instance bounded_isStableUnderRetracts (P : ObjectProperty C) [P.IsSerreClass] :
    (Bounded P).IsStableUnderRetracts where
  of_retract r hY := by
    refine ⟨bounded_of_retract r hY.1, fun n => ?_⟩
    exact P.prop_of_mono ((DerivedCategory.homologyFunctor C n).map r.i) (hY.2 n)

/-- Shift compatibility of bounded cohomology in a Serre class. -/
instance bounded_isStableUnderShift (P : ObjectProperty C) [P.IsSerreClass] :
    (Bounded P).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ObjectProperty.IsStableUnderShiftBy.mk <| by
    intro X hX
    refine ⟨(DerivedCategory.TStructure.t.bounded).le_shift a X hX.1, fun n => ?_⟩
    let F := DerivedCategory.homologyFunctor C 0
    let e := (F.shiftIso a n (n + a) (add_comm a n)).app X
    change P ((F.shift n).obj (X⟦a⟧))
    exact P.prop_of_iso e.symm (hX.2 (n + a))

/-- The long exact cohomology sequence proves two-out-of-three for bounded
cohomology in a Serre class. -/
instance bounded_isTriangulatedClosed₂ (P : ObjectProperty C) [P.IsSerreClass] :
    (Bounded P).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' <| by
    intro T hT h₁ h₃
    refine ⟨(DerivedCategory.TStructure.t.bounded).ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1,
      fun n => ?_⟩
    exact P.prop_X₂_of_exact
      ((DerivedCategory.homologyFunctor C 0).homologySequence_exact₂ T hT n)
      (h₁.2 n) (h₃.2 n)

/-- `D^b_P` is a triangulated subcategory for every Serre class `P`. -/
instance bounded_isTriangulated (P : ObjectProperty C) [P.IsSerreClass] :
    (Bounded P).IsTriangulated where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_, fun n => ?_⟩
    · exact (DerivedCategory.TStructure.t.bounded).prop_zero
    · exact P.prop_of_isZero
        ((DerivedCategory.homologyFunctor C n).map_isZero (isZero_zero _))

/-- A complex concentrated in degree zero has bounded cohomology in `P` if its
underlying object belongs to `P`. -/
lemma singleFunctor_zero_mem (P : ObjectProperty C) [P.IsSerreClass]
    (M : C) (hM : P M) : Bounded P ((DerivedCategory.singleFunctor C 0).obj M) := by
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n => ?_⟩
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact P.prop_of_isZero
      (DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor C 0).obj M)
        0 n hn)
  · exact P.prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M).symm hM
  · exact P.prop_of_isZero
      (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor C 0).obj M)
        0 n hn)

/-- Universal-property form of the two-out-of-three argument: the thick
triangulated envelope of an object concentrated in degree zero has bounded
cohomology in `P`. -/
theorem triangEnvelope_single_zero_le (P : ObjectProperty C) [P.IsSerreClass]
    (M : C) (hM : P M) :
    (ObjectProperty.singleton ((DerivedCategory.singleFunctor C 0).obj M)).triangEnvelope ≤
      Bounded P := by
  rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
  exact singleFunctor_zero_mem P M hM

end DerivedCohomology

section RingPerfect

variable (A : Type u) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- The regular module, regarded as a complex concentrated in degree zero. -/
noncomputable def ringObject : DerivedCategory (ModuleCat A) :=
  (DerivedCategory.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A A)

/-- The full subcategory of finitely generated `A`-modules. -/
def FiniteModules : ObjectProperty (ModuleCat A) := fun M => Module.Finite A M

/-- Finitely generated modules over a Noetherian ring form a Serre class. -/
instance finiteModules_isSerreClass [IsNoetherianRing A] :
    (FiniteModules A).IsSerreClass where
  exists_zero := ⟨0, isZero_zero _, by
    change Module.Finite A (0 : ModuleCat A)
    let _ : Subsingleton (0 : ModuleCat A) :=
      ModuleCat.subsingleton_of_isZero (isZero_zero _)
    rw [Module.finite_def, show (⊤ : Submodule A (0 : ModuleCat A)) = ⊥ from
      (Submodule.eq_bot_iff _).2 (fun x _ => Subsingleton.elim x 0)]
    exact Submodule.fg_bot⟩
  prop_of_mono := by
    intro X Y f _ hY
    let _ : Module.Finite A Y := hY
    let _ : IsNoetherian A Y := isNoetherian_of_isNoetherianRing_of_finite A Y
    exact Module.Finite.of_injective f.hom ((ModuleCat.mono_iff_injective f).1 inferInstance)
  prop_of_epi := by
    intro X Y f _ hX
    let _ : Module.Finite A X := hX
    exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).1 inferInstance)
  prop_X₂_of_shortExact := by
    intro S hS h₁ h₃
    let _ : Module.Finite A S.X₁ := h₁
    let _ : Module.Finite A S.X₃ := h₃
    exact Module.Finite.of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact)
      hS.moduleCat_surjective_g

/-- `D^b(A)` as an object property, rather than as a bundled full
subcategory.  This makes it directly comparable with `Perf A`. -/
def Db : ObjectProperty (DerivedCategory (ModuleCat A)) :=
  DerivedCategory.TStructure.t.bounded

/-- `D^b(A)` is triangulated. -/
instance db_isTriangulated : (Db A).IsTriangulated := by
  unfold Db
  infer_instance

/-- `D^b(A)` is closed under retracts. -/
instance db_isStableUnderRetracts : (Db A).IsStableUnderRetracts where
  of_retract := DerivedCohomology.bounded_of_retract

/-- `D^b_coh(A)`: bounded complexes with finitely generated cohomology in every
degree.  No Noetherian hypothesis is needed for the definition; it is used for
the closure theorems and for `perf_le_dbcoh`. -/
def Dbcoh : ObjectProperty (DerivedCategory (ModuleCat A)) :=
  DerivedCohomology.Bounded (FiniteModules A)

/-- Over a Noetherian ring, `D^b_coh(A)` is triangulated. -/
instance dbcoh_isTriangulated [IsNoetherianRing A] : (Dbcoh A).IsTriangulated := by
  unfold Dbcoh
  infer_instance

/-- Over a Noetherian ring, `D^b_coh(A)` is closed under retracts. -/
instance dbcoh_isStableUnderRetracts [IsNoetherianRing A] :
    (Dbcoh A).IsStableUnderRetracts := by
  unfold Dbcoh
  infer_instance

/-- **GL26, Section 2.2 (affine case).** `Perf(A)` is the smallest triangulated,
retract-closed object property containing `A[0]`.  Mathlib's
`triangEnvelope` includes shifts, finite binary sums, mapping cones and
retracts. -/
noncomputable def Perf : ObjectProperty (DerivedCategory (ModuleCat A)) :=
  (ObjectProperty.singleton (ringObject A)).triangEnvelope

/-- The defining generator is perfect. -/
theorem ringObject_mem_perf : Perf A (ringObject A) := by
  apply ObjectProperty.le_triangEnvelope
  exact ObjectProperty.ofObj_apply _ Unit.unit

/-- `Perf(A)` is a triangulated subcategory. -/
instance perf_isTriangulated : (Perf A).IsTriangulated := by
  unfold Perf
  infer_instance

/-- `Perf(A)` is closed under all retracts, in particular direct summands. -/
instance perf_isStableUnderRetracts : (Perf A).IsStableUnderRetracts := by
  unfold Perf
  infer_instance

/-- The zero object is perfect. -/
theorem perf_zero : Perf A (0 : DerivedCategory (ModuleCat A)) :=
  (Perf A).prop_zero

/-- Binary direct sums of perfect complexes are perfect. -/
theorem perf_biprod {X Y : DerivedCategory (ModuleCat A)}
    [HasBinaryBiproduct X Y] (hX : Perf A X) (hY : Perf A Y) : Perf A (X ⊞ Y) :=
  (Perf A).ext_of_isTriangulatedClosed₂ _
    (binaryBiproductTriangle_distinguished X Y) hX hY

/-- Closure of perfect complexes under integer shifts. -/
theorem perf_shift {X : DerivedCategory (ModuleCat A)} (hX : Perf A X) (n : ℤ) :
    Perf A (X⟦n⟧) :=
  (Perf A).le_shift n X hX

/-- Closure of perfect complexes under retracts and direct summands. -/
theorem perf_of_retract {X Y : DerivedCategory (ModuleCat A)}
    (r : Retract X Y) (hY : Perf A Y) : Perf A X :=
  (Perf A).prop_of_retract r hY

/-- Mapping cones of morphisms between perfect complexes can be chosen perfect.
This is the cone form of `perf_isTriangulated`. -/
theorem perf_exists_cone {X Y : DerivedCategory (ModuleCat A)}
    (f : X ⟶ Y) (hX : Perf A X) (hY : Perf A Y) :
    ∃ (Z : DerivedCategory (ModuleCat A)) (_ : Perf A Z) (g : Y ⟶ Z)
      (h : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang _ :=
  (Perf A).distinguished_cocone_triangle f hX hY

/-- A direct summand of a binary biproduct of perfect complexes is perfect. -/
theorem perf_of_biprod_left {X Y : DerivedCategory (ModuleCat A)}
    [HasBinaryBiproduct X Y] (h : Perf A (X ⊞ Y)) : Perf A X :=
  (Perf A).prop_of_retract (BinaryBiproduct.bicone X Y).retract_left h

/-- The other direct summand of a binary biproduct of perfect complexes is
perfect. -/
theorem perf_of_biprod_right {X Y : DerivedCategory (ModuleCat A)}
    [HasBinaryBiproduct X Y] (h : Perf A (X ⊞ Y)) : Perf A Y :=
  (Perf A).prop_of_retract (BinaryBiproduct.bicone X Y).retract_right h

/-- Every perfect complex is cohomologically bounded. -/
theorem perf_le_db : Perf A ≤ Db A := by
  rw [Perf, ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
  unfold ringObject
  exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩

/-- Over a Noetherian ring, every perfect complex belongs to `D^b_coh(A)`.
This is GL26 Section 2.2 in the affine case; its proof does not use the
compact-object theorem. -/
theorem perf_le_dbcoh [IsNoetherianRing A] : Perf A ≤ Dbcoh A := by
  exact DerivedCohomology.triangEnvelope_single_zero_le
    (FiniteModules A) (ModuleCat.of A A) (Module.Finite.self A)

/-- A strictly bounded representative of a derived object by degreewise
finitely generated projective modules.  The term `complex.IsStrictlyGE a` and
`complex.IsStrictlyLE b` say precisely that its terms vanish below `a` and above
`b`, not merely that its cohomology vanishes there. -/
structure BoundedFiniteProjectiveModel (A : Type u) [CommRing A]
    (X : DerivedCategory (ModuleCat A)) where
  /-- The representing cochain complex. -/
  complex : CochainComplex (ModuleCat A) ℤ
  /-- A lower strict bound. -/
  lower : ℤ
  /-- An upper strict bound. -/
  upper : ℤ
  /-- The complex is strictly bounded below. -/
  isStrictlyGE : complex.IsStrictlyGE lower
  /-- The complex is strictly bounded above. -/
  isStrictlyLE : complex.IsStrictlyLE upper
  /-- Every term is finitely generated. -/
  finite : ∀ n, Module.Finite A (complex.X n)
  /-- Every term is projective. -/
  projective : ∀ n, Module.Projective A (complex.X n)
  /-- The complex represents `X` in the derived category. -/
  iso : X ≅ DerivedCategory.Q.obj complex

/-- **External input, not asserted by this file.**  The equivalence between
`Perf A` and bounded complexes of finitely generated projective modules.

The mathematical proof is supplied by Stacks Definition 0657 together with
Lemmas 066R, 066S and 066T: finite projective modules are retracts of finite
free modules, and stupid truncation expresses a bounded complex as finitely
many extensions of its terms.  A future development should prove this field,
not introduce it as an axiom. -/
structure BoundedProjectiveModelInput (A : Type u) [CommRing A] where
  /-- `X` is in the thick envelope of `A[0]` exactly when it has a bounded
  finite-projective model. -/
  perf_iff_model : ∀ X : DerivedCategory (ModuleCat A),
    Perf A X ↔ Nonempty (BoundedFiniteProjectiveModel A X)

/-- **External compactness input.**  For an affine scheme, the compact objects
of the unbounded derived category are exactly the perfect complexes.

This is the affine case (take `T = |X|`) of Stacks Project Tag **0AED**
(Lemma 75.16.3): an object of `D_QCoh,T(O_X)` is compact if and only if it is
perfect as an object of `D(O_X)`; the two directions inside that proof are
Tag **09M8** (perfect objects are compact) and Tag **09SR** (the perfect
generator of Tag **0AEC** generates the compacts).  The same statement is
Neeman, *Bounded `t`-structures on the category of perfect complexes*,
Acta Math. 233 (2024), Theorem 3.2(i).  It is packaged as a structure field so
every use must carry the hypothesis explicitly; it is not an axiom. -/
structure CompactPerfectInput (A : Type u) [CommRing A] where
  /-- `IsCompactAb` is the coproduct-compactness notion used by the completed
  `WeakApprox` layer. -/
  compact_iff_perfect : ∀ X : DerivedCategory (ModuleCat A),
    IsCompactAb X ↔ Perf A X

end RingPerfect


end RelativeFM
