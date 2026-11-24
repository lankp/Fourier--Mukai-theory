/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Perfect complexes on a scheme

* `IsFiniteLocallyFree` for sheaves of modules on a scheme, built on Mathlib's
  local-generator/free API: iso-invariance, finite free modules, `0`, the
  structure sheaf, and the locally-free and quasicoherent instances.
* `IsBoundedVectorBundleComplex`: bounded complexes of vector bundles, with iso-,
  zero-, single-object and shift closure.
* `IsPerfect` (equivalently `IsPerfectComplex`) via the scheme-local model of
  Stacks 0BCJ, explicitly identified with 08CM; iso-invariance, `0` and all
  shifts are proved.
* Interfaces with the facts that are not in Mathlib: `VectorBundleCalculus`
  (restriction, tensor, dual, extensions and retracts, with 08CR/08CS thickness),
  `PerfectToDQCohInterface` (`Perf ⊆ D_qc`, the 09M1 direction), and
  `PerfectCompactInterface` (compacts = perfect, 09M1 / Bondal–Van den Bergh).
* The affine comparison: `affineThickGenerated` for `Perf(Spec A)` as the thick
  envelope of the structure sheaf, `AffinePerfectCharacterization` stating the
  two agree, and `affineThickGenerated_le_perfect` proving one inclusion under
  the interfaces.  The equality itself is explicitly not proved.

Found by a member of the Ultramath run `smwuyku7t` (direction R2).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u w

/-- The derived category of all `𝒪_X`-modules.  The parameter `w` is the
chosen hom-room of the localization; `HasDerivedCategory.standard` gives the
canonical choice `w = max u u`. -/
abbrev SchemeD (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules] :=
  DerivedCategory X.Modules

/-- A vector bundle on a scheme: Mathlib's local free presentations with finite
bases (Stacks Tag **01C6(2)**).  These are the local terms of `Perf(X)` in
GL26, **Section 2.2**. -/
class IsFiniteLocallyFree {X : Scheme.{u}} (M : X.Modules) : Prop where
  exists_isFiniteLocallyFreeData :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
      q.IsLocallyFreeData ∧ q.IsFiniteType

namespace IsFiniteLocallyFree

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Every finite locally free sheaf is locally free (Stacks Tag **01C6**). -/
instance toIsLocallyFree [hM : IsFiniteLocallyFree M] :
    SheafOfModules.IsLocallyFree.{u, u, u} M := by
  obtain ⟨q, hq, _⟩ := hM.exists_isFiniteLocallyFreeData
  letI := hq
  exact q.isLocallyFree

/-- Finite local freeness is invariant under isomorphism: carry the same local
bases across the isomorphism (Stacks Tag **01C6**). -/
theorem of_iso (e : M ≅ N) (hM : IsFiniteLocallyFree M) : IsFiniteLocallyFree N := by
  obtain ⟨q, hqfree, hqfinite⟩ := hM.exists_isFiniteLocallyFreeData
  let q' : SheafOfModules.LocalGeneratorsData.{u} N :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom }
  refine ⟨q', ?_, ?_⟩
  · constructor
    intro i
    have h₀ : IsIso (q.generators i).π := hqfree.isIso i
    have h₁ : IsIso ((q.generators i).π ≫
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom) := inferInstance
    exact Eq.mpr (congrArg IsIso (SheafOfModules.GeneratingSections.ofEpi_π
      (q.generators i)
      ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom)) h₁
  · constructor
    intro i
    letI : (q.generators i).IsFiniteType := hqfinite.isFiniteType i
    infer_instance

/-- A finitely based free `𝒪_X`-module is a vector bundle. -/
instance free (I : Type u) [Finite I] :
    IsFiniteLocallyFree (SheafOfModules.free (R := X.ringCatSheaf) I) := by
  let G := SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I
  haveI : G.IsFiniteType := ⟨by change Finite I; infer_instance⟩
  let q : SheafOfModules.LocalGeneratorsData.{u}
      (SheafOfModules.free (R := X.ringCatSheaf) I) := G.localGeneratorsData
  refine ⟨q, inferInstance, ?_⟩
  constructor
  intro i
  constructor
  change Finite G.I
  change Finite I
  infer_instance

/-- The rank-zero free sheaf is zero: it is the colimit of the empty diagram. -/
theorem isZero_free_empty :
    IsZero (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Empty)) := by
  apply IsColimit.isZero_pt (SheafOfModules.isColimitFreeCofan (ULift.{u} Empty))
  rw [Functor.isZero_iff]
  intro j
  exact isEmptyElim j.as.down

/-- Any zero `𝒪_X`-module is finite locally free of rank zero. -/
theorem of_isZero (hM : IsZero M) : IsFiniteLocallyFree M :=
  of_iso (IsZero.iso isZero_free_empty hM)
    (IsFiniteLocallyFree.free (ULift.{u} Empty))

/-- Every vector bundle is quasi-coherent, by Mathlib's local-presentation
construction (Stacks Tags **01C6** and **01BD**). -/
instance toIsQuasicoherent [hM : IsFiniteLocallyFree M] : M.IsQuasicoherent := by
  obtain ⟨q, hq, _⟩ := hM.exists_isFiniteLocallyFreeData
  letI := hq
  exact q.quasiCoherentData.isQuasicoherent

end IsFiniteLocallyFree

/-- A cohomologically bounded cochain complex of vector bundles.  This is the
local model in Stacks Tag **0BCJ**.  We deliberately do not call it “strictly
perfect”: the latter also has a global direct-summand-of-finite-free model.
On a scheme, Tag **0BCJ** says that the two local notions give the same perfect
objects. -/
structure IsBoundedVectorBundleComplex {X : Scheme.{u}} (P : CochainComplex X.Modules ℤ) : Prop where
  finiteLocallyFree (n : ℤ) : IsFiniteLocallyFree (P.X n)
  boundedBelow : ∃ a : ℤ, P.IsStrictlyGE a
  boundedAbove : ∃ b : ℤ, P.IsStrictlyLE b

namespace IsBoundedVectorBundleComplex

variable {X : Scheme.{u}} {P : CochainComplex X.Modules ℤ}

/-- Bounded vector-bundle complexes are invariant under isomorphism. -/
theorem of_iso {Q : CochainComplex X.Modules ℤ} (e : P ≅ Q)
    (hP : IsBoundedVectorBundleComplex P) : IsBoundedVectorBundleComplex Q where
  finiteLocallyFree n := IsFiniteLocallyFree.of_iso
    ((HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).mapIso e)
    (hP.finiteLocallyFree n)
  boundedBelow := by
    obtain ⟨a, ha⟩ := hP.boundedBelow
    letI := ha
    exact ⟨a, CochainComplex.isStrictlyGE_of_iso e a⟩
  boundedAbove := by
    obtain ⟨b, hb⟩ := hP.boundedAbove
    letI := hb
    exact ⟨b, CochainComplex.isStrictlyLE_of_iso e b⟩

/-- The zero complex is a bounded vector-bundle complex. -/
theorem zero : IsBoundedVectorBundleComplex (0 : CochainComplex X.Modules ℤ) where
  finiteLocallyFree n := IsFiniteLocallyFree.of_isZero
    ((HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).map_isZero (isZero_zero _))
  boundedBelow := ⟨0, inferInstance⟩
  boundedAbove := ⟨0, inferInstance⟩

/-- A vector bundle placed in a single cohomological degree is a bounded
vector-bundle complex. -/
theorem single (M : X.Modules) [IsFiniteLocallyFree M] (n : ℤ) :
    IsBoundedVectorBundleComplex ((CochainComplex.singleFunctor X.Modules n).obj M) where
  finiteLocallyFree i := by
    by_cases hi : i = n
    · subst i
      exact IsFiniteLocallyFree.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n M).symm inferInstance
    · exact IsFiniteLocallyFree.of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
  boundedBelow := ⟨n, inferInstance⟩
  boundedAbove := ⟨n, inferInstance⟩

/-- Shifting a bounded vector-bundle complex preserves its terms up to the
canonical shift isomorphisms and translates its two cohomological bounds. -/
theorem shift (hP : IsBoundedVectorBundleComplex P) (a : ℤ) : IsBoundedVectorBundleComplex (P⟦a⟧) where
  finiteLocallyFree n := IsFiniteLocallyFree.of_iso
    (P.shiftFunctorObjXIso a n (n + a) rfl) (hP.finiteLocallyFree (n + a))
  boundedBelow := by
    obtain ⟨b, hb⟩ := hP.boundedBelow
    letI := hb
    exact ⟨b - a, P.isStrictlyGE_shift b a (b - a) (by omega)⟩
  boundedAbove := by
    obtain ⟨b, hb⟩ := hP.boundedAbove
    letI := hb
    exact ⟨b - a, P.isStrictlyLE_shift b a (b - a) (by omega)⟩

end IsBoundedVectorBundleComplex

/-- Restriction to an open is additive, transported from the additive pullback
functor along `restrictFunctorIsoPullback`. -/
noncomputable instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).Additive :=
  Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback f).symm

/-- Restriction of a complex to an open subscheme, degreewise. -/
noncomputable abbrev restrictComplex {X : Scheme.{u}} (U : X.Opens)
    (K : CochainComplex X.Modules ℤ) : CochainComplex (U : Scheme.{u}).Modules ℤ :=
  ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- A perfect complex in the bounded vector-bundle local-model form of Stacks
Tag **0BCJ**: on an open cover it receives quasi-isomorphisms from bounded
complexes of finite locally free sheaves.  On a scheme this is equivalent to
Stacks Tag **08CM**.  The arrow points from the local model to the restriction,
as in Tag **08CM**.  The cover index is `Type u`, the same smallness imposed by
Mathlib's local-generator data; the derived hom-universe `w` is independent. -/
def IsPerfectComplex {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) : Prop :=
  ∃ (I : Type u) (U : I → X.Opens), iSup U = ⊤ ∧
    ∀ i : I, ∃ P : CochainComplex (U i : Scheme.{u}).Modules ℤ,
      IsBoundedVectorBundleComplex P ∧
        ∃ f : P ⟶ restrictComplex (U i) K, QuasiIso f

namespace IsPerfectComplex

variable {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}

/-- The zero complex is perfect, using the one-member cover by the top open. -/
theorem zero : IsPerfectComplex (0 : CochainComplex X.Modules ℤ) := by
  refine ⟨ULift.{u} Unit, fun _ ↦ ⊤, by simp, fun _ ↦ ⟨0, IsBoundedVectorBundleComplex.zero, 0, ?_⟩⟩
  have : IsIso (0 : (0 : CochainComplex (⊤ : X.Opens).toScheme.Modules ℤ) ⟶
      restrictComplex (⊤ : X.Opens) (0 : CochainComplex X.Modules ℤ)) :=
    (isIsoZero_iff_source_target_isZero _ _).2
      ⟨isZero_zero _, Functor.map_isZero _ (isZero_zero _)⟩
  infer_instance

/-- Perfectness of a complex is invariant under isomorphism. -/
theorem of_iso (e : K ≅ L) (hK : IsPerfectComplex K) : IsPerfectComplex L := by
  obtain ⟨I, U, hU, models⟩ := hK
  refine ⟨I, U, hU, fun i ↦ ?_⟩
  obtain ⟨P, hP, f, hf⟩ := models i
  letI := hf
  exact ⟨P, hP, f ≫
    (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso e).hom, inferInstance⟩

/-- Shifts of perfect complexes are perfect.  The two inputs are shift stability
of bounded vector-bundle complexes and Mathlib's compatibility of quasi-isomorphisms
and `mapHomologicalComplex` with shifts. -/
theorem shift (hK : IsPerfectComplex K) (a : ℤ) : IsPerfectComplex (K⟦a⟧) := by
  obtain ⟨I, U, hU, models⟩ := hK
  refine ⟨I, U, hU, fun i ↦ ?_⟩
  obtain ⟨P, hP, f, hf⟩ := models i
  letI := hf
  exact ⟨P⟦a⟧, hP.shift a, f⟦a⟧' ≫
    ((Scheme.Modules.restrictFunctor (U i).ι).mapCochainComplexShiftIso a).inv.app K,
    inferInstance⟩

end IsPerfectComplex

/-- A perfect derived object: an object represented by a bounded vector-bundle
local model in the sense of Stacks Tag **0BCJ**, equivalently by a perfect
complex in the sense of Tag **08CM**.  This is GL26 **Section 2.2**'s notion
underlying `Perf(X)`. -/
def IsPerfect {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
    (E : SchemeD X) : Prop :=
  ∃ K : CochainComplex X.Modules ℤ, IsPerfectComplex K ∧
    Nonempty (DerivedCategory.Q.obj K ≅ E)

/-- The full object property `Perf(X)` of GL26 **Section 2.2**, used in its
**Definitions 4.1 and 5.1** (`f`-perfect and `f`-quasi-perfect). -/
def perfect {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules] :
    ObjectProperty (SchemeD X) := IsPerfect

namespace IsPerfect

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
  {E E' : SchemeD X}

/-- A perfect complex represents a perfect derived object (Stacks Tag **0BCJ**). -/
theorem of_complex {K : CochainComplex X.Modules ℤ} (hK : IsPerfectComplex K) :
    IsPerfect (DerivedCategory.Q.obj K) := ⟨K, hK, ⟨Iso.refl _⟩⟩

/-- Perfectness is invariant under derived isomorphism. -/
theorem of_iso (e : E ≅ E') (hE : IsPerfect E) : IsPerfect E' := by
  obtain ⟨K, hK, ⟨f⟩⟩ := hE
  exact ⟨K, hK, ⟨f.trans e⟩⟩

/-- A zero object is perfect (Stacks Tags **08CM**, **0BCJ**). -/
theorem zero : IsPerfect (0 : SchemeD X) :=
  of_complex IsPerfectComplex.zero |>.of_iso (DerivedCategory.Q.mapZeroObject)

/-- Perfectness is stable under every integer shift. -/
theorem shift (hE : IsPerfect E) (a : ℤ) : IsPerfect (E⟦a⟧) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  exact ⟨K⟦a⟧, hK.shift a,
    ⟨(DerivedCategory.Q.commShiftIso a).app K ≪≫ (shiftFunctor _ a).mapIso e⟩⟩

end IsPerfect

instance {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules] :
    (perfect (X := X)).IsClosedUnderIsomorphisms where
  of_iso e hE := hE.of_iso e

instance {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules] :
    (perfect (X := X)).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ObjectProperty.IsStableUnderShiftBy.mk fun _ hE ↦ hE.shift a

/-! ### The structure sheaf is a vector bundle -/

namespace IsFiniteLocallyFree

/-- The free sheaf on a one-element type is the structure sheaf. -/
noncomputable def freePUnitIsoUnit (X : Scheme.{u}) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Unit) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  coproductUniqueIso _

/-- The structure sheaf is finite locally free of rank one. -/
instance unit (X : Scheme.{u}) :
    IsFiniteLocallyFree (SheafOfModules.unit X.ringCatSheaf) :=
  of_iso (freePUnitIsoUnit X) (IsFiniteLocallyFree.free (ULift.{u} Unit))

end IsFiniteLocallyFree

/-! ### Vector-bundle operations still to be supplied geometrically -/

/-- PROVISIONAL interface for the elementary vector-bundle calculus missing
from Mathlib.  All fields are local consequences of Stacks Tag **01C6**: a
restriction of a local trivialisation is a local trivialisation; finite direct
sums, extensions after local splitting, and retracts of finite locally free
sheaves are finite locally free. -/
structure VectorBundleCalculus where
  /-- Open restriction preserves finite local freeness (Stacks Tag **01C6**). -/
  restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    IsFiniteLocallyFree M → IsFiniteLocallyFree ((Scheme.Modules.restrictFunctor f).obj M)
  /-- Finite direct sums of vector bundles are vector bundles (Stacks Tag **01C6**). -/
  biprod {X : Scheme.{u}} (M N : X.Modules) :
    IsFiniteLocallyFree M → IsFiniteLocallyFree N → IsFiniteLocallyFree (M ⊞ N)
  /-- An extension of vector bundles is a vector bundle: after restriction to a
  common trivialising cover, the short exact sequence splits (Stacks Tag **01C6**). -/
  extension {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.Exact)
    [Mono S.f] [Epi S.g] :
    IsFiniteLocallyFree S.X₁ → IsFiniteLocallyFree S.X₃ → IsFiniteLocallyFree S.X₂
  /-- A retract of a vector bundle is a vector bundle; locally this is a finite
  projective direct summand of a finite free module (Stacks Tag **01C6**). -/
  retract {X : Scheme.{u}} {M N : X.Modules} :
    Retract M N → IsFiniteLocallyFree N → IsFiniteLocallyFree M

namespace IsBoundedVectorBundleComplex

/-- Restriction of a bounded vector-bundle complex to an open subscheme. -/
theorem restrict (H : VectorBundleCalculus.{u}) {X : Scheme.{u}}
    {P : CochainComplex X.Modules ℤ} (hP : IsBoundedVectorBundleComplex P) (U : X.Opens) :
    IsBoundedVectorBundleComplex (restrictComplex U P) where
  finiteLocallyFree n := H.restrict U.ι (P.X n) (hP.finiteLocallyFree n)
  boundedBelow := by
    obtain ⟨a, ha⟩ := hP.boundedBelow
    letI := ha
    exact ⟨a, inferInstance⟩
  boundedAbove := by
    obtain ⟨b, hb⟩ := hP.boundedAbove
    letI := hb
    exact ⟨b, inferInstance⟩

end IsBoundedVectorBundleComplex

namespace IsPerfectComplex

/-- A bounded vector-bundle complex is perfect: restrict it to the top open
and use the identity quasi-isomorphism (Stacks Tag **0BCJ**). -/
theorem of_boundedVectorBundleComplex (H : VectorBundleCalculus.{u}) {X : Scheme.{u}}
    {P : CochainComplex X.Modules ℤ} (hP : IsBoundedVectorBundleComplex P) : IsPerfectComplex P :=
  ⟨ULift.{u} Unit, fun _ ↦ ⊤, by simp, fun _ ↦
    ⟨restrictComplex (⊤ : X.Opens) P, hP.restrict H _, 𝟙 _, inferInstance⟩⟩

end IsPerfectComplex

namespace IsPerfect

/-- A bounded vector-bundle representative gives a perfect derived object. -/
theorem of_boundedVectorBundleComplex (H : VectorBundleCalculus.{u}) {X : Scheme.{u}}
    [HasDerivedCategory.{w} X.Modules] {P : CochainComplex X.Modules ℤ}
    (hP : IsBoundedVectorBundleComplex P) : IsPerfect (DerivedCategory.Q.obj P) :=
  of_complex (IsPerfectComplex.of_boundedVectorBundleComplex H hP)

/-- A vector bundle in a single degree is perfect. -/
theorem single (H : VectorBundleCalculus.{u}) {X : Scheme.{u}}
    [HasDerivedCategory.{w} X.Modules] (M : X.Modules) [IsFiniteLocallyFree M] (n : ℤ) :
    IsPerfect ((DerivedCategory.singleFunctor X.Modules n).obj M) :=
  of_complex (IsPerfectComplex.of_boundedVectorBundleComplex H (IsBoundedVectorBundleComplex.single M n))

end IsPerfect

/-! ### Tensor products and duals of vector bundles -/

/-- PROVISIONAL monoidal interface on one scheme.  Mathlib 4.33.1 has no tensor
or internal-dual functor on `SheafOfModules`; these are data, not fabricated
functors.  The two closure fields are the vector-bundle facts used by GL26
(Stacks Tags **01C6**, **0FPU** and **0FPV**). -/
structure VectorBundleMonoidal (X : Scheme.{u}) where
  /-- Tensor product of module sheaves. -/
  tensor : X.Modules ⥤ X.Modules ⥤ X.Modules
  /-- The dual vector bundle, contravariant in the input. -/
  dual : X.Modulesᵒᵖ ⥤ X.Modules
  /-- Tensor products of vector bundles are vector bundles (Stacks Tag **01C6**). -/
  tensor_bundle {M N : X.Modules} :
    IsFiniteLocallyFree M → IsFiniteLocallyFree N →
      IsFiniteLocallyFree ((tensor.obj M).obj N)
  /-- Duals of vector bundles are vector bundles (Stacks Tags **0FPU**, **0FPV**). -/
  dual_bundle {M : X.Modules} :
    IsFiniteLocallyFree M → IsFiniteLocallyFree (dual.obj (.op M))

/-! ### Triangulated and thick closure of perfect objects -/

/-- PROVISIONAL interface for the two non-formal closure theorems about perfect
objects.  The first is Stacks Tag **08CR** (mapping cones/two-out-of-three);
the second is Stacks Tag **08CS** (direct summands), used with idempotent
completeness of the derived category to handle arbitrary categorical retracts. -/
structure PerfectThicknessInterface (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules] where
  /-- If the outer vertices of a distinguished triangle are perfect, so is its
  middle vertex (Stacks Tag **08CR**). -/
  cone (T : Triangle (SchemeD X)) (hT : T ∈ distTriang (SchemeD X)) :
    IsPerfect T.obj₁ → IsPerfect T.obj₃ → IsPerfect T.obj₂
  /-- Perfectness descends to retracts (Stacks Tag **08CS**). -/
  retract {E F : SchemeD X} : Retract E F → IsPerfect F → IsPerfect E

namespace PerfectThicknessInterface

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

/-- The supplied `08CR` fact, together with the proved zero and shift results,
makes `Perf(X)` a triangulated object property. -/
@[instance_reducible] def triangulated (H : PerfectThicknessInterface X) :
    (perfect (X := X)).IsTriangulated where
  toContainsZero := ⟨⟨0, isZero_zero _, IsPerfect.zero⟩⟩
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' H.cone

/-- The supplied `08CS` fact makes `Perf(X)` stable under categorical retracts. -/
@[instance_reducible] def stableUnderRetracts (H : PerfectThicknessInterface X) :
    (perfect (X := X)).IsStableUnderRetracts where
  of_retract r hF := H.retract r hF

end PerfectThicknessInterface

/-! ### From perfect objects to `D_qc(X)` -/

/-- PROVISIONAL interface to R1's `D_qc(X)`.  `complex_mem` is exactly the missing
geometric input: bounded locally free models have quasi-coherent cohomology,
quasi-isomorphisms and exact open restriction preserve this, and
quasi-coherence is local (Stacks Tags **01LA** and **0BCJ**). -/
structure PerfectToDQCohInterface (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules] where
  /-- The full object property with quasi-coherent cohomology sheaves. -/
  DQCoh : ObjectProperty (SchemeD X)
  /-- R1's strict fullness of `D_qc(X)`. -/
  isoClosed : DQCoh.IsClosedUnderIsomorphisms
  /-- Every perfect representative has quasi-coherent cohomology. -/
  complex_mem (K : CochainComplex X.Modules ℤ) :
    IsPerfectComplex K → DQCoh (DerivedCategory.Q.obj K)

/-- With R1's interface supplied, every perfect object lies in `D_qc(X)`. -/
theorem perfect_le_dqcoh {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
    (H : PerfectToDQCohInterface X) : perfect (X := X) ≤ H.DQCoh := by
  letI := H.isoClosed
  intro E hE
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  exact H.DQCoh.prop_of_iso e (H.complex_mem K hK)

/-! ### Perfect objects versus compact objects -/

/-- The precise compact-versus-perfect statement on a quasi-compact
quasi-separated scheme, used in GL26 **Remark 2.6** when passing between
`D_qc` and `Perf`.  `compact` is intended to be instantiated by
`RelativeWeakApprox.IsCompactAb`; it is not specialized to compactness in the
larger derived category of all module sheaves. -/
def PerfectCompactStatement {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
    (H : PerfectToDQCohInterface X) (compact : ObjectProperty (SchemeD X)) : Prop :=
  ∀ E, H.DQCoh E → (compact E ↔ IsPerfect E)

/-- PROVISIONAL interface for **Bondal--Van den Bergh / Stacks Tag 09M1**:
on a qcqs scheme, an object of `D_qc(X)` is compact exactly when it is perfect.
For Noetherian schemes see also Hall--Rydh.  This theorem is *not* proved here.
The qcqs hypotheses follow from the Noetherian-scheme target. -/
structure PerfectCompactInterface (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]
    [CompactSpace X] [QuasiSeparatedSpace X] (H : PerfectToDQCohInterface X) where
  /-- Compact objects of `D_qc(X)`, supplied by the categorical layer. -/
  compact : ObjectProperty (SchemeD X)
  /-- Stacks Tag **09M1**. -/
  compact_iff_perfect : PerfectCompactStatement H compact

/-! ### The affine thick-generation characterization -/

/-- The property generated by the structure sheaf concentrated in degree zero;
its shifts are included automatically by `triangEnvelope`. -/
def affineUnitGenerators (A : CommRingCat.{u}) [HasDerivedCategory.{w} (Spec A).Modules] :
    ObjectProperty (SchemeD (Spec A)) := fun E ↦
  Nonempty (E ≅ (DerivedCategory.singleFunctor (Spec A).Modules 0).obj
    (SheafOfModules.unit (Spec A).ringCatSheaf))

/-- The thick subcategory generated by all shifts of `A`, viewed through
`tildeSelf` as the structure sheaf on `Spec A`. -/
def affineThickGenerated (A : CommRingCat.{u}) [HasDerivedCategory.{w} (Spec A).Modules] :
    ObjectProperty (SchemeD (Spec A)) := (affineUnitGenerators A).triangEnvelope

instance (A : CommRingCat.{u}) [HasDerivedCategory.{w} (Spec A).Modules] :
    (affineUnitGenerators A).Nonempty where
  exists_prop := ⟨_, ⟨Iso.refl _⟩⟩

/-- The affine thick envelope is unconditionally triangulated. -/
instance (A : CommRingCat.{u}) [HasDerivedCategory.{w} (Spec A).Modules] :
    (affineThickGenerated A).IsTriangulated := by
  dsimp [affineThickGenerated]
  infer_instance

/-- The affine thick envelope is unconditionally stable under retracts. -/
instance (A : CommRingCat.{u}) [HasDerivedCategory.{w} (Spec A).Modules] :
    (affineThickGenerated A).IsStableUnderRetracts := by
  dsimp [affineThickGenerated]
  infer_instance

/-- PROVISIONAL interface for the classical affine characterization
(Stacks Tags **07LT** and **06Z0**): bounded perfect complexes of modules are
precisely the thick closure of the shifts of `A`.  Only this equality remains
external; the right-hand side has already been proved triangulated and thick
above. -/
def AffinePerfectCharacterization (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (Spec A).Modules] : Prop :=
  perfect (X := Spec A) = affineThickGenerated A

/-- Modulo the affine comparison, `Perf(Spec A)` is triangulated. -/
@[instance_reducible] def perfect_isTriangulated_of_affine (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (Spec A).Modules] (h : AffinePerfectCharacterization A) :
    (perfect (X := Spec A)).IsTriangulated := by
  rw [h]
  infer_instance

/-- Modulo the affine comparison, `Perf(Spec A)` is stable under retracts. -/
@[instance_reducible] def perfect_stableUnderRetracts_of_affine (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (Spec A).Modules] (h : AffinePerfectCharacterization A) :
    (perfect (X := Spec A)).IsStableUnderRetracts := by
  rw [h]
  infer_instance

/-- Under the general `08CR`/`08CS` interface and elementary bundle restriction,
every object finitely built from the structure sheaf is perfect. -/
theorem affineThickGenerated_le_perfect (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (Spec A).Modules]
    (HB : VectorBundleCalculus.{u}) (HT : PerfectThicknessInterface (Spec A)) :
    affineThickGenerated A ≤ perfect (X := Spec A) := by
  letI := HT.triangulated
  letI := HT.stableUnderRetracts
  refine (ObjectProperty.triangEnvelope_le_iff (affineUnitGenerators A)).2 ?_
  intro E hE
  obtain ⟨e⟩ := hE
  exact (IsPerfect.single HB (SheafOfModules.unit (Spec A).ringCatSheaf) 0).of_iso e.symm

end RelativeFM
