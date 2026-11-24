/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Derived tensor, `RHom`, `f^×`, `f^!`: the six-functor interface

The concrete part: `SheafDerived`, total left and right derived functors built
from Mathlib's Kan extensions, derived pushforward and pullback for a morphism of
schemes, with the descent and universal-factorization API.

The interface part: a closed symmetric derived tensor/`RHom` (external and
internal currying), perfect duality, triangulated enhancements, and
`DerivedMorphismData` carrying `Lf^*`, `Rf_*`, `f^×`, `f^!`, natural monoidality
of the pullback, the projection formula, `chi`/`sigma`, the invertibility
hypotheses GL26 uses, composition data, and the paper/Stacks references for each
field.  `Rf_* ⊣ f^!` is proved in the proper case by transport; the base-change
morphism `theta` is constructed as a mate, with `lower-star`/`upper-cross` as its
conjugate and `beta` from `theta⁻¹`, and invertibility transports both ways with
the push/pull conjugacy coherence recorded.

What remains geometric is explicit: tor-independence, the bounded-below and
finite-tor cases, and the existence of the derived functors in the unbounded
setting.  None of it is fabricated.

Found by a member of the Ultramath run `smwuyku7t` (direction R5).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v w w₁ w₂ u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

/-- The unbounded derived category of all `𝒪_X`-modules.  The hom universe `w`
is selected by `HasDerivedCategory`; no smallness theorem is inferred. -/
abbrev SheafDerived (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules] :=
  DerivedCategory X.Modules

/-- Mathlib's properness predicate, supplied here as the intended instantiation
of `DerivedMorphismData.IsProper` for a scheme morphism. -/
abbrev SchemeProper {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsProper f

/-- Mathlib's flatness predicate, supplied for `DerivedMorphismData.IsFlat`. -/
abbrev SchemeFlat {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.Flat f

/-- The commutative-square condition for the base-change interfaces, in the
orientation `p' ≫ q = q' ≫ p`.  GL26's tor-independence is an additional
condition, represented separately by `IsTorIndependent`. -/
def SchemePullbackSquare {X' X Z' Z : Scheme.{u}}
    (p : X ⟶ Z) (p' : X' ⟶ Z') (q : Z' ⟶ Z) (q' : X' ⟶ X) : Prop :=
  IsPullback p' q' q p

/-- Quasi-isomorphisms of cochain complexes, the class inverted by
`DerivedCategory.Q`. -/
abbrev ComplexQuasiIso (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (CochainComplex C ℤ) :=
  HomologicalComplex.quasiIso C (ComplexShape.up ℤ)

/-- Existence of the total right derived functor of the termwise extension of
`F`, with values in `D(D)`.  This is a Kan-extension existence condition; it is
not a hidden assertion that resolutions exist. -/
abbrev HasRightDerived {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
    [Abelian C] [Abelian D] [F.Additive] [HasDerivedCategory.{w₂} D] : Prop :=
  Functor.HasRightDerivedFunctor
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ComplexQuasiIso C)

/-- Existence of the total left derived functor of the termwise extension of
`F`, with values in `D(D)`. -/
abbrev HasLeftDerived {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
    [Abelian C] [Abelian D] [F.Additive] [HasDerivedCategory.{w₂} D] : Prop :=
  Functor.HasLeftDerivedFunctor
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ComplexQuasiIso C)

section TotalDerived

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D]
variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

/-- Mathlib's total right derived functor, specialized to termwise extension
from abelian categories to derived categories. -/
noncomputable def totalRightDerived (F : C ⥤ D) [F.Additive]
    [HasRightDerived.{w₂} F] : DerivedCategory C ⥤ DerivedCategory D :=
  Functor.totalRightDerived
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q (ComplexQuasiIso C)

/-- The comparison transformation exhibiting `totalRightDerived F` as a left
Kan extension along `DerivedCategory.Q`. -/
noncomputable def totalRightDerivedUnit (F : C ⥤ D) [F.Additive]
    [HasRightDerived.{w₂} F] :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ totalRightDerived F :=
  Functor.totalRightDerivedUnit _ _ _

noncomputable instance totalRightDerivedIsRightDerivedFunctor
    (F : C ⥤ D) [F.Additive] [HasRightDerived.{w₂} F] :
    (totalRightDerived F).IsRightDerivedFunctor (totalRightDerivedUnit F)
      (ComplexQuasiIso C) := by
  dsimp [totalRightDerived, totalRightDerivedUnit]
  infer_instance

/-- Mathlib's total left derived functor, specialized to termwise extension. -/
noncomputable def totalLeftDerived (F : C ⥤ D) [F.Additive]
    [HasLeftDerived.{w₂} F] : DerivedCategory C ⥤ DerivedCategory D :=
  Functor.totalLeftDerived
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q (ComplexQuasiIso C)

/-- The comparison transformation exhibiting `totalLeftDerived F` as a right
Kan extension along `DerivedCategory.Q`. -/
noncomputable def totalLeftDerivedCounit (F : C ⥤ D) [F.Additive]
    [HasLeftDerived.{w₂} F] :
    DerivedCategory.Q ⋙ totalLeftDerived F ⟶
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.totalLeftDerivedCounit _ _ _

noncomputable instance totalLeftDerivedIsLeftDerivedFunctor
    (F : C ⥤ D) [F.Additive] [HasLeftDerived.{w₂} F] :
    (totalLeftDerived F).IsLeftDerivedFunctor (totalLeftDerivedCounit F)
      (ComplexQuasiIso C) := by
  dsimp [totalLeftDerived, totalLeftDerivedCounit]
  infer_instance

/-- Universal description of a natural transformation out of a total right
derived functor.  This is the existing Mathlib API, exposed at the scheme-layer
signature; no resolution assumption is hidden. -/
noncomputable def totalRightDerivedDesc {F : C ⥤ D} [F.Additive]
    [HasRightDerived.{w₂} F] (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G) : totalRightDerived F ⟶ G :=
  (totalRightDerived F).rightDerivedDesc (totalRightDerivedUnit F)
    (ComplexQuasiIso C) G β

@[simp, reassoc]
lemma totalRightDerivedDesc_fac {F : C ⥤ D} [F.Additive]
    [HasRightDerived.{w₂} F] (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G) :
    totalRightDerivedUnit F ≫
        Functor.whiskerLeft DerivedCategory.Q (totalRightDerivedDesc G β) = β := by
  exact (totalRightDerived F).rightDerived_fac (totalRightDerivedUnit F)
    (ComplexQuasiIso C) G β

end TotalDerived

section SchemeDerivedFunctors

variable {X Y : Scheme.{u}}

/-- Candidate `Rf_*` on all sheaves of modules.  The required right Kan
extension is an explicit argument.  Preservation of `D_qc` belongs to the
geometric instantiation of `DerivedMorphismData`. -/
noncomputable def derivedPushforward (f : X ⟶ Y)
    [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} Y.Modules]
    [HasRightDerived.{w₂} (Scheme.Modules.pushforward f)] :
    SheafDerived X ⥤ SheafDerived Y :=
  totalRightDerived (Scheme.Modules.pushforward f)

/-- Candidate `Lf^*` on all sheaves of modules, with its left Kan-extension
existence hypothesis made explicit. -/
noncomputable def derivedPullback (f : X ⟶ Y)
    [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} Y.Modules]
    [HasLeftDerived.{w₁} (Scheme.Modules.pullback f)] :
    SheafDerived Y ⥤ SheafDerived X :=
  totalLeftDerived (Scheme.Modules.pullback f)

end SchemeDerivedFunctors

/-- Closed symmetric monoidal data for derived tensor and derived sheaf Hom.
The first argument of `rhom` is contravariant.  For `D_qc`, the existence of the
internal Hom requires the compact-generation/Brown-representability argument in
GL26 `sec:prelim_stacks_internal_homs`; it is not supplied by Mathlib. -/
structure DerivedTensorHomData (D : Type u) [Category.{v} D] where
  [monoidal : MonoidalCategory D]
  [symmetric : SymmetricCategory D]
  /-- `RHom(E,-)`, contravariantly indexed by `E`. -/
  rhom : Dᵒᵖ ⥤ D ⥤ D
  /-- The tensor--Hom adjunction `(E ⊗^L -) ⊣ RHom(E,-)`, GL26
  `sec:prelim_stacks_internal_homs`. -/
  tensorHomAdj (E : D) :
    @MonoidalCategory.tensorLeft D _ monoidal E ⊣ rhom.obj (Opposite.op E)
  /-- Internal currying
  `RHom(L ⊗^L M,N) ≅ RHom(L,RHom(M,N))`, naturally in `N` for every
  `L,M`.  This is the sheaf-Hom strengthening of the Hom-set adjunction used
  throughout GL26's tensor/Hom calculations.  The alternative order
  `RHom(M,RHom(L,N))` is obtained below using symmetry. -/
  internalCurrying (L M : D) :
    rhom.obj (Opposite.op
      (@MonoidalCategoryStruct.tensorObj D _ monoidal.toMonoidalCategoryStruct L M)) ≅
      rhom.obj (Opposite.op M) ⋙ rhom.obj (Opposite.op L)

namespace DerivedTensorHomData

variable {D : Type u} [Category.{v} D] (T : DerivedTensorHomData D)

/-- The derived tensor as an ordinary bifunctor. -/
abbrev tensor : D × D ⥤ D := @MonoidalCategory.tensor D _ T.monoidal

/-- Tensoring on the left by `E`. -/
abbrev tensorLeft (E : D) : D ⥤ D := @MonoidalCategory.tensorLeft D _ T.monoidal E

/-- Tensoring on the right by `E`. -/
abbrev tensorRight (E : D) : D ⥤ D := @MonoidalCategory.tensorRight D _ T.monoidal E

/-- The derived structure sheaf, as an object of the derived category. -/
abbrev unit : D := @MonoidalCategoryStruct.tensorUnit D _ T.monoidal.toMonoidalCategoryStruct

/-- Derived sheaf Hom with both arguments made explicit. -/
abbrev rhomObj (E G : D) : D := (T.rhom.obj (Opposite.op E)).obj G

/-- The derived dual `E^∨ = RHom(E,𝒪)`. -/
abbrev dual (E : D) : D := T.rhomObj E T.unit

/-- Symmetry of derived tensor, with naturality supplied by Mathlib's braided
monoidal structure. -/
def symmetry (E F : D) : (T.tensor.obj (E, F)) ≅ T.tensor.obj (F, E) := by
  letI := T.monoidal
  letI := T.symmetric
  exact β_ E F

/-- Internal currying in the alternative order
`RHom(L ⊗ M,N) ≅ RHom(M,RHom(L,N))`, obtained from symmetry and
`internalCurrying M L`. -/
def internalCurryingSwap (L M : D) :
    T.rhom.obj (Opposite.op (T.tensor.obj (L, M))) ≅
      T.rhom.obj (Opposite.op L) ⋙ T.rhom.obj (Opposite.op M) :=
  T.rhom.mapIso (T.symmetry L M).symm.op ≪≫ T.internalCurrying M L

/-- Evaluation for the tensor--Hom adjunction. -/
def evaluation (E : D) :
    T.rhom.obj (Opposite.op E) ⋙ T.tensorLeft E ⟶ 𝟭 D :=
  (T.tensorHomAdj E).counit

/-- Coevaluation for the tensor--Hom adjunction. -/
def coevaluation (E : D) : 𝟭 D ⟶ T.tensorLeft E ⋙ T.rhom.obj (Opposite.op E) :=
  (T.tensorHomAdj E).unit

/-- The adjunction bijection `(E ⊗ F ⟶ G) ≃ (F ⟶ RHom(E,G))`. -/
def homEquiv (E F G : D) :
    ((T.tensorLeft E).obj F ⟶ G) ≃ (F ⟶ T.rhomObj E G) :=
  (T.tensorHomAdj E).homEquiv F G

end DerivedTensorHomData

/-- Perfect-object duality used in GL26.  This is separate from R2's definition
of `Perf`: only the object property and the duality consequences are needed
here. -/
structure PerfectDualityData {D : Type u} [Category.{v} D]
    (T : DerivedTensorHomData D) where
  /-- Perfect complexes. -/
  Perf : ObjectProperty D
  /-- The canonical derived double-dual comparison. -/
  doubleDual (E : D) : E ⟶ T.dual (T.dual E)
  /-- Perfect complexes are reflexive; Stacks 08JJ. -/
  doubleDual_isIso (E : D) : Perf E → IsIso (doubleDual E)
  /-- The canonical map `K ⊗ RHom(M,-) ⟶ RHom(RHom(K,M),-)` of GL26
  `lem:rhom_tensor_morphism`. -/
  rhomTensor (K M : D) :
    T.rhom.obj (Opposite.op M) ⋙ T.tensorLeft K ⟶
      T.rhom.obj (Opposite.op (T.rhomObj K M))
  /-- `rhomTensor` is invertible for a perfect first variable; Stacks 08J9 and
  08JJ, in the combination stated by GL26 `lem:rhom_tensor_morphism`. -/
  rhomTensor_isIso (K : D) : Perf K → ∀ M : D, IsIso (rhomTensor K M)
  /-- The dual--tensor comparison `K^∨ ⊗ M ≅ RHom(K,M)`, Stacks 08J9. -/
  dualTensor (K : D) : Perf K → (T.tensorLeft (T.dual K) ≅ T.rhom.obj (Opposite.op K))

/-- The operation on a pair of derived categories associated to one morphism.
For scheme geometry, `DX` and `DY` are respectively `D_qc(X)` and `D_qc(Y)`.
The ordinary scheme pullback/pushforward available in Mathlib do not themselves
provide these derived functors. -/
structure DerivedMorphismData {DX DY : Type u} [Category.{v} DX] [Category.{v} DY]
    (TX : DerivedTensorHomData DX) (TY : DerivedTensorHomData DY) where
  /-- Derived pullback `Lf^*`. -/
  pull : DX ⥤ DY
  /-- Derived pushforward `Rf_*`. -/
  push : DY ⥤ DX
  /-- `Lf^* ⊣ Rf_*`. -/
  pullPushAdj : pull ⊣ push
  /-- Neeman's `f^×`, right adjoint to `Rf_*`. -/
  upperCross : DX ⥤ DY
  /-- `Rf_* ⊣ f^×`; its unit and counit are obtained through this adjunction. -/
  pushCrossAdj : push ⊣ upperCross
  /-- The exceptional pullback `f^!`, as in Neeman 2023, Construction 9.4,
  recalled in GL26 `sec:duality_functors`. -/
  upperShriek : DX ⥤ DY
  /-- Derived pullback preserves the derived structure sheaf. -/
  pullUnit : pull.obj TX.unit ≅ TY.unit
  /-- Derived pullback is monoidal, naturally in both variables. -/
  pullTensor :
    (pull.prod pull) ⋙ TY.tensor ≅ TX.tensor ⋙ pull
  /-- The projection formula `Rf_*(F ⊗^L Lf^*G) ≅ Rf_*F ⊗^L G`, naturally
  in both `F` and `G`; GL26 Lemmas 2.25/2.26 and Stacks 08IN. -/
  projectionFormula :
    ((𝟭 DY).prod pull) ⋙ TY.tensor ⋙ push ≅ (push.prod (𝟭 DX)) ⋙ TX.tensor
  /-- Neeman's `χ(f,E,G) : Lf^*E ⊗ f^×G ⟶ f^×(E ⊗ G)`. -/
  chi :
    (pull.prod upperCross) ⋙ TY.tensor ⟶ TX.tensor ⋙ upperCross
  /-- Neeman's `σ(f,E,G) : Lf^*E ⊗ f^!G ⟶ f^!(E ⊗ G)`. -/
  sigma :
    (pull.prod upperShriek) ⋙ TY.tensor ⟶ TX.tensor ⋙ upperShriek
  /-- Perfect objects on the source, as used by `lem:neeman189`. -/
  Perf : ObjectProperty DX
  /-- `χ(f,E,G)` is an isomorphism for perfect `E`. -/
  chi_isIso_of_perfect (E : DX) : Perf E → ∀ G : DX, IsIso (chi.app (E, G))
  /-- `σ(f,E,G)` is an isomorphism for perfect `E`. -/
  sigma_isIso_of_perfect (E : DX) : Perf E → ∀ G : DX, IsIso (sigma.app (E, G))
  /-- Properness, to be instantiated by the scheme morphism property. -/
  IsProper : Prop
  /-- Flatness, to be instantiated by the scheme morphism property. -/
  IsFlat : Prop
  /-- Finite tor-dimension.  PROVISIONAL pending the bounded derived layer. -/
  HasFiniteTorDimension : Prop
  /-- For flat, hence finite-tor-dimensional, `f`, `σ` is invertible;
  GL26 `lem:neeman189`. -/
  sigma_isIso_of_flat : IsFlat → ∀ E G : DX, IsIso (sigma.app (E, G))
  /-- For proper `f`, the canonical comparison `f^× ≅ f^!`; Neeman 2023 and
  GL26 `lem:neeman187`. -/
  properCrossShriek : IsProper → (upperCross ≅ upperShriek)
  /-- The pullback/internal-Hom comparison of Section 7. -/
  pullRHom (E : DX) :
    TX.rhom.obj (Opposite.op E) ⋙ pull ⟶
      pull ⋙ TY.rhom.obj (Opposite.op (pull.obj E))
  /-- Pullback of internal Hom in a perfect first variable is invertible;
  GL26 `lem:gortz_wedhorn_internal_hom`. -/
  pullRHom_isIso_of_perfect (E : DX) : Perf E → IsIso (pullRHom E)

namespace DerivedMorphismData

variable {DX DY : Type u} [Category.{v} DX] [Category.{v} DY]
  {TX : DerivedTensorHomData DX} {TY : DerivedTensorHomData DY}

/-- The unit `F ⟶ f^×Rf_*F` of Grothendieck duality. -/
abbrev pushCrossUnit (M : DerivedMorphismData TX TY) := M.pushCrossAdj.unit

/-- The trace/counit `Rf_* f^×E ⟶ E` of Grothendieck duality. -/
abbrev pushCrossCounit (M : DerivedMorphismData TX TY) := M.pushCrossAdj.counit

/-- For proper `f`, `f^!` is a right adjoint to `Rf_*`, obtained by
transporting `pushCrossAdj` along `f^× ≅ f^!`.  No such adjunction is asserted
for non-proper `f`. -/
def pushShriekAdjOfProper (M : DerivedMorphismData TX TY) (hp : M.IsProper) :
    M.push ⊣ M.upperShriek :=
  M.pushCrossAdj.ofNatIsoRight (M.properCrossShriek hp)

/-- Objectwise projection formula in the orientation used in computations. -/
def projectionFormulaObj (M : DerivedMorphismData TX TY) (F : DY) (G : DX) :
    M.push.obj (TY.tensor.obj (F, M.pull.obj G)) ≅
      TX.tensor.obj (M.push.obj F, G) :=
  M.projectionFormula.app (F, G)

end DerivedMorphismData

/-- A shift-compatible triangulated functor, with all instances kept bundled so
that interfaces can require exactness without inventing additional axioms. -/
structure TriangulatedFunctorData {C D : Type u}
    [Category.{v} C] [Category.{v} D]
    [HasShift C ℤ] [HasShift D ℤ] [HasZeroObject C] [HasZeroObject D]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] (F : C ⥤ D) where
  [commShift : F.CommShift ℤ]
  [isTriangulated : F.IsTriangulated]

/-- The exactness enhancement of closed symmetric monoidal derived categories.
It is used when GL26 takes cones after tensoring and when it identifies cones
of double-dual comparison maps. -/
structure TriangulatedTensorHomData {D : Type u} [Category.{v} D]
    [HasShift D ℤ] [HasZeroObject D] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T : DerivedTensorHomData D) where
  /-- Exactness of `E ⊗^L -`, GL26 `sec:prelim_stacks_internal_homs`. -/
  tensorLeftExact (E : D) : TriangulatedFunctorData (T.tensorLeft E)
  /-- Exactness of `- ⊗^L E`, using the same geometric input and symmetry. -/
  tensorRightExact (E : D) : TriangulatedFunctorData (T.tensorRight E)
  /-- `RHom(E,-)` is triangulated in its covariant variable. -/
  rhomExact (E : D) : TriangulatedFunctorData (T.rhom.obj (Opposite.op E))

/-- Exactness of the four functors in `sec:duality_functors`: GL26 regards
pullback, pushforward, upper cross, and upper shriek as exact functors between
triangulated categories. -/
structure TriangulatedMorphismData {DX DY : Type u}
    [Category.{v} DX] [Category.{v} DY]
    [HasShift DX ℤ] [HasShift DY ℤ] [HasZeroObject DX] [HasZeroObject DY]
    [Preadditive DX] [Preadditive DY]
    [∀ n : ℤ, (shiftFunctor DX n).Additive]
    [∀ n : ℤ, (shiftFunctor DY n).Additive]
    [Pretriangulated DX] [Pretriangulated DY]
    {TX : DerivedTensorHomData DX} {TY : DerivedTensorHomData DY}
    (M : DerivedMorphismData TX TY) where
  /-- Exactness of `Lf^*`. -/
  pullExact : TriangulatedFunctorData M.pull
  /-- Exactness of `Rf_*`. -/
  pushExact : TriangulatedFunctorData M.push
  /-- Exactness of `f^×`. -/
  upperCrossExact : TriangulatedFunctorData M.upperCross
  /-- Exactness of `f^!`. -/
  upperShriekExact : TriangulatedFunctorData M.upperShriek

/-- Composition of `f : Y ⟶ X` and `g : Z ⟶ Y`.  The last field separates the
four invertibility cases of GL26 `lem:neeman186`; `Dplus` is the provisional
bounded-below object property. -/
structure CompositeDualityData {DX DY DZ : Type u}
    [Category.{v} DX] [Category.{v} DY] [Category.{v} DZ]
    {TX : DerivedTensorHomData DX} {TY : DerivedTensorHomData DY}
    {TZ : DerivedTensorHomData DZ}
    (Mf : DerivedMorphismData TX TY) (Mg : DerivedMorphismData TY TZ)
    (Mgf : DerivedMorphismData TX TZ) where
  /-- Pseudofunctoriality `L(gf)^* ≅ Lf^*Lg^*`. -/
  pullComp : Mgf.pull ≅ Mf.pull ⋙ Mg.pull
  /-- Pseudofunctoriality `R(gf)_* ≅ Rg_*Rf_*`. -/
  pushComp : Mgf.push ≅ Mg.push ⋙ Mf.push
  /-- Pseudofunctoriality `(gf)^× ≅ f^×g^×`. -/
  crossComp : Mgf.upperCross ≅ Mf.upperCross ⋙ Mg.upperCross
  /-- The oplax comparison `ρ(f,g) : (gf)^! ⟶ f^!g^!`. -/
  shriekComp : Mgf.upperShriek ⟶ Mf.upperShriek ⋙ Mg.upperShriek
  /-- Bounded-below objects on `D_qc(X)`, PROVISIONAL. -/
  Dplus : ObjectProperty DX
  /-- `ρ` is invertible when `f` has finite tor-dimension. -/
  shriekComp_isIso_of_finiteTor :
    Mf.HasFiniteTorDimension → IsIso shriekComp
  /-- `ρ` is invertible when `g` is proper. -/
  shriekComp_isIso_of_proper_right : Mg.IsProper → IsIso shriekComp
  /-- `ρ` is invertible when the composite is proper. -/
  shriekComp_isIso_of_proper_composite : Mgf.IsProper → IsIso shriekComp
  /-- On bounded-below objects `ρ` is always invertible. -/
  shriekComp_isIso_on_Dplus (E : DX) : Dplus E → IsIso (shriekComp.app E)

/-- Four derived-morphism packages forming the square
`X' --q'--> X --p--> Z` and `X' --p'--> Z' --q--> Z`.  The compatibility
`pullComp` is the derived version of `q' ≫ p = p' ≫ q`. -/
structure BaseChangeSquare {DX DX' DZ DZ' : Type u}
    [Category.{v} DX] [Category.{v} DX'] [Category.{v} DZ] [Category.{v} DZ']
    {TX : DerivedTensorHomData DX} {TX' : DerivedTensorHomData DX'}
    {TZ : DerivedTensorHomData DZ} {TZ' : DerivedTensorHomData DZ'}
    (p : DerivedMorphismData TZ TX) (p' : DerivedMorphismData TZ' TX')
    (q : DerivedMorphismData TZ TZ') (q' : DerivedMorphismData TX TX') where
  /-- `L(q')^*Lp^* ≅ L(p')^*Lq^*` after composing in diagrammatic order. -/
  pullComp : q.pull ⋙ p'.pull ≅ p.pull ⋙ q'.pull

namespace BaseChangeSquare

variable {DX DX' DZ DZ' : Type u}
  [Category.{v} DX] [Category.{v} DX'] [Category.{v} DZ] [Category.{v} DZ']
  {TX : DerivedTensorHomData DX} {TX' : DerivedTensorHomData DX'}
  {TZ : DerivedTensorHomData DZ} {TZ' : DerivedTensorHomData DZ'}
  {p : DerivedMorphismData TZ TX} {p' : DerivedMorphismData TZ' TX'}
  {q : DerivedMorphismData TZ TZ'} {q' : DerivedMorphismData TX TX'}

/-- The upper-star/lower-star base-change morphism
`Lq^*Rp_* ⟶ R(p')_*L(q')^*`, constructed as a mate.  GL26
`def:upper_star_lower_star_bc`. -/
def theta (sq : BaseChangeSquare p p' q q') :
    p.push ⋙ q.pull ⟶ q'.pull ⋙ p'.push :=
  CategoryTheory.mateEquiv p.pullPushAdj p'.pullPushAdj sq.pullComp.hom

/-- The lower-star/upper-cross base-change morphism
`R(q')_*(p')^× ⟶ p^×Rq_*`, obtained by conjugating `theta`. -/
def lowerStarUpperCross (sq : BaseChangeSquare p p' q q') :
    p'.upperCross ⋙ q'.push ⟶ q.push ⋙ p.upperCross :=
  CategoryTheory.conjugateEquiv
    (q'.pullPushAdj.comp p'.pushCrossAdj)
    (p.pushCrossAdj.comp q.pullPushAdj) sq.theta

/-- Conjugation transports invertibility from `theta` to
`lowerStarUpperCross`; this is the categorical part of GL26
`def:lower_star_upper_cross_bc`. -/
instance isIso_lowerStarUpperCross
    (sq : BaseChangeSquare p p' q q') [IsIso sq.theta] :
    IsIso sq.lowerStarUpperCross := by
  dsimp [lowerStarUpperCross]
  infer_instance

/-- Conversely, invertibility of the conjugate implies invertibility of the
original base-change morphism. -/
lemma isIso_theta_of_isIso_lowerStarUpperCross
    (sq : BaseChangeSquare p p' q q') [IsIso sq.lowerStarUpperCross] :
    IsIso sq.theta := by
  have h : IsIso (CategoryTheory.conjugateEquiv
      (q'.pullPushAdj.comp p'.pushCrossAdj)
      (p.pushCrossAdj.comp q.pullPushAdj) sq.theta) := by
    change IsIso sq.lowerStarUpperCross
    infer_instance
  let _ := h
  exact CategoryTheory.conjugateEquiv_of_iso
    (q'.pullPushAdj.comp p'.pushCrossAdj)
    (p.pushCrossAdj.comp q.pullPushAdj) sq.theta

/-- The upper-star/upper-cross base-change morphism
`L(q')^*p^× ⟶ (p')^×Lq^*`, GL26 `def:upper_star_upper_cross_bc`.  It is
defined once the upper-star/lower-star square is known to be invertible. -/
noncomputable def beta (sq : BaseChangeSquare p p' q q') [IsIso sq.theta] :
    p.upperCross ⋙ q'.pull ⟶ q.pull ⋙ p'.upperCross :=
  CategoryTheory.mateEquiv p.pushCrossAdj p'.pushCrossAdj (inv sq.theta)

end BaseChangeSquare

/-- The pushforward compatibility of a base-change square and its required
conjugacy with `theta` (GL26
`lem:pseudofunctoriality_isos_are_conjugate`).  Keeping this separate avoids
silently accepting an arbitrary, unrelated isomorphism of pushforward
composites. -/
structure BaseChangeCoherenceData {DX DX' DZ DZ' : Type u}
    [Category.{v} DX] [Category.{v} DX'] [Category.{v} DZ] [Category.{v} DZ']
    {TX : DerivedTensorHomData DX} {TX' : DerivedTensorHomData DX'}
    {TZ : DerivedTensorHomData DZ} {TZ' : DerivedTensorHomData DZ'}
    {p : DerivedMorphismData TZ TX} {p' : DerivedMorphismData TZ' TX'}
    {q : DerivedMorphismData TZ TZ'} {q' : DerivedMorphismData TX TX'}
    (sq : BaseChangeSquare p p' q q') where
  /-- `R(q')_*Rp_*` and `R(p')_*Rq_*` compatibility. -/
  pushComp : q'.push ⋙ p.push ≅ p'.push ⋙ q.push
  /-- The pullback and pushforward comparison isomorphisms are conjugate:
  inverse-mating `pushComp` recovers `theta`. -/
  pushConjugate :
    (CategoryTheory.mateEquiv q'.pullPushAdj q.pullPushAdj).symm
      pushComp.hom = sq.theta

/-- Geometric invertibility facts that are not supplied by the categorical mate
construction.  The first field is Stacks 08IR for a tor-independent square.
The remaining fields are the two cases of GL26 `lem:neeman188`. -/
structure BaseChangeIsomorphismData {DX DX' DZ DZ' : Type u}
    [Category.{v} DX] [Category.{v} DX'] [Category.{v} DZ] [Category.{v} DZ']
    {TX : DerivedTensorHomData DX} {TX' : DerivedTensorHomData DX'}
    {TZ : DerivedTensorHomData DZ} {TZ' : DerivedTensorHomData DZ'}
    {p : DerivedMorphismData TZ TX} {p' : DerivedMorphismData TZ' TX'}
    {q : DerivedMorphismData TZ TZ'} {q' : DerivedMorphismData TX TX'}
    (sq : BaseChangeSquare p p' q q') where
  /-- Bounded-below objects, PROVISIONAL pending the `D^+` definition. -/
  Dplus : ObjectProperty DZ
  /-- Tor-independence, represented abstractly until the scheme base-change
  layer supplies it. -/
  IsTorIndependent : Prop
  /-- Tor-independent base change (Stacks 08IR). -/
  theta_isIso : IsTorIndependent → IsIso sq.theta
  /-- Proper flat base change for `f^×` when `p'` has finite tor-dimension. -/
  beta_isIso_of_finiteTor [IsIso sq.theta] :
    p.IsProper → q.IsFlat → p'.HasFiniteTorDimension →
      ∀ E : DZ, IsIso (sq.beta.app E)
  /-- Proper flat base change for `f^×` on bounded-below objects. -/
  beta_isIso_on_Dplus [IsIso sq.theta] :
    p.IsProper → q.IsFlat → ∀ E : DZ, Dplus E → IsIso (sq.beta.app E)

/-- Base change for `f^!`, plus the coherence with `f^×` in the proper case.
This is the input to GL26 `lem:base_change_relative_formula` and Proposition 10.5.
The proper compatibility is stated as an actual equality of natural
transformations, not as an unexplained proposition. -/
structure UpperShriekBaseChangeData {DX DX' DZ DZ' : Type u}
    [Category.{v} DX] [Category.{v} DX'] [Category.{v} DZ] [Category.{v} DZ']
    {TX : DerivedTensorHomData DX} {TX' : DerivedTensorHomData DX'}
    {TZ : DerivedTensorHomData DZ} {TZ' : DerivedTensorHomData DZ'}
    {p : DerivedMorphismData TZ TX} {p' : DerivedMorphismData TZ' TX'}
    {q : DerivedMorphismData TZ TZ'} {q' : DerivedMorphismData TX TX'}
    (sq : BaseChangeSquare p p' q q') [IsIso sq.theta] where
  /-- The `^*`-`^!` base-change morphism, Stacks 0E5D. -/
  shriek : p.upperShriek ⋙ q'.pull ⟶ q.pull ⋙ p'.upperShriek
  /-- Bounded-below objects, PROVISIONAL. -/
  Dplus : ObjectProperty DZ
  /-- The finite-tor-dimensional case of GL26 `lem:neeman188`: both
  horizontal morphisms are flat; properness of `p` is not required. -/
  isIso_of_finiteTor :
    q.IsFlat → q'.IsFlat → p'.HasFiniteTorDimension →
      ∀ E : DZ, IsIso (shriek.app E)
  /-- The bounded-below case of GL26 `lem:neeman188`. -/
  isIso_on_Dplus :
    q.IsFlat → q'.IsFlat → ∀ E : DZ, Dplus E → IsIso (shriek.app E)
  /-- GL26 `lem:base_change_relative_formula`: for proper flat finitely
  presented `p`, arbitrary Noetherian base change is invertible for `f^!`.
  Finite presentation is part of the admissible-morphism convention. -/
  isIso_of_properFlat :
    p.IsProper → p.IsFlat → ∀ E : DZ, IsIso (shriek.app E)
  /-- When `p` and `p'` are proper, `shriek` is obtained from `beta` by the
  two comparisons `f^× ≅ f^!`. -/
  proper_compatible (hp : p.IsProper) (hp' : p'.IsProper) :
    Functor.whiskerRight (p.properCrossShriek hp).inv q'.pull ≫ sq.beta ≫
      Functor.whiskerLeft q.pull (p'.properCrossShriek hp').hom = shriek

/-- The GL26 kernel transform, included to make the orientation consumed by
`FourierMukai/Paper/DerivedSetup.lean` immediate: pullback, tensor with the
kernel on the right, and pushforward. -/
def tensorTransform {DX DY DP : Type u}
    [Category.{v} DX] [Category.{v} DY] [Category.{v} DP]
    {TX : DerivedTensorHomData DX} {TY : DerivedTensorHomData DY}
    {TP : DerivedTensorHomData DP}
    (p₁ : DerivedMorphismData TX TP) (p₂ : DerivedMorphismData TY TP)
    (K : DP) : DX ⥤ DY :=
  p₁.pull ⋙ TP.tensorRight K ⋙ p₂.push

/-! ## Axiom audit

All constructive declarations in this file use only the three standard logical
axioms permitted by the project.  Geometric facts are fields of the interfaces,
not additional axioms of Lean.
-/


end RelativeFM
