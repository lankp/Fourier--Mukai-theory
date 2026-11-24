/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Paper.DerivedSetup
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# GL26 for Noetherian schemes: the statement layer

A sorry-free restatement of the ten GL26 targets over Noetherian schemes, under
`RelativeFM.Noetherian`.  Every target is a `def ...Statement : Prop`, so the
layer compiles without a single `sorry`; the paper labels and Stacks tags are in
the docstrings.

The interface is built on actual schemes: `MorphismContext` carries a morphism
`f : Y ⟶ X` of Noetherian schemes with `Subcats` for `D_qc`, `D^b_coh` and
`Perf`; `FMContext` carries the two projections, the kernel and the transform;
`IsProperFlat`, `IsRelativelyPerfect`, `IsQuasiPerfect`, `EquivalenceOnDcoh`,
`FibreContext`, `FMSetup` and the `FM`/`fm` loci follow the paper's definitions.

Corrections relative to `FourierMukai/Paper/Statements.lean`: no vacuous `True`
hypothesis survives; Theorem 1.3 uses pseudocoherence; Corollary 6.18 carries its
boundedness hypothesis; Theorem 1.6 states full closed-fibre descent and ascent;
Theorem 1.7 asks for an autoequivalence of `D^b_coh`; and `DiagonalIdealData`
records the distinguished triangle identifying the ideal sheaf `I_Δ`.

Found by a member of the Ultramath run `smwuyku7t` (direction R4).
-/

@[expose] public section

namespace RelativeFM.Noetherian

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open AlgebraicGeometry

universe w u v

/- Hypotheses of a `...Statement` are deliberately absent from its conclusion:
they are universally quantified premises of the resulting specification. -/
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-- The four object predicates used by GL26, reused from the scheme-independent
interface.  See GL26 §2.2.2 and the authors' convention that, on a Noetherian
space, pseudocoherent objects of `D_qc` are precisely objects of `D^-_coh`. -/
abbrev Subcats (D : Type u) [Category.{v} D] := RelativeFM.Subcats D

/-! ## One morphism and relative perfectness -/

/-- The derived and geometric data attached to a morphism `f : Y ⟶ X` of
Noetherian schemes.  This is the scheme-level replacement for the abstract
algebraic-space `MorphismContext`.

The adjunction is Stacks 07A6.  Construction of the functors themselves, and of
the derived tensor product, belongs to the `D_qc`/derived-tensor layers. -/
structure MorphismContext (DX DY : Type u) [Category.{v} DX] [Category.{v} DY] where
  /-- The target scheme. -/
  X : Scheme.{w}
  /-- The source scheme. -/
  Y : Scheme.{w}
  /-- The underlying morphism of schemes. -/
  f : Y ⟶ X
  [noetherianX : IsNoetherian X]
  [noetherianY : IsNoetherian Y]
  /-- `Lf^* : D_qc(X) ⥤ D_qc(Y)`. -/
  pull : DX ⥤ DY
  /-- `Rf_* : D_qc(Y) ⥤ D_qc(X)`. -/
  push : DY ⥤ DX
  /-- `Lf^* ⊣ Rf_*` (Stacks 07A6). -/
  adj : pull ⊣ push
  /-- The endofunctor `(-) ⊗^L E` on `D_qc(Y)`. -/
  tensorRight : DY → DY ⥤ DY

namespace MorphismContext

variable {DX DY : Type u} [Category.{v} DX] [Category.{v} DY]

/-- Properness is the actual Mathlib predicate on the underlying scheme morphism. -/
def IsProper (M : MorphismContext DX DY) : Prop := AlgebraicGeometry.IsProper M.f

/-- Flatness is the actual Mathlib predicate on the underlying scheme morphism. -/
def IsFlat (M : MorphismContext DX DY) : Prop := AlgebraicGeometry.Flat M.f

/-- **GL26 Definition 4.1** (`def:relative_perf_stacks`).  An object `E` is
`f`-perfect when `E ⊗^L Lf^* A` is bounded with quasicoherent cohomology for
every `A ∈ D^b_qc(X)`. -/
def IsRelativelyPerfect (M : MorphismContext DX DY)
    (SX : Subcats DX) (SY : Subcats DY) (E : DY) : Prop :=
  ∀ A : DX, SX.DbQc A → SY.DbQc ((M.tensorRight E).obj (M.pull.obj A))

/-- **GL26 Definition 5.1** (`def:quasi_perf`).  An object `E` is
`f`-quasi-perfect when `Rf_*(E ⊗^L P)` is perfect for every perfect `P`. -/
def IsQuasiPerfect (M : MorphismContext DX DY)
    (SX : Subcats DX) (SY : Subcats DY) (E : DY) : Prop :=
  ∀ P : DY, SY.Perf P → SX.Perf (M.push.obj ((M.tensorRight E).obj P))

end MorphismContext

/-! ## A relative Fourier--Mukai square -/

/-- The geometric and derived data of GL26's fixed-base diagram for
`Y₁ ×_S Y₂`.  `pr1` and `pr2` are the usual projections.

The transform from the first factor pulls along `pr1` and pushes along `pr2`;
the names `pullFromOne`, `pushToTwo`, etc. record object transportation, avoiding
the paper's interchange of the indices in `f'_1` and `f'_2`. -/
structure FMContext (D1 D2 DP : Type u) [Category.{v} D1] [Category.{v} D2]
    [Category.{v} DP] where
  /-- The base Noetherian scheme. -/
  Base : Scheme.{w}
  /-- The first family. -/
  Y1 : Scheme.{w}
  /-- The second family. -/
  Y2 : Scheme.{w}
  /-- A model of the fibre product. -/
  Prod : Scheme.{w}
  [noetherianBase : IsNoetherian Base]
  [noetherianY1 : IsNoetherian Y1]
  [noetherianY2 : IsNoetherian Y2]
  [noetherianProd : IsNoetherian Prod]
  /-- `f₁ : Y₁ ⟶ S`. -/
  f1 : Y1 ⟶ Base
  /-- `f₂ : Y₂ ⟶ S`. -/
  f2 : Y2 ⟶ Base
  /-- The first projection `Y₁ ×_S Y₂ ⟶ Y₁`. -/
  pr1 : Prod ⟶ Y1
  /-- The second projection `Y₁ ×_S Y₂ ⟶ Y₂`. -/
  pr2 : Prod ⟶ Y2
  /-- The displayed square is Cartesian. -/
  square : IsPullback pr1 pr2 f1 f2
  /-- `Lpr₁^* : D_qc(Y₁) ⥤ D_qc(Y₁ ×_S Y₂)`. -/
  pullFromOne : D1 ⥤ DP
  /-- `Rpr₁_* : D_qc(Y₁ ×_S Y₂) ⥤ D_qc(Y₁)`. -/
  pushToOne : DP ⥤ D1
  /-- The pullback-pushforward adjunction for `pr₁`. -/
  adjOne : pullFromOne ⊣ pushToOne
  /-- `Lpr₂^* : D_qc(Y₂) ⥤ D_qc(Y₁ ×_S Y₂)`. -/
  pullFromTwo : D2 ⥤ DP
  /-- `Rpr₂_* : D_qc(Y₁ ×_S Y₂) ⥤ D_qc(Y₂)`. -/
  pushToTwo : DP ⥤ D2
  /-- The pullback-pushforward adjunction for `pr₂`. -/
  adjTwo : pullFromTwo ⊣ pushToTwo
  /-- The endofunctor `(-) ⊗^L K` on the product. -/
  tensorRight : DP → DP ⥤ DP
  /-- The subcategories on `Y₁`. -/
  S1 : Subcats D1
  /-- The subcategories on `Y₂`. -/
  S2 : Subcats D2
  /-- The subcategories on the fibre product. -/
  SP : Subcats DP

namespace FMContext

variable {D1 D2 DP : Type u} [Category.{v} D1] [Category.{v} D2] [Category.{v} DP]

/-- **GL26 §1, the integral transform**.  `Φ_K(A) =
Rpr₂_*(Lpr₁^* A ⊗^L K)`. -/
def transform (C : FMContext D1 D2 DP) (K : DP) : D1 ⥤ D2 :=
  C.pullFromOne ⋙ (C.tensorRight K) ⋙ C.pushToTwo

/-- The transform in the opposite direction, obtained by exchanging the two
projections. -/
def transform' (C : FMContext D1 D2 DP) (K : DP) : D2 ⥤ D1 :=
  C.pullFromTwo ⋙ (C.tensorRight K) ⋙ C.pushToOne

/-- The first projection, packaged as a `MorphismContext`. -/
def projectionOne (C : FMContext D1 D2 DP) : MorphismContext D1 DP where
  X := C.Y1
  Y := C.Prod
  f := C.pr1
  noetherianX := C.noetherianY1
  noetherianY := C.noetherianProd
  pull := C.pullFromOne
  push := C.pushToOne
  adj := C.adjOne
  tensorRight := C.tensorRight

/-- The second projection, packaged as a `MorphismContext`. -/
def projectionTwo (C : FMContext D1 D2 DP) : MorphismContext D2 DP where
  X := C.Y2
  Y := C.Prod
  f := C.pr2
  noetherianX := C.noetherianY2
  noetherianY := C.noetherianProd
  pull := C.pullFromTwo
  push := C.pushToTwo
  adj := C.adjTwo
  tensorRight := C.tensorRight

/-- Relative perfectness of a kernel over the first factor (GL26 §1, following
`thm:stacky_all_coincide`). -/
def IsRelativelyPerfectOverOne (C : FMContext D1 D2 DP) (K : DP) : Prop :=
  C.projectionOne.IsRelativelyPerfect C.S1 C.SP K

/-- Relative perfectness of a kernel over the second factor. -/
def IsRelativelyPerfectOverTwo (C : FMContext D1 D2 DP) (K : DP) : Prop :=
  C.projectionTwo.IsRelativelyPerfect C.S2 C.SP K

/-- Both structure morphisms are proper and flat, as in GL26 Setup 2.20
(`setup:fm_cube_pullback`). -/
def IsProperFlat (C : FMContext D1 D2 DP) : Prop :=
  AlgebraicGeometry.IsProper C.f1 ∧ AlgebraicGeometry.Flat C.f1 ∧
    AlgebraicGeometry.IsProper C.f2 ∧ AlgebraicGeometry.Flat C.f2

/-- `Φ_K` is an equivalence on the unbounded quasicoherent derived categories. -/
def IsEquivalence (C : FMContext D1 D2 DP) (K : DP) : Prop :=
  (C.transform K).IsEquivalence

/-- `Φ_K` is full and faithful on the unbounded quasicoherent derived categories. -/
def IsFullyFaithful (C : FMContext D1 D2 DP) (K : DP) : Prop :=
  (C.transform K).Full ∧ (C.transform K).Faithful

end FMContext

/-! ## Restriction to full subcategories -/

/-- A functor maps the full subcategory cut out by `P` into that cut out by `Q`. -/
def MapsTo {C D : Type u} [Category.{v} C] [Category.{v} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D) : Prop :=
  ∀ A : C, P A → Q (F.obj A)

/-- Full faithfulness on objects satisfying `P`; this is precisely bijectivity of
all Hom-maps between such objects. -/
def FullyFaithfulOn {C D : Type u} [Category.{v} C] [Category.{v} D]
    (P : ObjectProperty C) (F : C ⥤ D) : Prop :=
  ∀ A B : C, P A → P B → Function.Bijective (fun f : A ⟶ B => F.map f)

/-- Essential surjectivity onto the objects satisfying `Q`, with sources
required to satisfy `P`. -/
def EssentiallySurjectiveOn {C D : Type u} [Category.{v} C] [Category.{v} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D) : Prop :=
  ∀ B : D, Q B → ∃ A : C, P A ∧ Nonempty (F.obj A ≅ B)

/-- Equivalence of the full subcategories determined by `P` and `Q`, expressed
without constructing separate category types. -/
def EquivalenceOn {C D : Type u} [Category.{v} C] [Category.{v} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D) : Prop :=
  MapsTo P Q F ∧ FullyFaithfulOn P F ∧ EssentiallySurjectiveOn P Q F

/-- An equivalence on full subcategories is, in particular, fully faithful on
the source subcategory. -/
theorem EquivalenceOn.fullyFaithfulOn {C D : Type u} [Category.{v} C] [Category.{v} D]
    {P : ObjectProperty C} {Q : ObjectProperty D} {F : C ⥤ D}
    (h : EquivalenceOn P Q F) : FullyFaithfulOn P F :=
  h.2.1

/-- Full faithfulness of an integral transform on `D^b_coh` (GL26 §10). -/
def FullyFaithfulOnDcoh {D1 D2 DP : Type u} [Category.{v} D1] [Category.{v} D2]
    [Category.{v} DP] (C : FMContext D1 D2 DP) (K : DP) : Prop :=
  FullyFaithfulOn C.S1.Dcoh (C.transform K)

/-- Equivalence of integral transforms on `D^b_coh`, including preservation of
bounded coherent objects and essential surjectivity (GL26 Theorem 10.13). -/
def EquivalenceOnDcoh {D1 D2 DP : Type u} [Category.{v} D1] [Category.{v} D2]
    [Category.{v} DP] (C : FMContext D1 D2 DP) (K : DP) : Prop :=
  EquivalenceOn C.S1.Dcoh C.S2.Dcoh (C.transform K)

/-! ## Points and actual field representatives -/

/-- A field representative of a scheme point.  The existential says that the
(unique) point of the spectrum is sent to `p`; no choice of residue field is
built into the notion. -/
structure PointRepresentative {S : Scheme.{w}} (p : S) where
  /-- The representing field, packaged as a commutative ring. -/
  residue : CommRingCat.{w}
  isField : IsField residue
  /-- The representing morphism. -/
  map : Spec residue ⟶ S
  /-- The morphism represents `p`. -/
  represents : ∃ x : Spec residue, map x = p

namespace PointRepresentative

/-- The canonical representative `Spec κ(p) ⟶ S`
(Mathlib's `Scheme.fromSpecResidueField`). -/
noncomputable def canonical {S : Scheme.{w}} (p : S) : PointRepresentative p where
  residue := S.residueField p
  isField := Field.toIsField _
  map := S.fromSpecResidueField p
  represents := ⟨IsLocalRing.closedPoint _, S.fromSpecResidueField_apply p _⟩

end PointRepresentative

/-! ## Fibre contexts and the loci `FM` and `fm` -/

/-- The base-changed FM context at a field representative.  The three Cartesian
squares are the scheme-level content of GL26 Setup 2.20
(`setup:fm_cube_pullback`).  `baseIso` identifies the base of the supplied
fibre context with the spectrum of the representing field.

The `pullKernel` functor is the derived pullback along the induced map on the
product.  Its construction and pseudofunctoriality are part of the derived
geometric layer, not additional axioms in this file. -/
structure FibreContext {D1 D2 DP : Type u} [Category.{v} D1] [Category.{v} D2]
    [Category.{v} DP] (C : RelativeFM.Noetherian.FMContext.{w, u, v} D1 D2 DP) {p : C.Base}
    (t : PointRepresentative p) where
  /-- Derived-category objects on the first fibre. -/
  FD1 : Type u
  /-- Derived-category objects on the second fibre. -/
  FD2 : Type u
  /-- Derived-category objects on the product fibre. -/
  FDP : Type u
  [cat1 : Category.{v} FD1]
  [cat2 : Category.{v} FD2]
  [catP : Category.{v} FDP]
  /-- The FM context after base change. -/
  ctx : RelativeFM.Noetherian.FMContext.{w, u, v} FD1 FD2 FDP
  /-- Identification of its base with `Spec` of the representing field. -/
  baseIso : ctx.Base ≅ Spec t.residue
  /-- The map from the first fibre to `Y₁`. -/
  map1 : ctx.Y1 ⟶ C.Y1
  /-- The map from the second fibre to `Y₂`. -/
  map2 : ctx.Y2 ⟶ C.Y2
  /-- The map from the product fibre to the original product. -/
  mapP : ctx.Prod ⟶ C.Prod
  /-- The first fibre square is Cartesian. -/
  square1 : IsPullback map1 (ctx.f1 ≫ baseIso.hom) C.f1 t.map
  /-- The second fibre square is Cartesian. -/
  square2 : IsPullback map2 (ctx.f2 ≫ baseIso.hom) C.f2 t.map
  /-- The product fibre square is Cartesian. -/
  squareP : IsPullback mapP (ctx.pr1 ≫ ctx.f1 ≫ baseIso.hom)
    (C.pr1 ≫ C.f1) t.map
  /-- Compatibility with the first projections. -/
  commPr1 : mapP ≫ C.pr1 = ctx.pr1 ≫ map1
  /-- Compatibility with the second projections. -/
  commPr2 : mapP ≫ C.pr2 = ctx.pr2 ≫ map2
  /-- `L(t')^*`, the derived pullback of kernels. -/
  pullKernel : DP ⥤ FDP

attribute [instance] FibreContext.cat1 FibreContext.cat2 FibreContext.catP

/-- An FM setup with all base changes to field representatives.  Keeping the
representative in the indexing type is what makes GL26 Lemma 12.2 a substantive
statement rather than an opaque field. -/
structure FMSetup where
  /-- Derived-category objects on `Y₁`, `Y₂`, and their product. -/
  D1 : Type u
  D2 : Type u
  DP : Type u
  [cat1 : Category.{v} D1]
  [cat2 : Category.{v} D2]
  [catP : Category.{v} DP]
  /-- The context over the Noetherian base scheme. -/
  ctx : RelativeFM.Noetherian.FMContext.{w, u, v} D1 D2 DP
  /-- Cartesian fibre contexts and kernel pullbacks for every representative of
  every point of the base. -/
  fibre : ∀ {p : ctx.Base} (t : PointRepresentative p), FibreContext ctx t

attribute [instance] FMSetup.cat1 FMSetup.cat2 FMSetup.catP

namespace FMSetup

variable (X : FMSetup.{w, u, v})

/-- The integral transform obtained by base change to a chosen field
representative (GL26 Definition 12.1, `def:fm_locus`). -/
def fibreTransform (K : X.DP) {p : X.ctx.Base} (t : PointRepresentative p) :=
  (X.fibre t).ctx.transform ((X.fibre t).pullKernel.obj K)

/-- Full faithfulness of the fibre transform on unbounded `D_qc`. -/
def FullyFaithfulAt (K : X.DP) {p : X.ctx.Base} (t : PointRepresentative p) : Prop :=
  (X.fibreTransform K t).Full ∧ (X.fibreTransform K t).Faithful

/-- Being an equivalence of the fibre transform on unbounded `D_qc`. -/
def EquivalenceAt (K : X.DP) {p : X.ctx.Base} (t : PointRepresentative p) : Prop :=
  (X.fibreTransform K t).IsEquivalence

/-- **GL26 Definition 12.1**: the equivalence locus.  The existential over
representatives is intentional; Lemma 12.2 proves independence under its
relative-perfectness hypotheses. -/
def FM (K : X.DP) : Set X.ctx.Base :=
  {p | ∃ t : PointRepresentative p, X.EquivalenceAt K t}

/-- **GL26 Definition 12.1**: the full-faithfulness locus. -/
def fm (K : X.DP) : Set X.ctx.Base :=
  {p | ∃ t : PointRepresentative p, X.FullyFaithfulAt K t}

/-- The explicit assertion of representative independence: both fibrewise full
faithfulness and fibrewise equivalence are independent of the chosen field
representative of a point. -/
def RepIndependent (K : X.DP) : Prop :=
  ∀ {p : X.ctx.Base} (t t' : PointRepresentative p),
    (X.FullyFaithfulAt K t ↔ X.FullyFaithfulAt K t') ∧
      (X.EquivalenceAt K t ↔ X.EquivalenceAt K t')

/-- Full faithfulness of a fibre transform on `D^b_coh`. -/
def FullyFaithfulFibreOnDcoh (K : X.DP) {p : X.ctx.Base}
    (t : PointRepresentative p) : Prop :=
  FullyFaithfulOnDcoh (X.fibre t).ctx ((X.fibre t).pullKernel.obj K)

/-- Equivalence of a fibre transform on `D^b_coh`. -/
def EquivalenceFibreOnDcoh (K : X.DP) {p : X.ctx.Base}
    (t : PointRepresentative p) : Prop :=
  EquivalenceOnDcoh (X.fibre t).ctx ((X.fibre t).pullKernel.obj K)

@[simp] theorem mem_FM {K : X.DP} {p : X.ctx.Base} :
    p ∈ X.FM K ↔ ∃ t : PointRepresentative p, X.EquivalenceAt K t := Iff.rfl

@[simp] theorem mem_fm {K : X.DP} {p : X.ctx.Base} :
    p ∈ X.fm K ↔ ∃ t : PointRepresentative p, X.FullyFaithfulAt K t := Iff.rfl

end FMSetup

/-! ## Arbitrary Noetherian base change -/

/-- Base change of an entire FM setup along a morphism of Noetherian schemes.
No flatness is imposed on `mapBase`, as required by GL26 Theorem 1.2(2) and
Corollary 6.18. -/
structure BaseChange (X : FMSetup.{w, u, v}) where
  /-- The setup over the new base. -/
  over : FMSetup.{w, u, v}
  /-- The morphism from the new base to the old base. -/
  mapBase : over.ctx.Base ⟶ X.ctx.Base
  /-- Base-change maps on the two families and their product. -/
  map1 : over.ctx.Y1 ⟶ X.ctx.Y1
  map2 : over.ctx.Y2 ⟶ X.ctx.Y2
  mapP : over.ctx.Prod ⟶ X.ctx.Prod
  /-- The three squares in Setup 2.20 are Cartesian. -/
  square1 : IsPullback map1 over.ctx.f1 X.ctx.f1 mapBase
  square2 : IsPullback map2 over.ctx.f2 X.ctx.f2 mapBase
  squareP : IsPullback mapP (over.ctx.pr1 ≫ over.ctx.f1)
    (X.ctx.pr1 ≫ X.ctx.f1) mapBase
  /-- Compatibility with the projections. -/
  commPr1 : mapP ≫ X.ctx.pr1 = over.ctx.pr1 ≫ map1
  commPr2 : mapP ≫ X.ctx.pr2 = over.ctx.pr2 ≫ map2
  /-- Derived pullback of kernels along the induced map on products. -/
  pullKernel : X.DP ⥤ over.DP

/-! ## Quantification over closed-point fibres -/

/-- A fibre property holds at every finite-type field representative of every
closed point (the second clause of GL26 Theorem 10.13). -/
def EveryFiniteTypeClosedFibre (X : FMSetup.{w, u, v})
    (P : ∀ {p : X.ctx.Base}, PointRepresentative p → Prop) : Prop :=
  ∀ (p : X.ctx.Base), IsClosed ({p} : Set X.ctx.Base) →
    ∀ t : PointRepresentative p, LocallyOfFiniteType t.map → P t

/-- For each closed point, some field representative has the given property
(the third clause of GL26 Theorem 10.13). -/
def SomeClosedFibre (X : FMSetup.{w, u, v})
    (P : ∀ {p : X.ctx.Base}, PointRepresentative p → Prop) : Prop :=
  ∀ (p : X.ctx.Base), IsClosed ({p} : Set X.ctx.Base) →
    ∃ t : PointRepresentative p, P t

/-- The two implications relating a global property to the universal and
existential closed-point criteria in GL26 Theorem 10.13. -/
def DescentAscentStatement (X : FMSetup.{w, u, v}) (A : Prop)
    (P : ∀ {p : X.ctx.Base}, PointRepresentative p → Prop) : Prop :=
  (A ↔ EveryFiniteTypeClosedFibre X P) ∧
    (EveryFiniteTypeClosedFibre X P ↔ SomeClosedFibre X P)

/-! ## Diagonal data -/

/-- Data for the self-product diagonal.  Equality of the two source schemes,
structure morphisms, and subcategory packages is recorded explicitly rather
than left to an informal identification. -/
structure DiagonalFMData {D DP : Type u} [Category.{v} D] [Category.{v} DP]
    (C : FMContext D D DP) where
  /-- The two factors are the same scheme. -/
  sameSchemes : C.Y1 = C.Y2
  /-- They are the same family over the base. -/
  sameFamily : C.f1 = eqToHom sameSchemes ≫ C.f2
  /-- They use the same bounded-coherent/perfect subcategories. -/
  sameSubcats : C.S1 = C.S2
  /-- The diagonal morphism. -/
  diagonal : C.Y1 ⟶ C.Prod
  /-- The first projection splits the diagonal. -/
  diagonalPr1 : diagonal ≫ C.pr1 = 𝟙 _
  /-- The second projection splits the diagonal. -/
  diagonalPr2 : diagonal ≫ C.pr2 = eqToHom sameSchemes
  /-- `RΔ_* : D_qc(Y) ⥤ D_qc(Y ×_S Y)`. -/
  push : D ⥤ DP
  /-- The object `O_Y` in degree zero. -/
  unit : D

-- PROVISIONAL: `DiagonalFMData.push` and `.unit` are geometric interfaces until
-- the sheaf-of-modules and derived-pushforward layers identify them with `RΔ_*`
-- and the structure sheaf.  The two retraction equations are already genuine
-- equalities of scheme morphisms.

/-- The ideal-sheaf kernel of the diagonal, identified by its distinguished
triangle.  This is the triangle appearing in GL26 Lemma 11.1 and in the proof of
Theorem 11.4:
`I_Δ ⟶ O_(Y×_S Y) ⟶ RΔ_*O_Y ⟶ I_Δ[1]`.

The structure-sheaf object on the product and the unit comparison map remain
geometric data.  The fact that `ideal` is the kernel to which Theorem 1.7
applies, however, is enforced by the distinguished-triangle field. -/
structure DiagonalIdealData {D DP : Type u} [Category.{v} D] [Category.{v} DP]
    [HasZeroObject DP] [HasShift DP ℤ] [Preadditive DP]
    [∀ n : ℤ, Functor.Additive (shiftFunctor DP n)] [Pretriangulated DP]
    {C : RelativeFM.Noetherian.FMContext.{w, u, v} D D DP}
    (Δ : DiagonalFMData C) where
  /-- The structure sheaf `O_(Y×_S Y)` in degree zero. -/
  structureUnit : DP
  /-- The ideal-sheaf kernel `I_Δ` (equivalently, the negative shift of the cone
  of the unit). -/
  ideal : DP
  /-- The inclusion of the ideal-sheaf kernel in the structure sheaf. -/
  inclusion : ideal ⟶ structureUnit
  /-- The unit map to `RΔ_*O_Y`. -/
  unitMap : structureUnit ⟶ Δ.push.obj Δ.unit
  /-- The connecting morphism. -/
  connecting : Δ.push.obj Δ.unit ⟶ ideal⟦(1 : ℤ)⟧
  /-- The kernel really is the fibre of the unit map. -/
  distinguished : Triangle.mk inclusion unitMap connecting ∈ distTriang DP

/-! ## Elliptic-fibration inputs missing from Mathlib -/

/-- Predicates needed to state GL26's elliptic-fibration theorem.  Mathlib
4.33.1 has neither Gorenstein morphisms of schemes nor the arithmetic genus of
a curve, so these two predicates are parameters rather than silently weakened
definitions.

`IsGorensteinMorphism` must use the standard Stacks convention recalled in GL26
Reminder 11.2: in particular it includes flatness and local finite presentation.
`IsOneDimensionalGenusOneCurve` must assert Krull dimension one and arithmetic
genus one for the displayed curve over a field (Stacks 0BY7). -/
structure EllipticFibrationPredicates where
  /-- Proper Gorenstein morphisms, with flatness included in the convention. -/
  IsGorensteinMorphism : ∀ {Y S : Scheme.{w}}, (Y ⟶ S) → Prop
  /-- Geometric one-dimensional genus-one curves over a field. -/
  IsOneDimensionalGenusOneCurve : ∀ {k : CommRingCat.{w}}, IsField k →
    ∀ {F : Scheme.{w}}, (F ⟶ Spec k) → Prop

/-- The exact fibre condition in GL26 Reminder 11.2: for every point, some field
representative has a geometrically integral, one-dimensional, genus-one fibre.
The square witnessing the fibre is required to be Cartesian. -/
def HasEllipticFibres (P : EllipticFibrationPredicates.{w}) {Y S : Scheme.{w}}
    (f : Y ⟶ S) : Prop :=
  ∀ p : S, ∃ t : PointRepresentative p, ∃ F : Scheme.{w},
    ∃ fibreToField : F ⟶ Spec t.residue, ∃ fibreToY : F ⟶ Y,
      IsPullback fibreToY fibreToField f t.map ∧
        GeometricallyIntegral fibreToField ∧
        P.IsOneDimensionalGenusOneCurve t.isField fibreToField

/-- **GL26 Reminder 11.2** (`rem:elliptic_fibration`): a proper Gorenstein
morphism with geometrically integral one-dimensional genus-one fibres.
Flatness is made explicit to prevent the ambiguity discussed in the project
report. -/
def IsEllipticFibration (P : EllipticFibrationPredicates.{w}) {Y S : Scheme.{w}}
    (f : Y ⟶ S) : Prop :=
  AlgebraicGeometry.IsProper f ∧ AlgebraicGeometry.Flat f ∧
    P.IsGorensteinMorphism f ∧ HasEllipticFibres P f

/-! # The ten GL26 targets -/

/-- **GL26 Theorem 1.3** (`thm:stacky_all_coincide`; Theorem 6.2 and
Proposition 6.8).  For a proper morphism of Noetherian schemes and a
pseudocoherent `E`, relative perfectness, the bounded-coherent tensor test, and
relative quasi-perfectness are equivalent.

The scheme proof still requires properness/cohomological boundedness (Stacks
0GFH, 0GFI), pseudocoherence (08H4), and perfectness through derived fibres.
It no longer requires algebraic-space descent. -/
def theorem_1_3Statement {DX DY : Type u} [Category.{v} DX] [Category.{v} DY]
    (M : MorphismContext DX DY) (SX : Subcats DX) (SY : Subcats DY)
    (hproper : M.IsProper) (E : DY) (hE : SY.IsPseudocoherent E) : Prop :=
  (M.IsRelativelyPerfect SX SY E ↔
      (∀ A : DX, SX.Dcoh A → SY.Dcoh ((M.tensorRight E).obj (M.pull.obj A)))) ∧
    ((∀ A : DX, SX.Dcoh A → SY.Dcoh ((M.tensorRight E).obj (M.pull.obj A))) ↔
      M.IsQuasiPerfect SX SY E)

/-- **GL26 Theorem 12.3**
(`thm:openness_for_equivalence_fullfaithful_dbcoh`).  For a pseudocoherent
kernel relatively perfect over both factors, both `FM(K)` and `fm(K)` are open
in the Zariski topology of the Noetherian base scheme.

The proof contract includes adjoint kernels, compact generators (09IY, 09M8),
and closedness of the images of bounded-pseudocoherent supports (07TZ). -/
def theorem_12_3Statement (X : FMSetup.{w, u, v}) (hX : X.ctx.IsProperFlat) {K : X.DP}
    (hK : X.ctx.SP.IsPseudocoherent K)
    (hrel1 : X.ctx.IsRelativelyPerfectOverOne K)
    (hrel2 : X.ctx.IsRelativelyPerfectOverTwo K) : Prop :=
  IsOpen (X.FM K) ∧ IsOpen (X.fm K)

/-- **GL26 Theorem 1.2(1), Theorem 12.9** (`thm:fm_locus_weak_approx`).  For an
arbitrary bounded pseudocoherent kernel, `FM(K)` is open; no relative
perfectness hypothesis is imposed.

For schemes, the weak-approximability input is Neeman's published qcqs-scheme
theorem, together with 09SR.  The algebraic-space Hall--Rydh induction input is
removed. -/
def theorem_1_2_openStatement (X : FMSetup.{w, u, v}) (hX : X.ctx.IsProperFlat) {K : X.DP}
    (hK : X.ctx.SP.Dcoh K) : Prop :=
  IsOpen (X.FM K)

/-- **GL26 Theorem 1.2(2), Theorem 12.9(2)**.  The equivalence locus of an
arbitrary bounded pseudocoherent kernel commutes with arbitrary Noetherian base
change.  The map on base changes is not assumed flat. -/
def theorem_1_2_baseChangeStatement (X : FMSetup.{w, u, v}) (hX : X.ctx.IsProperFlat) {K : X.DP}
    (hK : X.ctx.SP.Dcoh K) (t : BaseChange X) : Prop :=
  t.mapBase ⁻¹' X.FM K = t.over.FM (t.pullKernel.obj K)

/-- **GL26 Corollary 12.10** (`cor:deform`), the relative-perfect strengthening
used for the second half of Theorem 1.2.  Both the full-faithfulness and
equivalence loci commute with arbitrary Noetherian base change.

The residue-field squares used in the proof are genuine scheme squares here;
the remaining input is affine faithfully flat descent and base change of the
adjoint transforms. -/
def corollary_12_10Statement (X : FMSetup.{w, u, v}) (hX : X.ctx.IsProperFlat) {K : X.DP}
    (hK : X.ctx.SP.IsPseudocoherent K)
    (hrel1 : X.ctx.IsRelativelyPerfectOverOne K)
    (hrel2 : X.ctx.IsRelativelyPerfectOverTwo K) (t : BaseChange X) : Prop :=
  t.mapBase ⁻¹' X.fm K = t.over.fm (t.pullKernel.obj K) ∧
    t.mapBase ⁻¹' X.FM K = t.over.FM (t.pullKernel.obj K)

/-- **GL26 Theorem 1.6, Theorem 10.13** (`thm:descent_ascent`).  Full
faithfulness and equivalence on `D^b_coh` are each equivalent to the universal
finite-type closed-fibre criterion and to the existential
some-representative-at-each-closed-point criterion.

The proof uses the mate calculus, base change of adjoint transforms and relative
dualizing complexes, and Stacks 09TF.  Unlike the old statement, this definition
contains both the full-faithfulness and equivalence assertions. -/
def theorem_1_6Statement (X : FMSetup.{w, u, v}) (hX : X.ctx.IsProperFlat) {K : X.DP}
    (hK : X.ctx.SP.Dcoh K)
    (hrel1 : X.ctx.IsRelativelyPerfectOverOne K)
    (hrel2 : X.ctx.IsRelativelyPerfectOverTwo K) : Prop :=
  DescentAscentStatement X (FullyFaithfulOnDcoh X.ctx K)
      (fun {_} t => X.FullyFaithfulFibreOnDcoh K t) ∧
    DescentAscentStatement X (EquivalenceOnDcoh X.ctx K)
      (fun {_} t => X.EquivalenceFibreOnDcoh K t)

/-- **GL26 Lemma 12.2** (`lem:independence_for_rep_with_ff_or_eq`).  For a
pseudocoherent kernel relatively perfect over both factors, full faithfulness
and equivalence at a point are independent of the field representative.

This is the actual pairwise statement over all `PointRepresentative`s, not an
uninterpreted `RepIndependent` field. -/
def lemma_12_2Statement (X : FMSetup.{w, u, v}) (hX : X.ctx.IsProperFlat) {K : X.DP}
    (hK : X.ctx.SP.IsPseudocoherent K)
    (hrel1 : X.ctx.IsRelativelyPerfectOverOne K)
    (hrel2 : X.ctx.IsRelativelyPerfectOverTwo K) : Prop :=
  X.RepIndependent K

/-- **GL26 Lemma 2.25** (`lem:funct_on_kernel`).  For a proper flat family, the
kernel `RΔ_* O_Y` induces the identity functor on `D_qc(Y)`.

The remaining geometric ingredients are the projection formula (Stacks 08IN),
functoriality of derived pullback/pushforward, and the two diagonal retraction
identities recorded in `DiagonalFMData`. -/
def lemma_2_25Statement {D DP : Type u} [Category.{v} D] [Category.{v} DP]
    (C : RelativeFM.Noetherian.FMContext.{w, u, v} D D DP)
    (hC : C.IsProperFlat) (Δ : DiagonalFMData C) : Prop :=
  Nonempty (C.transform (Δ.push.obj Δ.unit) ≅ 𝟭 D)

/-! ## Convolution of kernels -/

/-- Three composable FM contexts and an object-level convolution operation.
The equalities record the common base and the shared source/middle/target
families. -/
structure ConvolutionData {D1 D2 D3 DP12 DP23 DP13 : Type u}
    [Category.{v} D1] [Category.{v} D2] [Category.{v} D3]
    [Category.{v} DP12] [Category.{v} DP23] [Category.{v} DP13] where
  /-- The contexts on `Y₁ ×_S Y₂`, `Y₂ ×_S Y₃`, and `Y₁ ×_S Y₃`. -/
  C12 : RelativeFM.Noetherian.FMContext.{w, u, v} D1 D2 DP12
  C23 : RelativeFM.Noetherian.FMContext.{w, u, v} D2 D3 DP23
  C13 : RelativeFM.Noetherian.FMContext.{w, u, v} D1 D3 DP13
  /-- Compatibility of bases and shared families. -/
  sameBase12 : C12.Base = C23.Base
  sameBase13 : C13.Base = C12.Base
  sameMiddle : C12.Y2 = C23.Y1
  sameSource : C13.Y1 = C12.Y1
  sameTarget : C13.Y2 = C23.Y2
  /-- The shared families use the same subcategory packages. -/
  sameMiddleSubcats : C12.S2 = C23.S1
  sameSourceSubcats : C13.S1 = C12.S1
  sameTargetSubcats : C13.S2 = C23.S2
  /-- Object-level convolution `K₂ ⋆ K₁`. -/
  conv : DP12 → DP23 → DP13

-- PROVISIONAL: `ConvolutionData.conv` is object-level until the derived tensor
-- layer supplies the triple fibre-product cube.  Its intended definition is
-- `Rp₁₃_*(Lp₁₂^*K₁ ⊗^L Lp₂₃^*K₂)`.

/-- **GL26 Lemma 2.26** (`lem:convolution`).  Integral transforms compose by
convolution of their kernels for proper flat families of Noetherian schemes.

The proof contract is the projection formula (Stacks 08IN) and tor-independent
base change (08IR); flatness of the families supplies tor-independence. -/
def lemma_2_26Statement {D1 D2 D3 DP12 DP23 DP13 : Type u}
    [Category.{v} D1] [Category.{v} D2] [Category.{v} D3]
    [Category.{v} DP12] [Category.{v} DP23] [Category.{v} DP13]
    (B : ConvolutionData.{w, u, v} (D1 := D1) (D2 := D2) (D3 := D3)
      (DP12 := DP12) (DP23 := DP23) (DP13 := DP13))
    (h12 : B.C12.IsProperFlat) (h23 : B.C23.IsProperFlat) (h13 : B.C13.IsProperFlat)
    (K1 : DP12) (K2 : DP23) : Prop :=
  Nonempty (B.C12.transform K1 ⋙ B.C23.transform K2 ≅
    B.C13.transform (B.conv K1 K2))

/-- **GL26 Corollary 6.18**
(`cor:noetherian_base_change_for_relative_perfectness`).  Relative perfectness
of a bounded pseudocoherent kernel over the first projection is preserved by
arbitrary Noetherian base change.

The corresponding statement over the second projection is obtained by swapping
the two factors.  The proof interface retains pseudocoherent pullback (08H4),
boundedness descent, and affine/quasi-affine base change; the algebraic-space
étale-presentation step is unnecessary for schemes. -/
def corollary_6_18Statement (X : FMSetup.{w, u, v}) (hX : X.ctx.IsProperFlat) {K : X.DP}
    (hK : X.ctx.SP.Dcoh K) (hrel : X.ctx.IsRelativelyPerfectOverOne K)
    (t : BaseChange X) : Prop :=
  t.over.ctx.IsRelativelyPerfectOverOne (t.pullKernel.obj K)

/-- **GL26 Theorem 1.7, Theorem 11.4**
(`thm:elliptic_fibration_autoequivalence`).  For an elliptic fibration, the
ideal-sheaf kernel `I_Δ` induces an autoequivalence of `D^b_coh(Y)`.

The distinguished-triangle interface `Θ` identifies the ideal sheaf of the
diagonal supplied by `Δ`.  The remaining proof inputs are Lemma 11.1 (relative
perfectness), derived pullback of that ideal sheaf, GL26 Theorem 10.13, and the
genus-one-fibration calculation of Hernández López--Ruipérez--Sancho de Salas.
Relevant Stacks tags are 0BY7/0BY9, 0FD2, 0FW1, and 0A26. -/
def theorem_1_7Statement {D DP : Type u} [Category.{v} D] [Category.{v} DP]
    [HasZeroObject DP] [HasShift DP ℤ] [Preadditive DP]
    [∀ n : ℤ, Functor.Additive (shiftFunctor DP n)] [Pretriangulated DP]
    (C : RelativeFM.Noetherian.FMContext.{w, u, v} D D DP)
    (P : EllipticFibrationPredicates.{w}) (hC : C.IsProperFlat)
    (Δ : DiagonalFMData C) (Θ : DiagonalIdealData Δ)
    (hell : IsEllipticFibration P C.f1) : Prop :=
  EquivalenceOnDcoh C Θ.ideal

/-! ## Axiom audit of the proved glue and of the ten specifications -/


end RelativeFM.Noetherian
