/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Basic

/-!
# An abstract interface for relative Fourier--Mukai theory

The paper works with the unbounded derived category `D_qc(X)` of quasi-coherent
sheaves on a Noetherian algebraic space `X`, together with the full subcategories
`D^b_qc(X)`, `D^b_coh(X)` (bounded pseudocoherent complexes) and `Perf(X)`, the
derived tensor product, and the functors `Lf^*`, `Rf_*`, `f^×`, `f^!`.

None of this is available in Mathlib (there are no algebraic spaces, no étale
site of a scheme, and no derived category of quasi-coherent sheaves), so this
file fixes an *interface*: the data and the properties that the paper uses, as a
Lean structure.  Definitions such as `IsRelativelyPerfect` (Definition 4.1),
`IsQuasiPerfect` (Definition 5.1), the integral transform `Φ_K`, and the loci
`FM`/`fm` (Definition 12.1) are then *actual* Lean definitions on top of that
interface, and the paper's theorems can be stated about them.

The `sorry`s are confined to `FourierMukai/Paper/Statements.lean`.

## Main definitions

* `RelativeFM.Subcats` : the three full subcategories of a derived category.
* `RelativeFM.MorphismContext` / `IsRelativelyPerfect` / `IsQuasiPerfect`.
* `RelativeFM.FMContext` / `transform` : the integral transform `Φ_K`.
* `RelativeFM.FMSetup` / `FM` / `fm` : Definition 12.1.

## References

* [Guisado Villalgordo, Lank, *Relative Fourier--Mukai theory for algebraic spaces*]
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory

universe u v

/-! ### The three full subcategories of a derived category -/

/-- The three full subcategories of `D_qc(X)` that the paper uses: bounded complexes
with quasi-coherent cohomology, bounded pseudocoherent complexes, and perfect
complexes (Section 2.2).

Conventions, as fixed by the authors of the paper:

* *pseudocoherent* is the notion for ringed topoi: an object is pseudocoherent when
  it is locally quasi-isomorphic to a bounded above complex of finite free modules;
* `D^-_coh` is `D_qc^-` with coherent cohomology sheaves;
* on a Noetherian space, an object `E ∈ D_qc` is pseudocoherent if and only if
  `E ∈ D^-_coh`.  In particular `D^b_coh = D^b_qc ⊓ (pseudocoherent)`, which is the
  field `Dcoh` below, may be read either way in the Noetherian setting of the paper.
-/
structure Subcats (D : Type u) [Category.{v} D] where
  /-- `D^b_qc(X)`: bounded complexes with quasi-coherent cohomology. -/
  DbQc : ObjectProperty D
  /-- `D^b_coh(X)`: bounded pseudocoherent complexes, i.e. bounded objects of `D_qc`
  with coherent cohomology (the two agree on a Noetherian space). -/
  Dcoh : ObjectProperty D
  /-- `Perf(X)`: perfect complexes. -/
  Perf : ObjectProperty D
  /-- The notion of pseudocoherence underlying `Dcoh`, kept separate so that
  statements about `E ∈ D_qc` pseudocoherent (Definition 4.1's surrounding
  discussion, Theorem 1.3) can be phrased without committing to boundedness. -/
  IsPseudocoherent : D → Prop

namespace Subcats

variable {D : Type u} [Category.{v} D] (S : Subcats D)

/-- Every perfect complex is bounded pseudocoherent (in the paper's setting, a
perfect complex is a bounded complex of finite locally free modules).  This is an
interface condition, not an assumption of mathematics: any instantiation must
provide it. -/
def PerfLeDcoh : Prop := S.Perf ≤ S.Dcoh

/-- Every bounded pseudocoherent complex is bounded with quasi-coherent
cohomology (interface condition). -/
def DcohLeDbQc : Prop := S.Dcoh ≤ S.DbQc

/-- On a Noetherian space, `D^b_coh` is `D^b_qc` intersected with pseudocoherence.
This is the authors' convention recorded as an interface condition. -/
def DcohEq : Prop := ∀ E, S.Dcoh E ↔ S.DbQc E ∧ S.IsPseudocoherent E

end Subcats

/-! ### One morphism of spaces: relative and quasi-perfect complexes -/

/-- The functorial content of a morphism `f : Y ⟶ X` of spaces on their derived
categories: the derived pullback `Lf^*`, its right adjoint `Rf_*`, and the derived
tensor product with a fixed object on `Y`. -/
structure MorphismContext (DX DY : Type u) [Category.{v} DX] [Category.{v} DY] where
  /-- `Lf^* : D_qc(X) ⟶ D_qc(Y)`. -/
  pull : DX ⥤ DY
  /-- `Rf_* : D_qc(Y) ⟶ D_qc(X)`. -/
  push : DY ⥤ DX
  /-- The adjunction `Lf^* ⊣ Rf_*` (Stacks tag 07A6). -/
  adj : pull ⊣ push
  /-- The endofunctor `(-) ⊗^L E`. -/
  tensorRight : DY → DY ⥤ DY
  /-- The `f^×` functor, right adjoint to `Rf_*` (Stacks tag 0E55). -/
  upperCross : DX ⥤ DY
  /-- `f` is proper (interface condition). -/
  IsProper : Prop
  /-- `f` is flat (interface condition). -/
  IsFlat : Prop

namespace MorphismContext

variable {DX DY : Type u} [Category.{v} DX] [Category.{v} DY] (M : MorphismContext DX DY)

/-- **Definition 4.1** (`f`-perfect / relatively perfect over `X`): `E ∈ D_qc(Y)` is
`f`-perfect if `E ⊗^L Lf^* A ∈ D^b_qc(Y)` for every `A ∈ D^b_qc(X)`. -/
def IsRelativelyPerfect (SX : Subcats DX) (SY : Subcats DY) (E : DY) : Prop :=
  ∀ A : DX, SX.DbQc A → SY.DbQc ((M.tensorRight E).obj (M.pull.obj A))

/-- **Definition 5.1** (`f`-quasi-perfect): `Rf_*(E ⊗^L P)` is perfect for every
perfect `P` on `Y`. -/
def IsQuasiPerfect (SX : Subcats DX) (SY : Subcats DY) (E : DY) : Prop :=
  ∀ P : DY, SY.Perf P → SX.Perf (M.push.obj ((M.tensorRight E).obj P))

/-- The special case `E = O_Y` of Definition 4.1 recovers the condition that `f`
has finite tor-dimension (Remark 4.2(4)).  We record the predicate. -/
def HasFiniteTorDimension (SX : Subcats DX) (SY : Subcats DY) (unit : DY) : Prop :=
  M.IsRelativelyPerfect SX SY unit

end MorphismContext

/-! ### The integral transform -/

/-- The functorial content of the paper's Setup 2.20 at a fixed base: the two
projections from the fibre product `Y₁ ×_S Y₂`, and the tensor product on the
fibre product. -/
structure FMContext (D1 D2 DP : Type u) [Category.{v} D1] [Category.{v} D2]
    [Category.{v} DP] where
  /-- `(-) ⊗^L K` on `D_qc(Y₁ ×_S Y₂)`. -/
  tensorRight : DP → DP ⥤ DP
  /-- `L(f'_2)^* : D_qc(Y₁) ⟶ D_qc(Y₁ ×_S Y₂)`. -/
  pull : D1 ⥤ DP
  /-- `R(f'_1)_* : D_qc(Y₁ ×_S Y₂) ⟶ D_qc(Y₂)`. -/
  push : DP ⥤ D2
  /-- `L(f'_1)^*`, used for the symmetry of the theory. -/
  pull' : D2 ⥤ DP
  /-- `R(f'_2)_*`. -/
  push' : DP ⥤ D1
  /-- The kernel `RΔ_*O_{Y₁}` of the identity transform (Lemma 2.25). -/
  diagonalKernel : DP
  /-- The subcategories on each of the three spaces. -/
  S1 : Subcats D1
  S2 : Subcats D2
  SP : Subcats DP

namespace FMContext

variable {D1 D2 DP : Type u} [Category.{v} D1] [Category.{v} D2] [Category.{v} DP]

/-- **The integral transform** `Φ_K : D_qc(Y₁) ⟶ D_qc(Y₂)`,
`A ↦ R(f'_1)_*(L(f'_2)^*A ⊗^L K)`. -/
def transform (C : FMContext D1 D2 DP) (K : DP) : D1 ⥤ D2 :=
  C.pull ⋙ (C.tensorRight K) ⋙ C.push

/-- The transpose transform `Ψ_K : D_qc(Y₂) ⟶ D_qc(Y₁)` with the roles of `Y₁` and
`Y₂` exchanged. -/
def transform' (C : FMContext D1 D2 DP) (K : DP) : D2 ⥤ D1 :=
  C.pull' ⋙ (C.tensorRight K) ⋙ C.push'

/-- `Φ_K` is an equivalence. -/
def IsEquivalence (C : FMContext D1 D2 DP) (K : DP) : Prop :=
  (C.transform K).IsEquivalence

/-- `Φ_K` is fully faithful. -/
def IsFullyFaithful (C : FMContext D1 D2 DP) (K : DP) : Prop :=
  (C.transform K).Full ∧ (C.transform K).Faithful

/-- **Remark 2.6**: for a relative Fourier--Mukai transform with a relatively
perfect kernel, `Φ_K` is an equivalence on `D_qc` if and only if it restricts to an
equivalence on `Perf`. -/
def IsEquivalenceOnPerfect (C : FMContext D1 D2 DP) (K : DP) : Prop :=
  ∀ P : D1, C.S1.Perf P → ∃ Q : D2, C.S2.Perf Q ∧
    Nonempty ((C.transform K).obj P ≅ Q)

end FMContext

/-! ### The loci `FM(K)` and `fm(K)` -/

/-- A relative Fourier--Mukai context together with its fibres at the points of the
base (Definition 12.1).  The field `fibreTransform` encodes the base change
`L(t')^*K` of the kernel at a representative `t` of each point; see
`FMSetup`'s documentation in `results/REPORT.md` for why the geometry behind this
field cannot be defined in Mathlib today. -/
structure FMSetup where
  /-- The underlying topological space `|S|`. -/
  Base : Type u
  /-- Its topology. -/
  top : TopologicalSpace Base
  /-- `D_qc(Y₁)`, `D_qc(Y₂)` and `D_qc(Y₁ ×_S Y₂)`. -/
  D1 : Type u
  D2 : Type u
  DP : Type u
  [cat1 : Category.{v} D1]
  [cat2 : Category.{v} D2]
  [catP : Category.{v} DP]
  /-- The relative Fourier--Mukai context at the base. -/
  ctx : FMContext D1 D2 DP
  /-- The two fibre categories at each point `p ∈ |S|`. -/
  F1 : Base → Type u
  F2 : Base → Type u
  [fibcat1 : ∀ p, Category.{v} (F1 p)]
  [fibcat2 : ∀ p, Category.{v} (F2 p)]
  /-- The integral transform `Φ_{L(t')^*K}` at each point, for each kernel `K`. -/
  fibreTransform : (K : DP) → (p : Base) → F1 p ⥤ F2 p
  /-- The base is a Noetherian algebraic space, and `Y₁, Y₂` are proper flat over
  it.  This is interface data: it cannot be instantiated in Mathlib today. -/
  IsProperFlat : Prop
  /-- `K` is a bounded pseudocoherent kernel. -/
  IsBoundedPseudoCoherent : DP → Prop
  /-- The choice of representative of a point does not matter for full faithfulness
  and for being an equivalence (Lemma 12.2).  For each kernel, this is the assertion
  of Lemma 12.2. -/
  RepIndependent : DP → Prop

attribute [instance] FMSetup.cat1 FMSetup.cat2 FMSetup.catP FMSetup.fibcat1 FMSetup.fibcat2
attribute [instance] FMSetup.top

namespace FMSetup

variable (X : FMSetup)

/-- **Definition 12.1**: `FM(K)` is the set of points `p ∈ |S|` at which the fibre
integral transform `Φ_{L(t')^*K}` is an equivalence. -/
def FM (K : X.DP) : Set X.Base :=
  {p | (X.fibreTransform K p).IsEquivalence}

/-- **Definition 12.1**: `fm(K)` is the set of points `p ∈ |S|` at which the fibre
integral transform is fully faithful. -/
def fm (K : X.DP) : Set X.Base :=
  {p | (X.fibreTransform K p).Full ∧ (X.fibreTransform K p).Faithful}

theorem mem_FM {K : X.DP} {p : X.Base} :
    p ∈ X.FM K ↔ (X.fibreTransform K p).IsEquivalence := Iff.rfl

theorem mem_fm {K : X.DP} {p : X.Base} :
    p ∈ X.fm K ↔ (X.fibreTransform K p).Full ∧ (X.fibreTransform K p).Faithful := Iff.rfl

end FMSetup

/-- A base change `t : T ⟶ S` of relative Fourier--Mukai setups: the induced map on
points and the derived pullback of kernels. -/
structure BaseChange (X : FMSetup.{u, v}) where
  /-- The pulled back setup over `T`. -/
  over : FMSetup.{u, v}
  /-- The map `|T| ⟶ |S|`. -/
  ptMap : over.Base → X.Base
  /-- Derived pullback of kernels along `t' : Y₁ ×_S Y₂ ×_S T ⟶ Y₁ ×_S Y₂`. -/
  pullKernel : X.DP → over.DP

end RelativeFM
