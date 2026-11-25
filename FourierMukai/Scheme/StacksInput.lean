/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.AffineJUpperTensorHom
import FourierMukai.Scheme.AffineLocalCohomologyRingObject
import FourierMukai.Scheme.Duality
import FourierMukai.Scheme.Perfect

/-!
# A tagged interface to AxiomMath/Stacks

The AxiomMath/Stacks checkout cannot be imported by the Lean 4.33.1 build used
here. This file records propositions used from it as fields of `Prop`-valued
structures. No declaration imports, or claims to import, the Stacks library.

For the affine recollement there are two deliberately separate inputs:

* the derived tensor--Hom package, represented by `DerivedTensorHomData`; and
* **Stacks 0A6R**, the normalized Čech formula for local cohomology.

In particular, 0A6R is not the tensor--Hom adjunction. The AxiomMath source
which fixes the statement and its normalization is
`Stacks.LocalCohomology.CechFormula.localCohomologyCechIso` and
`localCohomologyCechIso_comp_augmentation` in
`RingTheory/LocalCohomology/CechFormula/Basic.lean`.

All declarations are in `RelativeFM.StacksInterface`.
-/

@[expose] public section

namespace RelativeFM.StacksInterface

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry
open RelativeFM RelativeFM.AffineLocalCohomology
open RelativeFM.TensorHom.ConcreteC

universe v u w

/-! ## Affine local cohomology: Stacks 0A6R -/

/-- Concrete tensor data against which the affine form of Stacks 0A6R is
stated. The second field is the augmentation
`C(f) ⊗^L_A (-) ⟶ 𝟙`, with `C(f) = RΓ_Z(A)` equal to the one-generator
extended Čech object. Supplying this map is part of constructing the derived
tensor package; it is not a `True` placeholder or an assertion of 0A6R. -/
structure AffineCechTensorData (A : Type u) [CommRing A] (f : A) where
  tensorHom : DerivedTensorHomData (AffineD A)
  cechToId : tensorHom.tensorLeft (ringLocalCohomologyObject A f) ⟶ 𝟭 (AffineD A)

namespace AffineCechTensorData

variable {A : Type u} [CommRing A] {f : A} (G : AffineCechTensorData A f)

/-- **Stacks Project, Tag 0A6R (Lemma 47.9.1), one-generator affine form.**
There is a natural isomorphism `RΓ_Z ≅ C(f) ⊗^L_A (-)` on `D(A)`,
normalized so that composition with the Čech augmentation is the canonical
local-cohomology counit.

This is AxiomMath/Stacks `localCohomologyCechIso` together with
`localCohomologyCechIso_comp_augmentation`, specialized to `I = (f)`. -/
def Tag0A6R : Prop :=
  ∃ e : derivedFunctor A f ≅
      G.tensorHom.tensorLeft (ringLocalCohomologyObject A f),
    e.hom ≫ G.cechToId = derivedCounit A f

/-- The external algebraic-geometric proposition which turns a derived
tensor--Hom package into the remaining adjoint of affine local cohomology.
The tensor package itself is a parameter and can instead be proved internally. -/
structure AffineStacksInput (G : AffineCechTensorData A f) : Prop where
  /-- AxiomMath/Stacks, Tag **0A6R**, including its counit normalization. -/
  tag_0A6R : Tag0A6R G

variable (I : AffineStacksInput G)

/-- The Čech isomorphism supplied by 0A6R. -/
noncomputable def cechIso : derivedFunctor A f ≅
    G.tensorHom.tensorLeft (ringLocalCohomologyObject A f) :=
  I.tag_0A6R.choose

/-- The normalization of the Čech isomorphism, as required by 0A6R. -/
theorem cechIso_comp_cechToId :
    (cechIso G I).hom ≫ G.cechToId = derivedCounit A f :=
  I.tag_0A6R.choose_spec

/-- Transport the formula from the explicit local-cohomology functor to the
supported functor used by the recollement. -/
noncomputable def supportedCechIso :
    jStar A f ⋙ affineDZι A f ≅
      G.tensorHom.tensorLeft (ringLocalCohomologyObject A f) :=
  jStarFactors A f ≪≫ cechIso G I

/-- **Conditional construction of `jStar ⊣ jUpper`.** The only Stacks input
is 0A6R; the adjunction itself comes from `G.tensorHom`, not from 0A6R. -/
noncomputable def jStarAdj :
    jStar A f ⊣
      affineDZι A f ⋙
        G.tensorHom.rhom.obj (Opposite.op (ringLocalCohomologyObject A f)) :=
  Recollement.JUpperM1.TensorHom.jStarAdj A f
    (G.tensorHom.tensorLeft (ringLocalCohomologyObject A f))
    (G.tensorHom.rhom.obj (Opposite.op (ringLocalCohomologyObject A f)))
    (G.tensorHom.tensorHomAdj (ringLocalCohomologyObject A f))
    (supportedCechIso G I)

/-- The full package of shift, exactness and full-faithfulness consequences
already proved in `AffineJUpperAdjoint`. -/
noncomputable def jUpperConsequences :
    Recollement.JUpperM1.Consequences A f
      (Recollement.JUpperM1.TensorHom.jUpper A f
        (G.tensorHom.rhom.obj (Opposite.op (ringLocalCohomologyObject A f))))
      (jStarAdj G I) :=
  Recollement.JUpperM1.TensorHom.consequences A f
    (G.tensorHom.tensorLeft (ringLocalCohomologyObject A f))
    (G.tensorHom.rhom.obj (Opposite.op (ringLocalCohomologyObject A f)))
    (G.tensorHom.tensorHomAdj (ringLocalCohomologyObject A f))
    (supportedCechIso G I)

end AffineCechTensorData

/-! ## The internal-Hom and duality statements used by GL26 -/

/-- The object predicates needed to state the internal-Hom theorems without
pretending that Mathlib 4.33.1 already has algebraic spaces or their coherent
derived categories.  Instantiating these predicates is geometry; the theorems
asserted below are not built into the signature. -/
structure InternalHomSignature (D : Type u) [Category.{v} D] where
  rhom : Dᵒᵖ ⥤ D ⥤ D
  dqCoh : ObjectProperty D
  dPlusQCoh : ObjectProperty D
  dMinusCoh : ObjectProperty D
  dPlusCoh : ObjectProperty D
  pseudocoherent : ObjectProperty D
  perfect : ObjectProperty D
  locallyBoundedBelow : ObjectProperty D
  locallyNoetherian : Prop

namespace InternalHomSignature

variable {D : Type u} [Category.{v} D] (G : InternalHomSignature D)

/-- Stacks 0A8A, with the two alternatives in the source kept as a
disjunction rather than split into differently named assumptions. -/
def Tag0A8A : Prop :=
  ∀ K L : D,
    (G.pseudocoherent K ∧ G.dPlusQCoh L) ∨ (G.perfect K ∧ G.dqCoh L) →
      G.dqCoh ((G.rhom.obj (Opposite.op K)).obj L)

/-- The two global-clause conclusions of Stacks 0A6H(1),(2), namely the
quasi-coherence and local-lower-bound assertions used by GL26.  The affine
comparison clauses (3)(a),(3)(b) and the Ext-sheaf clause (4) are intentionally
not smuggled into this signature. -/
def Tag0A6H_global : Prop :=
  (∀ K L : D, G.pseudocoherent K → G.dPlusQCoh L →
      G.dqCoh ((G.rhom.obj (Opposite.op K)).obj L) ∧
        G.locallyBoundedBelow ((G.rhom.obj (Opposite.op K)).obj L)) ∧
  (∀ K L : D, G.perfect K → G.dqCoh L →
      G.dqCoh ((G.rhom.obj (Opposite.op K)).obj L))

/-- Stacks 0D0S in its full coherent form. -/
def Tag0D0S : Prop :=
  G.locallyNoetherian → ∀ K L : D, G.dMinusCoh K → G.dPlusCoh L →
    G.dPlusCoh ((G.rhom.obj (Opposite.op K)).obj L)

end InternalHomSignature

/-- Raw functors for one quasi-compact quasi-separated morphism.  None of the
adjunctions or boundedness conclusions is a field of this signature. -/
structure UpperCrossSignature (DX DY : Type u) [Category.{v} DX] [Category.{v} DY] where
  pull : DX ⥤ DY
  push : DY ⥤ DX
  upperCross : DX ⥤ DY
  homologyIsZeroX : DX → ℤ → Prop
  homologyIsZero : DY → ℤ → Prop
  qcqs : Prop

namespace UpperCrossSignature

variable {DX DY : Type u} [Category.{v} DX] [Category.{v} DY]
  (A : UpperCrossSignature DX DY)

/-- Bounded-below objects on the target of `f`, stated through the same
cohomology-vanishing predicate as 0E56. -/
def BoundedBelowSource : ObjectProperty DX := fun K =>
  ∃ c : ℤ, ∀ i : ℤ, i ≤ c → A.homologyIsZeroX K i

/-- Bounded-below objects on the source of `f`. -/
def BoundedBelow : ObjectProperty DY := fun K =>
  ∃ c : ℤ, ∀ i : ℤ, i ≤ c → A.homologyIsZero K i

/-- Stacks 0E56, including its quantitative loss `N` of a lower bound. -/
def Tag0E56 : Prop := A.qcqs →
  ∃ N : ℤ, ∀ (K : DX) (c : ℤ),
    (∀ i : ℤ, i ≤ c → A.homologyIsZeroX K i) →
      ∀ i : ℤ, i ≤ c - N → A.homologyIsZero (A.upperCross.obj K) i

end UpperCrossSignature

/-- The site and derived-restriction data for 04LX/08JB.  `Site` and `Slice`
are the two ringed-site packages; compatibility with their structure sheaves
is part of the package denoted by `localization`, not a second hidden logical
assumption. -/
structure EtaleRestrictionSignature {D DU : Type u} [Category.{v} D] [Category.{v} DU]
    (G : InternalHomSignature D) (GU : InternalHomSignature DU) where
  Site : Type w
  Slice : Type w
  [siteCategory : Category.{w} Site]
  [sliceCategory : Category.{w} Slice]
  localization : Site ⥤ Slice
  restrict : D ⥤ DU
  comparison (K : D) :
    G.rhom.obj (Opposite.op K) ⋙ restrict ⟶
      restrict ⋙ GU.rhom.obj (Opposite.op (restrict.obj K))

attribute [instance] EtaleRestrictionSignature.siteCategory
  EtaleRestrictionSignature.sliceCategory

/-- The tagged Stacks inputs used in the internal-Hom part of GL26.  Every
field is a proposition with genuine mathematical content.  No field is a
restated conclusion of a GL26 target. -/
structure StacksInput {DX DY DU : Type u}
    [Category.{v} DX] [Category.{v} DY] [Category.{v} DU]
    (G : InternalHomSignature DY) (GU : InternalHomSignature DU)
    (A : UpperCrossSignature DX DY)
    (E : EtaleRestrictionSignature G GU) : Prop where
  /-- Stacks **07A6**: derived pullback is left adjoint to derived
  pushforward, in the qcqs case used here. -/
  tag_07A6 : A.qcqs → Nonempty (A.pull ⊣ A.push)
  /-- Stacks **0E55**: derived pushforward on `D_qc` has a right adjoint. -/
  tag_0E55 : A.qcqs → Nonempty (A.push ⊣ A.upperCross)
  /-- Stacks **0E56**, including the uniform integer `N` in the source. -/
  tag_0E56 : UpperCrossSignature.Tag0E56 A
  /-- Stacks **0A8A**, both alternatives of Lemma 75.13.10. -/
  tag_0A8A : InternalHomSignature.Tag0A8A G
  /-- Stacks **04LX** (especially 04M1/04M3): the small étale ringed site of
  an étale chart is identified with the localized ringed site. -/
  tag_04LX : E.localization.IsEquivalence
  /-- Stacks **08JB**: derived internal Hom commutes with restriction. -/
  tag_08JB : ∀ K : DY, IsIso (E.comparison K)
  /-- Stacks **0A6H(1),(2)**.  These are the global scheme clauses GL26
  uses to pass from `D_qc` to `D^+_qc`; clauses (3),(4) are separate affine
  comparison statements and are not silently claimed by this field. -/
  tag_0A6H : InternalHomSignature.Tag0A6H_global G
  /-- Stacks **0D0S**: coherent bounded-below cohomology of derived Hom on a
  locally Noetherian algebraic space. -/
  tag_0D0S : InternalHomSignature.Tag0D0S G

namespace StacksInput

variable {DX DY DU : Type u} [Category.{v} DX] [Category.{v} DY] [Category.{v} DU]
  {G : InternalHomSignature DY} {GU : InternalHomSignature DU}
  {A : UpperCrossSignature DX DY} {E : EtaleRestrictionSignature G GU}
  (I : StacksInput G GU A E)

include I

/-- The non-quantitative corollary of 0E56: `f^×` preserves bounded-below
objects.  This is proved from the quantitative field, not separately assumed. -/
theorem upperCross_maps_boundedBelow {K : DX} (hq : A.qcqs)
    (hK : A.BoundedBelowSource K) : A.BoundedBelow (A.upperCross.obj K) := by
  obtain ⟨N, hN⟩ := StacksInput.tag_0E56 I hq
  obtain ⟨c, hc⟩ := hK
  exact ⟨c - N, hN K c hc⟩

/-- Use 0A8A and the local lower-bound clause of 0A6H to obtain the exact
`D^+_qc` combination needed in GL26 Lemma `lem:quasi-perfect_bounded`. -/
theorem rhom_mem_dqCoh_and_locallyBoundedBelow {K L : DY}
    (hK : G.pseudocoherent K) (hL : G.dPlusQCoh L) :
    G.dqCoh ((G.rhom.obj (Opposite.op K)).obj L) ∧
      G.locallyBoundedBelow ((G.rhom.obj (Opposite.op K)).obj L) := by
  have hq : G.dqCoh ((G.rhom.obj (Opposite.op K)).obj L) :=
    StacksInput.tag_0A8A I K L (Or.inl ⟨hK, hL⟩)
  exact ⟨hq, ((StacksInput.tag_0A6H I).1 K L hK hL).2⟩

end StacksInput

/-! ## Projection formula and Tor-independent base change -/

/-- Raw monoidality and projection-formula transformations.  Their
invertibility is not part of the data.  The projection-formula orientation is
opposite to the displayed map in Stacks 08IN, which is harmless for an `IsIso`
assertion and agrees with `Duality`. -/
structure ProjectionFormulaSignature {DX DY : Type u} [Category.{v} DX] [Category.{v} DY]
    (TX : DerivedTensorHomData DX) (TY : DerivedTensorHomData DY)
    (A : UpperCrossSignature DX DY) where
  pullTensor : (A.pull.prod A.pull) ⋙ TY.tensor ⟶ TX.tensor ⋙ A.pull
  projectionFormula :
    ((𝟭 DY).prod A.pull) ⋙ TY.tensor ⋙ A.push ⟶
      (A.push.prod (𝟭 DX)) ⋙ TX.tensor

/-- A raw base-change transformation together with the geometric hypotheses
required by 08IR. -/
structure TorIndependentBaseChangeSignature (C D : Type u)
    [Category.{v} C] [Category.{v} D] where
  sourceFunctor : C ⥤ D
  targetFunctor : C ⥤ D
  comparison : sourceFunctor ⟶ targetFunctor
  qcqs : Prop
  torIndependent : Prop

/-- Monoidality and the two tagged propositions used by GL26 Lemma 2.26. -/
structure MorphismStacksInput {DX DY C D : Type u}
    [Category.{v} DX] [Category.{v} DY] [Category.{v} C] [Category.{v} D]
    {TX : DerivedTensorHomData DX} {TY : DerivedTensorHomData DY}
    {A : UpperCrossSignature DX DY}
    (P : ProjectionFormulaSignature TX TY A)
    (B : TorIndependentBaseChangeSignature C D) : Prop where
  /-- Stacks **07A4**: derived pullback is monoidal. -/
  tag_07A4 : IsIso P.pullTensor
  /-- Stacks **08IN**, the projection formula for a qcqs morphism. -/
  tag_08IN : A.qcqs → IsIso P.projectionFormula
  /-- Stacks **08IR**, invertibility of Tor-independent derived base change. -/
  tag_08IR : B.qcqs → B.torIndependent → IsIso B.comparison

/-! ## Perfect duality -/

/-- Raw maps whose invertibility is supplied by 08J9/08JJ. -/
structure PerfectDualitySignature {D : Type u} [Category.{v} D]
    (T : DerivedTensorHomData D) where
  perfect : ObjectProperty D
  doubleDual (K : D) : K ⟶ T.dual (T.dual K)
  currying (L M : D) :
    T.rhom.obj (Opposite.op (T.tensor.obj (L, M))) ⟶
      T.rhom.obj (Opposite.op M) ⋙ T.rhom.obj (Opposite.op L)
  dualTensor (K : D) : T.tensorLeft (T.dual K) ⟶ T.rhom.obj (Opposite.op K)
  rhomTensor (K M : D) :
    T.rhom.obj (Opposite.op M) ⋙ T.tensorLeft K ⟶
      T.rhom.obj (Opposite.op (T.rhomObj K M))

/-- Tagged perfect-duality inputs from GL26 §2. -/
structure PerfectStacksInput {D : Type u} [Category.{v} D]
    {T : DerivedTensorHomData D} (P : PerfectDualitySignature T) : Prop where
  /-- Stacks **08J9**: the internal-Hom currying comparison is invertible. -/
  tag_08J9 : ∀ L M : D, IsIso (P.currying L M)
  /-- Stacks **08JJ**: perfect complexes are derived-reflexive, and tensoring
  with the derived dual of a perfect object is derived internal Hom. -/
  tag_08JJ : (∀ K : D, P.perfect K → IsIso (P.doubleDual K)) ∧
    (∀ K : D, P.perfect K → IsIso (P.dualTensor K))
  /-- The composite comparison of GL26 `lem:rhom_tensor_morphism`, using
  **08J9 and 08JJ**. It is recorded separately because `P.rhomTensor` is a raw
  transformation, not a definitional composite of the preceding maps. -/
  tag_08J9_08JJ_rhomTensor : ∀ K M : D, P.perfect K → IsIso (P.rhomTensor K M)

namespace PerfectStacksInput

variable {D : Type u} [Category.{v} D] {T : DerivedTensorHomData D}
  {P : PerfectDualitySignature T} (I : PerfectStacksInput P)

include I

/-- Fill the existing `PerfectDualityData` interface from the tagged input. -/
noncomputable def toPerfectDualityData : PerfectDualityData T where
  Perf := P.perfect
  doubleDual := P.doubleDual
  doubleDual_isIso := I.tag_08JJ.1
  rhomTensor := P.rhomTensor
  rhomTensor_isIso K hK M := I.tag_08J9_08JJ_rhomTensor K M hK
  dualTensor K hK := by
    letI := I.tag_08JJ.2 K hK
    exact asIso (P.dualTensor K)

end PerfectStacksInput

/-! ## The affine comparison clauses of 0A6H -/

/-- Raw module and sheaf derived-Hom functors and the canonical affine
comparison.  `M` is intended to be `D(A)` and `S` the derived category of
`𝒪_{Spec A}`-modules. -/
structure AffineHomComparisonSignature (M S : Type u)
    [Category.{v} M] [Category.{v} S] where
  moduleRHom : Mᵒᵖ ⥤ M ⥤ M
  sheafRHom : Sᵒᵖ ⥤ S ⥤ S
  tilde : M ⥤ S
  pseudocoherent : ObjectProperty M
  perfect : ObjectProperty M
  boundedBelow : ObjectProperty M
  comparison (K L : M) :
    (sheafRHom.obj (Opposite.op (tilde.obj K))).obj (tilde.obj L) ⟶
      tilde.obj ((moduleRHom.obj (Opposite.op K)).obj L)

/-- The two affine comparison clauses of 0A6H(3), exactly where GL26 needs an
identification rather than merely a quasi-coherence assertion. -/
structure AffineHomStacksInput {M S : Type u} [Category.{v} M] [Category.{v} S]
    (H : AffineHomComparisonSignature M S) : Prop where
  /-- Stacks **0A6H(3)(a)**: for pseudo-coherent `K` and bounded-below `L`,
  the canonical comparison is an isomorphism. -/
  tag_0A6H_3a : ∀ K L : M, H.pseudocoherent K → H.boundedBelow L →
    IsIso (H.comparison K L)
  /-- Stacks **0A6H(3)(b)**: for perfect `K` and arbitrary `L`, the canonical
  comparison is an isomorphism. -/
  tag_0A6H_3b : ∀ K L : M, H.perfect K → IsIso (H.comparison K L)

/-! ## Direct replacements for existing provisional interfaces -/

/-- The direct 06Z0 comparison, offered as an alternative to rebuilding it
from the four auxiliary inputs 01HV/079W/08D4/01XB. -/
structure AffineComparisonStacksInput (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (QCModules A)]
    [HasDerivedCategory.{w} (Spec A).Modules] : Prop where
  /-- Stacks **06Z0**: `D(QCoh(Spec A)) ≌ D_QCoh(O_Spec A)`. -/
  tag_06Z0 : Nonempty (AffineCohomologyComparison A)

namespace AffineComparisonStacksInput

variable {A : CommRingCat.{u}} [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (QCModules A)] [HasDerivedCategory.{w} (Spec A).Modules]
  (I : AffineComparisonStacksInput A)

include I

/-- Extract the direct comparison as data for the existing affine modules. -/
noncomputable def comparison : AffineCohomologyComparison A :=
  Classical.choice I.tag_06Z0

/-- The ring-to-quasicoherent-cohomology comparison obtained directly from
06Z0, bypassing the auxiliary derived-global-sections input. -/
noncomputable def ringCohomologyEquivalence :
    DerivedCategory (ModuleCat.{u} A) ≌ (QuasicoherentCohomology A).FullSubcategory :=
  affineDerivedCohomologyEquivalence A (comparison I)

end AffineComparisonStacksInput

/-- Scheme-level perfectness and compactness, in exactly the shape of the
provisional interfaces in `Scheme/Perfect.lean`. -/
structure SchemePerfectStacksInput (X : Scheme.{u})
    [HasDerivedCategory.{w} X.Modules] [CompactSpace X] [QuasiSeparatedSpace X]
    (H : PerfectToDQCohInterface X) (compact : ObjectProperty (SchemeD X)) : Prop where
  /-- Stacks **08CR**: two-out-of-three for perfect objects in a distinguished
  triangle (in the orientation used by the existing interface). -/
  tag_08CR : ∀ (T : Triangle (SchemeD X)) (_ : T ∈ distTriang (SchemeD X)),
    IsPerfect T.obj₁ → IsPerfect T.obj₃ → IsPerfect T.obj₂
  /-- Stacks **08CS**: perfectness descends to categorical retracts. -/
  tag_08CS : ∀ {E F : SchemeD X}, Retract E F → IsPerfect F → IsPerfect E
  /-- Stacks **09M1**: on the qcqs scheme `X`, compact objects of `D_qc(X)`
  are exactly the perfect objects. -/
  tag_09M1 : PerfectCompactStatement H compact

namespace SchemePerfectStacksInput

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
  [CompactSpace X] [QuasiSeparatedSpace X]
  {H : PerfectToDQCohInterface X} {compact : ObjectProperty (SchemeD X)}
  (I : SchemePerfectStacksInput X H compact)

include I

/-- Fill the pre-existing triangle/retract interface, with no duplicated
mathematical assumption hidden in the constructor. -/
theorem toPerfectThicknessInterface : PerfectThicknessInterface X where
  cone := I.tag_08CR
  retract := I.tag_08CS

/-- Fill the pre-existing compact-versus-perfect interface. -/
def toPerfectCompactInterface : PerfectCompactInterface X H where
  compact := compact
  compact_iff_perfect := I.tag_09M1

end SchemePerfectStacksInput

/-- Preservation of pseudocoherence and perfectness by derived pullback.
These are Stacks 08H4 and 08H6 respectively. -/
structure PullbackStacksInput {DX DY : Type u} [Category.{v} DX] [Category.{v} DY]
    (GX : InternalHomSignature DX) (GY : InternalHomSignature DY)
    (A : UpperCrossSignature DX DY) : Prop where
  /-- Stacks **08H4**: derived pullback preserves pseudocoherence. -/
  tag_08H4 : A.qcqs → ∀ E : DX, GX.pseudocoherent E →
    GY.pseudocoherent (A.pull.obj E)
  /-- Stacks **08H6**: derived pullback preserves perfectness. -/
  tag_08H6 : A.qcqs → ∀ E : DX, GX.perfect E → GY.perfect (A.pull.obj E)

/-- Quasi-coherent closure of the derived tensor, Stacks 08F5.  The
associated sheaf/monoidal construction cited alongside it as 0FPQ is part of
`DerivedTensorHomData`, not a second vacuous proposition. -/
structure TensorStacksInput {D : Type u} [Category.{v} D]
    (G : InternalHomSignature D) (T : DerivedTensorHomData D) : Prop where
  /-- Stacks **08F5**: the derived tensor of two objects with quasi-coherent
  cohomology again has quasi-coherent cohomology. -/
  tag_08F5 : ∀ E F : D, G.dqCoh E → G.dqCoh F → G.dqCoh (T.tensor.obj (E, F))

#print axioms RelativeFM.StacksInterface.AffineCechTensorData.cechIso_comp_cechToId
#print axioms RelativeFM.StacksInterface.AffineCechTensorData.jStarAdj
#print axioms RelativeFM.StacksInterface.AffineCechTensorData.jUpperConsequences
#print axioms RelativeFM.StacksInterface.StacksInput.upperCross_maps_boundedBelow
#print axioms RelativeFM.StacksInterface.StacksInput.rhom_mem_dqCoh_and_locallyBoundedBelow
#print axioms RelativeFM.StacksInterface.AffineComparisonStacksInput.ringCohomologyEquivalence
#print axioms RelativeFM.StacksInterface.SchemePerfectStacksInput.toPerfectThicknessInterface
#print axioms RelativeFM.StacksInterface.SchemePerfectStacksInput.toPerfectCompactInterface
#print axioms RelativeFM.StacksInterface.PerfectStacksInput.toPerfectDualityData

end RelativeFM.StacksInterface
