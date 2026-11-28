/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Duality.Basic
import Spaces.InternalHom.TensorHom
import Spaces.BaseChange.Inputs

/-!
# GL26 Lemma 5.9 (`lem:neeman23lem5_3`): `Rf_* 𝐑𝓗om(E, f^× P) ≅ 𝐑𝓗om(Rf_* E, P)`

Guisado Villalgordo–Lank (GL26), §5 (`sec:quasi-perfect`), **Lemma 5.9** (`lem:neeman23lem5_3`):
let `f : Y ⟶ X` be a morphism of quasi-compact quasi-separated algebraic spaces.  For
`E ∈ D_qc(Y)` and `P ∈ D_qc(X)` there is an isomorphism

`Rf_* 𝐑𝓗om(E, f^× P) ≅ 𝐑𝓗om(Rf_* E, P)`,

with `𝐑𝓗om` the internal Hom of `D_qc` (bold in GL26; `Spaces/InternalHom/Basic.lean`, `qcHom`),
`f^×` the right adjoint of `Rf_* : D_qc(Y) ⥤ D_qc(X)` (`Spaces/Duality/Basic.lean`, `upperTimes`).

## Proof

GL26's proof is a Yoneda chain in `A ∈ D_qc(X)`: pull/push, tensor/hom, `Rf_* ⊣ f^×`, the projection
formula, tensor/hom.  Here it is the same argument, phrased as uniqueness of right adjoints:

* `P ↦ Rf_* 𝐑𝓗om(E, f^× P)` is right adjoint to `A ↦ Rf_*(Lf^*A ⊗^L E)`, the composite of the
  three adjunctions `Lf^* ⊣ Rf_*` (Stacks 07A6, restricted to `D_qc`: `pullQcPushQcAdj`),
  `- ⊗^L E ⊣ 𝐑𝓗om(E, -)` (`tensorQcRightQcHomAdj`) and `Rf_* ⊣ f^×` (`upperTimesAdj`);
* `P ↦ 𝐑𝓗om(Rf_* E, P)` is right adjoint to `A ↦ A ⊗^L Rf_* E`;
* the two left adjoints are isomorphic by the projection formula (Stacks 08IN,
  `BaseChange.Tag08INInput`) and the symmetry of `⊗^L` (`tensorBraiding`): `projIsoQc`;
* Mathlib's `conjugateIsoEquiv` turns that isomorphism of left adjoints into one of right
  adjoints.

The isomorphism is therefore natural in `P` (an isomorphism of functors `D_qc(X) ⥤ D_qc(X)`).

## Statement and differences from GL26

* `lemma_5_9_of_adj` is stated for *any* right adjoints `R_E` of `- ⊗^L E` on `D_qc(Y)` and
  `R_{Rf_*E}` of `- ⊗^L Rf_*E` on `D_qc(X)` (GL26 defines `𝐑𝓗om(E, -)` as such a right adjoint);
  `lemma_5_9` is the case `𝐑𝓗om = Q ∘ R𝓗om(i -, i -)` of Lemma 2.11 for any coherators `Q` of `X`
  and `Y` (which exist for qcqs spaces, `coheratorAdj`).
* The hypothesis on `f` is `IsQcqsHom hZ f` (`Y` quasi-compact and quasi-separated, `X`
  quasi-separated, `f` quasi-compact and quasi-separated), the hypotheses of Stacks 0E55 under
  which `f^×` is defined.  GL26 asks `X` and `Y` qcqs, which implies it; quasi-compactness of `X`
  is used only to construct the coherator of `X`, which is here an argument.
* GL26 states "there exists an isomorphism"; the Lean statement gives one natural in `P`.

## Assumptions

AxiomMath theorems only, as tagged inputs already in the tree: `Tag08F4Input`, `Tag08F5Input`,
`Tag08FAInput`, `Duality.Tag0E55Input`, `BaseChange.Tag08INInput`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space Opposite

namespace RelativeFM.Spaces.QuasiPerfect

open RelativeFM.Spaces RelativeFM.Spaces.Duality RelativeFM.Spaces.BaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### `Lf^* ⊣ Rf_*` on `D_qc` -/

section PullPush

variable (h08F4 : Tag08F4Input B S hS) (h08FA : Tag08FAInput B S hS)

/-- **`Lf^* ⊣ Rf_*` on `D_qc`** (Stacks 07A6, restricted to the full subcategories along
Stacks 08F4 and 08FA; Mathlib's `Adjunction.restrictFullyFaithful`). -/
def pullQcPushQcAdj {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    pullQc h08F4 f ⊣ pushQc h08FA f hfqc hfqs :=
  (pullPushAdj f).restrictFullyFaithful (Dqc X).fullyFaithfulι (Dqc Y).fullyFaithfulι
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

end PullPush

/-! ### The projection formula as an isomorphism of functors -/

section Projection

variable {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)

/-- The projection map `Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` (AxiomMath's
`smallEtaleProjectionFormulaMap`, `BaseChange.projectionFormulaMap`) is natural in `K`. -/
theorem projectionFormulaMap_naturality (E : D B S hS Y) {K K' : D B S hS X} (k : K ⟶ K') :
    ((tensor X).obj ((push f).obj E)).map k ≫ projectionFormulaMap f E K' =
      projectionFormulaMap f E K ≫ (push f).map (((tensor Y).obj E).map ((pull f).map k)) := by
  unfold projectionFormulaMap
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  have h := (smallEtaleDerivedPullbackTensorIso f).hom.naturality
    ((𝟙 ((push f).obj E), k) : ((push f).obj E, K) ⟶ ((push f).obj E, K'))
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id] at h ⊢
  rw [reassoc_of% h]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Functor.prod_obj, Category.assoc]
  refine congrArg
    (fun φ => (smallEtaleDerivedPullbackTensorIso f).hom.app ((push f).obj E, K) ≫ φ) ?_
  exact (Category.id_comp _).trans
    (((tensor Y).map ((pullPushAdj f).counit.app E)).naturality ((pull f).map k))

/-- **The projection formula, natural in `A`**: `A ⊗^L Rf_*E ⟶ Rf_*(Lf^*A ⊗^L E)`, the symmetry
of `⊗^L` followed by the projection map and by `Rf_*` of the symmetry. -/
def projNatTrans (E : D B S hS Y) :
    (tensor X).flip.obj ((push f).obj E) ⟶ pull f ⋙ (tensor Y).flip.obj E ⋙ push f where
  app A := ((tensorBraiding X).hom.app A).app ((push f).obj E) ≫ projectionFormulaMap f E A ≫
    (push f).map (((tensorBraiding Y).hom.app E).app ((pull f).obj A))
  naturality {A A'} a := by
    have h₁ := congrArg (fun φ => φ.app ((push f).obj E)) ((tensorBraiding X).hom.naturality a)
    have h₂ := ((tensorBraiding Y).hom.app E).naturality ((pull f).map a)
    simp only [NatTrans.comp_app, Functor.flip_map_app, Functor.flip_obj_map] at h₁ h₂
    simp only [Functor.flip_obj_obj, Functor.comp_obj, Functor.flip_obj_map, Functor.comp_map,
      Category.assoc]
    rw [reassoc_of% h₁, reassoc_of% (projectionFormulaMap_naturality f E a), ← Functor.map_comp,
      ← Functor.map_comp, h₂]

variable (h08IN : Tag08INInput B S hS) (h08F4 : Tag08F4Input B S hS) (h08F5 : Tag08F5Input B S hS)
  (h08FA : Tag08FAInput B S hS)

include h08IN in
/-- The components of `projNatTrans` at objects of `D_qc(X)` are invertible, for `E ∈ D_qc(Y)`
(Stacks 08IN, `Tag08INInput`). -/
theorem isIso_projNatTrans_app (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) {E : D B S hS Y} (hE : Dqc Y E) {A : D B S hS X}
    (hA : Dqc X A) : IsIso ((projNatTrans f E).app A) := by
  have := h08IN f hfqc hfqs E hE A hA
  dsimp only [projNatTrans]
  infer_instance

/-- **The projection formula on `D_qc`, natural in `A`**: `A ⊗^L Rf_*E ≅ Rf_*(Lf^*A ⊗^L E)` for
`E ∈ D_qc(Y)`, as an isomorphism of functors `D_qc(X) ⥤ D_qc(X)` (Stacks 08IN). -/
def projIsoQc (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : (Dqc Y).FullSubcategory) :
    tensorQcRight h08F5 ((pushQc h08FA f hfqc hfqs).obj E) ≅
      pullQc h08F4 f ⋙ tensorQcRight h08F5 E ⋙ pushQc h08FA f hfqc hfqs :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _
      (@asIso _ _ _ _ ((projNatTrans f E.obj).app A.obj)
        (isIso_projNatTrans_app f h08IN hfqc hfqs E.property A.property)))
    (fun {_ _} a => ObjectProperty.hom_ext _ ((projNatTrans f E.obj).naturality a.hom))

end Projection

/-! ### Lemma 5.9 -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))
variable (h08IN : Tag08INInput B S hS) (h08F4 : Tag08F4Input B S hS) (h08F5 : Tag08F5Input B S hS)
  (h08FA : Tag08FAInput B S hS) (h0E55 : Tag0E55Input B S hS)

variable {hZ} in
/-- **Lemma 5.9** (`lem:neeman23lem5_3`), for any internal Homs.  Let `f : Y ⟶ X` satisfy the
hypotheses of Stacks 0E55 (`IsQcqsHom`), `E ∈ D_qc(Y)`, and let `R_E` be a right adjoint of
`- ⊗^L E` on `D_qc(Y)` and `R_{Rf_*E}` one of `- ⊗^L Rf_*E` on `D_qc(X)` (GL26's `𝐑𝓗om(E, -)` and
`𝐑𝓗om(Rf_*E, -)`).  Then, naturally in `P ∈ D_qc(X)`,

`Rf_* R_E(f^× P) ≅ R_{Rf_*E}(P)`. -/
def lemma_5_9_of_adj {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsQcqsHom hZ f)
    (E : (Dqc Y).FullSubcategory)
    {RE : (Dqc Y).FullSubcategory ⥤ (Dqc Y).FullSubcategory} (adjE : tensorQcRight h08F5 E ⊣ RE)
    {RF : (Dqc X).FullSubcategory ⥤ (Dqc X).FullSubcategory}
    (adjF : tensorQcRight h08F5 ((pushQc h08FA f hf.qc hf.qs).obj E) ⊣ RF) :
    upperTimes h08FA h0E55 f hf ⋙ RE ⋙ pushQc h08FA f hf.qc hf.qs ≅ RF :=
  conjugateIsoEquiv
    ((pullQcPushQcAdj h08F4 h08FA f hf.qc hf.qs).comp
      (adjE.comp (upperTimesAdj h08FA h0E55 f hf)))
    adjF (projIsoQc f h08IN h08F4 h08F5 h08FA hf.qc hf.qs E)

variable {hZ} in
/-- **Lemma 5.9** (`lem:neeman23lem5_3`).  Let `f : Y ⟶ X` satisfy the hypotheses of Stacks 0E55
(`IsQcqsHom`; e.g. `f` a morphism of qcqs algebraic spaces), `adjX : i ⊣ Q_X`, `adjY : i ⊣ Q_Y`
coherators of `X` and `Y` (they exist for qcqs spaces, `coheratorAdj`), and `E ∈ D_qc(Y)`.  With
`𝐑𝓗om = Q ∘ R𝓗om(i -, i -)` (Lemma 2.11, `qcHom`), there is an isomorphism, natural in
`P ∈ D_qc(X)`,

`Rf_* 𝐑𝓗om(E, f^× P) ≅ 𝐑𝓗om(Rf_* E, P)`. -/
def lemma_5_9 {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsQcqsHom hZ f)
    {QX : D B S hS X ⥤ (Dqc X).FullSubcategory} (adjX : (Dqc X).ι ⊣ QX)
    {QY : D B S hS Y ⥤ (Dqc Y).FullSubcategory} (adjY : (Dqc Y).ι ⊣ QY)
    (E : (Dqc Y).FullSubcategory) :
    upperTimes h08FA h0E55 f hf ⋙ qcHom adjY E ⋙ pushQc h08FA f hf.qc hf.qs ≅
      qcHom adjX ((pushQc h08FA f hf.qc hf.qs).obj E) :=
  lemma_5_9_of_adj h08IN h08F4 h08F5 h08FA h0E55 f hf E (tensorQcRightQcHomAdj h08F5 adjY E)
    (tensorQcRightQcHomAdj h08F5 adjX _)

variable {hZ} in
/-- **Lemma 5.9** (`lem:neeman23lem5_3`) at one object `P ∈ D_qc(X)`:
`Rf_* 𝐑𝓗om(E, f^× P) ≅ 𝐑𝓗om(Rf_* E, P)`. -/
def lemma_5_9_app {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsQcqsHom hZ f)
    {QX : D B S hS X ⥤ (Dqc X).FullSubcategory} (adjX : (Dqc X).ι ⊣ QX)
    {QY : D B S hS Y ⥤ (Dqc Y).FullSubcategory} (adjY : (Dqc Y).ι ⊣ QY)
    (E : (Dqc Y).FullSubcategory) (P : (Dqc X).FullSubcategory) :
    (pushQc h08FA f hf.qc hf.qs).obj ((qcHom adjY E).obj ((upperTimes h08FA h0E55 f hf).obj P)) ≅
      (qcHom adjX ((pushQc h08FA f hf.qc hf.qs).obj E)).obj P :=
  (lemma_5_9 h08IN h08F4 h08F5 h08FA h0E55 f hf adjX adjY E).app P

end RelativeFM.Spaces.QuasiPerfect
