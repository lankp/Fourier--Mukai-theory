/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.InternalHom.TensorHom
import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedBidualNaturality

/-!
# GL26 Lemma 2.10 (`lem:rhom_tensor_morphism`): naturality in `K` and `M`

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), §2.2,
**Lemma 2.10**: for `K` perfect and `L, M ∈ D(X)` a *functorial* isomorphism
`K ⊗^L R𝓗om(M, L) ≅ R𝓗om(R𝓗om(K, M), L)`.  `TensorHom.lean` constructs it (`lemma_2_10`) as an
isomorphism of functors of `L`.  Here it is shown natural in the two other variables:

* `lemma_2_10_naturality_M`: for `m : M' ⟶ M`, the square with `K ⊗ R𝓗om(m, L)` and
  `R𝓗om(R𝓗om(K, m), L)` commutes (both sides are contravariant in `M`);
* `lemma_2_10_naturality_K`: for `k : K ⟶ K'` between perfect objects, the square with
  `k ⊗ R𝓗om(M, L)` and `R𝓗om(R𝓗om(k, M), L)` commutes (both sides are covariant in `K`).

Together with `lemma_2_10_naturality` (in `L`) this is GL26's "functorial" in all three
variables (`K` ranging over perfect objects, as in the lemma).

## Proof

The isomorphism is `K ⊗ - ≅ R𝓗om(K^∨, -)` (whiskered by `R𝓗om(M, -)`) followed by the conjugate
(Mathlib's `conjugateIsoEquiv`) of the isomorphism of left adjoints
`A ⊗ R𝓗om(K, M) ≅ (A ⊗ K^∨) ⊗ M`.  Naturality is then reduced, by Mathlib's calculus of conjugates
(`conjugateEquiv_comp`, `conjugateEquiv_whiskerLeft`, `conjugateEquiv_whiskerRight`), to:

* `conjugateEquiv_tensorSheafHomAdj`: `R𝓗om(φ, -)` is the conjugate of `- ⊗ φ` (from AxiomMath's
  dinaturality of Stacks 08J8, `smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinatural`);
* the naturality of Stacks 08JJ in the dualized object (`sheafHomIsoTensorDualRight_naturality`,
  from AxiomMath's model-level `RingedSite.derivedDualTensorSheafHomIso_naturality_dual`);
* the naturality of `K^∨∨ ≅ K` (`bidualIso_naturality`, from AxiomMath's
  `RingedSite.derivedBidual_naturality`);
* the naturality of the associator and of the symmetry of `⊗^L` (AxiomMath's
  `associatorGeneral_naturality_middle`, `associatorGeneral_naturality_right`).

Everything used is in the `Spaces` import list; there is no tagged input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Space Opposite

namespace RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The dual `g^∨ : E^∨ ⟶ E'^∨` of `g : E' ⟶ E`, i.e. `R𝓗om(g, 𝒪_X)`. -/
abbrev dualMap {E' E : D B S hS X} (g : E' ⟶ E) : dual E ⟶ dual E' :=
  ((sheafHom X).map g.op).app _

/-! ### Naturality of the pieces -/

/-- A diagram chase: from `F δ ≫ J' = J ≫ h` and `m ≫ D' = D ≫ δ` (isomorphisms `J, J', D, D'`)
follows `h ≫ J'⁻¹ ≫ F D'⁻¹ = J⁻¹ ≫ F D⁻¹ ≫ F m`. -/
theorem chase1 {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C') {a b : C'}
    {x y z c : C} (J : F.obj x ≅ a) (J' : F.obj y ≅ b) (h : a ⟶ b) (δ : x ⟶ y)
    (D : z ≅ x) (D' : c ≅ y) (m : z ⟶ c) (hJ : F.map δ ≫ J'.hom = J.hom ≫ h)
    (hD : m ≫ D'.hom = D.hom ≫ δ) :
    h ≫ J'.inv ≫ F.map D'.inv = J.inv ≫ F.map D.inv ≫ F.map m := by
  have h1 : h ≫ J'.inv = J.inv ≫ F.map δ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hJ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h2 : δ ≫ D'.inv = D.inv ≫ m := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hD, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [reassoc_of% h1, ← F.map_comp, h2, F.map_comp]

/-- The shape of `smallEtaleModelDerivedDualIso` (a counit followed by `H(-, s)`) is natural, for
any equivalence `e`, bifunctor `H` and isomorphism `s`. -/
theorem abstract_dualIso_nat {C C' : Type*} [Category C] [Category C'] (e : C ≌ C')
    (H : C'ᵒᵖ ⥤ C' ⥤ C') (O : C) (O' : C') (s : e.functor.obj O ≅ O') {E' E : C} (g : E' ⟶ E) :
    e.functor.map (e.inverse.map ((H.map (e.functor.map g).op).app (e.functor.obj O))) ≫
        (e.counitIso.app _ ≪≫ (H.obj (op (e.functor.obj E'))).mapIso s).hom =
      (e.counitIso.app _ ≪≫ (H.obj (op (e.functor.obj E))).mapIso s).hom ≫
        (H.map (e.functor.map g).op).app O' := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Equivalence.fun_inv_map,
    Category.assoc]
  simp

/-- The identification of the duals with the model (AxiomMath's `smallEtaleModelDerivedDualIso`)
is natural in the dualized object. -/
theorem modelDualIso_naturality {E' E : D B S hS X} (g : E' ⟶ E) :
    (smallEtaleModelDerivedEquivalence B S hS X).functor.map (dualMap g) ≫
        (smallEtaleModelDerivedDualIso B S hS X E').hom =
      (smallEtaleModelDerivedDualIso B S hS X E).hom ≫
        ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.map g).op).app
            (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2)) :=
  abstract_dualIso_nat (smallEtaleModelDerivedEquivalence B S hS X)
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)) _ _
    (smallEtaleModelDerivedStructureSheafIso B S hS X) g

/-- Stacks 08JJ on the model, natural in the dualized object (AxiomMath's
`RingedSite.derivedDualTensorSheafHomIso_naturality_dual`), combined with
`modelDualIso_naturality`. -/
theorem model08JJ_naturality {E' E : D B S hS X} (hE' : Perf X E') (hE : Perf X E) (g : E' ⟶ E)
    (N : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O))) :
    ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
        ((smallEtaleModelDerivedEquivalence B S hS X).functor.map g).op).app
          N ≫
      (RingedSite.derivedDualTensorSheafHomIso _
        ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E')
        N
        (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E' hE')).inv ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2)).obj
          N).map
        (smallEtaleModelDerivedDualIso B S hS X E').inv =
    (RingedSite.derivedDualTensorSheafHomIso _
        ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E)
        N
        (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE)).inv ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2)).obj
          N).map
        (smallEtaleModelDerivedDualIso B S hS X E).inv ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2)).obj
          N).map
        ((smallEtaleModelDerivedEquivalence B S hS X).functor.map (dualMap g)) :=
  chase1 _ _ _ _ _ _ _ _
    (RingedSite.derivedDualTensorSheafHomIso_naturality_dual _
      (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE)
      (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E' hE') _
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.map g))
    (modelDualIso_naturality g)

/-- The shape of `smallEtaleDerivedTensorRightIso` (a tensor product transported along an
equivalence by an isomorphism `τ` of bifunctors) is natural in the tensor factor. -/
theorem abstract_TRI_nat {C C' : Type*} [Category C] [Category C'] (e : C ≌ C')
    (T : C ⥤ C ⥤ C) (T' : C' ⥤ C' ⥤ C')
    (τ : Functor.uncurry.obj T ⋙ e.functor ≅ e.functor.prod e.functor ⋙ Functor.uncurry.obj T')
    {P P' : C} (p : P ⟶ P') :
    T.flip.map p ≫ ((Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ e.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.flipObjIsoOfUncurryIso τ P') _ ≪≫
      Functor.associator _ _ _).hom =
    ((Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ e.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.flipObjIsoOfUncurryIso τ P) _ ≪≫
      Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft e.functor (Functor.whiskerRight (T'.flip.map (e.functor.map p))
          e.inverse) := by
  ext A
  have h := τ.hom.naturality (X := (A, P)) (Y := (A, P')) (Prod.mkHom (𝟙 A) p)
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.flip_map_app, Iso.symm_hom,
    Functor.rightUnitor_inv_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id, Functor.comp_obj,
    Functor.id_obj, Functor.flip_obj_obj, Functor.flipObjIsoOfUncurryIso,
    NatIso.ofComponents_hom_app,
    Iso.app_hom]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Functor.prod_obj] at h
  rw [Category.assoc, ← Functor.map_comp, ← h, Functor.map_comp, ← Category.assoc,
    ← Category.assoc]
  congr 1
  exact e.unitIso.hom.naturality _

/-- AxiomMath's `smallEtaleDerivedTensorRightIso` (tensoring on `X` read on the model) is natural
in the tensor factor. -/
theorem tensorRightIso_naturality {P P' : D B S hS X} (p : P ⟶ P') :
    (tensor X).flip.map p ≫ (smallEtaleDerivedTensorRightIso B S hS X P').hom =
      (smallEtaleDerivedTensorRightIso B S hS X P).hom ≫
        Functor.whiskerLeft (smallEtaleModelDerivedEquivalence B S hS X).functor
          (Functor.whiskerRight ((Stacks.SheafOfModules.derivedTensorProductFunctor
            (smallEtaleModelRingedSite B S hS X.1 X.2)).flip.map
              ((smallEtaleModelDerivedEquivalence B S hS X).functor.map p))
            (smallEtaleModelDerivedEquivalence B S hS X).inverse) :=
  abstract_TRI_nat _ _ _ (smallEtaleModelDerivedTensorIso B S hS X) p

/-- The shape of `sheafHomIsoTensorDualRight`, natural in the dualized object as soon as its
model-level pieces are (`hnat`, `hT`). -/
theorem abstract_sHITDR_nat {C C' : Type*} [Category C] [Category C'] (e : C ≌ C')
    (H' : C'ᵒᵖ ⥤ C' ⥤ C') (T : C ⥤ C ⥤ C) (T' : C' ⥤ C' ⥤ C')
    {E' E : C} (g : E' ⟶ E) {dE dE' : C} (m : dE ⟶ dE') {d d' : C'}
    (nat : T'.flip.obj d ≅ H'.obj (op (e.functor.obj E)))
    (nat' : T'.flip.obj d' ≅ H'.obj (op (e.functor.obj E')))
    (dI : e.functor.obj dE ≅ d) (dI' : e.functor.obj dE' ≅ d')
    (TRI : T.flip.obj dE ≅ e.functor ⋙ T'.flip.obj (e.functor.obj dE) ⋙ e.inverse)
    (TRI' : T.flip.obj dE' ≅ e.functor ⋙ T'.flip.obj (e.functor.obj dE') ⋙ e.inverse)
    (hnat : ∀ N', (H'.map (e.functor.map g).op).app N' ≫ nat'.inv.app N' ≫
        (T'.obj N').map dI'.inv =
      nat.inv.app N' ≫ (T'.obj N').map dI.inv ≫ (T'.obj N').map (e.functor.map m))
    (hT : TRI.inv ≫ T.flip.map m =
      Functor.whiskerLeft e.functor (Functor.whiskerRight (T'.flip.map (e.functor.map m))
        e.inverse) ≫ TRI'.inv) :
    Functor.whiskerLeft e.functor (Functor.whiskerRight (H'.map (e.functor.map g).op)
        e.inverse) ≫
      ((Iso.refl _ : e.functor ⋙ H'.obj (op (e.functor.obj E')) ⋙ e.inverse ≅ _) ≪≫
        Functor.isoWhiskerLeft e.functor (Functor.isoWhiskerRight nat'.symm e.inverse) ≪≫
        Functor.isoWhiskerLeft e.functor (Functor.isoWhiskerRight (T'.flip.mapIso dI'.symm)
          e.inverse) ≪≫ TRI'.symm).hom =
    ((Iso.refl _ : e.functor ⋙ H'.obj (op (e.functor.obj E)) ⋙ e.inverse ≅ _) ≪≫
        Functor.isoWhiskerLeft e.functor (Functor.isoWhiskerRight nat.symm e.inverse) ≪≫
        Functor.isoWhiskerLeft e.functor (Functor.isoWhiskerRight (T'.flip.mapIso dI.symm)
          e.inverse) ≪≫ TRI.symm).hom ≫ T.flip.map m := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Category.id_comp, Category.assoc, hT]
  ext N
  have := congrArg e.inverse.map (hnat (e.functor.obj N))
  simp only [Functor.map_comp] at this
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.flip_map_app, ← Category.assoc] at this ⊢
  rw [this]

/-- **Stacks 08JJ natural in the dualized object**: for `g : E' ⟶ E` between perfect objects,
`R𝓗om(g, -)` and `- ⊗ g^∨` correspond under `R𝓗om(E, -) ≅ - ⊗ E^∨`. -/
theorem sheafHomIsoTensorDualRight_naturality {E' E : D B S hS X} (hE' : Perf X E')
    (hE : Perf X E) (g : E' ⟶ E) :
    (sheafHom X).map g.op ≫ (sheafHomIsoTensorDualRight E' hE').hom =
      (sheafHomIsoTensorDualRight E hE).hom ≫ (tensor X).flip.map (dualMap g) := by
  have hT : (smallEtaleDerivedTensorRightIso B S hS X (dual E)).inv ≫
      (tensor X).flip.map (dualMap g) =
      Functor.whiskerLeft (smallEtaleModelDerivedEquivalence B S hS X).functor
          (Functor.whiskerRight ((Stacks.SheafOfModules.derivedTensorProductFunctor
            (smallEtaleModelRingedSite B S hS X.1 X.2)).flip.map
              ((smallEtaleModelDerivedEquivalence B S hS X).functor.map (dualMap g)))
            (smallEtaleModelDerivedEquivalence B S hS X).inverse) ≫
        (smallEtaleDerivedTensorRightIso B S hS X (dual E')).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← tensorRightIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  unfold sheafHomIsoTensorDualRight
  refine abstract_sHITDR_nat _
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)) _ _ g
    (dualMap g) _ _ _ _ _ _ ?_ hT
  intro N'
  exact model08JJ_naturality hE' hE g N'

/-- The shape of `smallEtaleDerivedBidualIso` (a preimage under an equivalence of a composite of
duality isomorphisms and an inverted bidual map) is natural, given the naturality of its pieces. -/
theorem abstract_bidual_nat {C C' : Type*} [Category C] [Category C'] (e : C ≌ C')
    (H' : C'ᵒᵖ ⥤ C' ⥤ C') (O' : C') {K K' dK dK' ddK ddK' : C} (k : K ⟶ K') (dk : dK' ⟶ dK)
    (ddk : ddK ⟶ ddK')
    (dIK : e.functor.obj dK ≅ (H'.obj (op (e.functor.obj K))).obj O')
    (dIK' : e.functor.obj dK' ≅ (H'.obj (op (e.functor.obj K'))).obj O')
    (dIdK : e.functor.obj ddK ≅ (H'.obj (op (e.functor.obj dK))).obj O')
    (dIdK' : e.functor.obj ddK' ≅ (H'.obj (op (e.functor.obj dK'))).obj O')
    (β : e.functor.obj K ⟶ (H'.obj (op ((H'.obj (op (e.functor.obj K))).obj O'))).obj O')
    (β' : e.functor.obj K' ⟶ (H'.obj (op ((H'.obj (op (e.functor.obj K'))).obj O'))).obj O')
    (hβi : IsIso β) (hβi' : IsIso β')
    (hβ : e.functor.map k ≫ β' = β ≫ (H'.map ((H'.map (e.functor.map k).op).app O').op).app O')
    (hD1 : e.functor.map ddk ≫ dIdK'.hom = dIdK.hom ≫ (H'.map (e.functor.map dk).op).app O')
    (hD2 : e.functor.map dk ≫ dIK.hom = dIK'.hom ≫ (H'.map (e.functor.map k).op).app O') :
    ddk ≫ (e.fullyFaithfulFunctor.preimageIso
        (dIdK' ≪≫ (H'.mapIso dIK'.op.symm).app O' ≪≫ (@asIso _ _ _ _ β' hβi').symm)).hom =
      (e.fullyFaithfulFunctor.preimageIso
        (dIdK ≪≫ (H'.mapIso dIK.op.symm).app O' ≪≫ (@asIso _ _ _ _ β hβi).symm)).hom ≫ k := by
  apply e.functor.map_injective
  have h2 : dIK'.inv ≫ e.functor.map dk = (H'.map (e.functor.map k).op).app O' ≫ dIK.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hD2, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hβ' : (H'.map ((H'.map (e.functor.map k).op).app O').op).app O' ≫ inv β' =
      inv β ≫ e.functor.map k := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hβ, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.op_inv, asIso_inv,
    Category.assoc]
  rw [reassoc_of% hD1, ← NatTrans.comp_app_assoc, ← H'.map_comp, ← op_comp, h2, op_comp,
    H'.map_comp, NatTrans.comp_app_assoc, hβ']

/-- **`K^∨∨ ≅ K` is natural** (AxiomMath's `smallEtaleDerivedBidualIso`, from
`RingedSite.derivedBidual_naturality`): `k^∨∨ ≫ (K'^∨∨ ≅ K') = (K^∨∨ ≅ K) ≫ k`. -/
theorem bidualIso_naturality {K K' : D B S hS X} (hK : Perf X K) (hK' : Perf X K')
    (k : K ⟶ K') :
    dualMap (dualMap k) ≫ (smallEtaleDerivedBidualIso B S hS X K' hK').hom =
      (smallEtaleDerivedBidualIso B S hS X K hK).hom ≫ k := by
  unfold smallEtaleDerivedBidualIso
  refine abstract_bidual_nat (smallEtaleModelDerivedEquivalence B S hS X)
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)) _ k
    (dualMap k) (dualMap (dualMap k)) _ _ _ _ _ _ ?_ ?_ ?_ (modelDualIso_naturality (dualMap k))
    (modelDualIso_naturality k)
  exact RingedSite.derivedBidual_naturality (smallEtaleModelRingedSite B S hS X.1 X.2)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (smallEtaleModelRingedSite B S hS X.1 X.2))
    ((smallEtaleModelDerivedEquivalence B S hS X).functor.map k)

/-- `R𝓗om(K^∨, -) ≅ - ⊗ K` (`sheafHomDualIsoTensorRight`) is natural in the perfect object `K`. -/
theorem sheafHomDualIsoTensorRight_naturality {K K' : D B S hS X} (hK : Perf X K)
    (hK' : Perf X K') (k : K ⟶ K') :
    (sheafHom X).map (dualMap k).op ≫ (sheafHomDualIsoTensorRight K' hK').hom =
      (sheafHomDualIsoTensorRight K hK).hom ≫ (tensor X).flip.map k := by
  simp only [sheafHomDualIsoTensorRight, Iso.trans_hom, Functor.mapIso_hom]
  rw [reassoc_of% (sheafHomIsoTensorDualRight_naturality (perf_dual hK') (perf_dual hK)
    (dualMap k)), ← Functor.map_comp, bidualIso_naturality hK hK' k, Functor.map_comp,
    Category.assoc]

/-- `R𝓗om(K, -) ≅ K^∨ ⊗ -` (`sheafHomIsoTensorDualLeft`) is natural in the perfect object `K`;
it is natural in the second variable by construction. -/
theorem sheafHomIsoTensorDualLeft_naturality {K K' : D B S hS X} (hK : Perf X K)
    (hK' : Perf X K') (k : K ⟶ K') :
    (sheafHom X).map k.op ≫ (sheafHomIsoTensorDualLeft K hK).hom =
      (sheafHomIsoTensorDualLeft K' hK').hom ≫ (tensor X).map (dualMap k) := by
  simp only [sheafHomIsoTensorDualLeft, Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
  rw [reassoc_of% (sheafHomIsoTensorDualRight_naturality hK hK' k), Category.assoc,
    (tensorBraiding X).inv.naturality (dualMap k)]

/-- Inverting the horizontal isomorphisms of a commutative square. -/
theorem inv_square {C : Type*} [Category C] {a b c d : C} (α : a ≅ b) (β : c ≅ d) (x : a ⟶ c)
    (y : b ⟶ d) (h : x ≫ β.hom = α.hom ≫ y) : y ≫ β.inv = α.inv ≫ x := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- The associator is natural in the third variable (AxiomMath's
`associatorGeneral_naturality_right`), read on `tensorAssoc`. -/
theorem tensorAssoc_inv_naturality_right (P : D B S hS X) {M' M : D B S hS X} (m : M' ⟶ M)
    (A : D B S hS X) :
    ((tensor X).obj A).map (((tensor X).obj P).map m) ≫ (tensorAssoc P M).inv.app A =
      (tensorAssoc P M').inv.app A ≫ ((tensor X).obj (tensorObj A P)).map m := by
  exact inv_square _ _ _ _
    ((smallEtaleDerivedTensorProduct B S hS X).associatorGeneral_naturality_right A P m)

/-- The associator is natural in the middle variable (AxiomMath's
`associatorGeneral_naturality_middle`), read on `tensorAssoc`. -/
theorem tensorAssoc_inv_naturality_middle {P' P : D B S hS X} (a : P' ⟶ P) (M : D B S hS X)
    (A : D B S hS X) :
    ((tensor X).obj A).map (((tensor X).map a).app M) ≫ (tensorAssoc P M).inv.app A =
      (tensorAssoc P' M).inv.app A ≫ ((tensor X).map (((tensor X).obj A).map a)).app M := by
  exact inv_square _ _ _ _
    ((smallEtaleDerivedTensorProduct B S hS X).associatorGeneral_naturality_middle A a M)

/-- **`R𝓗om(φ, -)` is the conjugate of `- ⊗^L φ`** under the adjunctions `- ⊗ P ⊣ R𝓗om(P, -)`
(Stacks 08J8): a reformulation of AxiomMath's dinaturality
`smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinatural`. -/
theorem conjugateEquiv_tensorSheafHomAdj {P' P : D B S hS X} (φ : P' ⟶ P) :
    conjugateEquiv (tensorSheafHomAdj P) (tensorSheafHomAdj P') ((tensor X).flip.map φ) =
      (sheafHom X).map φ.op := by
  ext L
  apply ((tensorSheafHomAdj P').homEquiv _ _).symm.injective
  have h := smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinatural B S hS X
    (((sheafHom X).obj (op P)).obj L) L φ (𝟙 _)
  rw [Category.id_comp] at h
  simp only [tensorSheafHomAdj] at h ⊢
  rw [h, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, conjugateEquiv_counit,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The interchange law for whiskerings. -/
theorem whiskerRight_comp_whiskerLeft {A B C : Type*} [Category A] [Category B] [Category C]
    {F G : A ⥤ B} {H K : B ⥤ C} (f : F ⟶ G) (τ : H ⟶ K) :
    Functor.whiskerRight f H ≫ Functor.whiskerLeft G τ =
      Functor.whiskerLeft F τ ≫ Functor.whiskerRight f K := by
  ext a
  exact τ.naturality (f.app a)

/-- **Lemma 2.10** (`lem:rhom_tensor_morphism`), **naturality in `M`**, as an equation of natural
transformations of functors of `L`: for `m : M' ⟶ M`,
`(K ⊗ R𝓗om(m, -)) ≫ φ_{K,M'} = φ_{K,M} ≫ R𝓗om(R𝓗om(K, m), -)`. -/
theorem lemma_2_10_hom_naturality_M (K : D B S hS X) (hK : Perf X K) {M' M : D B S hS X}
    (m : M' ⟶ M) :
    Functor.whiskerRight ((sheafHom X).map m.op) ((tensor X).obj K) ≫
        (lemma_2_10 K M' hK).hom =
      (lemma_2_10 K M hK).hom ≫ (sheafHom X).map (((sheafHom X).obj (op K)).map m).op := by
  simp only [lemma_2_10, Iso.trans_hom, Functor.isoWhiskerLeft_hom, conjugateIsoEquiv_apply_hom]
  rw [← Category.assoc, whiskerRight_comp_whiskerLeft]
  simp only [Category.assoc]
  congr 1
  rw [← conjugateEquiv_tensorSheafHomAdj m, ← conjugateEquiv_whiskerLeft, conjugateEquiv_comp,
    ← conjugateEquiv_tensorSheafHomAdj, conjugateEquiv_comp]
  congr 1
  ext A
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.flip_map_app,
    lemma_2_10_leftAdjointIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc, Functor.flip_obj_obj]
  rw [← tensorAssoc_inv_naturality_right, ← Functor.map_comp_assoc,
    ← (sheafHomIsoTensorDualLeft K hK).hom.naturality m, Functor.map_comp_assoc]

/-- A functor applied to a commutative square, followed by a common map. -/
theorem map_square {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C') {a b c d : C} {e : C'}
    (i' : a ⟶ b) (t : b ⟶ c) (h : a ⟶ d) (i : d ⟶ c) (s : F.obj c ⟶ e)
    (hι : i' ≫ t = h ≫ i) :
    F.map i' ≫ F.map t ≫ s = F.map h ≫ F.map i ≫ s := by
  rw [← F.map_comp_assoc, hι, F.map_comp_assoc]

/-- **Lemma 2.10** (`lem:rhom_tensor_morphism`), **naturality in `K`**, as an equation of natural
transformations of functors of `L`: for `k : K ⟶ K'` between perfect objects,
`(k ⊗ R𝓗om(M, -)) ≫ φ_{K',M} = φ_{K,M} ≫ R𝓗om(R𝓗om(k, M), -)`. -/
theorem lemma_2_10_hom_naturality_K {K K' : D B S hS X} (hK : Perf X K) (hK' : Perf X K')
    (k : K ⟶ K') (M : D B S hS X) :
    Functor.whiskerLeft ((sheafHom X).obj (op M)) ((tensor X).map k) ≫
        (lemma_2_10 K' M hK').hom =
      (lemma_2_10 K M hK).hom ≫ (sheafHom X).map (((sheafHom X).map k.op).app M).op := by
  simp only [lemma_2_10, Iso.trans_hom, Functor.isoWhiskerLeft_hom, conjugateIsoEquiv_apply_hom]
  have hα : (tensor X).map k ≫ (((tensorBraiding X).app K').hom ≫
      (sheafHomDualIsoTensorRight K' hK').symm.hom) =
      (((tensorBraiding X).app K).hom ≫ (sheafHomDualIsoTensorRight K hK).symm.hom) ≫
        (sheafHom X).map (dualMap k).op := by
    rw [Iso.app_hom, Iso.app_hom, ← Category.assoc, (tensorBraiding X).hom.naturality k,
      Category.assoc, Category.assoc, Iso.symm_hom, Iso.symm_hom,
      inv_square _ _ _ _ (sheafHomDualIsoTensorRight_naturality hK hK' k)]
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, hα, Functor.whiskerLeft_comp]
  simp only [Category.assoc]
  refine congrArg (Functor.whiskerLeft ((sheafHom X).obj (op M))
    (((tensorBraiding X).app K).hom ≫ (sheafHomDualIsoTensorRight K hK).symm.hom) ≫ ·) ?_
  rw [← conjugateEquiv_tensorSheafHomAdj (dualMap k), ← conjugateEquiv_whiskerRight,
    conjugateEquiv_comp, ← conjugateEquiv_tensorSheafHomAdj, conjugateEquiv_comp]
  refine congrArg (conjugateEquiv _ _) ?_
  ext A
  have hι := NatTrans.congr_app (sheafHomIsoTensorDualLeft_naturality hK hK' k) M
  simp only [NatTrans.comp_app] at hι
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.flip_map_app,
    lemma_2_10_leftAdjointIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc, Functor.flip_obj_obj, Functor.flip_obj_map]
  rw [← tensorAssoc_inv_naturality_middle (dualMap k) M A]
  exact map_square _ _ _ _ _ _ hι.symm

/-- **Lemma 2.10** (`lem:rhom_tensor_morphism`), **naturality in `M`**: for `K` perfect and
`m : M' ⟶ M`, the square

`K ⊗ R𝓗om(M, L) ⟶ R𝓗om(R𝓗om(K, M), L)`
`K ⊗ R𝓗om(M', L) ⟶ R𝓗om(R𝓗om(K, M'), L)`

with vertical maps `K ⊗ R𝓗om(m, L)` and `R𝓗om(R𝓗om(K, m), L)` commutes. -/
theorem lemma_2_10_naturality_M (K : D B S hS X) (hK : Perf X K) {M' M : D B S hS X}
    (m : M' ⟶ M) (L : D B S hS X) :
    ((tensor X).obj K).map (((sheafHom X).map m.op).app L) ≫ (lemma_2_10_app K M' L hK).hom =
      (lemma_2_10_app K M L hK).hom ≫
        ((sheafHom X).map (((sheafHom X).obj (op K)).map m).op).app L :=
  NatTrans.congr_app (lemma_2_10_hom_naturality_M K hK m) L

/-- **Lemma 2.10** (`lem:rhom_tensor_morphism`), **naturality in `K`**: for `k : K ⟶ K'` between
perfect objects, the square

`K ⊗ R𝓗om(M, L) ⟶ R𝓗om(R𝓗om(K, M), L)`
`K' ⊗ R𝓗om(M, L) ⟶ R𝓗om(R𝓗om(K', M), L)`

with vertical maps `k ⊗ R𝓗om(M, L)` and `R𝓗om(R𝓗om(k, M), L)` commutes. -/
theorem lemma_2_10_naturality_K {K K' : D B S hS X} (hK : Perf X K) (hK' : Perf X K')
    (k : K ⟶ K') (M L : D B S hS X) :
    ((tensor X).map k).app (sheafHomObj M L) ≫ (lemma_2_10_app K' M L hK').hom =
      (lemma_2_10_app K M L hK).hom ≫
        ((sheafHom X).map (((sheafHom X).map k.op).app M).op).app L :=
  NatTrans.congr_app (lemma_2_10_hom_naturality_K hK hK' k M) L

end RelativeFM.Spaces
