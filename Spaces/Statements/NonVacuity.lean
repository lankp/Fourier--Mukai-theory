/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.NonVacuity
import Spaces.Statements.Inputs

/-!
# Non-vacuity of the statements of `Spaces/Statements/Main.lean`

CLAUDE.md, verification step 5: every hypothesis-carrying notion the statements rely on is
satisfiable.

Proved here **with no input**:

* `FullyFaithfulOn`, `IsEquivalenceOn` (hence `FFOrEquivOn`) hold for the identity functor on
  any full subcategory (`isEquivalenceOn_id`, `fullyFaithfulOn_id`), and an equivalence on
  `P → Q` is fully faithful on `P → Q` (`IsEquivalenceOn.fullyFaithfulOn`);
* every point of `|X|` has a representative (`Representative.exists_represents`);
* an identity morphism is quasi-affine (`isQuasiAffineHom_id`);
* a zero kernel lies in `D_qc` and `D^b_coh`, is pseudocoherent and relatively perfect over
  both factors, for any `f₁`, `f₂` (`zero_kernel_hypotheses`; from `Spaces/NonVacuity.lean`).

Proved **from the tagged inputs of `Spaces/Statements/Inputs.lean`** (AxiomMath theorems in
the closure of `SpacesVerified`, to be discharged there):

* an identity morphism of algebraic spaces is proper (`isProperHom_id`: separated by AxiomMath's
  `isSeparated_of_isIso`, which is in the import closure; locally of finite type by 06LT;
  quasi-compact and universally closed by the two `…OfIsIso` inputs) and flat
  (`isFlatHom_id`);
* for an affine, locally Noetherian base scheme `S` (e.g. `Spec k`, `k` a field), the base
  `S` itself is a Noetherian algebraic space (`isNoetherianSpace_baseSpace`: quasi-compact by
  `isQuasiCompactSpace_yoneda_of_isAffine` and locally Noetherian by
  `hasEtaleLocalProperty_of_representable`, both in the import closure; quasi-separated by the
  input `AffineQuasiSeparatedInput`).

Together (`setup_hypotheses_satisfiable`, and the `example` over `Spec k`): with
`S' = Y₁ = Y₂ = T` the base space, `f₁ = f₂ = t = 𝟙` and `K = 0`, all hypotheses of every
statement of `Main.lean` hold (Setup 2.20, `K ∈ D_qc` pseudocoherent, `K ∈ D^b_coh`,
relatively perfect over each `Y_i`, `Y_i` Noetherian).  The universally quantified notions in
conclusions (quasi-affine `t`, finite type representatives) are inhabited by the identity and
by `isProperHom_id` (finite type is part of proper).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Statements

open RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

/-! ### Restriction of functors -/

section Categorical

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- An equivalence on `P → Q` is fully faithful on `P → Q`. -/
theorem IsEquivalenceOn.fullyFaithfulOn {P : ObjectProperty C} {Q : ObjectProperty D}
    {F : C ⥤ D} (h : IsEquivalenceOn P Q F) : FullyFaithfulOn P Q F := by
  obtain ⟨hPQ, hF⟩ := h
  exact ⟨hPQ, inferInstance, inferInstance⟩

/-- **Non-vacuity of `IsEquivalenceOn`**: the identity functor restricts to an equivalence on
every full subcategory (the induced functor is the identity of `P.FullSubcategory`). -/
theorem isEquivalenceOn_id (P : ObjectProperty C) : IsEquivalenceOn P P (𝟭 C) :=
  ⟨fun _ h => h, (inferInstance : (𝟭 P.FullSubcategory).IsEquivalence)⟩

/-- **Non-vacuity of `FullyFaithfulOn`**. -/
theorem fullyFaithfulOn_id (P : ObjectProperty C) : FullyFaithfulOn P P (𝟭 C) :=
  (isEquivalenceOn_id P).fullyFaithfulOn

/-- **Non-vacuity of `FFOrEquivOn`**, both readings. -/
theorem fFOrEquivOn_id (equiv : Bool) (P : ObjectProperty C) :
    FFOrEquivOn equiv P P (𝟭 C) := by
  cases equiv
  · exact fullyFaithfulOn_id P
  · exact isEquivalenceOn_id P

end Categorical

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Points, quasi-affine morphisms, zero kernels (no input) -/

/-- Every point of `|X|` has a representative `Spec k ⟶ X` (`|X|` is a quotient of the
representatives). -/
theorem Representative.exists_represents {X : AlgebraicSpaces B S hS} (p : Pts X) :
    ∃ x : Representative X, x.Represents p :=
  Quot.exists_rep p

/-- **Non-vacuity of `IsQuasiAffineHom`**: an identity morphism is quasi-affine (each base
change to an affine scheme `Z` is `Z` itself, which is affine, hence quasi-affine). -/
theorem isQuasiAffineHom_id (X : AlgebraicSpaces B S hS) : IsQuasiAffineHom (𝟙 X) := by
  intro Z g
  have hZ : IsAffine
      ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z)) :=
    Z.property
  have : IsIso (𝟙 X : X ⟶ X).hom := by
    change IsIso (𝟙 X.1)
    infer_instance
  exact ⟨_, inferInstance, ⟨(asIso (pullback.fst g (𝟙 X : X ⟶ X).hom)).symm⟩⟩

/-- **The kernel hypotheses are satisfiable**: a zero object of `D(Y₁ ×_{S'} Y₂)` lies in
`D_qc` and `D^b_coh`, is pseudocoherent and is relatively perfect over each `Y_i`. -/
theorem zero_kernel_hypotheses {S' Y₁ Y₂ : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ S')
    (f₂ : Y₂ ⟶ S') {K : D B S hS (pullback f₁ f₂)} (hK : IsZero K) :
    Dqc _ K ∧ IsPseudoCoherent _ K ∧ DbCoh _ K ∧ IsRelPerfOverFst f₁ f₂ K ∧
      IsRelPerfOverSnd f₁ f₂ K :=
  ⟨Dqc_of_isZero hK, IsPseudoCoherent_of_isZero hK, DbCoh_of_isZero hK,
    isRelativelyPerfect_of_isZero _ hK, isRelativelyPerfect_of_isZero _ hK⟩

/-- `FM(K) ⊆ fm(K)`: a point where `Φ_K` is an equivalence is one where it is fully faithful. -/
theorem FMLocus_subset_fmLocus {S' Y₁ Y₂ : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ S')
    (f₂ : Y₂ ⟶ S') (K : D B S hS (pullback f₁ f₂)) :
    FMLocus f₁ f₂ K ⊆ fmLocus f₁ f₂ K :=
  fun _ ⟨x, hx, h⟩ => ⟨x, hx, h.fullyFaithfulOn⟩

/-! ### Proper, flat, Noetherian (from the tagged inputs) -/

section FromInputs

variable (B S hS)

/-- An identity morphism of algebraic spaces is **proper** (Stacks 03ZM), from the inputs 06LT,
`IsQuasiCompactOfIsIsoInput`, `UniversallyClosedOfIsIsoInput` and AxiomMath's
`isSeparated_of_isIso` (import closure). -/
theorem isProperHom_id (h06LT : Tag06LTInput B S hS) (hqc : IsQuasiCompactOfIsIsoInput B S hS)
    (huc : UniversallyClosedOfIsIsoInput B S hS) (X : AlgebraicSpaces B S hS) :
    IsProperHom (𝟙 X) := by
  change Space.IsProper B S hS (𝟙 X.1)
  exact ⟨isSeparated_of_isIso B S hS _, ⟨h06LT _ (isEtale_of_isIso B S hS _), hqc _⟩, huc _⟩

/-- An identity morphism of algebraic spaces is **flat**, from `IsFlatIdInput`. -/
theorem isFlatHom_id (hfl : IsFlatIdInput B S hS) (X : AlgebraicSpaces B S hS) :
    IsFlatHom (𝟙 X) :=
  hfl X.2

/-- For an affine, locally Noetherian base scheme `S`, the base `S` is a **Noetherian algebraic
space** (Stacks 03EA), from `AffineQuasiSeparatedInput`. -/
theorem isNoetherianSpace_baseSpace (hqs : AffineQuasiSeparatedInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [IsAffine S] [IsLocallyNoetherian S] :
    IsNoetherianSpace hZ (baseSpace B S hS) :=
  ⟨isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (inferInstanceAs (IsAffine S)),
    hqs hZ ⟨_, inferInstanceAs (IsAffine S), ⟨Iso.refl _⟩⟩,
    hasEtaleLocalProperty_of_representable B S hS _
      (fun X : Scheme.{u} => IsLocallyNoetherian X) _ (Iso.refl _)
      (inferInstanceAs (IsLocallyNoetherian S))⟩

/-- **All hypotheses of the statements of `Main.lean` are jointly satisfiable**: over an affine,
locally Noetherian base scheme `S`, take `S' = Y₁ = Y₂ = T` the base space,
`f₁ = f₂ = t = 𝟙` and `K = 0`. -/
theorem setup_hypotheses_satisfiable (h06LT : Tag06LTInput B S hS)
    (hqc : IsQuasiCompactOfIsIsoInput B S hS) (huc : UniversallyClosedOfIsIsoInput B S hS)
    (hfl : IsFlatIdInput B S hS) (hqs : AffineQuasiSeparatedInput B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) [IsAffine S] [IsLocallyNoetherian S] :
    IsNoetherianSpace hZ (baseSpace B S hS) ∧ IsProperHom (𝟙 (baseSpace B S hS)) ∧
      IsFlatHom (𝟙 (baseSpace B S hS)) ∧ IsFiniteTypeHom (𝟙 (baseSpace B S hS)) ∧
      IsQuasiAffineHom (𝟙 (baseSpace B S hS)) ∧
      ∀ K : D B S hS (pullback (𝟙 (baseSpace B S hS)) (𝟙 (baseSpace B S hS))), IsZero K →
        Dqc _ K ∧ IsPseudoCoherent _ K ∧ DbCoh _ K ∧
          IsRelPerfOverFst (𝟙 (baseSpace B S hS)) (𝟙 (baseSpace B S hS)) K ∧
          IsRelPerfOverSnd (𝟙 (baseSpace B S hS)) (𝟙 (baseSpace B S hS)) K :=
  ⟨isNoetherianSpace_baseSpace B S hS hqs hZ, isProperHom_id B S hS h06LT hqc huc _,
    isFlatHom_id B S hS hfl _, (isProperHom_id B S hS h06LT hqc huc _).2.1,
    isQuasiAffineHom_id _, fun _ hK => zero_kernel_hypotheses _ _ hK⟩

/-- The witness over `Spec k` for a field `k` (whose spectrum lies in the site). -/
example (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (h06LT : Tag06LTInput B _ hk) (hqc : IsQuasiCompactOfIsIsoInput B _ hk)
    (huc : UniversallyClosedOfIsIsoInput B _ hk) (hfl : IsFlatIdInput B _ hk)
    (hqs : AffineQuasiSeparatedInput B _ hk) (hZ : B.Contains (⊤_ Scheme.{u})) :
    IsNoetherianSpace hZ (baseSpace B _ hk) ∧ IsProperHom (𝟙 (baseSpace B _ hk)) ∧
      IsFlatHom (𝟙 (baseSpace B _ hk)) :=
  let h := setup_hypotheses_satisfiable B _ hk h06LT hqc huc hfl hqs hZ
  ⟨h.1, h.2.1, h.2.2.1⟩

end FromInputs

end RelativeFM.Spaces.Statements
