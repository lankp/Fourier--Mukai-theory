/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.BoxGeneration.Inputs
import Spaces.Conservative.Flat
import Spaces.Conservative.QuasiAffine
import Spaces.InternalHom.Pullback
import Spaces.InternalHom.TensorHom
import Spaces.QuasiPerfect.Inputs
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackStructureSheaf

/-!
# GL26 Lemma 5.4 (`lem:neeman2023cor5_10`): box products of compact generators

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), §5,
**Lemma 5.4** (`lem:neeman2023cor5_10`): let `f_i : Y_i ⟶ S'` (`i = 1, 2`) be morphisms of
quasi-compact quasi-separated algebraic spaces and `P_i` a compact generator of `D_qc(Y_i)`.  Then
`G = Lg₁^* P₁ ⊗^L Lg₂^* P₂` is a compact generator of `D_qc(Y₁ ×_{S'} Y₂)`, where
`g_i : Y₁ ×_{S'} Y₂ ⟶ Y_i` are the projections.

## What is proved

* `lemma_5_4_compact`: `G` is perfect, lies in `D_qc(W)` (`W = Y₁ ×_{S'} Y₂`) and is a compact
  object of `D_qc(W)`; `W` is quasi-compact and quasi-separated (`pullback_isQcqs`).
  Unconditional (AxiomMath inputs only).
* `lemma_5_4_of_conservative`: **GL26's proof, the cover argument, over algebraic spaces**, for an
  arbitrary étale surjection `s : U ⟶ Y₁` from a quasi-compact quasi-separated `U`: if
  `Rh₂_*` is conservative on `D_qc(U ×_{S'} Y₂)` (`h₂ : U ×_{S'} Y₂ ⟶ Y₂` the projection), then
  `G` is a compact generator of `D_qc(W)`.  The zero-detection half is `isZero_of_orthogonal_box`.
* `lemma_5_4_of_factorization`: the same when `s ≫ f₁ = j ≫ p` with `j` a quasi-compact open
  immersion and `p` affine; the conservativity of `Rh₂_*` then follows from wave 10's
  `Conservative.lemma_3_2_of_factorization` applied to the base change `h₂ = j' ≫ p'`.
* `lemma_5_4_of_isAffineHom`: **unconditional** (AxiomMath inputs only) when `f₁` is affine
  (`U = Y₁`, `s = 𝟙`, `h₂` affine).
* `isZero_of_orthogonal_box_unit_iff`: conversely, the conservativity of `Rh₂_*` is equivalent
  to the conclusion of the lemma for `Y₁ = U`, `P₁ = 𝒪_U` (zero detection by
  `Lh₁^*𝒪_U ⊗^L Lh₂^*P₂`); for `U` affine `𝒪_U` is a compact generator of `D_qc(U)` (Stacks 09IS),
  so Lemma 5.4 implies the residue of `lemma_5_4_of_conservative`: it is exactly what remains,
  and no proof of Lemma 5.4 avoids it.

## What is missing for Lemma 5.4 as stated

GL26 takes `U` affine and concludes with Lemma 2.17 (`lem:quasi_affine_diagonal`: `U ⟶ S'` is
quasi-affine, so `h₂` is) and Lemma 3.2 (`lem:quasi-affine_is_conservative`: `Rh₂_*` is
conservative).  Lemma 3.2 is proved in this repository only for a morphism given with a
factorization `j ≫ p` (`Conservative.lemma_3_2_of_factorization`, wave 10): the factorization of
a quasi-affine morphism through `\underline{Spec}(f_* 𝒪)` (Stacks 081X, 086S) is in AxiomMath
modules whose import closure contains `MilnorPatching.Relative`, outside the `Spaces` closure
(`Spaces/Conservative/QuasiAffine.lean`, "What is missing").  So `Lemma54Statement` (the paper's
statement) is not proved here.  It follows from `lemma_5_4_of_factorization` once one has, for
`Y₁` qcqs, an étale surjection `s : U ⟶ Y₁` from an affine `U` and a factorization of the
quasi-affine `s ≫ f₁` (Lemma 2.17) into a quasi-compact open immersion and an affine morphism
(Stacks 081X, 086S); equivalently, Lemma 3.2 for the base changes `h₂`.

## Proof of `lemma_5_4_of_conservative` (GL26's)

Let `E ∈ D_qc(W)` with `Hom(G[n], E) = 0` for all `n`, and `M = R𝓗om(Lg₂^*P₂, E)`, in `D_qc(W)`
(Stacks 0A8A, `Lg₂^*P₂` perfect).
1. Tensor/hom (Stacks 08J8), `Lg₁^* ⊣ Rg₁_*` and the shift compatibilities give
   `Hom(P₁[n], Rg₁_*M) ≅ Hom(G[n], E) = 0`; `Rg₁_*M ∈ D_qc(Y₁)` (Stacks 08FA), so `Rg₁_*M ≅ 0`.
2. `t : W' = U ×_{S'} Y₂ ⟶ W` is the base change of `s` along `g₁`; étale base change (Stacks 08GE,
   `EtaleBaseChangeInput`) gives `Rh₁_*(Lt^*M) ≅ Ls^*(Rg₁_*M) ≅ 0`, and
   `Lt^*M ≅ R𝓗om(Lh₂^*P₂, Lt^*E)` (Stacks 08I3 out of a perfect object, `Tag08I3PerfectInput`,
   and `Lt^*Lg₂^* ≅ Lh₂^*`, Stacks 0D6D).
3. `Hom(Lh₂^*P₂[m], Lt^*E) ≅ Hom(𝒪_U[m], Rh₁_*R𝓗om(Lh₂^*P₂, Lt^*E)) = 0` (unit of `⊗^L`,
   Stacks 0FPT, `Lh₁^*𝒪_U ≅ 𝒪_{W'}`, tensor/hom, adjunction).  This is where GL26 uses `U` affine;
   the argument does not need it.
4. So `Hom(P₂[m], Rh₂_*Lt^*E) = 0` for all `m`, `Rh₂_*Lt^*E ∈ D_qc(Y₂)`, and `Rh₂_*Lt^*E ≅ 0`.
5. Conservativity of `Rh₂_*` (the hypothesis) gives `Lt^*E ≅ 0`; `t` is étale and surjective
   (base change of `s`), and Lemma 2.14 (`Conservative.lemma_2_14`) gives `E ≅ 0`.

Compactness: `G` is perfect (Stacks 08H6, 09JB), so in `D_qc(W)` (AxiomMath's
`qcohDerived_of_isPerfect_derivedCategoryB`) and compact there (Stacks 09M8); `W` is qcqs by
Stacks 073B, base change of quasi-compact and quasi-separated morphisms, and AxiomMath's
`isAbsolutelyQuasiSeparated_of_isQuasiSeparated`.

## Rendering

* `D_qc(Y)` is `QuasicoherentDerivedCategory B S hS Y.1 Y.2 = (Dqc Y).FullSubcategory`; "`P` is a
  compact generator of `D_qc(Y)`" is `IsCompactGeneratorQc P`: `P` is a compact object of `D_qc(Y)`
  (`IsCompactObject.{u}`, direct sums indexed by `Type u`, as in Stacks 09M8) and every
  `E ∈ D_qc(Y)` receiving only zero maps from the shifts `P[n]` is zero.  The shifts and Homs are
  those of `D(Y)`; `D_qc(Y)` is a full subcategory closed under shifts, so this is generation
  in `D_qc(Y)` (GL26 §2.1).  This is the repository's convention for "compact generator"
  (`RelativeWeakApprox.IsPaperGenerator`, LP26 §2.1.2): compactness and zero detection by shifts,
  which is equivalent to GL26's localizing generation for a compact object (Schwede–Shipley,
  Lemma 2.2.1, as quoted in GL26 §2.1).
* The base space is `S'` (an algebraic space over the base scheme `S` of AxiomMath's site);
  quasi-separatedness is AxiomMath's absolute `IsAbsolutelyQuasiSeparated` (with `hZ` saying that
  the site contains `Spec ℤ`), as in `Spaces/Supported/CompactGeneration.lean`.
* `Y₁ ×_{S'} Y₂` is the pullback in `AlgebraicSpaces B S hS`.

## Assumptions

AxiomMath theorems only, as tagged inputs: `EtaleBaseChangeInput` (08GE, new, `Inputs.lean`);
`Spaces.Tag08F4Input`, `Spaces.Tag08FAInput`; `Tag0A8AInput`, `Tag08I3PerfectInput`
(`Spaces/InternalHom/Inputs.lean`); `QuasiPerfect.Tag09JBInput`; from `Spaces/LP26/Inputs.lean`
`PerfectPullbackInput`, `PerfectQcohInput`, `Tag09M8Input`, `Tag073BInput`, `Tag073BTwoInput`,
`QuasiCompactSourceInput`, `SupportEmptyInput`; from `Spaces/Conservative/Inputs.lean`
`FlatPullbackExactInput`, `FlatPullbackSupportInput`, and, for the corollaries,
`AffinePushforwardConservativeInput` and `LP26.OpenImmersionCounitInput`.  Nothing else.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space Opposite

namespace RelativeFM.Spaces.BoxGeneration

open RelativeFM.Spaces RelativeFM.Spaces.LP26 RelativeFM.Spaces.Statements

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Compact generators of `D_qc` -/

/-- The underlying object of `D(Y)` of an object of `D_qc(Y)`, typed in the spelling `D B S hS Y`
of `Spaces/Categories.lean` (so that shifts and zero morphisms are those of `D(Y)` in this file's
instance context; see "Spelling" in `Spaces/Supported/Inputs.lean`). -/
abbrev qcObj {Y : AlgebraicSpaces B S hS}
    (P : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) : D B S hS Y :=
  P.obj

/-- **`P` compactly generates `D_qc(Y)`** (GL26 §2.1): `P` is a compact object of `D_qc(Y)` and
every object of `D_qc(Y)` receiving only zero maps from the shifts of `P` is zero. -/
def IsCompactGeneratorQc {Y : AlgebraicSpaces B S hS}
    (P : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) : Prop :=
  IsCompactObject.{u} P ∧
    ∀ E : D B S hS Y, Dqc Y E → (∀ (n : ℤ) (g : (qcObj P)⟦n⟧ ⟶ E), g = 0) → IsZero E

/-! ### The box product and its compactness -/

section Box

variable {T Y₁ Y₂ : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ T) (f₂ : Y₂ ⟶ T)

/-- **The box product** `Lg₁^* P₁ ⊗^L Lg₂^* P₂ ∈ D(Y₁ ×_T Y₂)`, `g_i` the two projections. -/
abbrev boxObj (P₁ : D B S hS Y₁) (P₂ : D B S hS Y₂) : D B S hS (pullback f₁ f₂) :=
  tensorObj ((pull (pullback.fst f₁ f₂)).obj P₁) ((pull (pullback.snd f₁ f₂)).obj P₂)

/-- The box product of perfect objects is perfect (Stacks 08H6, 09JB). -/
theorem perf_boxObj (h09JB : QuasiPerfect.Tag09JBInput B S hS)
    (hpp : PerfectPullbackInput B S hS) {P₁ : D B S hS Y₁} {P₂ : D B S hS Y₂}
    (h₁ : Perf Y₁ P₁) (h₂ : Perf Y₂ P₂) : Perf (pullback f₁ f₂) (boxObj f₁ f₂ P₁ P₂) :=
  QuasiPerfect.perf_tensorObj h09JB (hpp _ _ h₁) (hpp _ _ h₂)

variable (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- The second leg `f₂ : Y₂ ⟶ T` is quasi-compact, and its base change `g₁ : Y₁ ×_T Y₂ ⟶ Y₁` is
quasi-compact and quasi-separated, when `Y₂` is quasi-compact quasi-separated and `T`
quasi-separated (Stacks 073B, base change). -/
theorem isQcqs_fst (h073B : Tag073BInput B S hS) (h073B2 : Tag073BTwoInput B S hS)
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T.1)
    (hY₂qc : IsQuasiCompactSpace B S hS Y₂.1) (hY₂qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₂.1) :
    IsQuasiCompact B S hS (pullback.fst f₁ f₂).hom ∧
      IsQuasiSeparated B S hS (pullback.fst f₁ f₂).hom := by
  have sq := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f₁ f₂).flip
  exact ⟨isQuasiCompact_of_isPullback B S hS sq (h073B hZ T.2 hTqs hY₂qc f₂.hom),
    isQuasiSeparated_of_isPullback B S hS sq (h073B2 hZ Y₂.2 hY₂qs f₂.hom)⟩

/-- **`Y₁ ×_T Y₂` is quasi-compact and quasi-separated** for `Y₁`, `Y₂` qcqs and `T`
quasi-separated. -/
theorem pullback_isQcqs (h073B : Tag073BInput B S hS) (h073B2 : Tag073BTwoInput B S hS)
    (hsrc : QuasiCompactSourceInput B S hS)
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T.1)
    (hY₁qc : IsQuasiCompactSpace B S hS Y₁.1) (hY₁qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₁.1)
    (hY₂qc : IsQuasiCompactSpace B S hS Y₂.1) (hY₂qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₂.1) :
    IsQuasiCompactSpace B S hS (pullback f₁ f₂).1 ∧
      IsAbsolutelyQuasiSeparated B S hS hZ (pullback f₁ f₂).1 := by
  obtain ⟨hqc, hqs⟩ := isQcqs_fst f₁ f₂ hZ h073B h073B2 hTqs hY₂qc hY₂qs
  exact ⟨hsrc Y₁.2 hY₁qc _ hqc,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (pullback f₁ f₂).2 hY₁qs hqs⟩

/-- **Lemma 5.4** (`lem:neeman2023cor5_10`), compactness: for `Y₁`, `Y₂` qcqs, `T`
quasi-separated and `P_i` compact in `D_qc(Y_i)`, the box product `G` is perfect, lies in
`D_qc(Y₁ ×_T Y₂)` and is a compact object there (Stacks 09M8, 08H6, 09JB). -/
theorem lemma_5_4_compact (h073B : Tag073BInput B S hS) (h073B2 : Tag073BTwoInput B S hS)
    (hsrc : QuasiCompactSourceInput B S hS) (h09M8 : Tag09M8Input B S hS)
    (h09JB : QuasiPerfect.Tag09JBInput B S hS) (hpp : PerfectPullbackInput B S hS)
    (hPq : PerfectQcohInput B S hS)
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T.1)
    (hY₁qc : IsQuasiCompactSpace B S hS Y₁.1) (hY₁qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₁.1)
    (hY₂qc : IsQuasiCompactSpace B S hS Y₂.1) (hY₂qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₂.1)
    (P₁ : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y₁.1 Y₁.2)
    (P₂ : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y₂.1 Y₂.2)
    (hP₁ : IsCompactObject.{u} P₁) (hP₂ : IsCompactObject.{u} P₂) :
    ∃ hG : Dqc (pullback f₁ f₂) (boxObj f₁ f₂ (qcObj P₁) (qcObj P₂)),
      Perf (pullback f₁ f₂) (boxObj f₁ f₂ (qcObj P₁) (qcObj P₂)) ∧
        IsCompactObject.{u}
          (⟨_, hG⟩ : Space.QuasicoherentDerivedCategory.{u, u} B S hS (pullback f₁ f₂).1
            (pullback f₁ f₂).2) := by
  have hperf := perf_boxObj f₁ f₂ h09JB hpp ((h09M8 hZ Y₁ hY₁qc hY₁qs P₁).1 hP₁)
    ((h09M8 hZ Y₂ hY₂qc hY₂qs P₂).1 hP₂)
  obtain ⟨hWqc, hWqs⟩ := pullback_isQcqs f₁ f₂ hZ h073B h073B2 hsrc hTqs hY₁qc hY₁qs hY₂qc hY₂qs
  have hG := hPq (pullback f₁ f₂) _ hperf
  exact ⟨hG, hperf, (h09M8 hZ (pullback f₁ f₂) hWqc hWqs ⟨_, hG⟩).2 hperf⟩

end Box

/-! ### Hom computations -/

section HomComputations

variable {X Y : AlgebraicSpaces B S hS}

/-- The unit object `𝒪_X[0]` of `D(X)`. -/
abbrev unitD (X : AlgebraicSpaces B S hS) : D B S hS X :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))

/-- `Lf^*𝒪_Y ≅ 𝒪_X` (AxiomMath's `derivedPullbackUnitIsoGeneral`). -/
def pullUnitIso (f : X ⟶ Y) : (pull f).obj (unitD Y) ≅ unitD X :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIsoGeneral
    (smallEtaleRingedToposHom B S hS f)

/-- `𝒪_X ⊗^L K ≅ K`: the braiding (`tensorBraiding`, Stacks 0FPT) followed by AxiomMath's right
unit `DerivedTensorProduct.unitIso`. -/
def leftUnitIso (K : D B S hS X) : tensorObj (unitD X) K ≅ K :=
  ((tensorBraiding X).app (unitD X)).app K ≪≫ (smallEtaleDerivedTensorProduct B S hS X).unitIso K

/-- **Step 3 of the proof**: if `Rh_* R𝓗om(K, N) ≅ 0` for some `h : X ⟶ Y`, then every morphism
`K[m] ⟶ N` vanishes: `Hom(K[m], N) ≅ Hom(𝒪_X[m], R𝓗om(K, N)) ≅ Hom(𝒪_Y[m], Rh_*R𝓗om(K, N))`
(the unit of `⊗^L`, tensor/hom, `Lh^*𝒪_Y ≅ 𝒪_X`, `Lh^* ⊣ Rh_*`). -/
theorem subsingleton_hom_of_isZero_push_sheafHom (h : X ⟶ Y) (K N : D B S hS X)
    (hz : IsZero ((push h).obj (sheafHomObj K N))) (m : ℤ) : Subsingleton (K⟦m⟧ ⟶ N) := by
  let _ : ((tensor X).flip.obj K).CommShift ℤ :=
    (smallEtaleDerivedTensorProduct B S hS X).commShift_left K
  let e₁ : tensorObj ((unitD X)⟦m⟧) K ≅ K⟦m⟧ :=
    (((tensor X).flip.obj K).commShiftIso m).app (unitD X) ≪≫
      (shiftFunctor _ m).mapIso (leftUnitIso K)
  let e₂ : (pull h).obj ((unitD Y)⟦m⟧) ≅ (unitD X)⟦m⟧ :=
    ((pull h).commShiftIso m).app (unitD Y) ≪≫ (shiftFunctor _ m).mapIso (pullUnitIso h)
  let e : (K⟦m⟧ ⟶ N) ≃ ((unitD Y)⟦m⟧ ⟶ (push h).obj (sheafHomObj K N)) :=
    (e₁.homCongr (Iso.refl N)).symm.trans <|
      ((tensorSheafHomAdj K).homEquiv _ _).trans <|
        (e₂.homCongr (Iso.refl _)).symm.trans ((pullPushAdj h).homEquiv _ _)
  have : Subsingleton ((unitD Y)⟦m⟧ ⟶ (push h).obj (sheafHomObj K N)) :=
    ⟨fun a b => hz.eq_of_tgt a b⟩
  exact e.subsingleton

/-- `Hom((Lf^*A)[n] ⊗^L K, E) ≅ Hom(A[n], Rf_*R𝓗om(K, E))`, for `f : X ⟶ Y` (step 1 of the
proof): tensor/hom (Stacks 08J8), `Lf^* ⊣ Rf_*` and the shift compatibilities. -/
def homEquivPushSheafHom (f : X ⟶ Y) (A : D B S hS Y) (K E : D B S hS X) (n : ℤ) :
    (A⟦n⟧ ⟶ (push f).obj (sheafHomObj K E)) ≃ ((tensorObj ((pull f).obj A) K)⟦n⟧ ⟶ E) :=
  letI : ((tensor X).flip.obj K).CommShift ℤ :=
    (smallEtaleDerivedTensorProduct B S hS X).commShift_left K
  ((pullPushAdj f).homEquiv _ _).symm.trans <|
    ((tensorSheafHomAdj K).homEquiv _ _).symm.trans <|
      Iso.homCongr
        (((tensor X).flip.obj K).mapIso (((pull f).commShiftIso n).app A) ≪≫
          (((tensor X).flip.obj K).commShiftIso n).app ((pull f).obj A))
        (Iso.refl E)

/-- `Hom(A[m], Rf_*N) ≅ Hom((Lf^*A)[m], N)` (step 4 of the proof). -/
def homEquivPushShift (f : X ⟶ Y) (A : D B S hS Y) (N : D B S hS X) (m : ℤ) :
    (A⟦m⟧ ⟶ (push f).obj N) ≃ (((pull f).obj A)⟦m⟧ ⟶ N) :=
  ((pullPushAdj f).homEquiv _ _).symm.trans
    ((((pull f).commShiftIso m).app A).homCongr (Iso.refl N))

end HomComputations

/-! ### The cover argument -/

section Cover

variable {T Y₁ Y₂ U : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ T) (f₂ : Y₂ ⟶ T) (s : U ⟶ Y₁)

/-- The base change `t : U ×_T Y₂ ⟶ Y₁ ×_T Y₂` of `s : U ⟶ Y₁` (the fibre product
`U ×_T Y₂` taken along `s ≫ f₁`). -/
abbrev coverMap : pullback (s ≫ f₁) f₂ ⟶ pullback f₁ f₂ :=
  pullback.lift (pullback.fst (s ≫ f₁) f₂ ≫ s) (pullback.snd (s ≫ f₁) f₂)
    (by rw [Category.assoc, pullback.condition])

/-- The square `t ≫ g₁ = h₁ ≫ s` is cartesian (pasting of pullback squares). -/
theorem isPullback_coverMap :
    IsPullback (coverMap f₁ f₂ s) (pullback.fst (s ≫ f₁) f₂) (pullback.fst f₁ f₂) s := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f₁ f₂).flip
  rw [pullback.lift_snd]
  exact (IsPullback.of_hasPullback (s ≫ f₁) f₂).flip

theorem coverMap_snd : coverMap f₁ f₂ s ≫ pullback.snd f₁ f₂ = pullback.snd (s ≫ f₁) f₂ :=
  pullback.lift_snd _ _ _

variable (h4 : Tag08F4Input B S hS) (h08FA : Tag08FAInput B S hS) (h0A8A : Tag0A8AInput B S hS)
  (h08I3 : Tag08I3PerfectInput B S hS) (hpp : PerfectPullbackInput B S hS)
  (hbc : EtaleBaseChangeInput B S hS)

include h0A8A h08FA h08I3 hpp hbc in
/-- **Steps 1–4 of the proof of Lemma 5.4**: for `E ∈ D_qc(Y₁ ×_T Y₂)` receiving only zero maps
from the shifts of `G = Lg₁^*P₁ ⊗^L Lg₂^*P₂`, with `P₁` generating `D_qc(Y₁)` and `P₂` perfect, and
an étale `s : U ⟶ Y₁`, every map `(Lh₂^*P₂)[m] ⟶ Lt^*E` vanishes. -/
theorem subsingleton_hom_coverMap {P₁ : D B S hS Y₁} {P₂ : D B S hS Y₂}
    (hP₁ : ∀ E : D B S hS Y₁, Dqc Y₁ E → (∀ (n : ℤ) (g : P₁⟦n⟧ ⟶ E), g = 0) → IsZero E)
    (hP₂ : Perf Y₂ P₂) (hg₁qc : IsQuasiCompact B S hS (pullback.fst f₁ f₂).hom)
    (hg₁qs : IsQuasiSeparated B S hS (pullback.fst f₁ f₂).hom)
    (hs : IsEtale B S hS s.hom) {E : D B S hS (pullback f₁ f₂)} (hE : Dqc _ E)
    (horth : ∀ (n : ℤ) (g : (boxObj f₁ f₂ P₁ P₂)⟦n⟧ ⟶ E), g = 0) (m : ℤ) :
    Subsingleton
      (((pull (pullback.snd (s ≫ f₁) f₂)).obj P₂)⟦m⟧ ⟶ (pull (coverMap f₁ f₂ s)).obj E) := by
  set g₁ := pullback.fst f₁ f₂
  set g₂ := pullback.snd f₁ f₂
  set t := coverMap f₁ f₂ s
  set K := (pull g₂).obj P₂
  have hKp : Perf _ K := hpp _ _ hP₂
  set M := sheafHomObj K E
  -- Step 1: `Rg₁_* M ≅ 0`.
  have hM : Dqc _ M := sheafHomObj_mem_Dqc_of_perfect h0A8A hKp hE
  have h₁ : IsZero ((push g₁).obj M) := by
    refine hP₁ _ (h08FA g₁ hg₁qc hg₁qs M hM) fun n g => ?_
    have : Subsingleton ((boxObj f₁ f₂ P₁ P₂)⟦n⟧ ⟶ E) :=
      ⟨fun a b => (horth n a).trans (horth n b).symm⟩
    have := (homEquivPushSheafHom g₁ P₁ K E n).subsingleton
    exact Subsingleton.elim _ _
  -- Step 2: étale base change, `Rh₁_*(Lt^* M) ≅ 0`.
  have sq := isPullback_coverMap f₁ f₂ s
  have h₂ : IsZero ((push (pullback.fst (s ≫ f₁) f₂)).obj ((pull t).obj M)) :=
    ((pull s).map_isZero h₁).of_iso (@asIso _ _ _ _ _ (hbc sq hs M)).symm
  -- `Lt^* M ≅ R𝓗om(Lh₂^* P₂, Lt^* E)`.
  have := h08I3 t K hKp E
  let eK : (pull (pullback.snd (s ≫ f₁) f₂)).obj P₂ ≅ (pull t).obj K :=
    (eqToIso (by rw [← coverMap_snd f₁ f₂ s])) ≪≫ ((BaseChange.moduleCompIso t g₂).app P₂).symm
  let eM : (pull t).obj M ≅
      sheafHomObj ((pull (pullback.snd (s ≫ f₁) f₂)).obj P₂) ((pull t).obj E) :=
    asIso (sheafHomPullbackMap t K E) ≪≫ ((sheafHom _).mapIso eK.op).app _
  -- Step 3: the unit.
  exact subsingleton_hom_of_isZero_push_sheafHom (pullback.fst (s ≫ f₁) f₂) _ _
    (h₂.of_iso ((push _).mapIso eM).symm) m

variable (hex : Conservative.FlatPullbackExactInput B S hS)
  (hsupp : Conservative.FlatPullbackSupportInput B S hS) (hempty : LP26.SupportEmptyInput B S hS)

include h4 h0A8A h08FA h08I3 hpp hbc hex hsupp hempty in
/-- **Lemma 5.4** (`lem:neeman2023cor5_10`), **zero detection, GL26's cover argument**: let
`P₁` generate `D_qc(Y₁)` and `P₂` generate `D_qc(Y₂)`, `P₂` perfect, let `s : U ⟶ Y₁` be étale
and surjective, and suppose that `g₁ : Y₁ ×_T Y₂ ⟶ Y₁` and `h₂ : U ×_T Y₂ ⟶ Y₂` are quasi-compact
and quasi-separated and that `Rh₂_*` is conservative on `D_qc(U ×_T Y₂)`.  Then every
`E ∈ D_qc(Y₁ ×_T Y₂)` receiving only zero maps from the shifts of `G` is zero. -/
theorem isZero_of_orthogonal_box {P₁ : D B S hS Y₁} {P₂ : D B S hS Y₂}
    (hP₁ : ∀ E : D B S hS Y₁, Dqc Y₁ E → (∀ (n : ℤ) (g : P₁⟦n⟧ ⟶ E), g = 0) → IsZero E)
    (hP₂g : ∀ E : D B S hS Y₂, Dqc Y₂ E → (∀ (n : ℤ) (g : P₂⟦n⟧ ⟶ E), g = 0) → IsZero E)
    (hP₂ : Perf Y₂ P₂) (hg₁qc : IsQuasiCompact B S hS (pullback.fst f₁ f₂).hom)
    (hg₁qs : IsQuasiSeparated B S hS (pullback.fst f₁ f₂).hom)
    (hs : IsEtale B S hS s.hom) (hsurj : IsSurjective B S hS s.hom)
    (hh₂qc : IsQuasiCompact B S hS (pullback.snd (s ≫ f₁) f₂).hom)
    (hh₂qs : IsQuasiSeparated B S hS (pullback.snd (s ≫ f₁) f₂).hom)
    (hcons : ∀ N : D B S hS (pullback (s ≫ f₁) f₂), Dqc _ N →
      IsZero ((push (pullback.snd (s ≫ f₁) f₂)).obj N) → IsZero N)
    {E : D B S hS (pullback f₁ f₂)} (hE : Dqc _ E)
    (horth : ∀ (n : ℤ) (g : (boxObj f₁ f₂ P₁ P₂)⟦n⟧ ⟶ E), g = 0) : IsZero E := by
  set t := coverMap f₁ f₂ s
  set h₂ := pullback.snd (s ≫ f₁) f₂
  have hN : Dqc _ ((pull t).obj E) := h4 t E hE
  -- Step 4: `Rh₂_* Lt^* E ≅ 0`, as `P₂` generates.
  have hpush : IsZero ((push h₂).obj ((pull t).obj E)) := by
    refine hP₂g _ (h08FA h₂ hh₂qc hh₂qs _ hN) fun m g => ?_
    have := subsingleton_hom_coverMap f₁ f₂ s h08FA h0A8A h08I3 hpp hbc hP₁ hP₂ hg₁qc hg₁qs hs
      hE horth m
    have := (homEquivPushShift h₂ P₂ ((pull t).obj E) m).subsingleton
    exact Subsingleton.elim _ _
  -- Step 5: conservativity of `Rh₂_*`, then Lemma 2.14 for the faithfully flat `t`.
  have sq := isPullback_coverMap f₁ f₂ s
  have ht : IsEtale B S hS t.hom :=
    isEtale_of_isPullback B S hS _ _ _ _ sq.flip hs
  exact Conservative.lemma_2_14 hex hsupp hempty t (isFlat_of_isEtale B S hS ht)
    (isSurjective_of_isPullback B S hS sq.flip hsurj) E hE (hcons _ hN hpush)

end Cover

/-! ### Lemma 5.4 -/

section Main

variable (hZ : B.Contains (⊤_ Scheme.{u}))
  (h4 : Tag08F4Input B S hS) (h08FA : Tag08FAInput B S hS) (h0A8A : Tag0A8AInput B S hS)
  (h08I3 : Tag08I3PerfectInput B S hS) (hpp : PerfectPullbackInput B S hS)
  (hbc : EtaleBaseChangeInput B S hS)
  (hex : Conservative.FlatPullbackExactInput B S hS)
  (hsupp : Conservative.FlatPullbackSupportInput B S hS) (hempty : LP26.SupportEmptyInput B S hS)
  (h073B : Tag073BInput B S hS) (h073B2 : Tag073BTwoInput B S hS)
  (hsrc : QuasiCompactSourceInput B S hS) (h09M8 : Tag09M8Input B S hS)
  (h09JB : QuasiPerfect.Tag09JBInput B S hS) (hPq : PerfectQcohInput B S hS)

/-- **Lemma 5.4** (`lem:neeman2023cor5_10`), the statement of the paper: for morphisms
`f_i : Y_i ⟶ T` of quasi-compact quasi-separated algebraic spaces and compact generators `P_i` of
`D_qc(Y_i)`, `Lg₁^*P₁ ⊗^L Lg₂^*P₂` lies in `D_qc(Y₁ ×_T Y₂)` and is a compact generator of it.
**Not proved** in this generality (module docstring, "What is missing"); see
`lemma_5_4_of_conservative`, `lemma_5_4_of_factorization`, `lemma_5_4_of_isAffineHom`. -/
def Lemma54Statement : Prop :=
  ∀ {T Y₁ Y₂ : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ T) (f₂ : Y₂ ⟶ T),
    IsQuasiCompactSpace B S hS T.1 → IsAbsolutelyQuasiSeparated B S hS hZ T.1 →
    IsQuasiCompactSpace B S hS Y₁.1 → IsAbsolutelyQuasiSeparated B S hS hZ Y₁.1 →
    IsQuasiCompactSpace B S hS Y₂.1 → IsAbsolutelyQuasiSeparated B S hS hZ Y₂.1 →
    ∀ (P₁ : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y₁.1 Y₁.2)
      (P₂ : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y₂.1 Y₂.2),
      IsCompactGeneratorQc P₁ → IsCompactGeneratorQc P₂ →
      ∃ hG : Dqc (pullback f₁ f₂) (boxObj f₁ f₂ (qcObj P₁) (qcObj P₂)),
        IsCompactGeneratorQc
          (⟨_, hG⟩ : Space.QuasicoherentDerivedCategory.{u, u} B S hS (pullback f₁ f₂).1
            (pullback f₁ f₂).2)

include h4 h08FA h0A8A h08I3 hpp hbc hex hsupp hempty h073B h073B2 hsrc h09M8 h09JB hPq in
/-- **Lemma 5.4** (`lem:neeman2023cor5_10`), **GL26's proof with the conservativity of `Rh₂_*`
as hypothesis**: let `f_i : Y_i ⟶ T` with `Y₁`, `Y₂` quasi-compact quasi-separated and `T`
quasi-separated, `P_i` a compact generator of `D_qc(Y_i)`, and `s : U ⟶ Y₁` an étale surjection
from a quasi-compact quasi-separated `U` such that `Rh₂_*` is conservative on `D_qc(U ×_T Y₂)`,
`h₂ : U ×_T Y₂ ⟶ Y₂` the projection.  Then `Lg₁^*P₁ ⊗^L Lg₂^*P₂` is a compact generator of
`D_qc(Y₁ ×_T Y₂)`.

GL26 takes `U` affine and obtains the conservativity from Lemmas 2.17 and 3.2, which are not
available here in that generality (module docstring); `T` quasi-compact is not needed. -/
theorem lemma_5_4_of_conservative {T Y₁ Y₂ U : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ T)
    (f₂ : Y₂ ⟶ T) (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T.1)
    (hY₁qc : IsQuasiCompactSpace B S hS Y₁.1) (hY₁qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₁.1)
    (hY₂qc : IsQuasiCompactSpace B S hS Y₂.1) (hY₂qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₂.1)
    (P₁ : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y₁.1 Y₁.2)
    (P₂ : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y₂.1 Y₂.2)
    (hP₁ : IsCompactGeneratorQc P₁) (hP₂ : IsCompactGeneratorQc P₂)
    (s : U ⟶ Y₁) (hs : IsEtale B S hS s.hom) (hsurj : IsSurjective B S hS s.hom)
    (hUqc : IsQuasiCompactSpace B S hS U.1) (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1)
    (hcons : ∀ N : D B S hS (pullback (s ≫ f₁) f₂), Dqc _ N →
      IsZero ((push (pullback.snd (s ≫ f₁) f₂)).obj N) → IsZero N) :
    ∃ hG : Dqc (pullback f₁ f₂) (boxObj f₁ f₂ (qcObj P₁) (qcObj P₂)),
      IsCompactGeneratorQc
        (⟨_, hG⟩ : Space.QuasicoherentDerivedCategory.{u, u} B S hS (pullback f₁ f₂).1
          (pullback f₁ f₂).2) := by
  obtain ⟨hG, -, hGc⟩ := lemma_5_4_compact f₁ f₂ hZ h073B h073B2 hsrc h09M8 h09JB hpp hPq hTqs
    hY₁qc hY₁qs hY₂qc hY₂qs P₁ P₂ hP₁.1 hP₂.1
  refine ⟨hG, hGc, fun E hE horth => ?_⟩
  obtain ⟨hg₁qc, hg₁qs⟩ := isQcqs_fst f₁ f₂ hZ h073B h073B2 hTqs hY₂qc hY₂qs
  have sq := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback (s ≫ f₁) f₂)
  exact isZero_of_orthogonal_box f₁ f₂ s h4 h08FA h0A8A h08I3 hpp hbc hex hsupp hempty
    hP₁.2 hP₂.2 ((h09M8 hZ Y₂ hY₂qc hY₂qs P₂).1 hP₂.1) hg₁qc hg₁qs hs hsurj
    (isQuasiCompact_of_isPullback B S hS sq (h073B hZ T.2 hTqs hUqc (s ≫ f₁).hom))
    (isQuasiSeparated_of_isPullback B S hS sq (h073B2 hZ U.2 hUqs (s ≫ f₁).hom)) hcons hE horth

variable (haff : Conservative.AffinePushforwardConservativeInput B S hS)

include h4 h08FA h0A8A h08I3 hpp hbc hex hsupp hempty h073B h073B2 hsrc h09M8 h09JB hPq haff in
/-- **Lemma 5.4** (`lem:neeman2023cor5_10`) **when `f₁` is affine**, unconditionally (AxiomMath
inputs only): for `f₁ : Y₁ ⟶ T` affine and `f₂ : Y₂ ⟶ T`, with `Y₁`, `Y₂` quasi-compact
quasi-separated, `T` quasi-separated and `P_i` compact generators of `D_qc(Y_i)`,
`Lg₁^*P₁ ⊗^L Lg₂^*P₂` is a compact generator of `D_qc(Y₁ ×_T Y₂)`.  The cover is `s = 𝟙`; the
projection `h₂` is affine, so `Rh₂_*` is conservative (Stacks 0E4R,
`AffinePushforwardConservativeInput`). -/
theorem lemma_5_4_of_isAffineHom {T Y₁ Y₂ : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ T)
    (f₂ : Y₂ ⟶ T) (hf₁ : IsAffineHom B S hS f₁.hom)
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T.1)
    (hY₁qc : IsQuasiCompactSpace B S hS Y₁.1) (hY₁qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₁.1)
    (hY₂qc : IsQuasiCompactSpace B S hS Y₂.1) (hY₂qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₂.1)
    (P₁ : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y₁.1 Y₁.2)
    (P₂ : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y₂.1 Y₂.2)
    (hP₁ : IsCompactGeneratorQc P₁) (hP₂ : IsCompactGeneratorQc P₂) :
    ∃ hG : Dqc (pullback f₁ f₂) (boxObj f₁ f₂ (qcObj P₁) (qcObj P₂)),
      IsCompactGeneratorQc
        (⟨_, hG⟩ : Space.QuasicoherentDerivedCategory.{u, u} B S hS (pullback f₁ f₂).1
          (pullback f₁ f₂).2) := by
  have hsurj : IsSurjective B S hS (𝟙 Y₁ : Y₁ ⟶ Y₁).hom := by
    change Function.Surjective (pointsMap B S hS Y₁.1 (𝟙 Y₁.1))
    rw [pointsMap_id]
    exact Function.surjective_id
  have hcomp : IsAffineHom B S hS (𝟙 Y₁ ≫ f₁).hom := by simpa using hf₁
  have hh₂ : IsAffineHom B S hS (pullback.snd (𝟙 Y₁ ≫ f₁) f₂).hom :=
    isAffineHom_of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback (𝟙 Y₁ ≫ f₁) f₂)) hcomp
  exact lemma_5_4_of_conservative hZ h4 h08FA h0A8A h08I3 hpp hbc hex hsupp hempty h073B h073B2
    hsrc h09M8 h09JB hPq f₁ f₂ hTqs hY₁qc hY₁qs hY₂qc hY₂qs P₁ P₂ hP₁ hP₂ (𝟙 Y₁)
    (isEtale_id B S hS Y₁.1) hsurj hY₁qc hY₁qs fun N hN h => haff _ hh₂ N hN h

variable (hcounit : LP26.OpenImmersionCounitInput B S hS)

include h4 h08FA h0A8A h08I3 hpp hbc hex hsupp hempty h073B h073B2 hsrc h09M8 h09JB hPq haff
  hcounit in
/-- **Lemma 5.4** (`lem:neeman2023cor5_10`) **given a factorization of the cover**: as in
`lemma_5_4_of_conservative`, with the conservativity of `Rh₂_*` replaced by a factorization
`s ≫ f₁ = j ≫ p` of `U ⟶ T` into a quasi-compact open immersion `j` and an affine morphism `p`.
Then `h₂ = j' ≫ p'` is the base change of that factorization, and `Rh₂_*` is conservative by
`Conservative.lemma_3_2_of_factorization` (wave 10's Lemma 3.2).  GL26's proof needs such a
factorization for `U` affine; it is Stacks 081X/086S for the quasi-affine `U ⟶ T` (Lemma 2.17). -/
theorem lemma_5_4_of_factorization {T Y₁ Y₂ U P : AlgebraicSpaces B S hS} (f₁ : Y₁ ⟶ T)
    (f₂ : Y₂ ⟶ T) (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T.1)
    (hY₁qc : IsQuasiCompactSpace B S hS Y₁.1) (hY₁qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₁.1)
    (hY₂qc : IsQuasiCompactSpace B S hS Y₂.1) (hY₂qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₂.1)
    (P₁ : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y₁.1 Y₁.2)
    (P₂ : Space.QuasicoherentDerivedCategory.{u, u} B S hS Y₂.1 Y₂.2)
    (hP₁ : IsCompactGeneratorQc P₁) (hP₂ : IsCompactGeneratorQc P₂)
    (s : U ⟶ Y₁) (hs : IsEtale B S hS s.hom) (hsurj : IsSurjective B S hS s.hom)
    (hUqc : IsQuasiCompactSpace B S hS U.1) (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1)
    (j : U ⟶ P) (p : P ⟶ T) (hj : IsOpenImmersion B S hS j.hom)
    (hjqc : IsQuasiCompact B S hS j.hom) (hp : IsAffineHom B S hS p.hom) (hfac : s ≫ f₁ = j ≫ p) :
    ∃ hG : Dqc (pullback f₁ f₂) (boxObj f₁ f₂ (qcObj P₁) (qcObj P₂)),
      IsCompactGeneratorQc
        (⟨_, hG⟩ : Space.QuasicoherentDerivedCategory.{u, u} B S hS (pullback f₁ f₂).1
          (pullback f₁ f₂).2) := by
  refine lemma_5_4_of_conservative hZ h4 h08FA h0A8A h08I3 hpp hbc hex hsupp hempty h073B h073B2
    hsrc h09M8 h09JB hPq f₁ f₂ hTqs hY₁qc hY₁qs hY₂qc hY₂qs P₁ P₂ hP₁ hP₂ s hs hsurj hUqc hUqs ?_
  -- `h₂ = j' ≫ p'`, with `j'` and `p'` the base changes of `j` and `p` along `f₂`.
  let j' : pullback (s ≫ f₁) f₂ ⟶ pullback p f₂ :=
    pullback.lift (pullback.fst (s ≫ f₁) f₂ ≫ j) (pullback.snd (s ≫ f₁) f₂)
      (by rw [Category.assoc, ← hfac, pullback.condition])
  have hfacj : j' ≫ pullback.snd p f₂ = pullback.snd (s ≫ f₁) f₂ := pullback.lift_snd _ _ _
  have sqj : IsPullback j' (pullback.fst (s ≫ f₁) f₂) (pullback.fst p f₂) j := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback p f₂).flip
    rw [hfacj, ← hfac]
    exact (IsPullback.of_hasPullback (s ≫ f₁) f₂).flip
  have sqj' := AlgebraicSpaces.isPullback_hom B S hS sqj.flip
  have hj' : IsOpenImmersion B S hS j'.hom := isOpenImmersion_of_isPullback B S hS sqj.flip hj
  have hj'qc : IsQuasiCompact B S hS j'.hom := isQuasiCompact_of_isPullback B S hS sqj' hjqc
  have hp' : IsAffineHom B S hS (pullback.snd p f₂).hom :=
    isAffineHom_of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback p f₂)) hp
  intro N hN h
  rw [← hfacj] at h
  exact Conservative.lemma_3_2_of_factorization h08FA hcounit haff j' (pullback.snd p f₂) hj'
    hj'qc hp' N hN h

/-! ### The residue is necessary -/

/-- **Lemma 5.4** (`lem:neeman2023cor5_10`), **the residue is necessary** (one direction of
`isZero_of_orthogonal_box_unit_iff`): for `a : U ⟶ T` and `f₂ : Y₂ ⟶ T`, if
`Lh₁^*𝒪_U ⊗^L Lh₂^*P₂` detects zero
objects of `D_qc(U ×_T Y₂)`, then `Rh₂_*` is conservative on `D_qc(U ×_T Y₂)`
(`Lh₁^*𝒪_U ⊗^L Lh₂^*P₂ ≅ Lh₂^*P₂` and `Hom((Lh₂^*P₂)[n], N) ≅ Hom(P₂[n], Rh₂_*N)`). -/
theorem conservative_of_isZero_of_orthogonal_box {T Y₂ U : AlgebraicSpaces B S hS} (a : U ⟶ T)
    (f₂ : Y₂ ⟶ T) (P₂ : D B S hS Y₂)
    (hgen : ∀ N : D B S hS (pullback a f₂), Dqc _ N →
      (∀ (n : ℤ) (g : (boxObj a f₂ (unitD U) P₂)⟦n⟧ ⟶ N), g = 0) → IsZero N) :
    ∀ N : D B S hS (pullback a f₂), Dqc _ N →
      IsZero ((push (pullback.snd a f₂)).obj N) → IsZero N := by
  intro N hN h
  refine hgen N hN fun n g => ?_
  let e : boxObj a f₂ (unitD U) P₂ ≅ (pull (pullback.snd a f₂)).obj P₂ :=
    ((tensor _).flip.obj _).mapIso (pullUnitIso _) ≪≫ leftUnitIso _
  have : Subsingleton (P₂⟦n⟧ ⟶ (push (pullback.snd a f₂)).obj N) :=
    ⟨fun x y => h.eq_of_tgt x y⟩
  have := (homEquivPushShift (pullback.snd a f₂) P₂ N n).symm.subsingleton
  have := (((shiftFunctor _ n).mapIso e).homCongr (Iso.refl N)).subsingleton
  exact Subsingleton.elim _ _

/-- **The residue of `lemma_5_4_of_conservative` is the case `P₁ = 𝒪_U` of Lemma 5.4**
(`lem:neeman2023cor5_10`): for `a : U ⟶ T`, `f₂ : Y₂ ⟶ T`, `P₂` generating `D_qc(Y₂)` and the
projection `h₂ : U ×_T Y₂ ⟶ Y₂` quasi-compact and quasi-separated, `Lh₁^*𝒪_U ⊗^L Lh₂^*P₂` detects
zero objects of `D_qc(U ×_T Y₂)` if and only if `Rh₂_*` is conservative on `D_qc(U ×_T Y₂)`.
Applied with `Y₁ = U` and `P₁ = 𝒪_U` (a compact generator of `D_qc(U)` for `U` affine,
Stacks 09IS), Lemma 5.4 therefore implies the hypothesis `hcons` of `lemma_5_4_of_conservative`:
no proof of Lemma 5.4 avoids it. -/
theorem isZero_of_orthogonal_box_unit_iff (h08FA : Tag08FAInput B S hS)
    {T Y₂ U : AlgebraicSpaces B S hS} (a : U ⟶ T) (f₂ : Y₂ ⟶ T) (P₂ : D B S hS Y₂)
    (hP₂g : ∀ E : D B S hS Y₂, Dqc Y₂ E → (∀ (n : ℤ) (g : P₂⟦n⟧ ⟶ E), g = 0) → IsZero E)
    (hh₂qc : IsQuasiCompact B S hS (pullback.snd a f₂).hom)
    (hh₂qs : IsQuasiSeparated B S hS (pullback.snd a f₂).hom) :
    (∀ N : D B S hS (pullback a f₂), Dqc _ N →
      (∀ (n : ℤ) (g : (boxObj a f₂ (unitD U) P₂)⟦n⟧ ⟶ N), g = 0) → IsZero N) ↔
    (∀ N : D B S hS (pullback a f₂), Dqc _ N →
      IsZero ((push (pullback.snd a f₂)).obj N) → IsZero N) := by
  refine ⟨conservative_of_isZero_of_orthogonal_box a f₂ P₂, fun hcons N hN horth => ?_⟩
  refine hcons N hN (hP₂g _ (h08FA _ hh₂qc hh₂qs N hN) fun n g => ?_)
  let e : boxObj a f₂ (unitD U) P₂ ≅ (pull (pullback.snd a f₂)).obj P₂ :=
    ((tensor _).flip.obj _).mapIso (pullUnitIso _) ≪≫ leftUnitIso _
  have : Subsingleton ((boxObj a f₂ (unitD U) P₂)⟦n⟧ ⟶ N) :=
    ⟨fun x y => (horth n x).trans (horth n y).symm⟩
  have := (((shiftFunctor _ n).mapIso e).homCongr (Iso.refl N)).symm.subsingleton
  have := (homEquivPushShift (pullback.snd a f₂) P₂ N n).subsingleton
  exact Subsingleton.elim _ _

end Main

end RelativeFM.Spaces.BoxGeneration
