/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Statements.Notions

/-!
# GL26's headline results over algebraic spaces: the statements

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26).  Each
result is a `def …Statement : Prop` over the algebraic-space layer `Spaces/` (AxiomMath's
algebraic spaces, `D(𝒪_X)` on the small étale site, `D_qc`, `D^b_coh`, `Perf`, `Lf^*`, `Rf_*`,
`⊗^L`), with the paper's hypotheses.  Nothing is proved here; these are the targets that
supersede the interface targets of `FourierMukai/Paper/Statements.lean` (table in
`Spaces/Statements.lean`).  The vocabulary is in `Spaces/Statements/Notions.lean`, whose
docstring records the conventions (base, points, restriction to `D_qc`/`D^b_coh`).

## Common conventions

* GL26's base algebraic space is `S'`, an object of `AlgebraicSpaces B S hS`; `Y₁ ×_{S'} Y₂` is
  `pullback f₁ f₂`; `K ∈ D(Y₁ ×_{S'} Y₂)`.
* **Setup 2.20** (`setup:fm_cube_pullback`): `t : T ⟶ S'` a morphism of Noetherian algebraic
  spaces and `f_i : Y_i ⟶ S'` proper and flat.  A statement that does not mention `T` takes
  only `S'` Noetherian (the existence of some Noetherian `T ⟶ S'` is automatic, `T = S'`).
* "relatively perfect over `Y_i`": `IsRelativelyPerfect` (Definition 4.1) for the projection
  onto `Y_i`.  GL26's Definition 4.1 includes `K ∈ D_qc`; the statements also state `Dqc K`
  explicitly where the paper writes `K ∈ D_qc(Y₁ ×_S Y₂)`.
* "pseudocoherent": `IsPseudoCoherent` (Stacks 08FT); `D^b_coh`: `DbCoh`.
* A "resp." statement is stated once for `equiv : Bool` (`FFOrEquivOn`): `false` reads
  "fully faithful", `true` reads "an equivalence".
* Every statement takes the base `(B, S, hS)` explicitly; the Noetherian hypotheses take
  `hZ : B.Contains (⊤_ Scheme)` (see `Notions.lean`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Statements

open RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Part 1: relatively perfect complexes -/

/-- **Theorem 1.3** (`thm:stacky_all_coincide`; proved in GL26 §6 from Propositions 6.2,
`prop:stacky_all_coincide`, and 6.8, `prop:preservation_of_dbcoh`).  For a proper morphism
`f : Y ⟶ X` of Noetherian algebraic spaces and a pseudocoherent `E ∈ D_qc(Y)`, the following
are equivalent: (1) `E` is `f`-perfect; (2) `E ⊗^L Lf^*A ∈ D^b_coh(Y)` for every
`A ∈ D^b_coh(X)`; (3) `E` is `f`-quasi-perfect.

Supersedes `RelativeFM.theorem_1_3` of `Paper/Statements.lean`.  No gap. -/
def theorem_1_3Statement : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X),
    IsNoetherianSpace hZ X → IsNoetherianSpace hZ Y → IsProperHom f →
    ∀ E : D B S hS Y, Dqc Y E → IsPseudoCoherent Y E →
      List.TFAE
        [IsRelativelyPerfect f E,
          ∀ A : D B S hS X, DbCoh X A → DbCoh Y (tensorObj E ((pull f).obj A)),
          IsQuasiPerfect f E]

/-- **Corollary 6.18** (`cor:noetherian_base_change_for_relative_perfectness`).  In Setup 2.20
(`t : T ⟶ S'` a morphism of Noetherian algebraic spaces, `f_i : Y_i ⟶ S'` proper flat), if
`K ∈ D^b_coh(Y₁ ×_{S'} Y₂)` is relatively perfect over `Y₁` (resp. over `Y₂`), then
`L(t')^*K` is relatively perfect over `Y₁ ×_{S'} T` (resp. over `Y₂ ×_{S'} T`), i.e. perfect
relative to the projection of `(Y₁ ×_{S'} T) ×_T (Y₂ ×_{S'} T)` onto that factor.

Supersedes `RelativeFM.corollary_6_18` of `Paper/Statements.lean` (an interface rendering over
an abstract base-change square).  No gap. -/
def corollary_6_18Statement : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {S' Y₁ Y₂ T : AlgebraicSpaces B S hS}
    (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S') (t : T ⟶ S'),
    IsNoetherianSpace hZ S' → IsNoetherianSpace hZ T →
    IsProperHom f₁ → IsFlatHom f₁ → IsProperHom f₂ → IsFlatHom f₂ →
    ∀ K : D B S hS (pullback f₁ f₂), DbCoh _ K →
      (IsRelPerfOverFst f₁ f₂ K →
          IsRelPerfOverFst (pullback.snd f₁ t) (pullback.snd f₂ t)
            (baseChangeKernel f₁ f₂ t K)) ∧
        (IsRelPerfOverSnd f₁ f₂ K →
          IsRelPerfOverSnd (pullback.snd f₁ t) (pullback.snd f₂ t)
            (baseChangeKernel f₁ f₂ t K))

/-! ### Part 2: fibrewise criteria -/

/-- **Theorem 10.13** (`thm:descent_ascent`).  In Setup 2.20, let `K ∈ D_qc(Y₁ ×_{S'} Y₂)` be
pseudocoherent and relatively perfect over each `Y_i`.  The following are equivalent, for
"fully faithful" (`equiv = false`) and for "an equivalence" (`equiv = true`):
1. `Φ_K` is fully faithful (resp. an equivalence) on `D^b_coh`;
2. `Φ_{L(t')^*K}` is so on `D^b_coh` for every quasi-affine morphism `t : T ⟶ S'` from a
   Noetherian algebraic space;
3. `Φ_{L(t')^*K}` is so on `D^b_coh` for every `t : Spec k ⟶ S'` of finite type representing
   a closed point of `|S'|`;
4. every closed point `p ∈ |S'|` has a representative `t : Spec k ⟶ S'` with `Φ_{L(t')^*K}`
   so on `D^b_coh`.

`Φ_K` itself is `fibreTransform` along `𝟙 S'` up to the canonical identification of
`Y_i ×_{S'} S'` with `Y_i`; item 1 is stated for `transformOver f₁ f₂ K` directly.
Supersedes `RelativeFM.theorem_1_6` of `Paper/Statements.lean` (together with
`theorem_1_6Statement`).  No gap. -/
def theorem_10_13Statement : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {S' Y₁ Y₂ : AlgebraicSpaces B S hS}
    (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S'),
    IsNoetherianSpace hZ S' →
    IsProperHom f₁ → IsFlatHom f₁ → IsProperHom f₂ → IsFlatHom f₂ →
    ∀ K : D B S hS (pullback f₁ f₂), Dqc _ K → IsPseudoCoherent _ K →
      IsRelPerfOverFst f₁ f₂ K → IsRelPerfOverSnd f₁ f₂ K →
      ∀ equiv : Bool,
        List.TFAE
          [FFOrEquivOn equiv (DbCoh _) (DbCoh _) (transformOver f₁ f₂ K),
            ∀ (T : AlgebraicSpaces B S hS) (t : T ⟶ S'), IsNoetherianSpace hZ T →
              IsQuasiAffineHom t →
              FFOrEquivOn equiv (DbCoh _) (DbCoh _) (fibreTransform f₁ f₂ t K),
            ∀ x : Representative S', IsClosedPt x.point → IsFiniteTypeHom x.hom →
              FFOrEquivOn equiv (DbCoh _) (DbCoh _) (fibreTransform f₁ f₂ x.hom K),
            ∀ p : Pts S', IsClosedPt p → ∃ x : Representative S', x.Represents p ∧
              FFOrEquivOn equiv (DbCoh _) (DbCoh _) (fibreTransform f₁ f₂ x.hom K)]

/-- **Theorem 1.6** (`introthm:descent_ascent`; = Theorem 10.13 without its item (2)).  Let
`S'` be a Noetherian algebraic space, `f_i : Y_i ⟶ S'` proper flat, and
`K ∈ D^b_coh(Y₁ ×_{S'} Y₂)` relatively perfect over each `Y_i`.  The following are equivalent
(for "fully faithful" and for "an equivalence"): (1) `Φ_K` is so on `D^b_coh`; (2)
`Φ_{L(t')^*K}` is so on `D^b_coh` for every finite type `t : Spec k ⟶ S'` representing a
closed point; (3) every closed point has a representative `t` with `Φ_{L(t')^*K}` so on
`D^b_coh`.

Supersedes `RelativeFM.theorem_1_6` of `Paper/Statements.lean`, whose two `True` hypotheses
are here the relative perfectness of `K` over `Y₁` and over `Y₂`.  No gap. -/
def theorem_1_6Statement : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {S' Y₁ Y₂ : AlgebraicSpaces B S hS}
    (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S'),
    IsNoetherianSpace hZ S' →
    IsProperHom f₁ → IsFlatHom f₁ → IsProperHom f₂ → IsFlatHom f₂ →
    ∀ K : D B S hS (pullback f₁ f₂), DbCoh _ K →
      IsRelPerfOverFst f₁ f₂ K → IsRelPerfOverSnd f₁ f₂ K →
      ∀ equiv : Bool,
        List.TFAE
          [FFOrEquivOn equiv (DbCoh _) (DbCoh _) (transformOver f₁ f₂ K),
            ∀ x : Representative S', IsClosedPt x.point → IsFiniteTypeHom x.hom →
              FFOrEquivOn equiv (DbCoh _) (DbCoh _) (fibreTransform f₁ f₂ x.hom K),
            ∀ p : Pts S', IsClosedPt p → ∃ x : Representative S', x.Represents p ∧
              FFOrEquivOn equiv (DbCoh _) (DbCoh _) (fibreTransform f₁ f₂ x.hom K)]

/-! ### Part 3: openness of the loci (Section 12) -/

/-- **Lemma 12.2** (`lem:independence_for_rep_with_ff_or_eq`).  In Setup 2.20, let
`K ∈ D_qc(Y₁ ×_{S'} Y₂)` be pseudocoherent and relatively perfect over each `Y_i`.  Whether
`Φ_K` is fully faithful (resp. an equivalence) at `p ∈ |S'|` does not depend on the
representative: for two representatives `x`, `y` of the same point, `Φ_{L(t_x')^*K}` is fully
faithful (resp. an equivalence) on `D_qc` iff `Φ_{L(t_y')^*K}` is.

Supersedes `RelativeFM.lemma_12_2` of `Paper/Statements.lean` (whose two `True` hypotheses are
here the relative perfectness of `K`).  No gap. -/
def lemma_12_2Statement : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {S' Y₁ Y₂ : AlgebraicSpaces B S hS}
    (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S'),
    IsNoetherianSpace hZ S' →
    IsProperHom f₁ → IsFlatHom f₁ → IsProperHom f₂ → IsFlatHom f₂ →
    ∀ K : D B S hS (pullback f₁ f₂), Dqc _ K → IsPseudoCoherent _ K →
      IsRelPerfOverFst f₁ f₂ K → IsRelPerfOverSnd f₁ f₂ K →
      ∀ (equiv : Bool) (x y : Representative S'), x.point = y.point →
        (FFOrEquivOn equiv (Dqc _) (Dqc _) (fibreTransform f₁ f₂ x.hom K) ↔
          FFOrEquivOn equiv (Dqc _) (Dqc _) (fibreTransform f₁ f₂ y.hom K))

/-- **Theorem 12.3** (`thm:openness_for_equivalence_fullfaithful_dbcoh`).  In Setup 2.20, let
`K ∈ D_qc(Y₁ ×_{S'} Y₂)` be pseudocoherent and relatively perfect over each `Y_i`.  Then
`FM(K)` and `fm(K)` (Definition 12.1) are open in `|S'|`.

Supersedes `RelativeFM.theorem_12_3` of `Paper/Statements.lean`.  No gap. -/
def theorem_12_3Statement : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {S' Y₁ Y₂ : AlgebraicSpaces B S hS}
    (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S'),
    IsNoetherianSpace hZ S' →
    IsProperHom f₁ → IsFlatHom f₁ → IsProperHom f₂ → IsFlatHom f₂ →
    ∀ K : D B S hS (pullback f₁ f₂), Dqc _ K → IsPseudoCoherent _ K →
      IsRelPerfOverFst f₁ f₂ K → IsRelPerfOverSnd f₁ f₂ K →
      IsOpen (FMLocus f₁ f₂ K) ∧ IsOpen (fmLocus f₁ f₂ K)

/-- **Corollary 12.4** (`cor:deform`).  In Setup 2.20 (`t : T ⟶ S'` a morphism of Noetherian
algebraic spaces), let `K ∈ D_qc(Y₁ ×_{S'} Y₂)` be pseudocoherent and relatively perfect over
each `Y_i`.  Then `|t|⁻¹(fm(K)) = fm(L(t')^*K)` and `|t|⁻¹(FM(K)) = FM(L(t')^*K)`, the loci of
`L(t')^*K` being taken for `Y_i ×_{S'} T ⟶ T`.

Supersedes `RelativeFM.theorem_1_2_baseChange` of `Paper/Statements.lean` in the relatively
perfect case.  No gap. -/
def corollary_12_4Statement : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {S' Y₁ Y₂ T : AlgebraicSpaces B S hS}
    (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S') (t : T ⟶ S'),
    IsNoetherianSpace hZ S' → IsNoetherianSpace hZ T →
    IsProperHom f₁ → IsFlatHom f₁ → IsProperHom f₂ → IsFlatHom f₂ →
    ∀ K : D B S hS (pullback f₁ f₂), Dqc _ K → IsPseudoCoherent _ K →
      IsRelPerfOverFst f₁ f₂ K → IsRelPerfOverSnd f₁ f₂ K →
      ptsMap t ⁻¹' fmLocus f₁ f₂ K =
          fmLocus (pullback.snd f₁ t) (pullback.snd f₂ t) (baseChangeKernel f₁ f₂ t K) ∧
        ptsMap t ⁻¹' FMLocus f₁ f₂ K =
          FMLocus (pullback.snd f₁ t) (pullback.snd f₂ t) (baseChangeKernel f₁ f₂ t K)

/-- **Theorem 12.9** (`thm:fm_locus_weak_approx`).  Let `f_i : Y_i ⟶ S'` be proper flat
morphisms of Noetherian algebraic spaces and `E ∈ D^b_coh(Y₁ ×_{S'} Y₂)` (no relative
perfectness).  Then (1) `FM(E)` is open in `|S'|`; (2) `FM(E)` commutes with arbitrary
Noetherian base change: `|t|⁻¹(FM(E)) = FM(L(t')^*E)` for every morphism `t : T ⟶ S'` of
Noetherian algebraic spaces.

Supersedes `RelativeFM.theorem_1_2_open` and `RelativeFM.theorem_1_2_baseChange` of
`Paper/Statements.lean`.  No gap. -/
def theorem_12_9Statement : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {S' Y₁ Y₂ : AlgebraicSpaces B S hS}
    (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S'),
    IsNoetherianSpace hZ S' → IsNoetherianSpace hZ Y₁ → IsNoetherianSpace hZ Y₂ →
    IsProperHom f₁ → IsFlatHom f₁ → IsProperHom f₂ → IsFlatHom f₂ →
    ∀ E : D B S hS (pullback f₁ f₂), DbCoh _ E →
      IsOpen (FMLocus f₁ f₂ E) ∧
        ∀ (T : AlgebraicSpaces B S hS) (t : T ⟶ S'), IsNoetherianSpace hZ T →
          ptsMap t ⁻¹' FMLocus f₁ f₂ E =
            FMLocus (pullback.snd f₁ t) (pullback.snd f₂ t) (baseChangeKernel f₁ f₂ t E)

/-- **Theorem 1.2** (`thm:fm_locus`; the main theorem).  Let `f_i : Y_i ⟶ S'` be proper flat
morphisms of Noetherian algebraic spaces and `K ∈ D^b_coh(Y₁ ×_{S'} Y₂)`.  Then (1) `FM(K)`
is open in `|S'|` and (2) commutes with arbitrary Noetherian base change; if moreover `K` is
relatively perfect over both `Y_i`, the same holds for `fm(K)`.  GL26 proves (1)–(2) as
Theorem 12.9 and the `fm` clause from Theorem 12.3 and Corollary 12.4.

Supersedes `RelativeFM.theorem_1_2_open` and `RelativeFM.theorem_1_2_baseChange` of
`Paper/Statements.lean`.  No gap. -/
def theorem_1_2Statement : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {S' Y₁ Y₂ : AlgebraicSpaces B S hS}
    (f₁ : Y₁ ⟶ S') (f₂ : Y₂ ⟶ S'),
    IsNoetherianSpace hZ S' → IsNoetherianSpace hZ Y₁ → IsNoetherianSpace hZ Y₂ →
    IsProperHom f₁ → IsFlatHom f₁ → IsProperHom f₂ → IsFlatHom f₂ →
    ∀ K : D B S hS (pullback f₁ f₂), DbCoh _ K →
      (IsOpen (FMLocus f₁ f₂ K) ∧
        ∀ (T : AlgebraicSpaces B S hS) (t : T ⟶ S'), IsNoetherianSpace hZ T →
          ptsMap t ⁻¹' FMLocus f₁ f₂ K =
            FMLocus (pullback.snd f₁ t) (pullback.snd f₂ t)
              (baseChangeKernel f₁ f₂ t K)) ∧
      (IsRelPerfOverFst f₁ f₂ K → IsRelPerfOverSnd f₁ f₂ K →
        IsOpen (fmLocus f₁ f₂ K) ∧
          ∀ (T : AlgebraicSpaces B S hS) (t : T ⟶ S'), IsNoetherianSpace hZ T →
            ptsMap t ⁻¹' fmLocus f₁ f₂ K =
              fmLocus (pullback.snd f₁ t) (pullback.snd f₂ t) (baseChangeKernel f₁ f₂ t K))

end RelativeFM.Spaces.Statements
