/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Affine.Support
import FourierMukai.Scheme.NeemanAffineSupport
import FourierMukai.Scheme.PaperTwoOpenGluing

/-!
# LP26 Corollary 1.2, affine base case, over AxiomMath's algebraic spaces

Lank–Pauwels, *Gluing weak approximability along recollements* (LP26), **Corollary 1.2**
(`cor:weak_approx_spaces`), affine base case: for the affine algebraic space `Spec R` and a
finitely generated ideal `I ⊆ R`, the category `D_{qc,V(I)}(Spec R)` of objects of
`D_qc(Spec R)` supported on `V(I)` is weakly approximable (LP26 Definition 2.1,
`def:weak_approx`, in the tree's form `PaperM2.SatisfiesPaperWA`).

Here `Spec R` is the algebraic space `h_U = yoneda.obj U` represented by an object `U` of the
big fppf site over `S` whose underlying scheme `X_U` is affine, `R = Γ(X_U, 𝒪)`;
`D_{qc,V(I)}` is `RelativeFM.Spaces.DqcSupported (space U) (zeroLocusPoints U I)`
(`Spaces/Categories.lean`: `D_qc` and support in AxiomMath's sense, Stacks 06UP, 04KA, 08GF).

## Main results

* `dqcSupported_eq_map`: `D_{qc,V(I)}(h_U)` is the essential image of `D_{V(I)}(R)` under
  `Φ : D(R) ⥤ D(𝒪_{h_U})`.
* `isTriangulated_dqcSupported`: `D_{qc,V(I)}(h_U)` is a triangulated subcategory of
  `D(𝒪_{h_U})` (for every ideal `I`).
* `supportedComparison`, `isEquivalence_supportedComparison`: the triangulated equivalence
  `D_{V(I)}(R) ≌ D_{qc,V(I)}(h_U)` induced by `Φ`.
* `satisfiesPaperWA_dqcSupported` and the headline `lp26_cor_1_2_affine`: weak
  approximability of `D_{qc,V(I)}(h_U)` for `I` finitely generated, transported from the module
  model (`NeemanAffineSupport.satisfiesPaperWA_of_fg`, wave 5) along that equivalence
  (`SchemeTwoOpenM3.satisfiesPaperWA_of_equivalence`).

## Assumptions

Only the tagged AxiomMath inputs of `Spaces/Affine/Inputs.lean`: `Tag06Z0ExactInput`,
`Tag06Z0QcohInput`, `Tag06Z0Input` (Stacks 06Z0 for `h_U`) and `Tag07TYInput` (Stacks 04KA,
07TY); `Tag021RInput` only for the non-vacuity example.  They are discharged by the orchestrator
in `SpacesVerified`.  No other hypothesis; Neeman 2024, Theorem 3.2 is not used (the module-model
theorem it replaces is proved in the tree).

## Difference from LP26

The statement is LP26's affine base case for the affine algebraic spaces of the site, with
`Z = V(I)`, `I` finitely generated (that is, `Z` closed with quasi-compact complement).  The
weak approximability is the tree's `PaperM2.SatisfiesPaperWA` (LP26 Definition 2.1 with the
paper's zero-detection generation), whose `t`-structure is existential: the one produced is the
transport along `supportedComparison` of the module-model one; that it is the standard
`t`-structure of `D_{qc,V(I)}` is not stated.  The
triangulated structure on `D_{qc,V(I)}(h_U)` is not an instance of the tree: it is produced
(`isTriangulated_dqcSupported`, which uses the inputs), so the headline asserts its existence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space
open RelativeWeakApprox

namespace RelativeFM.Spaces.Affine

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section

variable {X : AlgebraicSpaces B S hS}

/-- `D_qc(X)` is closed under isomorphisms. -/
theorem dqc_of_iso {E F : D B S hS X} (e : E ≅ F) (hE : Dqc X E) : Dqc X F := fun n =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).mapIso e) (hE n)

/-- Being supported on `T` is invariant under isomorphism. -/
theorem cohomologySupportedOn_of_iso {T : Set (points B S hS X.1)} {E F : D B S hS X}
    (e : E ≅ F) (hE : Space.CohomologySupportedOn.{u, u} B S hS X.1 X.2 T E) :
    Space.CohomologySupportedOn.{u, u} B S hS X.1 X.2 T F := fun n => by
  rw [← supportOfSheaf_eq_of_iso
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).mapIso e)]
  exact hE n

end

section Main

variable (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [PreservesFiniteLimits (associated U)]

/-- `Φ`, as a functor `D(R) ⥤ D_qc(h_U)` (AxiomMath's `representedAffineDerivedAssociatedQcoh`,
by its body). -/
abbrev derivedAssociatedQcoh (hq : Tag06Z0QcohInput B S hS) :
    DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
      (Dqc (space U)).FullSubcategory :=
  (Dqc (space U)).lift (derivedAssociated U) (dqc_derivedAssociated U hq)

/-- `Φ : D(R) ⥤ D(𝒪_{h_U})` is fully faithful, from Stacks 06Z0 (`Tag06Z0Input`): it is the
equivalence `D(R) ≌ D_qc(h_U)` followed by the inclusion. -/
def fullyFaithful_derivedAssociated (hq : Tag06Z0QcohInput B S hS)
    (h06Z0 : Tag06Z0Input B S hS) : (derivedAssociated U).FullyFaithful :=
  have := h06Z0 U (dqc_derivedAssociated U hq)
  ((Functor.FullyFaithful.ofFullyFaithful (derivedAssociatedQcoh U hq)).comp
    (Dqc (space U)).fullyFaithfulι).ofIso
      ((Dqc (space U)).liftCompιIso _ (dqc_derivedAssociated U hq))

/-- `Φ : D(R) ⥤ D(𝒪_{h_U})` is full, from Stacks 06Z0 (`Tag06Z0Input`). -/
theorem full_derivedAssociated (hq : Tag06Z0QcohInput B S hS) (h06Z0 : Tag06Z0Input B S hS) :
    (derivedAssociated U).Full :=
  (fullyFaithful_derivedAssociated U hq h06Z0).full

/-- `Φ : D(R) ⥤ D(𝒪_{h_U})` is faithful, from Stacks 06Z0 (`Tag06Z0Input`). -/
theorem faithful_derivedAssociated (hq : Tag06Z0QcohInput B S hS)
    (h06Z0 : Tag06Z0Input B S hS) : (derivedAssociated U).Faithful :=
  (fullyFaithful_derivedAssociated U hq h06Z0).faithful

/-- **`D_{qc,V(I)}(h_U)` is the essential image of `D_{V(I)}(R)` under `Φ`**: from Stacks 06Z0
(every object of `D_qc(h_U)` is `Φ` of an object of `D(R)`) and the support matching
`cohomologySupportedOn_iff`. -/
theorem dqcSupported_eq_map (hq : Tag06Z0QcohInput B S hS) (h06Z0 : Tag06Z0Input B S hS)
    (h07TY : Tag07TYInput B S hS) (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    DqcSupported (space U) (zeroLocusPoints U I) =
      (NeemanFiniteSupportM4.AffineIsSupportedIdeal
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) I).map (derivedAssociated U) := by
  have := h06Z0 U (dqc_derivedAssociated U hq)
  funext E
  apply propext
  constructor
  · rintro ⟨hE, hs⟩
    let F := derivedAssociatedQcoh U hq
    let e : (derivedAssociated U).obj (F.objPreimage ⟨E, hE⟩) ≅ E :=
      (Dqc (space U)).ι.mapIso (F.objObjPreimageIso ⟨E, hE⟩)
    exact ⟨F.objPreimage ⟨E, hE⟩,
      (cohomologySupportedOn_iff U h07TY I _).1 (cohomologySupportedOn_of_iso e.symm hs), ⟨e⟩⟩
  · rintro ⟨M, hM, ⟨e⟩⟩
    exact ⟨dqc_of_iso e (dqc_derivedAssociated U hq M),
      cohomologySupportedOn_of_iso e ((cohomologySupportedOn_iff U h07TY I M).2 hM)⟩

/-- **`D_{qc,V(I)}(h_U)` is a triangulated subcategory of `D(𝒪_{h_U})`**, for every ideal `I`:
it is the essential image of the triangulated subcategory `D_{V(I)}(R)` under the full
triangulated functor `Φ` (`dqcSupported_eq_map`). -/
theorem isTriangulated_dqcSupported (hq : Tag06Z0QcohInput B S hS)
    (h06Z0 : Tag06Z0Input B S hS) (h07TY : Tag07TYInput B S hS)
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (DqcSupported (space U) (zeroLocusPoints U I)).IsTriangulated := by
  have := full_derivedAssociated U hq h06Z0
  rw [dqcSupported_eq_map U hq h06Z0 h07TY I]
  infer_instance

section Comparison

variable (hq : Tag06Z0QcohInput B S hS) (h06Z0 : Tag06Z0Input B S hS)
  (h07TY : Tag07TYInput B S hS) (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))

/-- **The comparison functor** `D_{V(I)}(R) ⥤ D_{qc,V(I)}(h_U)`, `M ↦ Φ(M)`. -/
def supportedComparison :
    NeemanFiniteSupportM4.AffineDZIdeal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) I ⥤
      (DqcSupported (space U) (zeroLocusPoints U I)).FullSubcategory :=
  (DqcSupported (space U) (zeroLocusPoints U I)).lift
    ((NeemanFiniteSupportM4.AffineIsSupportedIdeal _ I).ι ⋙ derivedAssociated U)
    (fun M => ⟨dqc_derivedAssociated U hq M.obj,
      (cohomologySupportedOn_iff U h07TY I M.obj).2 M.property⟩)

include h06Z0 in
/-- **The comparison functor is an equivalence** `D_{V(I)}(R) ≌ D_{qc,V(I)}(h_U)`. -/
theorem isEquivalence_supportedComparison :
    (supportedComparison U hq h07TY I).IsEquivalence := by
  let P := DqcSupported (space U) (zeroLocusPoints U I)
  let e := P.liftCompιIso ((NeemanFiniteSupportM4.AffineIsSupportedIdeal _ I).ι ⋙
    derivedAssociated U) (fun M => ⟨dqc_derivedAssociated U hq M.obj,
      (cohomologySupportedOn_iff U h07TY I M.obj).2 M.property⟩)
  let hff : (supportedComparison U hq h07TY I ⋙ P.ι).FullyFaithful :=
    (((NeemanFiniteSupportM4.AffineIsSupportedIdeal _ I).fullyFaithfulι.comp
      (fullyFaithful_derivedAssociated U hq h06Z0))).ofIso e.symm
  let hF : (supportedComparison U hq h07TY I).FullyFaithful := hff.ofCompFaithful
  have := hF.full
  have := hF.faithful
  have : (supportedComparison U hq h07TY I).EssSurj := ⟨fun Y => by
    have hY : P Y.obj := Y.property
    rw [show P = _ from dqcSupported_eq_map U hq h06Z0 h07TY I] at hY
    obtain ⟨M, hM, ⟨f⟩⟩ := hY
    exact ⟨⟨M, hM⟩, ⟨P.fullyFaithfulι.preimageIso f⟩⟩⟩
  exact { }

include hq h06Z0 h07TY in
/-- **Weak approximability of `D_{qc,V(I)}(h_U)`**, for any triangulated structure instance
(the instance is a proposition, and one exists: `isTriangulated_dqcSupported`), from the module
model along the triangulated equivalence `supportedComparison`. -/
theorem satisfiesPaperWA_dqcSupported (hI : I.FG)
    [(DqcSupported (space U) (zeroLocusPoints U I)).IsTriangulated] :
    PaperM2.SatisfiesPaperWA (DqcSupported (space U) (zeroLocusPoints U I)).FullSubcategory := by
  have := isEquivalence_supportedComparison U hq h06Z0 h07TY I
  letI : (supportedComparison U hq h07TY I).CommShift ℤ :=
    ObjectProperty.commShiftLift (DqcSupported (space U) (zeroLocusPoints U I)) _ _
  have : (supportedComparison U hq h07TY I).IsTriangulated :=
    ObjectProperty.isTriangulated_lift (DqcSupported (space U) (zeroLocusPoints U I)) _ _
  exact SchemeTwoOpenM3.satisfiesPaperWA_of_equivalence (supportedComparison U hq h07TY I)
    (NeemanAffineSupport.satisfiesPaperWA_of_fg _ I hI)

end Comparison

end Main

/-- **LP26 Corollary 1.2, affine base case** (`cor:weak_approx_spaces`), over AxiomMath's
algebraic spaces.  Let `U` be an object of the big fppf site over `S` with affine underlying
scheme, `R = Γ(U, 𝒪)`, so that `h_U = yoneda.obj U` is the algebraic space `Spec R`, and let
`I ⊆ R` be a finitely generated ideal.  Then `D_{qc,V(I)}(Spec R)`
(`DqcSupported (space U) (zeroLocusPoints U I)`: the objects of `D_qc(𝒪_{h_U})` whose
cohomology sheaves are supported on `|V(I)|`) is a triangulated subcategory of
`D(𝒪_{h_U})`, and is weakly approximable (LP26 Definition 2.1, `def:weak_approx`).

Conditional only on the tagged AxiomMath inputs `Tag06Z0ExactInput`, `Tag06Z0QcohInput`,
`Tag06Z0Input` (Stacks 06Z0) and `Tag07TYInput` (Stacks 04KA, 07TY). -/
theorem lp26_cor_1_2_affine (hex : Tag06Z0ExactInput B S hS) (hq : Tag06Z0QcohInput B S hS)
    (h06Z0 : Tag06Z0Input B S hS) (h07TY : Tag07TYInput B S hS)
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) (hI : I.FG) :
    ∃ h : (DqcSupported (space U) (zeroLocusPoints U I)).IsTriangulated,
      letI := h
      PaperM2.SatisfiesPaperWA (DqcSupported (space U) (zeroLocusPoints U I)).FullSubcategory := by
  haveI := hex U
  haveI := isTriangulated_dqcSupported U hq h06Z0 h07TY I
  exact ⟨inferInstance, satisfiesPaperWA_dqcSupported U hq h06Z0 h07TY I hI⟩

/-! ### Non-vacuity

CLAUDE.md, verification step 5.  The hypotheses of `lp26_cor_1_2_affine` are a big fppf site
`B`, a base `S ∈ B`, an object `U` with affine underlying scheme, a finitely generated ideal,
and the tagged inputs.  For `S = Spec ℤ` (in some big fppf site, by `Tag021RInput`), `U = S`
itself and `I = (p)`, all of them hold, and the headline applies.  The tagged inputs are
AxiomMath theorems, discharged in `SpacesVerified`. -/

/-- The base `Spec ℤ`, as an object of the big fppf site over itself. -/
abbrev intObject (B : BigFppfSite.{0}) (hS : B.Contains (Spec (.of ℤ))) :
    BigFppfOver B (Spec (.of ℤ)) hS :=
  Over.mk (𝟙 (B.obj hS))

instance (B : BigFppfSite.{0}) (hS : B.Contains (Spec (.of ℤ))) :
    IsAffine ((BigFppfOver.toScheme B _ hS).obj (intObject B hS)) :=
  inferInstanceAs (IsAffine (Spec (.of ℤ)))

/-- **Non-vacuity of LP26 Corollary 1.2, affine base case**: `A = ℤ`, `I = (p)`.  Some big fppf
site contains `Spec ℤ` (`Tag021RInput`); over it, `U = Spec ℤ` has affine underlying scheme and
`(p)` is finitely generated, so the headline applies. -/
theorem lp26_cor_1_2_affine_int (h021R : Tag021RInput.{0}) (p : ℕ) :
    ∃ (B : BigFppfSite.{0}) (hS : B.Contains (Spec (.of ℤ))),
      ∀ (_hex : Tag06Z0ExactInput B _ hS) (_hq : Tag06Z0QcohInput B _ hS)
        (_h06Z0 : Tag06Z0Input B _ hS) (_h07TY : Tag07TYInput B _ hS),
        ∃ h : (DqcSupported (space (intObject B hS)) (zeroLocusPoints (intObject B hS)
            (Ideal.span {(p : Γ((BigFppfOver.toScheme B _ hS).obj (intObject B hS), ⊤))}))).IsTriangulated,
          letI := h
          PaperM2.SatisfiesPaperWA (DqcSupported (space (intObject B hS)) (zeroLocusPoints
            (intObject B hS) (Ideal.span
              {(p : Γ((BigFppfOver.toScheme B _ hS).obj (intObject B hS), ⊤))}))).FullSubcategory := by
  obtain ⟨B, hS⟩ := h021R (Spec (.of ℤ))
  exact ⟨B, hS, fun hex hq h06Z0 h07TY =>
    lp26_cor_1_2_affine hex hq h06Z0 h07TY _ _ ⟨{(p : Γ((BigFppfOver.toScheme B _ hS).obj
      (intObject B hS), ⊤))}, by simp⟩⟩

end RelativeFM.Spaces.Affine
