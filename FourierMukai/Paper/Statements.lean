/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Paper.DerivedSetup
import FourierMukai.Scheme.DiagonalIdentity

/-!
# Statements of the main results of *Relative Fourier--Mukai theory for algebraic spaces*

This file collects the numbered results of the paper as Lean theorems about the
abstract interface of `FourierMukai/Paper/DerivedSetup.lean`.

**All but one theorem in this file is stated, not proved.**  `lemma_2_25` is
proved from the three inputs that the paper's own proof of it uses
(`DiagonalIdentityData`, `FourierMukai/Scheme/DiagonalIdentity.lean`); the other
nine are specifications.  Their proofs are the content of the 102-page paper;
they depend on Grothendieck duality for algebraic spaces, Nagata
compactification, weak approximability of `D_qc`, and the theory of relatively
perfect complexes developed in Parts 1 and 2 of the paper.  None of that is
available in Lean today; see `results/REPORT.md` for a detailed inventory.

Each statement records in its docstring

* the number of the result in the paper,
* the Stacks Project tags (and other references) on which the paper's proof rests,
* which part of the interface the statement uses.

The nine remaining `sorry`s are therefore *specifications*, not gaps in an
otherwise complete proof: they are the formalization targets.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory

universe u v

/-! ### Relative and quasi-perfect complexes (Part 1) -/

section Perfectness

variable {DX DY : Type u} [Category.{v} DX] [Category.{v} DY]

/-- **Theorem 1.3** (paper) = Theorem 6.2 + Proposition 6.8 (`thm:stacky_all_coincide`).

For a proper morphism `f : Y ⟶ X` of Noetherian algebraic spaces and a
pseudocoherent `E ∈ D_qc(Y)`, the following are equivalent:

1. `E` is `f`-perfect;
2. `E ⊗^L Lf^*A ∈ D^b_coh(Y)` for all `A ∈ D^b_coh(X)`;
3. `E` is `f`-quasi-perfect.

The paper's proof uses the characterisation of perfect complexes through their
derived fibres (Proposition 3.12) and the boundedness criterion via compact
generators (`lem:boundedness_via_coaisle`, Stacks tags 0GFH and 0GFI). -/
theorem theorem_1_3 (M : MorphismContext DX DY) (SX : Subcats DX) (SY : Subcats DY)
    (hproper : M.IsProper) (E : DY) (hE : SY.Dcoh E) :
    (M.IsRelativelyPerfect SX SY E ↔
      (∀ A : DX, SX.Dcoh A →
        SY.Dcoh ((M.tensorRight E).obj (M.pull.obj A)))) ∧
      ((∀ A : DX, SX.Dcoh A →
        SY.Dcoh ((M.tensorRight E).obj (M.pull.obj A))) ↔
        M.IsQuasiPerfect SX SY E) := by
  sorry

end Perfectness

/-! ### Base change for relative perfectness (Corollary 6.18) -/

/-- A base-change square for relative perfectness: `L(t_Y)^* Lf^* ≅ L(f')^* L(t_X)^*`. -/
structure PerfectnessSquare {DX DY DX' DY' : Type u}
    [Category.{v} DX] [Category.{v} DY] [Category.{v} DX'] [Category.{v} DY']
    (M : MorphismContext DX DY) (M' : MorphismContext DX' DY') where
  /-- `L(t_X)^* : D_qc(X) ⟶ D_qc(X')`. -/
  pullX : DX ⥤ DX'
  /-- `L(t_Y)^* : D_qc(Y) ⟶ D_qc(Y')`. -/
  pullY : DY ⥤ DY'
  /-- The base-change isomorphism `L(t_Y)^* Lf^* ≅ L(f')^* L(t_X)^*`. -/
  comm : pullX ⋙ M'.pull ≅ M.pull ⋙ pullY

/-- **Corollary 6.18** (`cor:noetherian_base_change_for_relative_perfectness`), easy
direction: if `K` is relatively perfect over `Y₁` (resp. `Y₂`), then its derived
pullback along an arbitrary morphism of Noetherian algebraic spaces is relatively
perfect over `Y₁ ×_S T` (resp. `Y₂ ×_S T`).  The converse directions of Theorem
1.5 additionally need the closed-point criterion (Theorem 6.16) and a faithfully
flat cover; expressing "for every `t : T ⟶ S`" requires a category of base-change
data that the interface does not yet provide. -/
theorem corollary_6_18 {DX DY DX' DY' : Type u}
    [Category.{v} DX] [Category.{v} DY] [Category.{v} DX'] [Category.{v} DY']
    {M : MorphismContext DX DY} {M' : MorphismContext DX' DY'}
    (SX : Subcats DX) (SY : Subcats DY) (SX' : Subcats DX') (SY' : Subcats DY')
    (sq : PerfectnessSquare M M') (hflat : M.IsFlat) {E : DY}
    (hE : M.IsRelativelyPerfect SX SY E) :
    M'.IsRelativelyPerfect SX' SY' (sq.pullY.obj E) := by
  sorry

/-! ### The loci and their behaviour -/

variable (X : FMSetup.{u, v})

/-- **Theorem 12.3** (`thm:openness_for_equivalence_fullfaithful_dbcoh`).

Let `K ∈ D_qc(Y₁ ×_S Y₂)` be pseudocoherent and relatively perfect over each `Y_i`.
Then the set of `p ∈ |S|` at which the fibre transform `Φ_{L(t')^*K}` is an
equivalence (resp. fully faithful) is open.

The paper's proof (Section 12.1) expresses the failure of full faithfulness through
the support of the cone of `Φ_K ⊗ Φ_{K'} → 𝟙` and uses upper semicontinuity of the
support of a bounded pseudocoherent complex (Lemma 12.x, `lem:perfect_locus_open`,
Stacks tag 07TZ). -/
theorem theorem_12_3 (hX : X.IsProperFlat) {K : X.DP}
    (hK : X.IsBoundedPseudoCoherent K) (hrel₁ : True) (hrel₂ : True) :
    IsOpen (X.FM K) ∧ IsOpen (X.fm K) := by
  sorry

/-- **Theorem 1.2(1) / Theorem 12.9** (`thm:fm_locus_weak_approx`): for *arbitrary*
bounded pseudocoherent kernels (no relative perfectness), `FM(K)` is open.

The proof restricts to the open locus where `K` is relatively perfect over both
`Y_i` (Proposition 12.8) and then applies Theorem 12.3. -/
theorem theorem_1_2_open (hX : X.IsProperFlat) {K : X.DP}
    (hK : X.IsBoundedPseudoCoherent K) :
    IsOpen (X.FM K) := by
  sorry

/-- **Theorem 1.2(2) / Corollary 12.10** (`cor:deform`): `FM` and `fm` commute with
arbitrary Noetherian base change:
`t^{-1}(FM(K)) = FM(L(t')^*K)`. -/
theorem theorem_1_2_baseChange (hX : X.IsProperFlat) {K : X.DP}
    (hK : X.IsBoundedPseudoCoherent K) (t : BaseChange X) :
    t.ptMap ⁻¹' X.FM K = t.over.FM (t.pullKernel K) := by
  sorry

/-- **Lemma 12.2** (`lem:independence_for_rep_with_ff_or_eq`): if `K` is
pseudocoherent and relatively perfect over each `Y_i`, then being fully faithful
(resp. an equivalence) at `p` is independent of the chosen representative of `p`. -/
theorem lemma_12_2 (hX : X.IsProperFlat) {K : X.DP}
    (hK : X.IsBoundedPseudoCoherent K) (hrel₁ : True) (hrel₂ : True) :
    X.RepIndependent K := by
  sorry

/-! ### Fibrewise criteria (Part 2) -/

/-- Full faithfulness of `Φ_K` on `D^b_coh`, as a predicate. -/
def FullyFaithfulOnDcoh {D1 D2 DP : Type u} [Category.{v} D1] [Category.{v} D2]
    [Category.{v} DP] (C : FMContext D1 D2 DP) (K : DP) : Prop :=
  ∀ A B : D1, C.S1.Dcoh A → C.S1.Dcoh B →
    Function.Bijective (fun f : A ⟶ B => (C.transform K).map f)

/-- **Theorem 1.6 / Theorem 10.13** (`thm:descent_ascent`): if `K ∈ D^b_coh(Y₁ ×_S Y₂)`
is relatively perfect over each `Y_i`, then `Φ_K` is fully faithful (resp. an
equivalence) on `D^b_coh` if and only if the same holds for every closed point of
`|S|`.

The proof rests on Proposition 10.5 (`prop:pullbacks_is_a_morphism_of_adjoint_integral_transforms`),
i.e. on the calculus of mates (Section 7, [Kelly--Street 1974]) and on base change for
the relative dualising complexes (`lem:base_change_relative_dualizing_complex`). -/
theorem theorem_1_6 (hX : X.IsProperFlat) {K : X.DP}
    (hK : X.IsBoundedPseudoCoherent K) (hrel₁ : True) (hrel₂ : True) :
    FullyFaithfulOnDcoh X.ctx K ↔
      ∀ p : X.Base, (X.fibreTransform K p).Full ∧ (X.fibreTransform K p).Faithful := by
  sorry

/-! ### Functoriality of integral transforms (Section 2.5) -/

section Functoriality

variable {D DP : Type u} [Category.{v} D] [Category.{v} DP]
  (C : FMContext D D DP)

/-- **Lemma 2.25** (`lem:funct_on_kernel`): for `f : Y ⟶ S` proper flat,
`Φ_{RΔ_*O_Y} ≅ 𝟙`, where `Δ : Y ⟶ Y ×_S Y` is the diagonal.

GL26's proof uses only the projection formula (Stacks tag 08IN), the derived
tensor unit, and `f'_1 ∘ Δ = f'_2 ∘ Δ = 𝟙`.  Those are the fields of
`core : DiagonalIdentityData`; `unit` is `O_Y` and `C.diagonalKernel` is
`RΔ_*O_Y = core.diagonal.obj unit`.  The lemma is stated here over exactly those
inputs, and proved.

The *bare* rendering of this lemma -- the same conclusion quantified over a
`FMContext` with free `pull`, `push`, `tensorRight`, with `core` and the four
equalities dropped -- is **false**, as `FourierMukai/Paper/InterfaceAudit.lean`
shows, because such an interface does not tie the functors to any geometry.  That
is a defect of the interface, not of the lemma.  The scheme-layer form, with the
same inputs, is `RelativeFM.Noetherian.lemma_2_25Statement_proved`. -/
theorem lemma_2_25 (unit : D) (core : DiagonalIdentityData D DP unit)
    (hK : C.diagonalKernel = core.diagonal.obj unit)
    (hT : C.tensorRight = core.tensorRight)
    (hP : C.pull = core.pull) (hS : C.push = core.push) :
    Nonempty (C.transform C.diagonalKernel ≅ 𝟭 D) := by
  unfold FMContext.transform
  rw [hP, hS, hT, hK]
  exact core.identity_transform_isId

end Functoriality

section Convolution

variable {D1 D2 D3 DP12 DP23 DP13 : Type u}
  [Category.{v} D1] [Category.{v} D2] [Category.{v} D3]
  [Category.{v} DP12] [Category.{v} DP23] [Category.{v} DP13]

/-- **Lemma 2.26** (`lem:convolution`): `Φ_{K₂} ∘ Φ_{K₁} ≅ Φ_{K₂ ⋆ K₁}`, where
`⋆` is the convolution of kernels.  The proof is the same computation as in
[Huybrechts, *Fourier--Mukai transforms in algebraic geometry*, Proposition 5.10]
and uses the projection formula (Stacks tag 08IN) and tor-independent base change
(Stacks tag 08IR).

This is the **bare interface rendering**, kept only as a specification: `conv` is
an arbitrary function and the three contexts are unrelated, so the proposition
does not follow from its arguments, and `Scheme/ConvolutionCounterexample.lean`
refutes it (`bare_lemma_2_26_has_countermodel`).  The faithful form supplies the
derived triple-product cube, the projection formulas (08IN), monoidality and
pseudofunctoriality of pullback, and an invertible 08IR mate; see
`Scheme/AffineConvolution.lean` and
`RelativeFM.Convolution.NoetherianBridge.CorrectedConvolutionData`.  GL26's lemma
itself is not in question -- as with Lemma 2.25, the defect is the interface. -/
theorem lemma_2_26 (C12 : FMContext D1 D2 DP12) (C23 : FMContext D2 D3 DP23)
    (C13 : FMContext D1 D3 DP13) (conv : DP12 → DP23 → DP13) (K₁ : DP12) (K₂ : DP23) :
    Nonempty (C12.transform K₁ ⋙ C23.transform K₂ ≅ C13.transform (conv K₁ K₂)) := by
  sorry

end Convolution

/-! ### Elliptic fibrations (Section 11) -/

/-- **Theorem 1.7 / Theorem 11.4** (`thm:elliptic_fibration_autoequivalence`): if
`f : Y ⟶ X` is an elliptic `X`-fibration and `I_Δ` is the ideal sheaf of the
diagonal, then `Φ_{I_Δ}` induces an autoequivalence of `D^b_coh(Y)`.

The proof uses that `I_Δ` is relatively perfect over each projection (Lemma 11.1,
`lem:ideal_sheaf_relatively_perfect`) and that `Φ_{I_Δ}` is fully faithful and
essentially surjective by the theory of Fourier--Mukai transforms on genus-one
fibrations. -/
theorem theorem_1_7 (hX : X.IsProperFlat) (idealDiag : X.DP)
    (hell : True) :
    X.ctx.IsEquivalence idealDiag := by
  sorry

end RelativeFM
