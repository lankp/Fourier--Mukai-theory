/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Paper.DerivedSetup
import FourierMukai.Scheme.DiagonalIdentity

/-!
# GL26 Lemma 2.25 over the abstract interface

GL26 Lemma 2.25 (`lem:funct_on_kernel`) over the abstract interface of
`FourierMukai/Paper/DerivedSetup.lean`, proved from the three inputs the paper's own proof
uses (`DiagonalIdentityData`, `FourierMukai/Scheme/DiagonalIdentity.lean`).

Until 26 November 2026 this file also held nine of GL26's results stated over the same
interface and left as `sorry` targets.  They were removed: the project keeps no unproven
claims, and that interface does not tie its functors to any geometry
(`Paper/InterfaceAudit.lean`), so its renderings were not the paper's statements (one,
Lemma 2.26, is refuted in `Scheme/ConvolutionCounterexample.lean`).  The results stay open
in `results/COVERAGE.md` and are being stated over algebraic spaces in `Spaces/`.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory

universe u v

/-! ### Relative and quasi-perfect complexes (Part 1) -/

section Perfectness

variable {DX DY : Type u} [Category.{v} DX] [Category.{v} DY]

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

/-! ### The loci and their behaviour -/

variable (X : FMSetup.{u, v})

/-! ### Fibrewise criteria (Part 2) -/

/-- Full faithfulness of `Φ_K` on `D^b_coh`, as a predicate. -/
def FullyFaithfulOnDcoh {D1 D2 DP : Type u} [Category.{v} D1] [Category.{v} D2]
    [Category.{v} DP] (C : FMContext D1 D2 DP) (K : DP) : Prop :=
  ∀ A B : D1, C.S1.Dcoh A → C.S1.Dcoh B →
    Function.Bijective (fun f : A ⟶ B => (C.transform K).map f)

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

end Convolution

/-! ### Elliptic fibrations (Section 11) -/

end RelativeFM
