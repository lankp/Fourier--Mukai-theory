/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.InternalHom.Pullback
import Spaces.InternalHom.TensorHom
import Spaces.NonVacuity
import Spaces.Supported.CompactGeneration

/-!
# Non-vacuity for GL26 Lemmas 2.10, 2.11 and 2.16 over algebraic spaces

CLAUDE.md, verification step 5: every hypothesis-carrying notion of the statements of
`Spaces/InternalHom/` is satisfiable.

* **Coherators** (`adj : i ⊣ Q`, data of Lemmas 2.11 and 2.16): one exists on every quasi-compact
  quasi-separated space (`coheratorAdj`, Stacks 0CR4), for instance on the affine space
  `h_{T₀}` (`exists_coherator_affine`, through `Supported.nonVacuity_affine_univ`).
* **Right adjoints of `- ⊗^L E` on `D_qc(X)`** (the `adjR` of Lemma 2.11): `qcHom adj E` is one
  (`tensorQcRightQcHomAdj`).
* **`Perf`, `IsPseudoCoherent`, `D_qc`, `D^+_qc`**: the zero object has all four
  (`Perf_of_isZero`, `IsPseudoCoherent_of_isZero`, `Dqc_of_isZero`, `DplusQc_of_isZero`).
* **Invertibility of `ρ_f`** (hypothesis of `lemma_2_16_pseudoCoherent_of_isIso`): it holds at a
  perfect, for instance zero, first argument (`Tag08I3PerfectInput`).

The theorems below exhibit every hypothesis of `lemma_2_11_of_isPseudoCoherent`, `lemma_2_10`,
`lemma_2_16_perfect_qcqs` and `lemma_2_16_pseudoCoherent_of_isIso` at once.  Inputs used: the
tagged inputs of the statements themselves, and `AffineQuasiSeparatedInput` (affine schemes are
quasi-separated, `Spaces/Supported/Inputs.lean`) for the affine witness.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space Opposite
open ZeroObject

namespace RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS}

/-- The zero object of `D(X)` lies in `D^+_qc(X)`. -/
theorem DplusQc_of_isZero {E : D B S hS X} (hE : IsZero E) : DplusQc X E :=
  ⟨DerivedCategoryB.isBoundedBelow_of_isZero hE, Dqc_of_isZero hE⟩

/-- The zero object of `D_qc(X)`. -/
def zeroQc (X : AlgebraicSpaces B S hS) : (Dqc X).FullSubcategory :=
  ⟨0, Dqc_of_isZero (isZero_zero _)⟩

/-- **A coherator exists on the affine space `h_{T₀}`** (quasi-compact and quasi-separated),
from Stacks 0CR4 (`Tag0CR4Input`). -/
theorem exists_coherator_affine (h0CR4 : Tag0CR4Input B S hS)
    (hqs : Supported.AffineQuasiSeparatedInput B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ∃ Q : D B S hS (Supported.representedSpace T₀) ⥤
        (Dqc (Supported.representedSpace T₀)).FullSubcategory,
      Nonempty ((Dqc (Supported.representedSpace T₀)).ι ⊣ Q) := by
  obtain ⟨hqc, hqs', -, -⟩ := Supported.nonVacuity_affine_univ hqs hZ T₀ hT₀
  exact ⟨_, ⟨coheratorAdj h0CR4 hZ _ hqc hqs'⟩⟩

/-- **Non-vacuity of Lemma 2.11** (`lem:internal_hom`) with its last sentence: on every space `X`
with a coherator, `E = L = 0` meets every hypothesis of `lemma_2_11_of_isPseudoCoherent`, with
`R = qcHom adj E`. -/
theorem lemma_2_11_nonVacuity (h : Tag08F5Input B S hS) (h0A8A : Tag0A8AInput B S hS)
    {Q : D B S hS X ⥤ (Dqc X).FullSubcategory} (adj : (Dqc X).ι ⊣ Q) :
    Nonempty (tensorQcRight h (zeroQc X) ⊣ qcHom adj (zeroQc X)) ∧
      IsPseudoCoherent X (zeroQc X).obj ∧ DplusQc X (zeroQc X).obj ∧
      Nonempty ((Dqc X).ι.obj ((qcHom adj (zeroQc X)).obj (zeroQc X)) ≅
        sheafHomObj (zeroQc X).obj (zeroQc X).obj) :=
  ⟨⟨tensorQcRightQcHomAdj h adj _⟩, IsPseudoCoherent_of_isZero (isZero_zero _),
    DplusQc_of_isZero (isZero_zero _),
    ⟨lemma_2_11_of_isPseudoCoherent h h0A8A adj _ (tensorQcRightQcHomAdj h adj _)
      (IsPseudoCoherent_of_isZero (isZero_zero _)) _ (DplusQc_of_isZero (isZero_zero _))⟩⟩

/-- **Non-vacuity of Lemma 2.10** (`lem:rhom_tensor_morphism`): the zero object is perfect, so
`lemma_2_10` applies on every algebraic space. -/
theorem lemma_2_10_nonVacuity (X : AlgebraicSpaces B S hS) (M : D B S hS X) :
    Perf X (0 : D B S hS X) ∧
      Nonempty ((sheafHom X).obj (op M) ⋙ (tensor X).obj 0 ≅
        (sheafHom X).obj (op (sheafHomObj 0 M))) :=
  ⟨Perf_of_isZero (isZero_zero _), ⟨lemma_2_10 0 M (Perf_of_isZero (isZero_zero _))⟩⟩

/-- **Non-vacuity of Lemma 2.16 (1)** (`lem:gortz_wedhorn_internal_hom1`) in GL26's setting: on the
affine (quasi-compact, quasi-separated) space `X = h_{T₀}`, with `f = 𝟙`, `E = 0` perfect and
`G = 0`, every hypothesis of `lemma_2_16_perfect_qcqs` holds and the canonical morphism is an
isomorphism. -/
theorem lemma_2_16_perfect_nonVacuity (h4 : Tag08F4Input B S hS) (h0A8A : Tag0A8AInput B S hS)
    (h08I3 : Tag08I3PerfectInput B S hS) (h0CR4 : Tag0CR4Input B S hS)
    (hqs : Supported.AffineQuasiSeparatedInput B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (T₀ : BigFppfOver B S hS) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ∃ (hqc : IsQuasiCompactSpace B S hS (Supported.representedSpace T₀).1)
      (hqs' : IsAbsolutelyQuasiSeparated B S hS hZ (Supported.representedSpace T₀).1),
      Perf (Supported.representedSpace T₀) (zeroQc _).obj ∧
        IsIso (qcHomPullbackMap h4 (𝟙 _) (coheratorAdj h0CR4 hZ _ hqc hqs')
          (coheratorAdj h0CR4 hZ _ hqc hqs') (zeroQc _) (zeroQc _)) := by
  obtain ⟨hqc, hqs', -, -⟩ := Supported.nonVacuity_affine_univ hqs hZ T₀ hT₀
  exact ⟨hqc, hqs', Perf_of_isZero (isZero_zero _),
    lemma_2_16_perfect_qcqs h4 h0A8A h08I3 h0CR4 hZ _ hqc hqs' hqc hqs' _ _
      (Perf_of_isZero (isZero_zero _))⟩

/-- **Non-vacuity of the conditional case (2)** (`lemma_2_16_pseudoCoherent_of_isIso`): for every
`f` and coherators, `E = G = 0` is pseudo-coherent, resp. in `D^+_qc`, and `ρ_f` is invertible at
`(0, 0)` (`0` is perfect, `Tag08I3PerfectInput`). -/
theorem lemma_2_16_pseudoCoherent_nonVacuity (h08I3 : Tag08I3PerfectInput B S hS) (f : Y ⟶ X) :
    IsPseudoCoherent X (zeroQc X).obj ∧ DplusQc X (zeroQc X).obj ∧
      IsIso (sheafHomPullbackMap f (zeroQc X).obj (zeroQc X).obj) :=
  ⟨IsPseudoCoherent_of_isZero (isZero_zero _), DplusQc_of_isZero (isZero_zero _),
    h08I3 f _ (Perf_of_isZero (isZero_zero _)) _⟩

end RelativeFM.Spaces
