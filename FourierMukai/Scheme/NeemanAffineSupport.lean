/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.RegularCompactEndpoints
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Neeman's weak approximability for affine schemes with support (module model)

**LP26 Corollary 1.2, affine base case** (`cor:weak_approx_spaces`) = Neeman,
*Acta Math.* 233 (2024), Theorem 3.2(iv) for `Spec A` and `Z = V(I)`, `I` finitely
generated.  LP26 Corollary 1.2 combines this case with the induction principle for
algebraic spaces; this file proves the base case, **with no hypothesis and no named
input of any kind**.

Model.  Stated in the module model of the tree: `AffineD A = D(A-Mod)` (standard
localization), and its ideal-supported full subcategory
`AffineDZIdeal A I = {X | every H^n(X) is I-power torsion}` (`NeemanFiniteSupportM4`),
which for `I = (f₁,…,fₙ)` is `D_{V(I)}(A-Mod)`.  Weak approximability is the paper's
`PaperM2.SatisfiesPaperWA` (LP26 Definition 2.1, `def:weak_approx`), witnessed by the
degree-one Koszul object `K(f₁,…,fₙ)`, the standard `t`-structure and a bound `N`.

* `satisfiesPaperWA_idealSupported`: every commutative ring `A`, every finite list
  `fs`;
* `satisfiesPaperWA_of_fg`: every finitely generated ideal `I`.

Difference from the paper.  The paper's category is `D_{qc,Z}(Spec A)` (sheaves on
the scheme, or on the small étale site of the algebraic space `Spec A`); the
transport from `D_{V(I)}(A-Mod)` to AxiomMath's `D_qc,Z(Spec A)` is a later task
(`wave5/neeman-affine-transport`).  The scheme forms already in the tree
(`RegularCompact.neemanSupported_of_finiteIdeal`, `..._of_qc_closedComplement`,
`..._of_isAffine`) still carry the named comparison
`AffineSupportedSchemeBaseM1.AffineSupportedSchemeComparisonInput`, which is not
discharged here.

Ingredients, all proved: the Koszul objects and their support (`FiniteKoszulM1`),
the power envelope and zero detection (`KoszulFiniteInputs`, via the chain-level
`KoszulConeSwap.coneSwapIso`), supported direct sums and compactness
(`KoszulSupportAdjoint`), compactness of `A[0]` (`RegularCompact.ringObject_isCompactAb`)
and the free-cover approximation (`IdealNeemanM1`).
-/

@[expose] public section

namespace RelativeFM.NeemanAffineSupport

open RelativeFM RelativeWeakApprox
open RelativeFM.NeemanFiniteSupportM4 RelativeFM.FiniteKoszulM1

universe u

/-- **LP26 Corollary 1.2, affine base case** (`cor:weak_approx_spaces`) = Neeman 2024,
Theorem 3.2(iv) for `Spec A`, `Z = V(I)`, here for `I = (f₁,…,fₙ)` given by a finite
list.  Stated in the module model: `D_{V(fs)}(A-Mod)`, the ideal-supported full
subcategory `AffineDZIdeal A (functionIdeal A fs)` of `AffineD A = D(A-Mod)`,
satisfies the paper's weak approximability (LP26 Definition 2.1, `def:weak_approx`).
No hypothesis beyond `A` and `fs`. -/
theorem satisfiesPaperWA_idealSupported (A : Type u) [CommRing A] (fs : List A) :
    PaperM2.SatisfiesPaperWA (AffineDZIdeal A (functionIdeal A fs)) :=
  IdealNeemanM1.satisfiesPaperWA_idealSupported A fs (RegularCompact.ringObject_isCompactAb A)

/-- **LP26 Corollary 1.2, affine base case** (`cor:weak_approx_spaces`) = Neeman 2024,
Theorem 3.2(iv) for `Spec A`, `Z = V(I)`, `I` finitely generated.  Module model:
`AffineDZIdeal A I ⊆ D(A-Mod)` satisfies the paper's weak approximability.  No
hypothesis beyond `A`, `I` and `I.FG`. -/
theorem satisfiesPaperWA_of_fg (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    PaperM2.SatisfiesPaperWA (AffineDZIdeal A I) := by
  classical
  obtain ⟨s, rfl⟩ := hI
  have h : functionIdeal A s.toList = Ideal.span (s : Set A) := by
    rw [AffineSupportedSchemeBaseM1.functionIdeal_eq_span_toFinset, Finset.toList_toFinset]
  rw [← h]
  exact satisfiesPaperWA_idealSupported A s.toList

/-! ### Non-vacuity

The headline theorems have no hypothesis; the examples below instantiate them for a
principal and for a non-principal closed subset. -/

/-- `Z = V(2) ⊆ Spec ℤ`. -/
example : PaperM2.SatisfiesPaperWA (AffineDZIdeal ℤ (functionIdeal ℤ [2])) :=
  satisfiesPaperWA_idealSupported ℤ [2]

/-- `Z = V(x, y) ⊆ Spec ℤ[x, y]` (the ideal `(x, y)` is not principal). -/
example : PaperM2.SatisfiesPaperWA (AffineDZIdeal (MvPolynomial (Fin 2) ℤ)
    (functionIdeal (MvPolynomial (Fin 2) ℤ) [MvPolynomial.X 0, MvPolynomial.X 1])) :=
  satisfiesPaperWA_idealSupported _ _

/-- The finitely generated form, for the same non-principal ideal. -/
example : PaperM2.SatisfiesPaperWA (AffineDZIdeal (MvPolynomial (Fin 2) ℤ)
    (Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1})) :=
  satisfiesPaperWA_of_fg _ _ ⟨{MvPolynomial.X 0, MvPolynomial.X 1}, by simp⟩

end RelativeFM.NeemanAffineSupport

#print axioms RelativeFM.NeemanAffineSupport.satisfiesPaperWA_idealSupported
#print axioms RelativeFM.NeemanAffineSupport.satisfiesPaperWA_of_fg
