/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Spaces
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage

/-!
# Discharge of the tagged AxiomMath inputs of `Spaces`

Each tagged input of `Spaces/AxiomMathInputs.lean` is proved here by the AxiomMath/Stacks
declaration it names (commit `f56a316`), so nothing in the algebraic-space layer is
assumed: the `D_qc`-valued functors and the triangulated structure of `D_qc` hold
unconditionally.

| input | Stacks | proved by |
|---|---|---|
| `Tag06UQInput` | 06UQ | `AlgebraicGeometry.Space.isTriangulated_quasicoherentDerivedCategory` |
| `Tag08F4Input` | 08F4 | `AlgebraicGeometry.Space.derivedQuasicoherent_smallEtaleDerivedModulePullback` |
| `Tag08F5Input` | 08F5 | `AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedTensor` |
| `Tag08FAInput` | 08FA (1) | `AlgebraicGeometry.Space.qcohDerived_derivedModulePushforward_obj` |

Building this file compiles the AxiomMath theorem modules above (part of the full
AxiomMath build; see README, "Building").
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.SpacesVerified

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06UQ**, proved: `D_qc(𝒪_F)` is a triangulated subcategory of `D(𝒪_F)`. -/
theorem tag06UQ : Spaces.Tag06UQInput B S hS := fun F hF =>
  isTriangulated_quasicoherentDerivedCategory B S hS F hF

/-- **Stacks 08F4**, proved: `Lf^*` preserves `D_qc`. -/
theorem tag08F4 : Spaces.Tag08F4Input B S hS := fun f E hE =>
  derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS f E hE

/-- **Stacks 08F5**, proved: `D_qc` is closed under `⊗^L`. -/
theorem tag08F5 : Spaces.Tag08F5Input B S hS := fun X K L hK hL =>
  qcohDerived_smallEtaleDerivedTensor X K L hK hL

/-- **Stacks 08FA (1)**, proved: `Rf_*` preserves `D_qc` for `f` quasi-compact and
quasi-separated. -/
theorem tag08FA : Spaces.Tag08FAInput B S hS := fun f hfqc hfqs E hE =>
  qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs E hE

variable {B S hS}

/-- `D_qc(X)` is a triangulated subcategory of `D(X)`, unconditionally. -/
theorem Dqc_isTriangulated (X : AlgebraicSpaces B S hS) : (Spaces.Dqc X).IsTriangulated :=
  Spaces.Dqc_isTriangulated (tag06UQ B S hS) X

/-- `Lf^* : D_qc(X) ⥤ D_qc(Y)`, unconditionally. -/
abbrev pullQc {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    (Spaces.Dqc X).FullSubcategory ⥤ (Spaces.Dqc Y).FullSubcategory :=
  Spaces.pullQc (tag08F4 B S hS) f

/-- `E ⊗^L - : D_qc(X) ⥤ D_qc(X)`, unconditionally. -/
abbrev tensorQc {X : AlgebraicSpaces B S hS} (E : (Spaces.Dqc X).FullSubcategory) :
    (Spaces.Dqc X).FullSubcategory ⥤ (Spaces.Dqc X).FullSubcategory :=
  Spaces.tensorQc (tag08F5 B S hS) E

/-- `Rf_* : D_qc(X) ⥤ D_qc(Y)` for `f` quasi-compact and quasi-separated, unconditionally. -/
abbrev pushQc {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    (Spaces.Dqc X).FullSubcategory ⥤ (Spaces.Dqc Y).FullSubcategory :=
  Spaces.pushQc (tag08FA B S hS) f hfqc hfqs

end RelativeFM.SpacesVerified

#print axioms RelativeFM.SpacesVerified.tag06UQ
#print axioms RelativeFM.SpacesVerified.tag08F4
#print axioms RelativeFM.SpacesVerified.tag08F5
#print axioms RelativeFM.SpacesVerified.tag08FA
#print axioms RelativeFM.SpacesVerified.Dqc_isTriangulated
