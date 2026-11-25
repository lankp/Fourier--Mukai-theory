/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.AisleGenBrutal
import WeakApprox.StatementAudit
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Bounded complexes in a coproduct/extension closure -/

@[expose] public section

namespace RelativeFM.AisleGeneration.Bounded

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeFM.AisleGeneration.Brutal

universe w v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A strictly bounded complex belongs to `Coprod S` if all its degree-wise
single complexes do.  The induction removes the bottom term using a brutal,
degree-split short exact sequence. -/
theorem coprod_Q_obj_of_support (S : ObjectProperty (DerivedCategory C))
    (n : ℕ) (K : CochainComplex C ℤ) (a : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE (a + (n : ℤ))]
    (hterm : ∀ i : ℤ, a ≤ i → i ≤ a + (n : ℤ) →
      Coprod S (DerivedCategory.Q.obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) i).obj (K.X i)))) :
    Coprod S (DerivedCategory.Q.obj K) := by
  induction n generalizing K a with
  | zero =>
      letI : K.IsStrictlyLE a :=
        (CochainComplex.isStrictlyLE_iff K a).2 (fun i hi =>
          K.isZero_of_isStrictlyLE (a + ((0 : ℕ) : ℤ)) i (by simpa using hi))
      exact (Coprod S).prop_of_iso
        (DerivedCategory.Q.mapIso (isoSingleOfBounds K a)).symm
        (hterm a le_rfl (by simp))
  | succ n ih =>
      letI : K.IsStrictlyLE (a + 1 + (n : ℤ)) :=
        (CochainComplex.isStrictlyLE_iff K _).2 (fun i hi =>
          K.isZero_of_isStrictlyLE (a + ((n + 1 : ℕ) : ℤ)) i (by
            push_cast at hi ⊢
            omega))
      have hfirst : Coprod S (DerivedCategory.Q.obj (brutalGE K (a + 1))) := by
        apply ih (brutalGE K (a + 1)) (a + 1)
        intro i hai hib
        have hi : a + 1 ≤ i := hai
        let e := (HomologicalComplex.single C (ComplexShape.up ℤ) i).mapIso
          (brutalGEXIso K (a + 1) i hi)
        exact (Coprod S).prop_of_iso (DerivedCategory.Q.mapIso e).symm
          (hterm i (by omega) (by omega))
      exact Coprod.of_extension
        (DerivedCategory.triangleOfSES (brutalGEShortComplex_shortExact K a))
        (DerivedCategory.triangleOfSES_distinguished (brutalGEShortComplex_shortExact K a))
        hfirst (hterm a le_rfl (by omega))

end

end RelativeFM.AisleGeneration.Bounded

#print axioms RelativeFM.AisleGeneration.Bounded.coprod_Q_obj_of_support
