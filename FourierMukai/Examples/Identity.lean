/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Prelim.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# A non-vacuous example: the identity trinatural transformation

To check that the definitions of `FourierMukai/Prelim/Triangulated.lean` are
instantiable, we build the identity trinatural transformation of the identity
functor on the derived category of an abelian category, and apply Lemma 2.3(2).

`DerivedCategory A` is Mathlib's derived category of an abelian category `A`
(`Mathlib.Algebra.Homology.DerivedCategory.Basic`); it is pretriangulated and
triangulated (`instance : IsTriangulated (DerivedCategory A)`).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory Limits Pretriangulated

namespace Trinatural

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The identity trinatural transformation of the identity functor is the general
`Trinatural.id` of `FourierMukai/Prelim/Triangulated.lean`. -/
example : Trinatural (𝟭 C) (𝟭 C) := Trinatural.id (𝟭 C)

/-- Lemma 2.3(2) applied to the identity transformation: the objects at which the
identity of the identity functor is an isomorphism form a triangulated
subcategory of `C`. -/
example : (Trinatural.id (𝟭 C)).isoLocus.IsTriangulated := inferInstance

/-- ... and this subcategory is everything. -/
example (X : C) : (Trinatural.id (𝟭 C)).isoLocus X := by
  change IsIso (𝟙 X)
  infer_instance

end Trinatural

end RelativeFM
