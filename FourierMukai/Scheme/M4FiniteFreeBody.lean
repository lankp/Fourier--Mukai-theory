import FourierMukai.Scheme.CompactToPerfect
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

@[expose] public section

namespace RelativeFM.Stacks07LT.M4

open CategoryTheory CategoryTheory.Limits Module
open scoped ZeroObject

universe uA uM uN uI

noncomputable section

variable {A : Type uA} [CommRing A]
variable {M : Type uM} [AddCommGroup M] [Module A M]
variable {N : Type uN} [AddCommGroup N] [Module A N]
variable {ι : Type uI}

/-- The basis indices not belonging to a finite set. -/
abbrev Tail (s : Finset ι) := {i // i ∉ s}

/-- Projection onto the basis coordinates outside a finite set. -/
def tailMap (b : Basis ι A N) (s : Finset ι) : N →ₗ[A] (Tail s →₀ A) := by
  classical
  exact (Finsupp.lsubtypeDomain (R := A) (M := A) {i | i ∉ s}).comp
    b.repr.toLinearMap

@[simp]
lemma tailMap_apply (b : Basis ι A N) (s : Finset ι) (x : N) (i : Tail s) :
    tailMap b s x i = b.repr x i := rfl

lemma tailMap_surjective (b : Basis ι A N) (s : Finset ι) :
    Function.Surjective (tailMap b s) := by
  classical
  intro f
  refine ⟨b.repr.symm f.extendDomain, ?_⟩
  ext i
  simp [tailMap_apply, Finsupp.extendDomain_apply, i.property]

/-- A linear map out of a finitely generated module has zero coordinates outside
some finite set of basis indices. -/
lemma exists_finset_repr_apply_eq_zero [Module.Finite A M]
    (b : Basis ι A N) (f : M →ₗ[A] N) :
    ∃ s : Finset ι, ∀ (x : M) (i : ι), i ∉ s → b.repr (f x) i = 0 := by
  classical
  obtain ⟨t, ht⟩ := Module.finite_def.mp (inferInstance : Module.Finite A M)
  refine ⟨t.biUnion fun x => (b.repr (f x)).support, fun x i hi => ?_⟩
  have hx : x ∈ Submodule.span A (t : Set M) := by rw [ht]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
      apply Finsupp.notMem_support_iff.mp
      intro hiy
      exact hi (Finset.mem_biUnion.mpr ⟨y, hy, hiy⟩)
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul a y _ hy => simp [hy]

/-- Consequently, the projection away from a suitable finite basis set kills a
map with finitely generated source. -/
lemma exists_finset_tailMap_comp_eq_zero [Module.Finite A M]
    (b : Basis ι A N) (f : M →ₗ[A] N) :
    ∃ s : Finset ι, (tailMap b s).comp f = 0 := by
  obtain ⟨s, hs⟩ := exists_finset_repr_apply_eq_zero b f
  refine ⟨s, ?_⟩
  ext x i
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.zero_apply,
    tailMap_apply] using hs x i i.property

/-- The kernel of `tailMap` is canonically the submodule of coordinates
supported on the finite exceptional set. -/
def kernelTailMapEquivSupported (b : Basis ι A N) (s : Finset ι) :
    LinearMap.ker (tailMap b s) ≃ₗ[A]
      Finsupp.supported A A (s : Set ι) where
  toFun x := ⟨b.repr x.1, by
    rw [Finsupp.mem_supported']
    intro i hi
    have hi' : i ∉ s := by simpa using hi
    have hx := LinearMap.mem_ker.mp x.property
    simpa only [tailMap_apply, Finsupp.zero_apply] using
      congrArg (fun f : Tail s →₀ A => f ⟨i, hi'⟩) hx⟩
  invFun y := ⟨b.repr.symm y.1, by
    rw [LinearMap.mem_ker]
    ext i
    simp only [tailMap_apply, Finsupp.zero_apply, LinearEquiv.coe_coe,
      b.repr.apply_symm_apply]
    exact (Finsupp.mem_supported' _ _).mp y.property i (by simpa using i.property)⟩
  left_inv x := by
    apply Subtype.ext
    exact b.repr.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact b.repr.apply_symm_apply y.1
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

/-- The kernel is a finite free module with basis indexed by `s`. -/
def kernelTailMapEquivFinsupp (b : Basis ι A N) (s : Finset ι) :
    LinearMap.ker (tailMap b s) ≃ₗ[A] (s →₀ A) :=
  kernelTailMapEquivSupported b s ≪≫ₗ
    (Finsupp.supportedEquivFinsupp (R := A) (M := A) (s : Set ι))

lemma moduleFinite_kernelTailMap (b : Basis ι A N) (s : Finset ι) :
    Module.Finite A (LinearMap.ker (tailMap b s)) := by
  letI : Finite s := Finite.of_fintype s
  exact Module.Finite.equiv (kernelTailMapEquivFinsupp b s).symm

lemma moduleFree_kernelTailMap (b : Basis ι A N) (s : Finset ι) :
    Module.Free A (LinearMap.ker (tailMap b s)) := by
  exact Module.Free.of_equiv (kernelTailMapEquivFinsupp b s).symm

end
end RelativeFM.Stacks07LT.M4

#print axioms RelativeFM.Stacks07LT.M4.tailMap_surjective
#print axioms RelativeFM.Stacks07LT.M4.exists_finset_tailMap_comp_eq_zero
#print axioms RelativeFM.Stacks07LT.M4.kernelTailMapEquivFinsupp
#print axioms RelativeFM.Stacks07LT.M4.moduleFinite_kernelTailMap
#print axioms RelativeFM.Stacks07LT.M4.moduleFree_kernelTailMap
