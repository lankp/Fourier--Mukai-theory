/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Paper.DerivedSetup
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.TensorProduct.Maps
import FourierMukai.Scheme.Affine
import FourierMukai.Scheme.DiagonalIdentity

/-!
# GL26 Lemma 2.25 for affine schemes

GL26's Lemma 2.25 says `Φ_{RΔ_*O_Y} ≅ 𝟭`, and it is correct.
`FourierMukai/Paper/InterfaceAudit.lean` shows that its *bare* rendering over the
abstract `FMContext` is not a consequence of that interface: the functors there
are free fields, so a degenerate legal context refutes the bare rendering.  This
file supplies the missing data explicitly and proves the lemma in the affine
derived-module model, conditionally on that data.

* `affine_pullDiagonalUnderived` and `affine_diagonalPushUnderived` are the
  ordinary restriction/extension functors along the tensor inclusions and the
  multiplication, and both underived diagonal identities are proved.
* `DiagonalIdentityData` carries exactly the three derived inputs the proof uses:
  the projection formula (Stacks 08IN), the derived tensor unit, and the two
  diagonal retractions.  `identity_transform_isId` derives the identity
  transform from them.
* `AffineDiagonalContext.toFMContext` is an honest `FMContext` whose
  `diagonalKernel` is `C.core.diagonal.obj (affineUnit A)`, where the supplied
  `diagonal` is *intended* to model `RΔ_*`; and `affine_lemma_2_25` proves
  `Nonempty (transform diagonalKernel ≅ 𝟭)` for any supplied context over
  Noetherian rings.  Nothing here constructs that context from the rings: it is
  a conditional derived-module form of the lemma, not a ring-only construction of
  the geometric six-functor inputs.

Every remaining derived input (derived tensor, change of rings) is a documented
field with its source; there are no `True` placeholders.

Found by a member of the Ultramath run `smwuz1thx` (direction B3).
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory
open scoped TensorProduct

universe u v

noncomputable section

-- `AffineD` is `DerivedCategory (ModuleCat A)`, imported from
-- `FourierMukai/Scheme/Affine.lean` so that both affine files use the same
-- category; B1 must still supply its identification with `D_qc(Spec A)`.

/-- The derived module category modeling `D_qc(Spec (A ⊗[R] A))`. --
PROVISIONAL: pending B1's affine dictionary and its compatibility with pullback. -/
noncomputable abbrev AffineSelfProductD (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] : Type (u + 1) :=
  AffineD (A ⊗[R] A)

/-- The structure module in degree zero, `A[0]`, viewed in `AffineD A`. --
PROVISIONAL: under B1 this is the chosen representative of `O_(Spec A)`. -/
noncomputable def affineUnit (A : Type u) [CommRing A] : AffineD A := by
  letI : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _
  exact (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)

/-! ## The concrete ordinary change-of-rings functors -/

/-- Multiplication `A ⊗[R] A → A`, the ring map contravariantly modeling the
relative diagonal `Spec A → Spec (A ⊗[R] A)`. -/
noncomputable def affineDiagonalAlgHom (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] : A ⊗[R] A →ₐ[R] A :=
  Algebra.TensorProduct.lmul' R

/-- Ordinary extension of scalars along the first inclusion.  Its derived
version is the `pull` occurring in the affine integral transform. -/
noncomputable def affinePullUnderived (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] : ModuleCat A ⥤ ModuleCat (A ⊗[R] A) :=
  ModuleCat.extendScalars
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom

/-- Ordinary restriction of scalars along the second inclusion.  Its derived
version is the `push` occurring in the affine integral transform. -/
noncomputable def affinePushUnderived (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] : ModuleCat (A ⊗[R] A) ⥤ ModuleCat A :=
  ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom

/-- Ordinary restriction along multiplication, modeling `Δ_*` before deriving. -/
noncomputable def affineDiagonalUnderived (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] : ModuleCat A ⥤ ModuleCat (A ⊗[R] A) :=
  ModuleCat.restrictScalars (affineDiagonalAlgHom R A).toRingHom

/-- Ordinary extension along multiplication, modeling `LΔ^*` before deriving. -/
noncomputable def affineDiagonalPullUnderived (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] : ModuleCat (A ⊗[R] A) ⥤ ModuleCat A :=
  ModuleCat.extendScalars (affineDiagonalAlgHom R A).toRingHom

/-- The ordinary scalar-functor form of `(f₁' ∘ Δ)^* = 1`. -/
noncomputable def affine_pullDiagonalUnderived (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] :
    affinePullUnderived R A ⋙ affineDiagonalPullUnderived R A ≅ 𝟭 (ModuleCat A) := by
  let e := ModuleCat.extendScalarsComp
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom
    (affineDiagonalAlgHom R A).toRingHom
  have h : (affineDiagonalAlgHom R A).toRingHom.comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom =
      RingHom.id A :=
    congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.lmul'_comp_includeLeft (R := R) (S := A))
  rw [h] at e
  exact e.symm ≪≫ ModuleCat.extendScalarsId A

/-- The ordinary scalar-functor form of `(f₂' ∘ Δ)_* = 1`. -/
noncomputable def affine_diagonalPushUnderived (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] :
    affineDiagonalUnderived R A ⋙ affinePushUnderived R A ≅ 𝟭 (ModuleCat A) := by
  let e := ModuleCat.restrictScalarsComp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom
    (affineDiagonalAlgHom R A).toRingHom
  have h : (affineDiagonalAlgHom R A).toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom =
      RingHom.id A :=
    congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.lmul'_comp_includeRight (R := R) (S := A))
  exact e.symm ≪≫ ModuleCat.restrictScalarsCongr h ≪≫ ModuleCat.restrictScalarsId A

/-! ## The corrected diagonal interface and the kernel computation

`DiagonalIdentityData` and the computation of the identity transform now live in
`FourierMukai/Scheme/DiagonalIdentity.lean`, so that both statement layers can use
them.  They are imported here and instantiated in `AffineDiagonalContext` below. -/


/-! ## Affine `FMContext` and the Noetherian statement -/

/-- Affine derived Fourier--Mukai data for `Y = Spec A` over `Spec R`.

The field `core` is the corrected diagonal interface.  `pull'` and `push'` are
the other projection's derived functors, needed to form the existing symmetric
`FMContext`; Lemma 2.25 does not use them.  `S` and `SP` are genuine supplied
subcategory packages, not vacuous `True` placeholders. -/
structure AffineDiagonalContext (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] where
  /-- The projection formula, tensor unit, and diagonal identities. -/
  core : DiagonalIdentityData (AffineD A) (AffineSelfProductD R A) (affineUnit A)
  /-- Derived pullback along the other projection, for the transpose transform. -/
  pull' : AffineD A ⥤ AffineSelfProductD R A
  /-- Derived pushforward along the other projection, for the transpose transform. -/
  push' : AffineSelfProductD R A ⥤ AffineD A
  /-- The chosen bounded/pseudocoherent/perfect subcategories on `Spec A`. -/
  S : Subcats (AffineD A)
  /-- The corresponding chosen subcategories on the self fibre product. -/
  SP : Subcats (AffineSelfProductD R A)

namespace AffineDiagonalContext

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (C : AffineDiagonalContext R A)

/-- Package affine diagonal data as the repository's `FMContext`.  Its diagonal
kernel is `C.core.diagonal.obj (affineUnit A)`, i.e. it is *built from* the
supplied `diagonal` functor rather than being an unrelated object; the functor
itself is still supplied, not constructed. -/
noncomputable def toFMContext :
    FMContext (AffineD A) (AffineD A) (AffineSelfProductD R A) where
  tensorRight := C.core.tensorRight
  pull := C.core.pull
  push := C.core.push
  pull' := C.pull'
  push' := C.push'
  diagonalKernel := C.core.diagonal.obj (affineUnit A)
  S1 := C.S
  S2 := C.S
  SP := C.SP

/-- The natural isomorphism proving GL26 Lemma 2.25 in the affine model. -/
noncomputable def diagonalTransformIso :
    C.toFMContext.transform C.toFMContext.diagonalKernel ≅ 𝟭 (AffineD A) :=
  C.core.identityIso

/-- **Conditional affine derived-module form of GL26 Lemma 2.25.**

Given an `AffineDiagonalContext RB A` -- which supplies the derived functors, the
08IN projection formula, the tensor unit and the two diagonal identities -- the
transform on `AffineD A` with kernel `RΔ_*O_Y` is naturally isomorphic to the
identity.  The rings enter only as the parameters of `AffineD`; **no such context
is constructed from the Noetherian-ring hypotheses here**, so this is not a
ring-only construction of the geometric inputs, and it introduces no additional
properness, flatness or vacuous hypothesis either. -/
theorem affine_lemma_2_25 {RB A : Type u} [CommRing RB] [CommRing A]
    [Algebra RB A] [IsNoetherianRing RB] [IsNoetherianRing A]
    (C : AffineDiagonalContext RB A) :
    Nonempty (C.toFMContext.transform C.toFMContext.diagonalKernel ≅ 𝟭 (AffineD A)) :=
  ⟨C.diagonalTransformIso⟩

end AffineDiagonalContext

end

end RelativeFM
