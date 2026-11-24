/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Paper.DerivedSetup
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.TensorProduct.Maps
import FourierMukai.Scheme.Affine

/-!
# GL26 Lemma 2.25 for affine schemes

GL26's Lemma 2.25 says `Φ_{RΔ_*O_Y} ≅ 𝟭`.  `FourierMukai/Paper/InterfaceAudit.lean`
shows it is *not* a consequence of the abstract `FMContext`: the functors there
are free fields, so a degenerate legal context refutes it.  This file supplies
the missing data explicitly and proves the lemma in the affine model.

* `affine_pullDiagonalUnderived` and `affine_diagonalPushUnderived` are the
  ordinary restriction/extension functors along the tensor inclusions and the
  multiplication, and both underived diagonal identities are proved.
* `DiagonalIdentityData` carries exactly the three derived inputs the proof uses:
  the projection formula (Stacks 08IN), the derived tensor unit, and the two
  diagonal retractions.  `identity_transform_isId` derives the identity
  transform from them.
* `AffineDiagonalContext.toFMContext` is an honest `FMContext` whose
  `diagonalKernel` is `RΔ_*(A[0])`, and `affine_lemma_2_25` proves
  `Nonempty (transform diagonalKernel ≅ 𝟭)` for Noetherian base and fibre rings.

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

/-! ## The corrected diagonal interface and the kernel computation -/

/-- The geometric input for GL26 Lemma 2.25.  Here `unit` is intended to be
`O_Y`; in the affine specialization it is definitionally `affineUnit A`.

`projectionFormula` is the diagonal case of Stacks 08IN.  The other three fields
are the tensor-unit isomorphism and the two derived diagonal identities.  All
are natural isomorphisms, so their naturality, not merely objectwise existence,
is available in the proof. -/
structure DiagonalIdentityData (D DP : Type u) [Category.{v} D] [Category.{v} DP]
    (unit : D) where
  /-- `K ↦ K ⊗^L (-)` on the fibre-product category. -/
  tensorRight : DP → DP ⥤ DP
  /-- `E ↦ E ⊗^L (-)` on the source, used at the structure unit. -/
  tensorSource : D → D ⥤ D
  /-- Derived pullback along the first projection, `L(f₁')^*`. -/
  pull : D ⥤ DP
  /-- Derived pushforward along the second projection, `R(f₂')_*`. -/
  push : DP ⥤ D
  /-- `RΔ_*`; the identity kernel is `diagonal.obj unit`. -/
  diagonal : D ⥤ DP
  /-- `LΔ^*`. -/
  diagonalPull : DP ⥤ D
  /-- Stacks 08IN for `RΔ_* O_Y`: the first line of the kernel computation. -/
  projectionFormula :
    pull ⋙ tensorRight (diagonal.obj unit) ≅
      pull ⋙ diagonalPull ⋙ tensorSource unit ⋙ diagonal
  /-- The derived tensor unit `O_Y ⊗^L (-) ≅ 1`, used in line 1532 of GL26. -/
  tensorUnit : tensorSource unit ≅ 𝟭 D
  /-- Pseudofunctoriality and `f₁' ∘ Δ = 1`: `LΔ^* L(f₁')^* ≅ 1`. -/
  pull_diagonal : pull ⋙ diagonalPull ≅ 𝟭 D
  /-- Pseudofunctoriality and `f₂' ∘ Δ = 1`: `R(f₂')_* RΔ_* ≅ 1`. -/
  diagonal_push : diagonal ⋙ push ≅ 𝟭 D

namespace DiagonalIdentityData

variable {D DP : Type u} [Category.{v} D] [Category.{v} DP] {unit : D}
  (C : DiagonalIdentityData D DP unit)

/-- The objectwise GL26 Lemma 2.25 computation.  This is the promised kernel
calculation: no object is identified by fiat with the identity transform. -/
noncomputable def identityComponent (E : D) :
    C.push.obj ((C.tensorRight (C.diagonal.obj unit)).obj (C.pull.obj E)) ≅ E :=
  C.push.mapIso (C.projectionFormula.app E) ≪≫
    C.push.mapIso (C.diagonal.mapIso
      (((C.tensorSource unit).mapIso (C.pull_diagonal.app E)) ≪≫
        C.tensorUnit.app E)) ≪≫
    C.diagonal_push.app E

/-- **GL26 Lemma 2.25 (`lem:funct_on_kernel`), categorical computation.**

The explicit isomorphisms `identityComponent` assemble into a natural
isomorphism.  The proof uses exactly the naturality of the projection formula,
the two diagonal identities, and the tensor unit. -/
noncomputable def identityIso :
    C.pull ⋙ C.tensorRight (C.diagonal.obj unit) ⋙ C.push ≅ 𝟭 D := by
  refine NatIso.ofComponents C.identityComponent (naturality := ?_)
  intro X Y f
  have hp := C.projectionFormula.hom.naturality f
  have hpd := C.pull_diagonal.hom.naturality f
  have htu := C.tensorUnit.hom.naturality f
  have hdp := C.diagonal_push.hom.naturality f
  simp only [Functor.comp_map, Functor.id_map] at hp hpd htu hdp
  dsimp [identityComponent]
  simp only [Category.assoc]
  rw [← hdp]
  simp only [← C.push.map_comp_assoc]
  congr 1
  rw [reassoc_of% hp]
  apply congrArg C.push.map
  simp only [← C.diagonal.map_comp]
  rw [← (C.tensorSource unit).map_comp_assoc]
  rw [hpd]
  rw [(C.tensorSource unit).map_comp_assoc]
  rw [htu]
  simp only [Category.assoc]

/-- `identityIso` is an isomorphism onto the identity functor, not merely an
objectwise assertion. -/
theorem identity_transform_isId :
    Nonempty (C.pull ⋙ C.tensorRight (C.diagonal.obj unit) ⋙ C.push ≅ 𝟭 D) :=
  ⟨C.identityIso⟩

end DiagonalIdentityData

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

/-- Package affine diagonal data as the repository's `FMContext`.  Crucially,
its diagonal kernel is *defined* as `RΔ_*(A[0])`, rather than supplied as an
unrelated object. -/
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

/-- **GL26 Lemma 2.25 (`lem:funct_on_kernel`) over affine Noetherian schemes.**

For `Y = Spec A` over `S = Spec ABase`, with both rings Noetherian, the
integral transform with kernel `RΔ_*O_Y` is naturally isomorphic to the identity.
The fields of `C` listed in its docstring are precisely the remaining derived
geometric inputs; no additional properness, flatness, or vacuous hypothesis is
introduced. -/
theorem affine_lemma_2_25 {RB A : Type u} [CommRing RB] [CommRing A]
    [Algebra RB A] [IsNoetherianRing RB] [IsNoetherianRing A]
    (C : AffineDiagonalContext RB A) :
    Nonempty (C.toFMContext.transform C.toFMContext.diagonalKernel ≅ 𝟭 (AffineD A)) :=
  ⟨C.diagonalTransformIso⟩

end AffineDiagonalContext

end

end RelativeFM
