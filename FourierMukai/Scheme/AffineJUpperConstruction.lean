/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.AffineDerivedTensorHom
import FourierMukai.Scheme.AffineSecondGluingAssembly

/-!
# The right adjoint of affine local cohomology, from the open right adjoint

Sources: GL26 Lemma A.4 (`lem:spacey_recollement`), affine case, and LP26
Setup 4.1: the recollement `D(A[1/f]) → D(A) → D_Z(A)`.  This file supplies the
last field of `AffineRecollementInput`, the right adjoint `jUpper` of local
cohomology `jStar = RΓ_Z : D(A) → D_Z(A)` with `jStar ⊣ jUpper`.

## What is proved

A **categorical Bousfield-localization construction** (section `Generic`).  In a
triangulated category `D`, let `ι : S ⥤ D` be fully faithful with right adjoint
`jStar`, and let `L : U ⥤ D` be fully faithful and triangulated with a right
adjoint `R`.  Assume

* every counit `ι (jStar X) ⟶ X` has a cone in the essential image of `L`, and
* every map from `ι Y` to the essential image of `L` is zero.

Then `jStar` has a right adjoint.  Its value on `Y` is the cone `W Y` of the
counit `L (R (ι Y)) ⟶ ι Y`, and the Hom bijection is
`(jStar X ⟶ Y) ≃ (ι jStar X ⟶ ι Y) ≃ (ι jStar X ⟶ W Y) ≃ (X ⟶ W Y)`.  The
middle bijection uses the second hypothesis and the third uses the first, together
with right orthogonality of `W Y` to `L` (already proved in
`AffineSecondGluing`).  The functor and the adjunction come from Mathlib's
`Adjunction.rightAdjointOfEquiv` / `adjunctionOfEquivRight`.

Mathematically, `W Y = cone(RHom_A(A_f, Y) → Y) ≅ RHom_A(RΓ_Z A, Y)`.  It is the
same functor as the tensor–Hom candidate of `AffineJUpperTensorHom`, because
right adjoints are unique, but its construction uses neither `⊗^L` nor `RHom`.

**Affine application** (section `Affine`).  Both hypotheses hold for the affine
data: the kernel of `jStar` is the image of restriction of scalars
(`supported_kernel`), and `jStar ∘ Rj_* = 0` (`isZero_jStar_derivedRestrictionScalars`).
So every right adjoint `iShriek` of restriction of scalars
`Rj_* : D(A[1/f]) → D(A)` gives

* `jUpperOfIShriek` and `jStarAdjOfIShriek : jStar A f ⊣ jUpperOfIShriek`;
* `adjointInputOfIShriek`, `affineRecollementInputOfIShriek`,
  `affineRecollementOfIShriek`: **every field of `AffineRecollementInput`** from
  `iShriek` and its adjunction;
* `affineRecollementOfStacks0E55`: the same from the tagged input
  `AffineOpenRightAdjointStacksInput` (Stacks 0E55, the right adjoint of
  `Rj_*` for the qcqs open immersion `Spec A_f → Spec A`), which
  is already registered as an `S` input in `results/ASSUMPTIONS.md`;
* `affineRecollementOfExactCoextension`: an **unconditional** construction
  when coextension of scalars `Hom_A(A_f, -)` is right exact, because then the
  repository's `derivedCoextendScalars` (`AffineIShriek.lean`) is a right adjoint.

## What is assumed

Nothing beyond the hypotheses in the statements.  The generic construction and the
`iShriek`-conditional affine construction use no Stacks input.  The 0E55 corollary
uses exactly `AffineOpenRightAdjointStacksInput`.  This route does **not** use
Stacks 0A6R, the derived tensor–Hom package (06YU/08J8) or the Čech augmentation,
which `AffineDerivedTensorHom.RecollementAssembly.toRecollement` needed in
addition to 0E55.

## Difference from the paper

GL26 and LP26 take the recollement as standard.  Here, completing it is reduced to
one input, a right adjoint of `Rj_*`; for a general `f` that input is the
Stacks 0E55 field.  An unconditional construction of `RHom_A(A_f, -)` on
unbounded complexes (K-injective resolutions, or Brown representability) is not
in the tree.  Conversely, any `jUpper` gives such an adjoint (the dual
construction); that direction is not formalized here.
-/

@[expose] public section

namespace RelativeFM.Recollement.JUpperConstruction

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeFM.Recollement.SecondGluing

universe vS uS vD uD vU uU

noncomputable section

section Generic

variable {S : Type uS} {D : Type uD} {U : Type uU}
  [Category.{vS} S] [Category.{vD} D] [Category.{vU} U]
  [Preadditive D] [Preadditive U] [HasZeroObject D] [HasZeroObject U]
  [HasShift D ℤ] [HasShift U ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor U n).Additive]
  [Pretriangulated D] [Pretriangulated U]
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated U]

variable (ι : S ⥤ D) [ι.Full] [ι.Faithful] (jStar : D ⥤ S) (adj₁ : ι ⊣ jStar)
variable (L : U ⥤ D) (R : D ⥤ U) (adjL : L ⊣ R)
  [L.CommShift ℤ] [L.IsTriangulated] [L.Full] [L.Faithful]
  [R.CommShift ℤ] [R.IsTriangulated]

/-- The first hypothesis: the counit of `ι ⊣ jStar` at every object has a cone
in the essential image of `L`. -/
def FirstTriangleHyp : Prop :=
  ∀ X : D, ∃ (Z : D) (g : X ⟶ Z) (h : Z ⟶ (ι.obj (jStar.obj X))⟦(1 : ℤ)⟧),
    Triangle.mk (adj₁.counit.app X) g h ∈ distTriang D ∧ L.essImage Z

/-- The second hypothesis: every map from the image of `ι` to the essential
image of `L` is zero. -/
def MixedVanishingHyp : Prop :=
  ∀ (Y : S) (Z : D) (g : ι.obj Y ⟶ Z), L.essImage Z → g = 0

/-- The value of the right adjoint: a chosen cone of the counit
`L (R (ι Y)) ⟶ ι Y`. -/
def obj (Y : S) : D := (coneTriangle (adjL.counit.app (ι.obj Y))).obj₃

/-- The comparison map `ι Y ⟶ W Y`. -/
def toObj (Y : S) : ι.obj Y ⟶ obj ι L R adjL Y :=
  (coneTriangle (adjL.counit.app (ι.obj Y))).mor₂

set_option linter.unusedSectionVars false in
lemma obj_rightOrthogonal (Y : S) : L.essImage.rightOrthogonal (obj ι L R adjL Y) :=
  coneCounit_obj₃_rightOrthogonal L R adjL (ι.obj Y)

set_option linter.unusedSectionVars false in
variable {ι L} in
/-- For a source in the image of `ι`, postcomposition with `ι Y ⟶ W Y` is
bijective. -/
lemma postcomp_bijective (hmixed : MixedVanishingHyp ι L) (Y' Y : S) :
    Function.Bijective (fun β : ι.obj Y' ⟶ ι.obj Y ↦ β ≫ toObj ι L R adjL Y) := by
  let T := coneTriangle (adjL.counit.app (ι.obj Y))
  have hT : T ∈ distTriang D := coneTriangle_distinguished _
  have h₁ : L.essImage T.obj₁ := ⟨R.obj (ι.obj Y), ⟨Iso.refl _⟩⟩
  constructor
  · intro β₁ β₂ h
    have hz : (β₁ - β₂) ≫ toObj ι L R adjL Y = 0 := by
      change β₁ ≫ toObj ι L R adjL Y = β₂ ≫ toObj ι L R adjL Y at h
      rw [Preadditive.sub_comp]
      exact sub_eq_zero.mpr h
    obtain ⟨γ, hγ⟩ := T.coyoneda_exact₂ hT (β₁ - β₂) hz
    have hγ0 : γ = 0 := hmixed Y' _ γ h₁
    rw [hγ0, zero_comp] at hγ
    exact sub_eq_zero.mp hγ
  · intro α
    have hz : α ≫ T.mor₃ = 0 := hmixed Y' _ _ (L.essImage.le_shift 1 _ h₁)
    obtain ⟨β, hβ⟩ := T.coyoneda_exact₃ hT α hz
    exact ⟨β, hβ.symm⟩

set_option linter.unusedSectionVars false in
variable {ι jStar adj₁ L} in
/-- For a target right orthogonal to `L`, precomposition with the counit
`ι (jStar X) ⟶ X` is bijective. -/
lemma precomp_bijective (hfirst : FirstTriangleHyp ι jStar adj₁ L) (X : D) {W : D}
    (hW : L.essImage.rightOrthogonal W) :
    Function.Bijective (fun φ : X ⟶ W ↦ adj₁.counit.app X ≫ φ) := by
  obtain ⟨Z, g, h, hT, hZ⟩ := hfirst X
  let T := Triangle.mk (adj₁.counit.app X) g h
  constructor
  · intro φ₁ φ₂ hφ
    have hz : T.mor₁ ≫ (φ₁ - φ₂) = 0 := by
      change adj₁.counit.app X ≫ φ₁ = adj₁.counit.app X ≫ φ₂ at hφ
      change adj₁.counit.app X ≫ (φ₁ - φ₂) = 0
      rw [Preadditive.comp_sub]
      exact sub_eq_zero.mpr hφ
    obtain ⟨ψ, hψ⟩ := T.yoneda_exact₂ hT (φ₁ - φ₂) hz
    have hψ0 : ψ = 0 := hW ψ hZ
    rw [hψ0, comp_zero] at hψ
    exact sub_eq_zero.mp hψ
  · intro α
    have hT' : T.invRotate ∈ distTriang D := inv_rot_of_distTriang _ hT
    have hz : T.invRotate.mor₁ ≫ α = 0 := hW _ (L.essImage.le_shift (-1) _ hZ)
    obtain ⟨φ, hφ⟩ := T.invRotate.yoneda_exact₂ hT' α hz
    exact ⟨φ, hφ.symm⟩

variable {ι jStar adj₁ L R} in
/-- The Hom bijection `(jStar X ⟶ Y) ≃ (X ⟶ W Y)`. -/
def homEquiv (hfirst : FirstTriangleHyp ι jStar adj₁ L)
    (hmixed : MixedVanishingHyp ι L) (X : D) (Y : S) :
    (jStar.obj X ⟶ Y) ≃ (X ⟶ obj ι L R adjL Y) :=
  (Functor.FullyFaithful.ofFullyFaithful ι).homEquiv.trans
    ((Equiv.ofBijective _ (postcomp_bijective R adjL hmixed (jStar.obj X) Y)).trans
      (Equiv.ofBijective _
        (precomp_bijective hfirst X (obj_rightOrthogonal ι L R adjL Y))).symm)

variable {ι jStar adj₁ L R} in
lemma counit_comp_homEquiv (hfirst : FirstTriangleHyp ι jStar adj₁ L)
    (hmixed : MixedVanishingHyp ι L) (X : D) (Y : S) (g : jStar.obj X ⟶ Y) :
    adj₁.counit.app X ≫ homEquiv adjL hfirst hmixed X Y g =
      ι.map g ≫ toObj ι L R adjL Y := by
  dsimp only [homEquiv, Equiv.trans_apply]
  exact Equiv.ofBijective_apply_symm_apply
    (fun φ : X ⟶ obj ι L R adjL Y ↦ adj₁.counit.app X ≫ φ) _ _

variable {ι jStar adj₁ L R} in
lemma homEquiv_naturality (hfirst : FirstTriangleHyp ι jStar adj₁ L)
    (hmixed : MixedVanishingHyp ι L) (X' X : D) (Y : S) (f : X' ⟶ X)
    (g : jStar.obj X ⟶ Y) :
    homEquiv adjL hfirst hmixed X' Y (jStar.map f ≫ g) =
      f ≫ homEquiv adjL hfirst hmixed X Y g := by
  apply (precomp_bijective hfirst X' (obj_rightOrthogonal ι L R adjL Y)).1
  show adj₁.counit.app X' ≫ homEquiv adjL hfirst hmixed X' Y (jStar.map f ≫ g) =
    adj₁.counit.app X' ≫ f ≫ homEquiv adjL hfirst hmixed X Y g
  have hn : adj₁.counit.app X' ≫ f = ι.map (jStar.map f) ≫ adj₁.counit.app X :=
    (adj₁.counit_naturality f).symm
  rw [counit_comp_homEquiv, ← Category.assoc, hn, Category.assoc, counit_comp_homEquiv,
    Functor.map_comp, Category.assoc]

variable {ι jStar adj₁ L R} in
/-- **The right adjoint of `jStar`**, built from the right adjoint of `L`. -/
def rightAdjoint (hfirst : FirstTriangleHyp ι jStar adj₁ L)
    (hmixed : MixedVanishingHyp ι L) : S ⥤ D :=
  Adjunction.rightAdjointOfEquiv (G_obj := obj ι L R adjL)
    (homEquiv adjL hfirst hmixed) (homEquiv_naturality adjL hfirst hmixed)

variable {ι jStar adj₁ L R} in
/-- **The adjunction `jStar ⊣ rightAdjoint`.** -/
def adjunction (hfirst : FirstTriangleHyp ι jStar adj₁ L)
    (hmixed : MixedVanishingHyp ι L) :
    jStar ⊣ rightAdjoint adjL hfirst hmixed :=
  Adjunction.adjunctionOfEquivRight _ _

@[simp] lemma rightAdjoint_obj (hfirst : FirstTriangleHyp ι jStar adj₁ L)
    (hmixed : MixedVanishingHyp ι L) (Y : S) :
    (rightAdjoint adjL hfirst hmixed).obj Y = obj ι L R adjL Y := rfl

set_option linter.unusedSectionVars false in
variable {ι jStar L} in
include adj₁ in
/-- The mixed-vanishing hypothesis from the adjunction `ι ⊣ jStar` and
`jStar ∘ L = 0`. -/
lemma mixedVanishing_of_isZero (hzero : ∀ Z : U, IsZero (jStar.obj (L.obj Z))) :
    MixedVanishingHyp ι L := by
  intro Y Z g ⟨Z', ⟨e⟩⟩
  have hZ : IsZero (jStar.obj Z) := (hzero Z').of_iso (jStar.mapIso e).symm
  apply (adj₁.homEquiv Y Z).injective
  exact hZ.eq_of_tgt _ _

end Generic

section GenericFirst

variable {S : Type uS} {D : Type uD} {U : Type uU}
  [Category.{vS} S] [Category.{vD} D] [Category.{vU} U]
  [Preadditive S] [Preadditive D] [HasZeroObject S] [HasZeroObject D]
  [HasShift S ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor S n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated S] [Pretriangulated D] [CategoryTheory.IsTriangulated D]

variable {ι : S ⥤ D} [ι.Full] [ι.Faithful] {jStar : D ⥤ S} (adj₁ : ι ⊣ jStar)
  [jStar.CommShift ℤ] [jStar.IsTriangulated] {L : U ⥤ D}

/-- The first-triangle hypothesis follows from exactness of `jStar` and the
description of its kernel as the essential image of `L`. -/
lemma firstTriangle_of_kernel (hker : ∀ X : D, IsZero (jStar.obj X) → L.essImage X) :
    FirstTriangleHyp ι jStar adj₁ L := by
  intro X
  let T := coneTriangle (adj₁.counit.app X)
  have hT : T ∈ distTriang D := coneTriangle_distinguished _
  refine ⟨T.obj₃, T.mor₂, T.mor₃, hT, hker _ ?_⟩
  have hiso : IsIso (jStar.map (adj₁.counit.app X)) := by
    have h := adj₁.right_triangle_components X
    have : IsIso (adj₁.unit.app (jStar.obj X) ≫ jStar.map (adj₁.counit.app X)) := by
      rw [h]; exact IsIso.id _
    exact IsIso.of_isIso_comp_left (adj₁.unit.app (jStar.obj X)) _
  exact Triangle.isZero₃_of_isIso₁ (jStar.mapTriangle.obj T)
    (jStar.map_distinguished T hT) hiso

end GenericFirst

section Affine

universe u

attribute [local instance] HasDerivedCategory.standard

open RelativeFM RelativeFM.AffineLocalCohomology

variable (A : Type u) [CommRing A] (f : A)

lemma affineFirstTriangle :
    FirstTriangleHyp (affineDZι A f) (jStar A f) (jShriekAdj A f)
      (derivedRestrictionScalars A f) := by
  apply firstTriangle_of_kernel
  intro X hX
  obtain ⟨Y, ⟨e⟩⟩ := (supported_kernel A f (jStar A f) (jStarFactors A f) X).1
    ⟨hX.isoZero⟩
  exact ⟨Y, ⟨e.symm⟩⟩

lemma affineMixedVanishing :
    MixedVanishingHyp (affineDZι A f) (derivedRestrictionScalars A f) :=
  mixedVanishing_of_isZero (jShriekAdj A f)
    (MixedZero.isZero_jStar_derivedRestrictionScalars A f)

variable {A f}

/-- **The right adjoint of affine local cohomology**, from any right adjoint
`iShriek` of `Rj_* : D(A[1/f]) → D(A)`.  On objects it is the cone of
`Rj_* iShriek Y ⟶ Y`. -/
def jUpperOfIShriek {iShriek : AffineD A ⥤ AffineD (Away A f)}
    (iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek) : AffineDZ A f ⥤ AffineD A :=
  letI : iShriek.CommShift ℤ := iLowerAdj.rightAdjointCommShift ℤ
  letI : iLowerAdj.CommShift ℤ := iLowerAdj.commShift_of_leftAdjoint ℤ
  letI : iShriek.IsTriangulated := iLowerAdj.isTriangulated_rightAdjoint
  rightAdjoint iLowerAdj (affineFirstTriangle A f) (affineMixedVanishing A f)

/-- **GL26 Lemma A.4** (`lem:spacey_recollement`), affine case, the last
adjunction `j^* ⊣ j_*` of the recollement `D(A[1/f]) → D(A) → D_Z(A)`
(LP26 Setup 4.1), for `j^* = RΓ_Z`.  Conditional only on a right adjoint of
restriction of scalars. -/
def jStarAdjOfIShriek {iShriek : AffineD A ⥤ AffineD (Away A f)}
    (iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek) :
    jStar A f ⊣ jUpperOfIShriek iLowerAdj :=
  letI : iShriek.CommShift ℤ := iLowerAdj.rightAdjointCommShift ℤ
  letI : iLowerAdj.CommShift ℤ := iLowerAdj.commShift_of_leftAdjoint ℤ
  letI : iShriek.IsTriangulated := iLowerAdj.isTriangulated_rightAdjoint
  adjunction iLowerAdj (affineFirstTriangle A f) (affineMixedVanishing A f)

/-- The two remaining adjunctions, from `iShriek` alone. -/
def adjointInputOfIShriek {iShriek : AffineD A ⥤ AffineD (Away A f)}
    (iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek) :
    SecondGluing.AssemblyM4.AdjointInput A f where
  iShriek := iShriek
  iLowerAdj := iLowerAdj
  jUpper := jUpperOfIShriek iLowerAdj
  jStarAdj := jStarAdjOfIShriek iLowerAdj

/-- **GL26 Lemma A.4** (`lem:spacey_recollement`), affine case; LP26 Setup 4.1.
Every field of `AffineRecollementInput`, from a right adjoint of
restriction of scalars. -/
def affineRecollementInputOfIShriek {iShriek : AffineD A ⥤ AffineD (Away A f)}
    (iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek) : AffineRecollementInput A f :=
  (adjointInputOfIShriek iLowerAdj).toAffineRecollementInput

/-- **GL26 Lemma A.4** (`lem:spacey_recollement`), affine case: the recollement
`D(A[1/f]) → D(A) → D_Z(A)`, from a right adjoint of restriction of scalars. -/
def affineRecollementOfIShriek {iShriek : AffineD A ⥤ AffineD (Away A f)}
    (iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek) : AffineRecollement A f :=
  (adjointInputOfIShriek iLowerAdj).toRecollement

/-- **GL26 Lemma A.4** (`lem:spacey_recollement`), affine case, conditional on
the single tagged input Stacks **0E55** (`AffineOpenRightAdjointStacksInput`).
Stacks 0A6R and the derived tensor–Hom package are not used. -/
def affineRecollementInputOfStacks0E55 {iShriek : AffineD A ⥤ AffineD (Away A f)}
    (hOpen : KProjectiveTensorHom.AffineOpenRightAdjointStacksInput f iShriek) :
    AffineRecollementInput A f :=
  affineRecollementInputOfIShriek (Classical.choice hOpen.tag_0E55)

/-- The recollement, conditional on Stacks 0E55 alone. -/
def affineRecollementOfStacks0E55 {iShriek : AffineD A ⥤ AffineD (Away A f)}
    (hOpen : KProjectiveTensorHom.AffineOpenRightAdjointStacksInput f iShriek) :
    AffineRecollement A f :=
  affineRecollementOfIShriek (Classical.choice hOpen.tag_0E55)

/-- **GL26 Lemma A.4** (`lem:spacey_recollement`), affine case,
**unconditionally** in the case where coextension of scalars
`Hom_A(A_f, -)` is right exact.  Then `derivedCoextendScalars` is a right
adjoint of `Rj_*` (`AffineIShriek.lean`). -/
def affineRecollementInputOfExactCoextension
    [PreservesFiniteColimits (IShriek.underivedCandidate A f)] :
    AffineRecollementInput A f :=
  affineRecollementInputOfIShriek (IShriek.derivedRestrictionCoextendAdjunction A f)

/-- The recollement in the right-exact coextension case, with no input. -/
def affineRecollementOfExactCoextension
    [PreservesFiniteColimits (IShriek.underivedCandidate A f)] :
    AffineRecollement A f :=
  affineRecollementOfIShriek (IShriek.derivedRestrictionCoextendAdjunction A f)

/-- The constructed `jUpper` is the one in the assembled recollement input. -/
@[simp] lemma affineRecollementInputOfIShriek_jUpper
    {iShriek : AffineD A ⥤ AffineD (Away A f)}
    (iLowerAdj : derivedRestrictionScalars A f ⊣ iShriek) :
    (affineRecollementInputOfIShriek iLowerAdj).jUpper = jUpperOfIShriek iLowerAdj := rfl

end Affine

section NonVacuity

universe u

attribute [local instance] HasDerivedCategory.standard

open RelativeFM

variable (A : Type u) [CommRing A]

/-- For `f = 0` the localization `A[1/0]` is the zero ring. -/
lemma subsingleton_away_zero : Subsingleton (Away A (0 : A)) :=
  IsLocalization.subsingleton (M := Submonoid.powers (0 : A)) ⟨1, pow_one 0⟩

/-- Every functor into a category of modules over the zero ring preserves finite
colimits, because all such modules are zero. -/
instance preservesFiniteColimits_underivedCandidate_zero :
    PreservesFiniteColimits (IShriek.underivedCandidate A (0 : A)) := by
  have := subsingleton_away_zero A
  have hz : ∀ M : ModuleCat.{u} (Away A (0 : A)), IsZero M := fun M ↦ by
    have : Subsingleton M := Module.subsingleton (Away A (0 : A)) M
    exact ModuleCat.isZero_of_subsingleton M
  refine ⟨fun J _ _ ↦ ⟨fun {K} ↦ ⟨fun {c} _ ↦ ⟨?_⟩⟩⟩⟩
  exact
    { desc := fun s ↦ (hz _).to_ s.pt
      fac := fun s j ↦ (hz _).eq_of_src _ _
      uniq := fun s m _ ↦ (hz _).eq_of_src _ _ }

/-- **Non-vacuity** of `affineRecollementInputOfExactCoextension`, hence of the
`iShriek` hypothesis of `affineRecollementInputOfIShriek`: for `f = 0` the
right-exactness instance holds, so the whole recollement input is constructed
with no input at all. -/
example : AffineRecollementInput A (0 : A) := affineRecollementInputOfExactCoextension

/-- The right adjoint of restriction of scalars exists for `f = 0`. -/
example : derivedRestrictionScalars A (0 : A) ⊣
    IShriek.derivedCoextendScalars A (0 : A) :=
  IShriek.derivedRestrictionCoextendAdjunction A 0

end NonVacuity

end

end RelativeFM.Recollement.JUpperConstruction

#print axioms RelativeFM.Recollement.JUpperConstruction.adjunction
#print axioms RelativeFM.Recollement.JUpperConstruction.firstTriangle_of_kernel
#print axioms RelativeFM.Recollement.JUpperConstruction.jStarAdjOfIShriek
#print axioms RelativeFM.Recollement.JUpperConstruction.affineRecollementInputOfIShriek
#print axioms RelativeFM.Recollement.JUpperConstruction.affineRecollementOfIShriek
#print axioms RelativeFM.Recollement.JUpperConstruction.affineRecollementInputOfStacks0E55
#print axioms RelativeFM.Recollement.JUpperConstruction.affineRecollementOfStacks0E55
#print axioms RelativeFM.Recollement.JUpperConstruction.affineRecollementInputOfExactCoextension
#print axioms RelativeFM.Recollement.JUpperConstruction.affineRecollementOfExactCoextension
