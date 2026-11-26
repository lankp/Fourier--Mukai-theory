/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.MainMinimal
import WeakApprox.CompactVanishing
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The scheme route through Lank--Pauwels: the measured interface

This file separates the *last categorical implication* of the scheme rehaul from
the geometric construction of its input package.  There are no `sorry`s and no
new axioms: every missing geometric fact is an explicit structure field with a
docstring saying where it comes from.

## What is proved

`SchemeOpenClosedDerived` bundles Mathlib's open immersion and closed complement
together with the `SetupMainMinimal` package of LP and the support predicate
with its kernel characterization.  From that data:

* `weakApprox_dqcX_of_gluing` concludes `SatisfiesWA DX` — weak approximability
  of the middle category — by applying LP Theorem 1.1
  (`SetupMainMinimal.theorem_1_1`) with Neeman's Theorem 3.2 as the 09SR input
  and `CompactHomZeroAtTop` for the vanishing;
* `weakApprox_dqcX_of_eventual` does the same from the single-generator
  vanishing statement, which is the form LP Theorem 1.1 has;
* `weakApprox_dqcX_of_compactHomZeroAtTop` removes 09SR entirely, using the
  repository's `CompactVanishing` module;
* `jShriek_compact` and `iLower_supported` are the geometric side conditions,
  proved from the interface fields rather than assumed.

## What this measures

The categorical implication is done: once the interface is inhabited, weak
approximability of `D_qc(X)` follows from LP's theorem with no further work.
The interface fields are the contract the geometric layer must satisfy, and they
are exactly the objects `results/archive/MATHLIB_INVENTORY.md` reports as missing
(`D_qc`, `Perf`, support, the derived recollement).  Neeman's published theorem
supplies the *proof* of the fields' content for qcqs schemes, but not the
categories in which they are stated.

## Primary source

Neeman, *Bounded `t`-structures on the category of perfect complexes*, Acta
Math. 233 (2024), 239--284, Theorem 3.2(i)--(iv), for qcqs schemes: compacts are
supported perfect complexes, there is a single compact generator, the standard
`t`-structure is preferred, and `D_qc,Z(X)` is weakly approximable.
https://doi.org/10.4310/ACTA.2024.v233.n2.a2 .  Noetherianity is not needed.

Found by a member of the Ultramath run `smwuyellz` (direction D5).
-/

@[expose] public section

namespace RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open AlgebraicGeometry

universe v u uZ uD uU

#check AlgebraicGeometry.Scheme
#check AlgebraicGeometry.IsNoetherian
#check AlgebraicGeometry.IsOpenImmersion
#check AlgebraicGeometry.Scheme.Hom.opensRange
#check RelativeWeakApprox.SetupMainMinimal.theorem_1_1
#check RelativeWeakApprox.exists_setup_4_4_3_of_compactHomZeroAtTop
#check RelativeWeakApprox.recollement_jShriek_compact
#check RelativeWeakApprox.satisfiesWA_of_setup
#check RelativeWeakApprox.CompactHomZeroAtTop
#check RelativeWeakApprox.compactHomZeroAtTop_of_isClassicalGeneratorOnCompacts
#check RelativeWeakApprox.WeakApproximationData.eventuallyHomZero_self
#check RelativeWeakApprox.WeakApproximationData.monoBound
#check RelativeWeakApprox.Setup44Reduced.toSetup44
#check RelativeWeakApprox.Recollement.kernel

/-- An open immersion of schemes and its closed set-theoretic complement.
This is the actual Mathlib scheme layer; derived categories are added
separately because Mathlib 4.33.1 does not supply their `D_qc` instantiation. -/
structure SchemeOpenClosed where
  /-- Ambient scheme. -/
  X : Scheme.{u}
  /-- Open subscheme, represented separately. -/
  U : Scheme.{u}
  /-- The open immersion `j : U ⟶ X`. -/
  j : U ⟶ X
  /-- `j` is an open immersion. -/
  [j_open : IsOpenImmersion j]
  /-- The complement of the image of `j`. -/
  Z : Set X
  /-- The displayed complement is closed. -/
  Z_closed : IsClosed Z
  /-- Identification with the complement of `j`'s open image. -/
  Z_eq : Z = ((j.opensRange : X.Opens) : Set X)ᶜ

attribute [instance] SchemeOpenClosed.j_open

/-- Stacks Tag 09SR, in the exact form required by `theorem_1_1`.
For a scheme instantiation the geometric input identifying compacts with
perfect complexes is Neeman 2024, Theorem 3.2(i); the finite thick-envelope
statement itself remains the cited Stacks input. -/
def Stacks09SR (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] : Prop :=
  ∀ (G : C), IsGenerator G → IsCompactAb G → IsClassicalGeneratorOnCompacts G

/-- Weak approximability plus 09SR gives the positive compact Hom-vanishing
for every pair of compacts.  This is the forward, categorical consequence of
Neeman's input, not a second geometric boundedness postulate. -/
theorem compactHomZeroAtTop_of_satisfiesWA {C : Type u} [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    (hWA : SatisfiesWA C) (h09SR : Stacks09SR C) : CompactHomZeroAtTop C := by
  obtain ⟨W⟩ := hWA
  exact compactHomZeroAtTop_of_isClassicalGeneratorOnCompacts
    W.eventuallyHomZero_self (h09SR W.G W.G_generates W.G_compact)

section DerivedInterface

variable (DZ : Type uZ) (DX : Type uD) (DU : Type uU)
  [Category.{v} DZ] [Category.{v} DX] [Category.{v} DU]
  [Preadditive DZ] [Preadditive DX] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DX] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DX ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor DX n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DX] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DX]
  [CategoryTheory.IsTriangulated DU]

/-- Geometric interface for an open/closed derived recollement.

`DX`, `DU`, `DZ` are intended to be `D_qc,S(X)`, `D_qc,S∩U(U)`, and
`D_qc,S∩Z(X)` respectively.  In the basic case `S = X`, these are `D_qc(X)`,
`D_qc(U)`, and `D_qc,Z(X)`.  The last is a support subcategory of `D(X)`, not
necessarily the derived category of a chosen closed subscheme structure on
`Z`.  `setup.R` contains all six functors `j_! ⊣ j^* ⊣ j_*` and
`i^* ⊣ i_* ⊣ i^!`, their exactness, and both distinguished gluing triangles.

The field `supported_iff` is the missing geometric identification of support
with the kernel of restriction.  (The three compact/perfect fields
`CompactsArePerfect` were deleted in wave 6: their `Perf` was a free field, so
they carried no content; `results/OPEN_INPUTS.md` row 2.11, F4.)  Nothing in
this structure asserts existence of the
abstract categories; an instantiation must provide them. -/
structure SchemeOpenClosedDerived where
  /-- Actual open immersion and its closed complement in Mathlib. -/
  geometry : SchemeOpenClosed.{u}
  /-- The 20-field minimal LP setup, including both six-functor adjunction
  chains and weak approximation data on the two ends. -/
  setup : SetupMainMinimal DZ DX DU
  /-- Cohomological support on the closed complement, as a predicate on the
  middle category. -/
  supportedOnZ : ObjectProperty DX
  /-- Support is detected by vanishing under restriction to the open.  For a
  geometric instantiation this comes from the support kernel description in
  GL26 Appendix A, `lem:spacey_recollement`; it is not supplied by Mathlib. -/
  supported_iff : ∀ E : DX, supportedOnZ E ↔ Nonempty (setup.R.jStar.obj E ≅ 0)

end DerivedInterface

section DerivedInterfaceLemmas

namespace SchemeOpenClosedDerived

variable {DZ DX DU}
  [Category.{v} DZ] [Category.{v} DX] [Category.{v} DU]
  [Preadditive DZ] [Preadditive DX] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DX] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DX ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor DX n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DX] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DX]
  [CategoryTheory.IsTriangulated DU]

variable (I : SchemeOpenClosedDerived DZ DX DU)

include I

/-- Weak approximability of the closed-support end, extracted from its supplied
Neeman/geometric approximation data. -/
theorem weakApprox_closed : SatisfiesWA DZ :=
  ⟨SetupMainMinimal.approxZ (SchemeOpenClosedDerived.setup I)⟩

/-- Weak approximability of the open end, extracted from its supplied
Neeman/geometric approximation data. -/
theorem weakApprox_open : SatisfiesWA DU :=
  ⟨SetupMainMinimal.approxU (SchemeOpenClosedDerived.setup I)⟩

/-- The open compact generator is compact; no separate perfectness assumption
is needed for this categorical fact. -/
theorem GU_compact : IsCompactAb I.setup.GU := by
  rw [← I.setup.approxU_G]
  exact I.setup.approxU.G_compact

/-- `j_!` preserves compactness by adjunction.  This proves the suggested
geometric hypothesis categorically, using LP Lemma 4.3(2)'s implementation. -/
theorem jShriek_compact : IsCompactAb (I.setup.R.jShriek.obj I.setup.GU) :=
  recollement_jShriek_compact I.setup.R I.GU_compact

/-- Every object in the essential image of the closed-support inclusion is
supported on the closed complement, using `supported_iff` and the kernel part
of the recollement. -/
theorem iLower_supported (P : DZ) : I.supportedOnZ (I.setup.R.iLower.obj P) := by
  apply (I.supported_iff _).mpr
  exact (I.setup.R.kernel _).mpr ⟨P, ⟨Iso.refl _⟩⟩

/-- **The requested categorical gluing step.**  Once all geometric fields of
`SetupMainMinimal` are supplied, LP Theorem 1.1 turns eventual self-Hom
vanishing of a middle compact generator into weak approximability of `DX`.

The two remaining external inputs are deliberately explicit: the Stacks 09SR
finite thick-envelope statement and `CompactHomZeroAtTop DX`. -/
theorem weakApprox_dqcX_of_gluing [HasCoproducts.{v} DZ] [HasCoproducts.{v} DX]
    [HasCoproducts.{v} DU] (h09SR : Stacks09SR DX) (hvan : CompactHomZeroAtTop DX) :
    SatisfiesWA DX :=
  (SetupMainMinimal.theorem_1_1 (SchemeOpenClosedDerived.setup I) h09SR).mpr
    (hvan _ _ (SetupMainMinimal.G'_compact (SchemeOpenClosedDerived.setup I))
      (SetupMainMinimal.G'_compact (SchemeOpenClosedDerived.setup I)))

/-- Equivalently, one can supply eventual vanishing only for the chosen middle
compact generator, exactly as in the statement of LP Theorem 1.1. -/
theorem weakApprox_dqcX_of_eventual [HasCoproducts.{v} DZ] [HasCoproducts.{v} DX]
    [HasCoproducts.{v} DU] (h09SR : Stacks09SR DX)
    (hG' : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      ∀ f : I.setup.G' ⟶ I.setup.G'⟦n⟧, f = 0) : SatisfiesWA DX :=
  (SetupMainMinimal.theorem_1_1 (SchemeOpenClosedDerived.setup I) h09SR).mpr hG'

end SchemeOpenClosedDerived
end DerivedInterfaceLemmas

/-! ## A 09SR-free version of the reverse implication

`theorem_1_1` is used above exactly as requested.  Independently, the repository
already contains the compact-vanishing version of Setup 4.4(3).  The following
construction exposes the consequence: for the WA conclusion, the uniform
`CompactHomZeroAtTop` hypothesis suffices without any Stacks 09SR hypothesis.
-/

namespace SetupMainMinimal

section CompactVanishingAlternative

variable {DZ : Type uZ} {DX : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} DX] [Category.{v} DU]
  [Preadditive DZ] [Preadditive DX] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DX] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DX ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor DX n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DX] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DX]
  [CategoryTheory.IsTriangulated DU]

variable (S : SetupMainMinimal DZ DX DU)

include S

/-- Compactness of the open generator, transported from the approximation data. -/
theorem GU_compact : IsCompactAb S.GU := by
  rw [← S.approxU_G]
  exact S.approxU.G_compact

/-- Build `Setup44Reduced` using only uniform positive compact Hom-vanishing.
The common bound is chosen exactly as in `toSetup44Reduced`; the difference is
that `exists_setup_4_4_3_of_compactHomZeroAtTop`, rather than 09SR, supplies the
initial cutoff and vanishing. -/
noncomputable def toSetup44ReducedOfCompactHomZeroAtTop
    (hvan : CompactHomZeroAtTop DX) : Setup44Reduced DZ DX DU := by
  classical
  have hG' : EventuallyHomZero S.G' S.G' :=
    hvan _ _ S.G'_compact S.G'_compact
  have haisle : S.tD.le 0 =
      Coprod (shiftTail (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) 0) :=
    S.tD_compactlyGenerated
  let hex : ∃ A : ℤ, 0 < A ∧
      (∀ {Y : DX}, S.tD.le (-A) Y →
        ∀ f : (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) ⟶ Y, f = 0) :=
    (exists_setup_4_4_3_of_compactHomZeroAtTop S.R S.tD S.G' S.GU S.m
      S.G'_compact S.GU_compact hvan haisle).imp fun A hA => ⟨hA.1, hA.2.2⟩
  let A₀ : ℤ := hex.choose
  have hA₀pos : 0 < A₀ := hex.choose_spec.1
  have hvan₀ : ∀ {Y : DX}, S.tD.le (-A₀) Y →
      ∀ f : (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) ⟶ Y, f = 0 :=
    hex.choose_spec.2
  let A : ℤ := max A₀ (max S.approxZ.A S.approxU.A)
  have hA₀ : A₀ ≤ A := le_max_left _ _
  have hAZ : S.approxZ.A ≤ A :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hAU : S.approxU.A ≤ A :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hpos : 0 < A := lt_of_lt_of_le hA₀pos hA₀
  refine
    { R := S.R
      tD := S.tD
      tZ := S.tZ
      tU := S.tU
      approxZ := S.approxZ.monoBound hAZ
      approxU := S.approxU.monoBound hAU
      GU := S.GU
      G' := S.G'
      G'_compact := S.G'_compact
      G'_generates := S.G'_generates
      G'_eventual := hG'
      m := S.m
      jStar_G'_mem := S.jStar_G'_mem
      normalized_biproduct := S.normalized_biproduct
      tD_compactlyGenerated := S.tD_compactlyGenerated
      tZ_compactlyGenerated := S.tZ_compactlyGenerated
      tU_compactlyGenerated := S.tU_compactlyGenerated
      approxZ_t := S.approxZ_t
      approxU_t := S.approxU_t
      approxZ_G := S.approxZ_G
      approxU_G := S.approxU_G
      A := A
      A_pos := hpos
      approxZ_A := rfl
      approxU_A := rfl
      G_hom_vanishing := fun {Y} hY f =>
        hvan₀ (S.tD.le_monotone (by omega) Y hY) f }

/-- The full Setup 4.4 package, still without 09SR. -/
noncomputable def toSetup44OfCompactHomZeroAtTop (hvan : CompactHomZeroAtTop DX) :
    Setup44 DZ DX DU :=
  (S.toSetup44ReducedOfCompactHomZeroAtTop hvan).toSetup44

/-- **09SR-free reverse gluing.**  The geometric approximation data on the two
ends, the minimal recollement/t-structure package, and positive compact
Hom-vanishing in the middle category imply weak approximability there. -/
theorem satisfiesWA_of_compactHomZeroAtTop [HasCoproducts.{v} DZ]
    [HasCoproducts.{v} DX] [HasCoproducts.{v} DU]
    (hvan : CompactHomZeroAtTop DX) : SatisfiesWA DX :=
  satisfiesWA_of_setup (S.toSetup44OfCompactHomZeroAtTop hvan)

end CompactVanishingAlternative
end SetupMainMinimal

namespace SchemeOpenClosedDerived

section CompactVanishingAlternative

variable {DZ : Type uZ} {DX : Type uD} {DU : Type uU}
  [Category.{v} DZ] [Category.{v} DX] [Category.{v} DU]
  [Preadditive DZ] [Preadditive DX] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject DX] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift DX ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive]
  [∀ (n : ℤ), (shiftFunctor DX n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated DX] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated DX]
  [CategoryTheory.IsTriangulated DU]

variable (I : SchemeOpenClosedDerived DZ DX DU)

include I

/-- The scheme gluing interface with `CompactHomZeroAtTop` as its only external
categorical-vanishing input.  Unlike `weakApprox_dqcX_of_gluing`, this version
requires no Stacks 09SR argument. -/
theorem weakApprox_dqcX_of_compactHomZeroAtTop [HasCoproducts.{v} DZ]
    [HasCoproducts.{v} DX] [HasCoproducts.{v} DU]
    (hvan : CompactHomZeroAtTop DX) : SatisfiesWA DX :=
  SetupMainMinimal.satisfiesWA_of_compactHomZeroAtTop
    (SchemeOpenClosedDerived.setup I) hvan

end CompactVanishingAlternative
end SchemeOpenClosedDerived

end RelativeWeakApprox

#print axioms RelativeWeakApprox.SchemeOpenClosedDerived.weakApprox_dqcX_of_gluing
#print axioms RelativeWeakApprox.SchemeOpenClosedDerived.weakApprox_dqcX_of_eventual
#print axioms RelativeWeakApprox.SchemeOpenClosedDerived.weakApprox_dqcX_of_compactHomZeroAtTop
#print axioms RelativeWeakApprox.SchemeOpenClosedDerived.jShriek_compact
