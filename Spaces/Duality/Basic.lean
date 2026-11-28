/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Duality.Inputs
import Spaces.Statements.Notions
import Spaces.LP26.Inputs

/-!
# The functors of GL26 §2.4 over algebraic spaces: `(Sp/S)_{Noeth,sep,fp}`, `f^×`, `f^!`

Guisado Villalgordo–Lank (GL26), §2.4 (`sec:duality`), subsections `sec:duality_2cats` and
`sec:duality_functors`:

* the category `(Sp/S)_{Noeth,sep,fp}`: Noetherian algebraic spaces and separated morphisms of
  finite presentation (`IsNoethSepFpHom`);
* a **Nagata compactification** `f = p ∘ j` of a morphism `f`: `j` an open immersion, `p`
  proper (`Compactification`);
* **`f^×`**, the right adjoint of `Rf_* : D_qc(Y) ⥤ D_qc(X)` (`upperTimes`, with the
  adjunction `upperTimesAdj`), for `f` a quasi-compact quasi-separated morphism between
  quasi-compact quasi-separated spaces (Stacks 0E55, `Tag0E55Input`);
* the pseudofunctoriality isomorphism **`δ(f,g) : (g ∘ f)^× ≅ f^× ∘ g^×`** (`upperTimesCompIso`);
* **`f^! := Lj^* ∘ p^×`** for a compactification `f = p ∘ j` (`upperShriek`).

## Rendering and differences from GL26

* **The 2-category.**  GL26's `Sp/S` is a `(2,1)`-category whose 2-morphisms are invertible
  (Stacks 003S); for algebraic spaces, i.e. sheaves of sets, the 2-morphisms between two
  1-morphisms are identities, and the category of AxiomMath's `AlgebraicSpaces B S hS`
  (Stacks 025Y) is the underlying 1-category.  `(Sp/S)_{Noeth,sep,fp}` is rendered by the
  property `IsNoethSepFpHom f` of a morphism (source and target Noetherian, `f` separated and of
  finite presentation).
* **`f^!` depends on the chosen compactification.**  GL26 defines `f^!` by Neeman's
  Construction 9.4: "if `f = p ∘ j` is a Nagata compactification, then `f^! := Lj^* ∘ p^×`".
  Here `upperShriek c` is that functor for the compactification `c`; that it does not depend on
  `c` up to isomorphism is part of Neeman's theory and is not proved here.  The statements of
  `Spaces/Duality/` are made for *every* compactification, which is the strongest reading.
  Existence of a compactification is Nagata's theorem for algebraic spaces (Stacks 0F4D,
  AxiomMath's `hasCompactification_of_isSeparated_of_isFiniteType`); it is not needed for the
  statements here, which quantify over compactifications.
* **Domains.**  `f^×` and `f^!` are functors `D_qc(X) ⥤ D_qc(Y)` between the full subcategories
  `(Dqc X).FullSubcategory` of `D(𝒪)` (GL26: "on `D_qc`").  `Rf_*` on `D_qc` is
  `Spaces.pushQc` (Stacks 08FA (1)), `Lj^*` on `D_qc` is `Spaces.pullQc` (Stacks 08F4).
* `f^×` is Mathlib's `Functor.rightAdjoint` of `Rf_*` under the `IsLeftAdjoint` instance given
  by Stacks 0E55; this is AxiomMath's definition of the twisted inverse image
  (`quasicoherentDerivedRightAdjoint`, `twistedInverseImage`), whose module is outside the import
  list.  Any right adjoint is uniquely isomorphic to it (`Adjunction.rightAdjointUniq`).

## Assumptions

`Spaces.Tag08FAInput`, `Spaces.Tag08F4Input`, `Tag0E55Input` and `LP26.QuasiCompactSourceInput`
(the source of a quasi-compact morphism to a quasi-compact space is quasi-compact), each an
AxiomMath theorem.  Separated morphisms are quasi-separated and a quasi-separated morphism into a
quasi-separated space has quasi-separated source: AxiomMath theorems in the import closure
(`isQuasiSeparated_of_isSeparated`, Stacks 03KK; `isAbsolutelyQuasiSeparated_of_isQuasiSeparated`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

namespace RelativeFM.Spaces.Duality

open RelativeFM.Spaces RelativeFM.Spaces.Statements

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### Quasi-compact quasi-separated morphisms between qcqs spaces -/

/-- The hypotheses of Stacks 0E55 on a morphism `f : X ⟶ Y`: `X` quasi-compact and
quasi-separated, `Y` quasi-separated, and `f` quasi-compact and quasi-separated (the last two
follow from the first three, Stacks 073B; they are recorded so that `Rf_*` on `D_qc` can be
written). -/
structure IsQcqsHom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Prop where
  srcQc : IsQuasiCompactSpace B S hS X.1
  srcQs : IsAbsolutelyQuasiSeparated B S hS hZ X.1
  tgtQs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1
  qc : IsQuasiCompact B S hS f.hom
  qs : IsQuasiSeparated B S hS f.hom

/-! ### The category `(Sp/S)_{Noeth,sep,fp}` -/

/-- **A 1-morphism of `(Sp/S)_{Noeth,sep,fp}`** (GL26 `sec:duality_2cats`): source and target
are Noetherian algebraic spaces (Stacks 03EA) and `f` is separated (Stacks 03HL) and of finite
presentation (Stacks 03XF, 06G4). -/
structure IsNoethSepFpHom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Prop where
  noetherian_source : IsNoetherianSpace hZ X
  noetherian_target : IsNoetherianSpace hZ Y
  separated : IsSeparated B S hS f.hom
  finitePresentation : IsFinitePresentation B S hS f.hom

variable {hZ} in
/-- A 1-morphism of `(Sp/S)_{Noeth,sep,fp}` satisfies the hypotheses of Stacks 0E55. -/
theorem IsNoethSepFpHom.isQcqsHom {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (hf : IsNoethSepFpHom hZ f) : IsQcqsHom hZ f :=
  ⟨hf.noetherian_source.1, hf.noetherian_source.2.1, hf.noetherian_target.2.1,
    hf.finitePresentation.2.1, hf.finitePresentation.2.2⟩

/-! ### Nagata compactifications -/

/-- **A Nagata compactification** of `f : Y ⟶ X` (GL26 `sec:duality_2cats`; Stacks 0F44):
a factorization `f = p ∘ j` (in Lean, `j ≫ p = f`) with `j : Y ⟶ Y'` an open immersion and
`p : Y' ⟶ X` proper. -/
structure Compactification {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) where
  /-- The compactifying space `Y'`. -/
  space : AlgebraicSpaces B S hS
  /-- The open immersion `j : Y ⟶ Y'`. -/
  j : Y ⟶ space
  /-- The proper morphism `p : Y' ⟶ X`. -/
  p : space ⟶ X
  isOpenImmersion_j : IsOpenImmersion B S hS j.hom
  isProper_p : IsProper B S hS p.hom
  fac : j ≫ p = f

variable {hZ} in
/-- The proper part `p : Y' ⟶ X` of a compactification satisfies the hypotheses of Stacks 0E55
when `X` is quasi-compact and quasi-separated: `p` is quasi-compact (it is of finite type) and
quasi-separated (it is separated, Stacks 03KK), so `Y'` is quasi-compact
(`QuasiCompactSourceInput`) and quasi-separated. -/
theorem Compactification.isQcqsHom_p (hqcs : LP26.QuasiCompactSourceInput B S hS)
    {Y X : AlgebraicSpaces B S hS} {f : Y ⟶ X} (c : Compactification f)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    IsQcqsHom hZ c.p :=
  have hpqs : IsQuasiSeparated B S hS c.p.hom :=
    isQuasiSeparated_of_isSeparated B S hS c.isProper_p.1
  ⟨hqcs X.2 hXqc c.p.hom c.isProper_p.2.1.2,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ c.space.2 hXqs hpqs, hXqs,
    c.isProper_p.2.1.2, hpqs⟩

/-! ### `f^×` -/

section UpperTimes

variable (h08FA : Tag08FAInput B S hS) (h0E55 : Tag0E55Input B S hS)

include h0E55 in
variable {hZ} in
/-- `Rf_* : D_qc(X) ⥤ D_qc(Y)` is a left adjoint (Stacks 0E55, `Tag0E55Input`). -/
theorem isLeftAdjoint_pushQc {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsQcqsHom hZ f) :
    (pushQc h08FA f hf.qc hf.qs).IsLeftAdjoint :=
  h0E55 hZ f hf.srcQc hf.srcQs hf.tgtQs _

variable {hZ} in
/-- **`f^× : D_qc(Y) ⥤ D_qc(X)`** (GL26 `sec:duality_functors`): the right adjoint of
`Rf_* : D_qc(X) ⥤ D_qc(Y)`, which exists by Stacks 0E55. -/
def upperTimes {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsQcqsHom hZ f) :
    (Dqc Y).FullSubcategory ⥤ (Dqc X).FullSubcategory :=
  haveI := isLeftAdjoint_pushQc h08FA h0E55 f hf
  (pushQc h08FA f hf.qc hf.qs).rightAdjoint

variable {hZ} in
/-- The adjunction `Rf_* ⊣ f^×` on `D_qc`; its counit is the trace map (Stacks 0E5K). -/
def upperTimesAdj {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsQcqsHom hZ f) :
    pushQc h08FA f hf.qc hf.qs ⊣ upperTimes h08FA h0E55 f hf :=
  haveI := isLeftAdjoint_pushQc h08FA h0E55 f hf
  Adjunction.ofIsLeftAdjoint _

/-- `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` on `D_qc` (Stacks 0D6E, AxiomMath's
`smallEtaleDerivedPushforwardCompIso`, restricted to the full subcategories). -/
def pushQcCompIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom)
    (hfgqc : IsQuasiCompact B S hS (f ≫ g).hom) (hfgqs : IsQuasiSeparated B S hS (f ≫ g).hom) :
    pushQc h08FA f hfqc hfqs ⋙ pushQc h08FA g hgqc hgqs ≅ pushQc h08FA (f ≫ g) hfgqc hfgqs :=
  NatIso.ofComponents
    (fun E => ObjectProperty.isoMk _ ((smallEtaleDerivedPushforwardCompIso B S hS f g).app E.obj))
    (fun φ => ObjectProperty.hom_ext _
      ((smallEtaleDerivedPushforwardCompIso B S hS f g).hom.naturality φ.hom))

variable {hZ} in
/-- **`δ(f,g) : (g ∘ f)^× ≅ f^× ∘ g^×`** (GL26 `sec:duality_functors`; in Lean `f ≫ g` is
`g ∘ f`): the pseudofunctoriality of `(-)^×`, by uniqueness of right adjoints from
`R(g ∘ f)_* ≅ Rg_* ∘ Rf_*` (Mathlib's `Adjunction.comp`, `Adjunction.rightAdjointUniq`). -/
def upperTimesCompIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsQcqsHom hZ f) (hg : IsQcqsHom hZ g) (hfg : IsQcqsHom hZ (f ≫ g)) :
    upperTimes h08FA h0E55 (f ≫ g) hfg ≅ upperTimes h08FA h0E55 g hg ⋙ upperTimes h08FA h0E55 f hf :=
  (upperTimesAdj h08FA h0E55 (f ≫ g) hfg).rightAdjointUniq
    (((upperTimesAdj h08FA h0E55 f hf).comp (upperTimesAdj h08FA h0E55 g hg)).ofNatIsoLeft
      (pushQcCompIso h08FA f g hf.qc hf.qs hg.qc hg.qs hfg.qc hfg.qs))

end UpperTimes

/-! ### `f^!` -/

variable (h08FA : Tag08FAInput B S hS) (h08F4 : Tag08F4Input B S hS)
  (h0E55 : Tag0E55Input B S hS) (hqcs : LP26.QuasiCompactSourceInput B S hS)

variable {hZ} in
/-- **`f^! := Lj^* ∘ p^×`** (GL26 `sec:duality_functors`, Neeman's Construction 9.4) for a
Nagata compactification `c : f = p ∘ j` of `f : Y ⟶ X`, `X` quasi-compact and quasi-separated:
the functor `D_qc(X) ⥤ D_qc(Y)`, `E ↦ Lj^*(p^× E)`. -/
def upperShriek {Y X : AlgebraicSpaces B S hS} {f : Y ⟶ X} (c : Compactification f)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    (Dqc X).FullSubcategory ⥤ (Dqc Y).FullSubcategory :=
  upperTimes h08FA h0E55 c.p (c.isQcqsHom_p hqcs hXqc hXqs) ⋙ pullQc h08F4 c.j

end RelativeFM.Spaces.Duality
