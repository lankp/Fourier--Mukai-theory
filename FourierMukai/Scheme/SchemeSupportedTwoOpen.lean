/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Scheme.SchemeWeakApproxStatement
import FourierMukai.Scheme.PaperTwoOpenGluing

/-!
# Neeman weak approximability from open--closed gluing

This file connects the zero-detection LP gluing theorem to the concrete scheme
statement layer `SchemeWeakApproxStatementM1`.  In particular the conclusions
are `NeemanWeakApproximability` and `NeemanSupportedWeakApproximability`, not
merely `SatisfiesPaperWA`: the approximation data have the restricted standard
`t`-structure.

The two-open theorem takes supported approximation data on the second open and
transports them through an explicit excision equivalence.  This is the correct
recollement input.  If `X = U ∪ V` and `Z = X \ U`, the open--closed sequence is

`D_qc,Z(X) → D_qc(X) → D_qc(U)`,

and excision identifies its left term with `D_qc,Z(V)`.  Bare approximation
data on `D_qc(V)` are not the required left endpoint.  When gluing a supported
category `D_qc,S(X)`, all three categories acquire the compatible support
condition; that form is `neemanSupportedWeakApproximability_of_excision`.

The geometric recollement, excision, compactly-generated-aisle equalities and
compact/perfect comparisons remain fields of the input.  None of them is
asserted as a global instance here.
-/

@[expose] public section

namespace RelativeFM.SchemeSupportedTwoOpenM3

open RelativeFM RelativeFM.SchemeWeakApproxStatementM1
open RelativeWeakApprox RelativeWeakApprox.PaperM2
open RelativeWeakApprox.SchemeTwoOpenM3
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry
open scoped AlgebraicGeometry ZeroObject

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The closed complement already carried by `SchemeOpenClosed`, packaged as
an element of `TopologicalSpace.Closeds`. -/
abbrev closedComplement (g : SchemeOpenClosed.{u}) : TopologicalSpace.Closeds g.X :=
  ⟨g.Z, g.Z_closed⟩

/-- Open--closed LP data for an ordinary `D_qc` middle category and the
concrete supported category on the displayed closed complement. -/
abbrev DqcNeemanOpenClosedInput (g : SchemeOpenClosed.{u}) :=
  PaperSchemeOpenClosedDerived
    (DqcSupported g.X (closedComplement g)) (Dqc g.X) (Dqc g.U)

/-- Open--closed LP data for a supported middle category.  `SX` is the support
retained in the conclusion, `SZ` is the closed-support left endpoint, and `SU`
is the support on the open endpoint.  A geometric instantiation must identify
these with the corresponding intersections. -/
abbrev DqcSupportedNeemanOpenClosedInput (g : SchemeOpenClosed.{u})
    (SX SZ : TopologicalSpace.Closeds g.X)
    (SU : TopologicalSpace.Closeds g.U) :=
  PaperSchemeOpenClosedDerived
    (DqcSupported g.X SZ) (DqcSupported g.X SX) (DqcSupported g.U SU)

/-- The same ordinary gluing data without a closed approximation package. -/
abbrev DqcNeemanOpenClosedSeed (g : SchemeOpenClosed.{u}) :=
  PaperSchemeOpenClosedSeed
    (DqcSupported g.X (closedComplement g)) (Dqc g.X) (Dqc g.U)

/-- Supported gluing data without a closed approximation package. -/
abbrev DqcSupportedNeemanOpenClosedSeed (g : SchemeOpenClosed.{u})
    (SX SZ : TopologicalSpace.Closeds g.X)
    (SU : TopologicalSpace.Closeds g.U) :=
  PaperSchemeOpenClosedSeed
    (DqcSupported g.X SZ) (DqcSupported g.X SX) (DqcSupported g.U SU)

/-- **Ordinary Neeman gluing in the repository's model.**  The equality `htD`
is precisely the assertion that the glued middle `t`-structure is the
restricted standard one.  The input contains approximation data only on the
open and closed-support ends. -/
theorem neemanWeakApproximability_of_openClosed
    {g : SchemeOpenClosed.{u}} (I : DqcNeemanOpenClosedInput g)
    [HasCoproducts.{u + 1} (DqcSupported g.X (closedComplement g))]
    [HasCoproducts.{u + 1} (Dqc g.X)] [HasCoproducts.{u + 1} (Dqc g.U)]
    (htD : I.setup.tD = dqcStandardTStructure g.X)
    (hvan : CompactHomZeroAtTop (Dqc g.X)) :
    NeemanWeakApproximability g.X := by
  obtain ⟨W, ht, _⟩ := I.exists_paperData_of_compactHomZeroAtTop hvan
  exact ⟨⟨W, ht.trans htD⟩⟩

/-- **Neeman's supported gluing statement.**  The output is exactly
`DqcSupportedStandardPaperWeakApproximationData` for `D_qc,SX(X)`. -/
theorem neemanSupportedWeakApproximability_of_openClosed
    {g : SchemeOpenClosed.{u}} {SX SZ : TopologicalSpace.Closeds g.X}
    {SU : TopologicalSpace.Closeds g.U}
    (I : DqcSupportedNeemanOpenClosedInput g SX SZ SU)
    [HasCoproducts.{u + 1} (DqcSupported g.X SZ)]
    [HasCoproducts.{u + 1} (DqcSupported g.X SX)]
    [HasCoproducts.{u + 1} (DqcSupported g.U SU)]
    (htD : I.setup.tD = dqcSupportedStandardTStructure g.X SX)
    (hvan : CompactHomZeroAtTop (DqcSupported g.X SX)) :
    NeemanSupportedWeakApproximability g.X SX := by
  obtain ⟨W, ht, _⟩ := I.exists_paperData_of_compactHomZeroAtTop hvan
  exact ⟨⟨W, ht.trans htD⟩⟩

/-- **The two-open step, ordinary form.**  In the intended application `V` is
the second open of a cover of `g.X`, `SV` is the restriction of the closed
complement of `g.U` to `V`, and `F` is supported excision.  `WV` is standard
supported approximation data on `V`.

Only two compatibility conditions remain after excision: the transported
standard `t`-structure is the setup's supported `tZ`-structure, and the
transported generator is the setup's normalized supported generator.  The
conclusion has the restricted standard `t`-structure on `g.X`. -/
theorem neemanWeakApproximability_of_excision
    {g : SchemeOpenClosed.{u}} (I : DqcNeemanOpenClosedSeed g)
    (V : Scheme.{u}) (SV : TopologicalSpace.Closeds V)
    (F : DqcSupported V SV ⥤ DqcSupported g.X (closedComplement g))
    [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (WV : DqcSupportedStandardPaperWeakApproximationData V SV)
    [HasCoproducts.{u + 1} (DqcSupported g.X (closedComplement g))]
    [HasCoproducts.{u + 1} (Dqc g.X)] [HasCoproducts.{u + 1} (Dqc g.U)]
    (htZ : transportTStructure F (dqcSupportedStandardTStructure V SV) = I.setup.tZ)
    (hGZ : (SchemeTwoOpenM3.transportPaperWeakApproximationData F WV.1).G =
      I.setup.R.iStar.obj
        (I.setup.G'⟦I.setup.m⟧ ⊞ I.setup.R.jShriek.obj I.setup.GU))
    (htD : I.setup.tD = dqcStandardTStructure g.X)
    (hvan : CompactHomZeroAtTop (Dqc g.X)) :
    NeemanWeakApproximability g.X := by
  have htW : (SchemeTwoOpenM3.transportPaperWeakApproximationData F WV.1).t = I.setup.tZ := by
    rw [SchemeTwoOpenM3.transportPaperWeakApproximationData_t, WV.2]
    exact htZ
  let J := PaperSchemeOpenClosedSeed.toPaperSchemeOpenClosedDerived
    (I := I) (WZ := SchemeTwoOpenM3.transportPaperWeakApproximationData F WV.1)
    (ht := htW) (hG := hGZ)
  obtain ⟨W, ht, _⟩ := J.exists_paperData_of_compactHomZeroAtTop hvan
  exact ⟨⟨W, ht.trans htD⟩⟩

/-- **The two-open step for Neeman's full supported target.**  The standard
supported approximation data on `(V, SV)` are transported through excision and
replace the left endpoint of the recollement.  No approximation data on the
middle category are assumed. -/
theorem neemanSupportedWeakApproximability_of_excision
    {g : SchemeOpenClosed.{u}} {SX SZ : TopologicalSpace.Closeds g.X}
    {SU : TopologicalSpace.Closeds g.U}
    (I : DqcSupportedNeemanOpenClosedSeed g SX SZ SU)
    (V : Scheme.{u}) (SV : TopologicalSpace.Closeds V)
    (F : DqcSupported V SV ⥤ DqcSupported g.X SZ)
    [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (WV : DqcSupportedStandardPaperWeakApproximationData V SV)
    [HasCoproducts.{u + 1} (DqcSupported g.X SZ)]
    [HasCoproducts.{u + 1} (DqcSupported g.X SX)]
    [HasCoproducts.{u + 1} (DqcSupported g.U SU)]
    (htZ : transportTStructure F (dqcSupportedStandardTStructure V SV) = I.setup.tZ)
    (hGZ : (SchemeTwoOpenM3.transportPaperWeakApproximationData F WV.1).G =
      I.setup.R.iStar.obj
        (I.setup.G'⟦I.setup.m⟧ ⊞ I.setup.R.jShriek.obj I.setup.GU))
    (htD : I.setup.tD = dqcSupportedStandardTStructure g.X SX)
    (hvan : CompactHomZeroAtTop (DqcSupported g.X SX)) :
    NeemanSupportedWeakApproximability g.X SX := by
  have htW : (SchemeTwoOpenM3.transportPaperWeakApproximationData F WV.1).t = I.setup.tZ := by
    rw [SchemeTwoOpenM3.transportPaperWeakApproximationData_t, WV.2]
    exact htZ
  let J := PaperSchemeOpenClosedSeed.toPaperSchemeOpenClosedDerived
    (I := I) (WZ := SchemeTwoOpenM3.transportPaperWeakApproximationData F WV.1)
    (ht := htW) (hG := hGZ)
  obtain ⟨W, ht, _⟩ := J.exists_paperData_of_compactHomZeroAtTop hvan
  exact ⟨⟨W, ht.trans htD⟩⟩

end
end RelativeFM.SchemeSupportedTwoOpenM3

#print axioms RelativeFM.SchemeSupportedTwoOpenM3.neemanWeakApproximability_of_openClosed
#print axioms RelativeFM.SchemeSupportedTwoOpenM3.neemanSupportedWeakApproximability_of_openClosed
#print axioms RelativeFM.SchemeSupportedTwoOpenM3.neemanWeakApproximability_of_excision
#print axioms RelativeFM.SchemeSupportedTwoOpenM3.neemanSupportedWeakApproximability_of_excision
