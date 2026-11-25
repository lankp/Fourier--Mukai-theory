/-
Copyright (c) 2026 Relative Fourier--Mukai formalization project.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FourierMukai.Prelim.Triangulated
import FourierMukai.Prelim.Coproduct
import FourierMukai.Prelim.EssentiallyDense
import FourierMukai.Prelim.Mates
import FourierMukai.Prelim.Lemma25
import FourierMukai.Prelim.Thickness
import FourierMukai.Prelim.Generation
import FourierMukai.Paper.DerivedSetup
import FourierMukai.Paper.Statements
import FourierMukai.Paper.InterfaceAudit
import FourierMukai.Examples.Identity
import FourierMukai.Scheme.Inputs
import FourierMukai.Scheme.DerivedCoproducts
import FourierMukai.Scheme.KProjectiveResolution
import FourierMukai.Scheme.SpecialDirectLimits
import FourierMukai.Scheme.SpaltensteinStage
import FourierMukai.Scheme.SpaltensteinIteration
import FourierMukai.Scheme.SpaltensteinColimit
import FourierMukai.Scheme.SpaltensteinReplacement
import FourierMukai.Scheme.SpaltensteinCanonicalTruncation
import FourierMukai.Scheme.SpaltensteinSequentialComparisons
import FourierMukai.Scheme.SpaltensteinTheoremC
import FourierMukai.Scheme.AffineSpaltenstein
import FourierMukai.Scheme.ProjectiveModel
import FourierMukai.Scheme.SmallObjectPresentable
import FourierMukai.Scheme.GeneratingCofibrations
import FourierMukai.Scheme.WeakApprox
import FourierMukai.Scheme.OpenImmersion
import FourierMukai.Scheme.Derived
import FourierMukai.Scheme.QCohSerre
import FourierMukai.Scheme.QCohSerreExtension
import FourierMukai.Scheme.QCohSerreExtension01IE
import FourierMukai.Scheme.Statements
import FourierMukai.Scheme.Duality
import FourierMukai.Scheme.DerivedTensorHomClosed
import FourierMukai.Scheme.Lemma54
import FourierMukai.Scheme.PerfectRing
import FourierMukai.Scheme.PerfectField
import FourierMukai.Scheme.PerfectModel
import FourierMukai.Scheme.PerfectModelConverse
import FourierMukai.Scheme.LeChen
import FourierMukai.Scheme.Affine
import FourierMukai.Scheme.AffineCoproducts
import FourierMukai.Scheme.AffineBoundedAboveCoproducts
import FourierMukai.Scheme.AffineUniverse
import FourierMukai.Scheme.AisleCoproducts
import FourierMukai.Scheme.SmallAffineAssembly
import FourierMukai.Scheme.AffineRecollement
import FourierMukai.Scheme.AffineLocalCohomology
import FourierMukai.Scheme.AffineGluing
import FourierMukai.Scheme.AffineLocalCohomologyRingObject
import FourierMukai.Scheme.AffineLocalCohomologySupport
import FourierMukai.Scheme.AffineMixedZero
import FourierMukai.Scheme.AffineIShriek
import FourierMukai.Scheme.AffineSupportedTStructure
import FourierMukai.Scheme.AffineSupportedAisle
import FourierMukai.Scheme.AffineSupportedCoprodLift
import FourierMukai.Scheme.AffineKoszulGenerator
import FourierMukai.Scheme.AisleGenBrutal
import FourierMukai.Scheme.AisleGenBounded
import FourierMukai.Scheme.AisleGenFiltration
import FourierMukai.Scheme.AisleGenUnbounded
import FourierMukai.Scheme.AisleGenFreeResolution
import FourierMukai.Scheme.AisleGenDerivedCoproduct
import FourierMukai.Scheme.AisleGenRingAisle
import FourierMukai.Scheme.AisleGenRingGeneration
import FourierMukai.Scheme.AisleGenDD
import FourierMukai.Scheme.AffineSpecificAisleGeneration
import FourierMukai.Scheme.AffineRecollementAssembly
import FourierMukai.Scheme.AffineSetupInventory
import FourierMukai.Scheme.AffineJUpperAdjoint
import FourierMukai.Scheme.AffineSecondGluing
import FourierMukai.Scheme.AffineSecondGluingAssembly
import FourierMukai.Scheme.AffineJUpperTensorHom
import FourierMukai.Scheme.AffineJUpperCandidateRefuted
import FourierMukai.Scheme.AffineSupportedAssembly
import FourierMukai.Scheme.AffineMain
import FourierMukai.Scheme.AffineDictionary
import FourierMukai.Scheme.AffineQCoh
import FourierMukai.Scheme.AffineDiagonal
import FourierMukai.Scheme.AffineConvolution
import FourierMukai.Scheme.ConvolutionCounterexample
import FourierMukai.Scheme.Perfect
import FourierMukai.Scheme.StacksInput
import FourierMukai.Scheme.KProjHomComplex
import FourierMukai.Scheme.KProjIndependence
import FourierMukai.Scheme.KProjHomContravariant
import FourierMukai.Scheme.FixedDerivedTensorHom
import FourierMukai.Scheme.AffineDerivedTensorHom
import FourierMukai.Scheme.TensorHom
import FourierMukai.Scheme.PerfectRingStacks
import FourierMukai.Scheme.PerfectCompactThick
import FourierMukai.Scheme.CompactToPerfect
import FourierMukai.Scheme.Affine066S

/-!
# Relative Fourier--Mukai theory for algebraic spaces: Lean formalization

Root module.  See `results/REPORT.md` for the state of the formalization, the
inventory of missing prerequisites, and the list of statements that are stated
but not proved.
-/
