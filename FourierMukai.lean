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
import FourierMukai.Scheme.WeakApprox
import FourierMukai.Scheme.OpenImmersion
import FourierMukai.Scheme.Derived
import FourierMukai.Scheme.QCohSerre
import FourierMukai.Scheme.QCohSerreExtension
import FourierMukai.Scheme.Statements
import FourierMukai.Scheme.Duality
import FourierMukai.Scheme.Lemma54
import FourierMukai.Scheme.PerfectRing
import FourierMukai.Scheme.PerfectField
import FourierMukai.Scheme.PerfectModel
import FourierMukai.Scheme.PerfectModelConverse
import FourierMukai.Scheme.Affine
import FourierMukai.Scheme.AffineCoproducts
import FourierMukai.Scheme.AffineRecollement
import FourierMukai.Scheme.AffineMain
import FourierMukai.Scheme.AffineDictionary
import FourierMukai.Scheme.AffineQCoh
import FourierMukai.Scheme.AffineDiagonal
import FourierMukai.Scheme.Perfect
import FourierMukai.Scheme.PerfectRingStacks

/-!
# Relative Fourier--Mukai theory for algebraic spaces: Lean formalization

Root module.  See `results/REPORT.md` for the state of the formalization, the
inventory of missing prerequisites, and the list of statements that are stated
but not proved.
-/
