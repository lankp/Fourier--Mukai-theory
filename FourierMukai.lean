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
import FourierMukai.Scheme.Inputs
import FourierMukai.Scheme.WeakApprox
import FourierMukai.Scheme.OpenImmersion
import FourierMukai.Scheme.Derived
import FourierMukai.Scheme.Statements
import FourierMukai.Scheme.Duality
import FourierMukai.Scheme.PerfectRing
import FourierMukai.Scheme.Affine
import FourierMukai.Paper.Statements
import FourierMukai.Paper.InterfaceAudit
import FourierMukai.Examples.Identity

/-!
# Relative Fourier--Mukai theory for algebraic spaces: Lean formalization

Root module.  See `results/REPORT.md` for the state of the formalization, the
inventory of missing prerequisites, and the list of statements that are stated
but not proved.
-/
