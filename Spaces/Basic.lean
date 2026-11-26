/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import StacksFrontier.AlgebraicGeometry.Spaces.Category
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory

/-!
# The algebraic-space layer: entry point

GL26 §2.2 (`sec:preliminaries_stacks`) works with algebraic spaces over a fixed base
scheme, following the Stacks Project.  This library builds GL26's notions on
AxiomMath/Stacks' definitions (`AlgebraicGeometry.AlgebraicSpaces`, the small étale
site, `D(𝒪_X)`, `D_QCoh`); see `results/AXIOMMATH_MAP.md` for the fidelity audit of
each definition.  This file only fixes the base imports.  The notions are in
`Spaces/Categories.lean` (`D`, `D_qc`, `D^b_qc`, `D^-_coh`, `D^b_coh`, `Perf`, support,
`D_{qc,T}`), `Spaces/Functors.lean` (`Lf^*`, `Rf_*`, `⊗^L`), `Spaces/RelativePerfect.lean`
(GL26 Definitions 4.1 and 5.1), `Spaces/IntegralTransform.lean` (`Φ_K`),
`Spaces/AxiomMathInputs.lean` (tagged inputs) and `Spaces/NonVacuity.lean`.
-/
