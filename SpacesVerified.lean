/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces

/-!
# Full verification of the algebraic-space layer

Discharges every tagged AxiomMath input of the `Spaces` library by the AxiomMath
theorem it names, so that the headline statements hold unconditionally with axioms
`propext`, `Classical.choice`, `Quot.sound` only.  Building it compiles the AxiomMath
theorems themselves (~8 500 modules); see README, "Full verification".  Empty until
`Spaces` has tagged inputs.
-/
