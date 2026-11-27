/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import SpacesVerified.Affine
import SpacesVerified.Discharge
import SpacesVerified.Statements

/-!
# Full verification of the algebraic-space layer

Discharges every tagged AxiomMath input of the `Spaces` library by the AxiomMath
theorem it names (`SpacesVerified/Discharge.lean`, `Statements.lean`, `Affine.lean`), so that the results over algebraic
spaces hold unconditionally with axioms `propext`, `Classical.choice`, `Quot.sound` only.
Building it compiles AxiomMath theorem modules beyond `Spaces`' definitions; see README, "Building".
-/
