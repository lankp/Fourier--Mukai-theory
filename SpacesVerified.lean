/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import SpacesVerified.Affine
import SpacesVerified.BaseChange
import SpacesVerified.Coherence
import SpacesVerified.Detecting
import SpacesVerified.Discharge
import SpacesVerified.LocallySmall
import SpacesVerified.LP26
import SpacesVerified.LP26Inputs
import SpacesVerified.StandardWA
import SpacesVerified.Statements
import SpacesVerified.Supported

/-!
# Full verification of the algebraic-space layer

Discharges every tagged AxiomMath input of the `Spaces` library by the AxiomMath
theorem it names (`SpacesVerified/Discharge.lean`, `Statements.lean`, `Affine.lean`,
`Supported.lean`, `BaseChange.lean`, `LP26Inputs.lean`, `Detecting.lean`;
consequences in `LP26.lean`, `StandardWA.lean`, `LocallySmall.lean`, `Coherence.lean`), so that the results over algebraic
spaces hold unconditionally with axioms `propext`, `Classical.choice`, `Quot.sound` only.
Building it compiles AxiomMath theorem modules beyond `Spaces`' definitions; see README, "Building".
-/
