## Your task: `wave8/neeman-approximability` (effort: high)

Goal: the part of Neeman's approximability theory (Neeman 2024 and the papers it rests on) that
GL26 Lemma A.9 (`lem:preferred_eq_class`) and LP26 Corollary 1.2 need over qcqs algebraic spaces,
proved here (AxiomMath does not contain it; Neeman is not an allowed assumption): the standard
`t`-structure on `D_qc,Z(X)` is in the preferred equivalence class.  Follow the affine proof
`NeemanPreferredM6.inPreferredClass_of_compactlyGenerated` and the wave 7 result
(`Spaces/Supported/`, compact generation of `D_qc,Z(X)` by one perfect generator).

Branch `wave8/neeman-approximability` from `origin/formalization` (after `wave8/universe-bridge`
if you need its universes; coordinate through the orchestrator).  Files: `Spaces/Supported/`.
Tagged AxiomMath inputs in `Spaces/Supported/Inputs.lean`.  Report what of Neeman's theory you
needed, by result number.  Seven verification steps, `lake build Spaces`, both statement checks.
