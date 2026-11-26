## Your task: `wave7/spaces-compact-generation` (effort: high)

Goal: **GL26 Lemma A.9 (`lem:preferred_eq_class`) / Neeman 2024 Thm 3.2(iii) over algebraic
spaces**, from AxiomMath, so that `SupportedCategoryInput.neeman_3_2_iii`
(`results/OPEN_INPUTS.md` row 2.10, not a permitted input) gets a proved replacement: for a
qcqs algebraic space `X` and a closed `Z` with quasi-compact complement, `D_qc,Z(X)`
(`Spaces.DqcSupported`) has a single compact generator, is compactly generated, its compact
objects are the perfect complexes supported on `Z`, and its standard `t`-structure is in the
preferred equivalence class (`InPreferredClass`, as in the affine proof
`NeemanPreferredM6.inPreferredClass_of_compactlyGenerated`).

Branch `wave7/spaces-compact-generation` from `origin/formalization`.  Files:
`Spaces/Supported/*.lean` (namespace `RelativeFM.Spaces.Supported`),
`Spaces/Supported/Inputs.lean` for tagged inputs, `Spaces.lean` (one import line),
`Spaces/Audit.lean` (append only), `scripts/axiommath/spaces-imports.txt` (definitions only).

AxiomMath modules to read (theorems become tagged inputs): `Spaces/Perfect/SupportedPerfectGenerator`,
`Spaces/Perfect/SupportedCompactPerfect`, `Spaces/Perfect/SupportedQuasicoherentDerived`,
`Spaces/CompactGeneration/QcqsCompactGeneration`, `Spaces/Perfect/PerfectCompactQcqs`
(paths under `StacksFrontier/AlgebraicGeometry/`; Stacks 0AEC, 0AED, 09M8).  09SR is already a
theorem (`Spaces.Stacks.tag09SRPaper`); use the bridges in `Spaces/Stacks/Bridges.lean`.

Headlines with docstrings citing GL26 Lemma A.9 by number and label; any difference from the
paper's statement stated precisely (the statement text is not in the repository: if you
need more than `results/COVERAGE.md` says, stop and report).  Non-vacuity: `Z = ∅` or an
affine `X`.  Report every tagged input you add.  Seven verification steps for `lake build
Spaces`; default build and both statement checks unaffected.
