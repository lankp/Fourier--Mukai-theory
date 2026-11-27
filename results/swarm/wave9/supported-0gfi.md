## Your task: `wave9/supported-0gfi` (effort: high)

Goal: prove `SupportedDetectsBelowStatement X T` (`Spaces/Supported/Preferred.lean`), the
supported form of Stacks 0GFI, for every closed `T` with quasi-compact complement, so that GL26
Lemma A.9's preferred-class clause (`lem:preferred_eq_class`) holds for general supports, not
only `T = |X|`.  wave 8 found that it needs AxiomMath's machinery of elementary distinguished
squares (outside the import list): add the definition modules you need to
`scripts/axiommath/spaces-imports.txt` (check with `scripts/axiommath/built.py`) and take the
theorems as tagged inputs in `Spaces/Supported/Inputs.lean`.  Files: `Spaces/Supported/`.
Commit verified pieces as you go.  Seven verification steps; `lake build Spaces`.
