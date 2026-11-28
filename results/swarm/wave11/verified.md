## Your task: `wave11/verified` (Opus, effort: high; full AxiomMath build)

Goal: the `SpacesVerified` forms of wave 11's results, every tagged-input hypothesis discharged
by its AxiomMath theorem.  Build regime of `results/swarm/wave9/verified.md`.

Notes from the merges:
* `wave11/gl26-quasi-perfect` (merged `54381a7`): discharge `Tag09JBInput`, `Tag0GFHInput`,
  `Tag0GFIInput` (of `Spaces/QuasiPerfect/Inputs.lean`; distinct from the one in
  `Spaces/Supported/`), `QcohTruncLEInput`, `StructureSheafQcohInput`; `SpacesVerified` forms of
  `lemma_5_9`, `lemma_5_3_tensor`, `lemma_5_3_bounded`.
* (the other wave 11 merges add their notes here)

Pin the new headline declarations in `StatementCheckVerified.lean`, run
`scripts/check_statements.sh --verified` and report the drift (do not `--update`).  Seven
verification steps.  Commit verified pieces as you go.
