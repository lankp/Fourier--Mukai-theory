## Your task: `wave11/verified` (Opus, effort: high; full AxiomMath build)

Goal: the `SpacesVerified` forms of wave 11's results, every tagged-input hypothesis discharged
by its AxiomMath theorem.  Build regime of `results/swarm/archive/wave9/verified.md`.

Notes from the merges:
* `wave11/gl26-quasi-perfect` (merged `54381a7`): discharge `Tag09JBInput`, `Tag0GFHInput`,
  `Tag0GFIInput` (of `Spaces/QuasiPerfect/Inputs.lean`; distinct from the one in
  `Spaces/Supported/`), `QcohTruncLEInput`, `StructureSheafQcohInput`; `SpacesVerified` forms of
  `lemma_5_9`, `lemma_5_3_tensor`, `lemma_5_3_bounded`.
* `wave11/gl26-kernels` (merged `b228f65`): no new input; `SpacesVerified` forms of `lemma_2_25`, `lemma_2_26`.
* `wave11/gl26-box-generation` (merged `edce58a`): discharge `EtaleBaseChangeInput` (Stacks 08GE:
  `fun sq hg K => isIso_smallEtaleDerivedModuleBaseChangeMap _ _ _ _ sq hg K`); prove **GL26
  Lemma 5.4** (`lem:neeman2023cor5_10`) in general: `lemma_5_4_of_factorization` with the
  relative-Spec factorization of the quasi-affine `U ×_T Y₂ → Y₂` (GL26 Lemma 2.17; as for the
  general Lemma 3.2 in `wave10/verified`, `SpacesVerified/`), i.e. `Lemma54Statement`.
* (the other wave 11 merges add their notes here)

Pin the new headline declarations in `StatementCheckVerified.lean`, run
`scripts/check_statements.sh --verified` and report the drift (do not `--update`).  Seven
verification steps.  Commit verified pieces as you go.
