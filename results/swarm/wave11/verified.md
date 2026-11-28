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
* `wave11/gl26-pullback-hom` (merged `81a3d9b`): no new input; `SpacesVerified` forms of
  `lemma_2_10_naturality_M`, `lemma_2_10_naturality_K`.  Also prove **GL26 Lemma 2.16 (2)**
  (`lem:gortz_wedhorn_internal_hom2`) in `SpacesVerified/` directly: `ρ_f` invertible for `E`
  pseudo-coherent, `G ∈ D^+_qc`, `f` of finite Tor dimension (`HasFiniteTorDimension`), by
  (1) conservativity of affine étale charts of `Y` (`isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace`),
  (2) refining through affine étale charts of `X`, (3) the composition law
  (`smallEtaleDerivedPullbackSheafHomMap_comp`) and the étale case
  (`isIso_smallEtaleDerivedPullbackSheafHomMap_of_isEtale`), (4) the affine case
  (`isIso_smallEtaleDerivedPullbackSheafHomMap_of_isAffineHom_of_isPseudoCoherent`, with
  `hasFiniteTorDimension_derivedPushforward_structureDerived_representedSpaceMap`); then
  `lemma_2_16_pseudoCoherent_of_isIso` (`Spaces/InternalHom/Pullback.lean`).
* (the other wave 11 merges add their notes here)

Pin the new headline declarations in `StatementCheckVerified.lean`, run
`scripts/check_statements.sh --verified` and report the drift (do not `--update`).  Seven
verification steps.  Commit verified pieces as you go.

Timing: launched while `wave10/verified` (general Lemma 3.2, needed for the general Lemma 5.4)
and `wave11/gl26-shriek-calculus` are still running.  Start the full build first; do the parts
that need nothing new; when the orchestrator tells you `wave10/verified` is merged, fetch
`origin/formalization` and do Lemma 5.4.  Rebase onto `origin/formalization` before the final push.
