## Your task: `wave10/verified` (Opus, effort: high; at the end of wave 10)

Goal: the `SpacesVerified` forms of wave 10's results, with every tagged-input hypothesis
discharged by its AxiomMath theorem (as `SpacesVerified/LP26Inputs.lean` does), and the parts
that need AxiomMath theorem modules outside the `Spaces` closure.  Same build regime as
`results/swarm/wave9/verified.md` (full `lake build SpacesVerified`, 16 GB swap,
`vm.max_map_count`, foreground waits, restart after a container restart).

Notes from the merges:
* `wave10/gl26-conservativity` (merged `cb6b5ad`): discharge the five inputs of
  `Spaces/Conservative/Inputs.lean` (the fifth, `AffinePushforwardConservativeInput`, was only
  compared by eye: check it against `isZero_of_isZero_derivedModulePushforward_of_isAffineHom`);
  prove **GL26 Lemma 3.2** (`lem:quasi-affine_is_conservative`) for every quasi-affine `f` of
  qcqs spaces: `j = (toDirectImageSpec f).left`, `p` the structure morphism (affine), `j` an open
  immersion by 086S (`isQuasiAffineHom_iff_isOpenImmersion_toDirectImageSpec`), quasi-compact as
  `f` is quasi-compact and `p` separated; then `lemma_3_2_of_factorization`.
* `wave10/gl26-upper-shriek` (merged `ebffeca`): discharge `Tag0E55Input` (the worker suggests
  `fun hZ X Y f hXqc hXqs hYqs hR => isLeftAdjoint_quasicoherentDerivedPushforward hZ f hXqc hXqs
  hYqs`; it writes out the bodies of three definitions outside the import list: check they agree)
  and `Tag04NXInput` (`isProper_of_comp_of_isSeparated`); the `SpacesVerified` form of
  `lemma_2_22`.
* `wave10/gl26-internal-hom` (merged `c828460`): discharge `Tag0CR4Input`, `Tag0A8AInput`,
  `Tag08I3PerfectInput` (`Spaces/InternalHom/Inputs.lean`; `QcohDerived` written as `Dqc`); the
  `SpacesVerified` forms of `lemma_2_10`, `lemma_2_11`, `lemma_2_16_perfect_qcqs`.

Pin the new headline declarations in `StatementCheckVerified.lean`, run
`scripts/check_statements.sh --verified` and report the drift (do not `--update`).  Seven
verification steps.  Commit verified pieces as you go.
