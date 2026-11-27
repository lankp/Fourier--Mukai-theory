## Your task: `wave9/verified` (Opus, effort: high; at the end of wave 9)

Goal: the `SpacesVerified` forms of wave 9's results, so they hold with nothing assumed.  In
`SpacesVerified/` (one new file per area, as the existing ones), prove each wave 9 headline
theorem with every tagged-input hypothesis discharged by its AxiomMath theorem (as
`SpacesVerified/LP26Inputs.lean` does for `proposition_5_8`, `corollary_1_2`):

* `Spaces/LP26/StandardWA.lean`: `proposition_5_8_standard`, `corollary_1_2_standard` (no new
  input; all are already discharged);
* `Spaces/LP26/Coherence.lean` (if merged) and `Spaces/Supported/` (wave 9 additions): their
  headline theorems and every new tagged input of `Spaces/LP26/Inputs.lean`,
  `Spaces/Supported/Inputs.lean`;
* `LocallySmall.{u}` of AxiomMath's `D(𝒪_X)`, so that `theorem_1_1_univ` applies to a given space.

Then pin the new declarations: add them to `StatementCheckVerified.lean`, run
`scripts/check_statements.sh --verified` and report the drift (additions only expected); do not
run `--update` yourself, the orchestrator does.  This task runs `lake build SpacesVerified`
(~14 600 AxiomMath modules, ~12 h, peak ~25 GB: add 16 GB of swap first, `sysctl -w
vm.max_map_count=262144`, build memory-heavy modules alone; after a restart restore both and
restart the build, Lake skips what is built).  Wait in the foreground in slices of at most ten
minutes.  Commit verified pieces as you go.  Seven verification steps.
