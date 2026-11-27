## Your task: `wave8/axiommath-verified` (effort: high)

Goal, in two parts, both in this session's own container (it stays up while you work, which
the orchestrator's does not):

1. **Build the full verification.**  `lake build SpacesVerified` compiles ~8 500 AxiomMath
   modules (several hours) and one module, `StacksFrontier.RingTheory.MilnorPatching.Relative`,
   peaks near 13.6 GB.  Before starting: add 8 GB of swap
   (`fallocate -l 8G /swapfile && chmod 600 /swapfile && mkswap /swapfile && swapon /swapfile`;
   if that is refused, report it), and try `sysctl -w vm.max_map_count=262144`.  Build that module
   alone first (`lake build StacksFrontier.RingTheory.MilnorPatching.Relative`), then
   `lake build SpacesVerified`, with nothing else running.  Use
   `scripts/axiommath/build.sh .lake/packages/Stacks <log> <modules>` for AxiomMath-only targets
   (it keeps the disk small).  If a module is killed for memory (exit 137), rebuild it alone.
2. **Discharge wave 7's tagged inputs.**  Prove in `SpacesVerified` every tagged AxiomMath input
   of `Spaces/Affine/Inputs.lean`, `Spaces/Supported/Inputs.lean` and
   `Spaces/BaseChange/Inputs.lean` (17 in all) by the AxiomMath declaration it names, as
   `SpacesVerified/Discharge.lean` and `SpacesVerified/Statements.lean` do; then the
   unconditional forms of the wave 7 headlines (LP26 Corollary 1.2 affine base, GL26 Lemma A.9
   generation part, GL26 Lemmas 6.11, 10.1 over spaces).  Pin them in
   `StatementCheckVerified.lean`; do not edit `results/statement-baseline-verified.txt` (the
   orchestrator re-records it): report the output of `scripts/check_statements.sh --verified`.
   If an input's statement is not AxiomMath's verbatim, stop and report.

Commit verified progress as you go (each discharged file once it builds and its axioms are
clean), so an interruption loses little.  Branch `wave8/axiommath-verified`.  Files:
`SpacesVerified/*.lean`, `SpacesVerified.lean`, `StatementCheckVerified.lean`.  Seven
verification steps with `lake build SpacesVerified`; report build times and peak memory.
