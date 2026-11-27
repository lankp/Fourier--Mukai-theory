## Your task: `wave8/discharge-wave7-inputs` (effort: high; runs in the orchestrator's container)

Goal: prove in `SpacesVerified` every tagged AxiomMath input added in wave 7, by the AxiomMath
declaration it names, as `SpacesVerified/Discharge.lean` and `SpacesVerified/Statements.lean` do:
the inputs of `Spaces/Affine/Inputs.lean`, `Spaces/Supported/Inputs.lean` and
`Spaces/BaseChange/Inputs.lean` (17 in all).  Then the unconditional forms of the wave 7
headlines (LP26 Cor 1.2 affine base, GL26 Lemma A.9 generation part, Lemmas 6.11 and 10.1 over
spaces), pinned in `StatementCheckVerified.lean` (the orchestrator re-records the baseline).

Before building, `python3 -I scripts/axiommath/built.py .lake/packages/Stacks <modules>`; build
missing AxiomMath modules with `scripts/axiommath/build.sh`, alone (memory).  If an input's
statement is not AxiomMath's verbatim, stop and report.  Files: `SpacesVerified/*.lean`,
`SpacesVerified.lean`, `StatementCheckVerified.lean`.  Seven verification steps with
`lake build SpacesVerified`.
