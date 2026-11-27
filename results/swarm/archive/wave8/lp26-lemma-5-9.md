## Your task: `wave8/lp26-lemma-5-9` (effort: high; runs in the orchestrator's container)

Goal: LP26 Lemma 5.9 (`lem:characterize_T-_c`) over algebraic spaces, stated as in the current
LP26 manuscript (path in your task message), for the standard `t`-structure on `D_qc,S(X)`
(`Spaces/LP26/StandardTStructure.lean`).  `wave8/lp26-section5` found the AxiomMath results it
needs: perfect ⇒ pseudo-coherent, 08FV, the `IsLE` criterion, monotonicity of
`m`-pseudo-coherence, 08HP (and a bridge from "`Tᶜ` compact" to the quasi-compactness of the
complement's inclusion), and for the Noetherian clause `isPseudoCoherent_iff_of_isNoetherian`.
Tagged inputs in `Spaces/LP26/Inputs.lean` (append).  Files: `Spaces/LP26/Lemma59.lean`.
Commit and push each verified piece as you go.  Seven verification steps, `lake build Spaces`,
both statement checks.
