## Your task: `wave9/lp26-noetherian-coherence` (effort: high; runs in the orchestrator's container; after lp26-standard-wa)

Goal: the last clause of LP26 Corollary 1.2 (`cor:weak_approx_spaces`): for `X` Noetherian,
`D_qc,S(X)` is coherent, as the current LP26 manuscript states it.  Its proof uses standard
W.A. and the coherence criterion of CHNS (Example 10.1.2 there): prove what that needs here
(the literature is not an allowed assumption), on LP26 Lemma 5.9
(`Spaces/LP26/Lemma59.lean`).  Files: `Spaces/LP26/Coherence.lean`.  Commit verified pieces as
you go.  Seven verification steps; `lake build Spaces`.

Scratch files (probes, logs) stay in your clone, never in the orchestrator's scratchpad.
