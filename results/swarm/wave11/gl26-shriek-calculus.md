## Your task: `wave11/gl26-shriek-calculus` (Opus, effort: high; full AxiomMath build)

Goal: GL26 Lemmas 2.21 (`lem:neeman186`), 2.23 (`lem:neeman188`) and 2.24 (`lem:neeman189`) over
algebraic spaces, on wave 10's `f^×`, `f^!` and `Compactification` (`Spaces/Duality/`), with
Neeman's maps `ρ(f,g)`, `σ`, `χ` and the base-change map for `f^!` (GL26 §2, after
`lem:neeman186`; Neeman 2023, Construction 9.4, Theorem 1.8).

Wave 10 found that the AxiomMath results these need (Stacks 0E5P/0E5Q, flat base change for
`f^×`) lie in modules whose import closure contains `MilnorPatching.Relative`, outside the
`Spaces` closure.  So this task works in **`SpacesVerified`** directly (new directory
`SpacesVerified/Duality/`), importing the AxiomMath modules it needs and using their theorems
as theorems; the results there are unconditional.  It runs `lake build SpacesVerified`
(regime of `results/swarm/archive/wave9/verified.md`: 16 GB swap, `vm.max_map_count`, foreground waits,
restart after a container restart).  Prove what AxiomMath lacks (independence of the
compactification if needed, `ρ`, the base-change map) here; stop and report if something needs
an assumption outside AxiomMath.  Statements and proofs: `manuscripts/GL26/main.tex`.  Pin the
headline declarations in `StatementCheckVerified.lean` and report the drift of
`scripts/check_statements.sh --verified` (do not `--update`).  Commit verified pieces as you go
(one lemma at a time).  Seven verification steps.
