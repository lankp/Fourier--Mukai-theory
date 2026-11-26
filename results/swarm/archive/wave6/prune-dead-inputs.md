## Your task: `wave6/prune-dead-inputs` (effort: medium)

Delete the named inputs that `results/OPEN_INPUTS.md` marks **delete**, now that the false/vacuous ones are refuted in the tree (`Scheme/Refute*.lean`, wave 6) and the vacuous pins are removed. Goal (CLAUDE.md rule 2): only AxiomMath/Stacks is assumed; dead inputs and the declarations whose only role is to consume them go.

Branch `wave6/prune-dead-inputs`: `git fetch --depth=50 origin formalization && git checkout -B wave6/prune-dead-inputs origin/formalization`. Check `git log --oneline -- manuscripts` prints nothing before you push (the repository is public; the manuscripts are not in it).

1. For each row marked **delete** in `results/OPEN_INPUTS.md` (1.8–1.10, 1.15, 1.19, 1.20, 2.8, 2.11, 3.5–3.8, 3.13, 4.2, 4.3, 4.5, 4.6, 5.4, 5.5, 5.9, 6.16, 7.3, 7.10; skip any already removed by `wave5/neeman-prune`), delete the input and every declaration whose only role is to take it as a hypothesis or produce it, and modules left empty. **Keep** anything proved unconditionally that a kept declaration uses (in particular `M4Unconditional`, `M6Unconditional`, `compactToPerfectInput_unconditional`: F6), and keep the `Refute*.lean` refutations and what they import.
2. **Do not touch** any declaration pinned in `results/statement-baseline.txt` or its proof dependencies; `scripts/check_statements.sh` must pass **unchanged**. If a delete row is used by a pinned declaration, keep it and report.
3. Do not edit files under `WeakApprox/` (another worker, `wave6/lp26-paper-hypotheses`, adds files there) except the root import line if a deleted module is imported there.
4. Update `results/OPEN_INPUTS.md` (mark each row "deleted (wave 6)" or "kept: reason"), `results/ASSUMPTIONS.md` rows, the root import file and `Audit.lean`. List every deleted declaration and module in your report.

Verification: all seven steps; full `lake build`; audit (removed `#print axioms` lines listed); statement check passes unchanged. This is a mechanical refactor: no new mathematics, no new hypotheses.
