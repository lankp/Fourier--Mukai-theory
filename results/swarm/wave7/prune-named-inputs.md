## Your task: `wave7/prune-named-inputs` (effort: medium)

Maintainer's rule (26 November 2026): **no assumptions and no unproven parts except
AxiomMath's Stacks Project.**  The tree still has conditional results whose hypotheses are
named inputs that are not Stacks theorems.  Those marked in `results/OPEN_INPUTS.md` as
**delete**, **being removed**, false or refuted are dead: delete them, with every
declaration that takes them and nothing else.

Rows to delete (with their consumers): 2.4 `SmallNeemanCompactToPerfectInput`, 2.5
`Neeman_3_2_i`, 2.6 `Neeman_3_2_ii`, 2.7 `Neeman_3_2_iv` / `NeemanPublishedWeakApproximation`,
2.9 `NeemanAffineCompactModelInput`, 7.3 (`WeakApproximationData`, `SetupMainMinimal`,
`Setup44*`, `SatisfiesWA`: the `IsGenerator` form, F2), and any remaining consumer of 4.3,
7.10.  Also `CompactPerfectInput` (2.1) where only vacuous endpoints use it.

**Keep** (they are being proved over algebraic spaces by other tasks): rows 1.x (Stacks
fields), 2.10, 3.x, 5.1, 5.3, 5.6, 5.7, 6.x, 7.1, 7.2, 7.4–7.7, and everything in
`Spaces/` and `SpacesVerified/`.  If a declaration you would delete is used by something
you keep, stop and report it.

**Pinned declarations** (`StatementCheck.lean`, `results/statement-baseline.txt`): do not
delete them and do not edit the baseline.  List each pinned declaration that depends on a
row above; the orchestrator removes it at merge.

Branch `wave7/prune-named-inputs` from `origin/formalization`.  Files: anything under
`FourierMukai/` and `WeakApprox/` (not `Spaces/`, `SpacesVerified/`), the root import files,
`FourierMukai/Audit.lean`, and `results/OPEN_INPUTS.md` (mark each row `→ deleted (wave 7)`).
No new hypotheses, no new statements.  Verification: default `lake build` and
`scripts/check_statements.sh` pass, `lake build Spaces` still passes, no `sorry`; report
the deleted declarations by file, the pinned ones that must go, and the line count removed.
