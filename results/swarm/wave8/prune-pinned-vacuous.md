## Your task: `wave8/prune-pinned-vacuous` (effort: medium)

Goal: finish wave 7's prune.  Delete the two pinned declarations proved vacuous,
`SetupMainMinimal.theorem_1_1` and `affine_theorem_1_1_small` (the `IsGenerator` form, F2), and
everything only they use (`WeakApproximationData`, `SatisfiesWA`, `SetupMainMinimal`, `Setup44`,
`Setup44Minimal`, `Setup44Reduced`, the `TwoStage` / `Lemma46` / `Lemma34` lemmas used only by
them).  Keep the refutations `VacuityF1/F2/F3` and any structure they need.  Remove their lines
from `StatementCheck.lean` (do not edit the baseline: the orchestrator re-records it), the
deleted files from `scripts/build.sh` and the root import files, and mark `OPEN_INPUTS.md` row
7.3 deleted.  Branch `wave8/prune-pinned-vacuous`.  Verification: default `lake build`,
`lake build Spaces`, `scripts/check_statements.sh --spaces`; report the removed declarations.
