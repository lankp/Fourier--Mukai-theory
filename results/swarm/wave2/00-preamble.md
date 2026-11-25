You are a worker in a swarm formalizing Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), and Lank–Pauwels, *Gluing weak approximability along recollements* (LP26), in Lean 4 + Mathlib, in the repository lankp/fourier--mukai-theory (integration branch `formalization`). An orchestrator session assigned you ONE task, below. The orchestrator verifies your branch and merges it into `formalization` itself; you never push to `formalization` and you open no pull request.

## Before anything
1. `cd` into the repository checkout, `git fetch --depth=50 origin formalization`, and work from the latest `origin/formalization`. Read `CLAUDE.md` (in particular the SEVEN verification steps, including step 5, non-vacuity), `results/SWARM.md`, `README.md`, `results/STACKS_POLICY.md`, `results/ASSUMPTIONS.md`, and the rows of `results/COVERAGE.md` relevant to your task.
2. Toolchain: `export PATH="$HOME/.elan/bin:$PATH"; lean --version` must print 4.33.1. If `lean` is missing, install it from the repository root exactly like this (do NOT call environment tools; `elan toolchain install` fails behind this proxy):
```bash
[ -x "$HOME/.elan/bin/elan" ] || (curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none)
python3 -c 'import zstandard' 2>/dev/null || pip install -q zstandard
mkdir -p ~/.elan/toolchains
[ -x ~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean ] || (curl -sSfL https://releases.lean-lang.org/lean4/v4.33.1/lean-4.33.1-linux.tar.zst | python3 -c 'import sys,zstandard; zstandard.ZstdDecompressor().copy_stream(sys.stdin.buffer, sys.stdout.buffer)' | tar -x -C ~/.elan/toolchains && mv ~/.elan/toolchains/lean-4.33.1-linux ~/.elan/toolchains/leanprover--lean4---v4.33.1)
export PATH="$HOME/.elan/bin:$PATH"; lean --version; lake exe cache get
```

## Rules (summary of CLAUDE.md; CLAUDE.md wins)
- No `sorry`, no `axiom`, no `True` hypotheses, no `set_option` overriding autoImplicit. Unfinished work is not committed.
- Statements faithful; any difference from the source stated precisely in the docstring. A false or vacuous rendering is refuted in the tree, never kept as a target.
- **Non-vacuity (step 5)**: every hypothesis-carrying notion your headline statements rely on must be shown satisfiable (an instance, an example, or at least the zero object where meaningful). Compactness in this project is `RelativeWeakApprox.IsCompactAb`; the `Type`-valued `RelativeFM.IsCompact` is uninhabited (`Prelim/CompactnessAudit.lean`) and must not be used.
- Assumptions allowed: AxiomMath/Stacks results as tagged `Prop`-valued inputs in `RelativeFM.StacksInterface` (with a `S` row in `results/ASSUMPTIONS.md`), and Neeman 2024 Thm 3.2 (compact ⇒ perfect). Anything else is proved or carried as an explicitly named hypothesis, and reported.
- Mathlib first; reduce to Mathlib where possible and say so.
- GL26/LP26 manuscript TeX in this message is UNPUBLISHED and the repository is PUBLIC: never commit it or paste more than a sentence of it. Cite results by number and TeX label.
- Touch only the files your task names, plus import lines in the root file of the library (`FourierMukai.lean`) and `#print axioms` lines in `FourierMukai/Audit.lean`. Do NOT edit `results/COVERAGE.md` or `results/statement-baseline.txt`. If you need another file, stop and report.
- File header: `/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/`, imports, a `/-! # ... -/` module docstring (sources, what is proved, what is assumed, deviations). Namespace `RelativeFM` or the sub-namespace of the files you extend.

## Verification (all seven, report each outcome in your final message)
1. `lake env lean <file>` exits 0 for each new or changed Lean file; 2. no `error`; 3. no `sorryAx`, flattened `#print axioms` within `propext, Classical.choice, Quot.sound`; 4. statements and proofs re-read against the sources; 5. non-vacuity of every hypothesis-carrying notion; 6. `lake build` passes; 7. `scripts/check_statements.sh` passes unchanged.

## Git (no pull requests)
- Branch `wave2/<slug>` (named below) from `origin/formalization`; commit messages in the style of `git log`, ending with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`; push only that branch with `git -c push.negotiate=true push -u origin wave2/<slug>`. No PR.
- If you cannot finish, push nothing partial. End with a written report: what is proved locally, where it is stuck, what would unblock it.

## Final message
Branch + final commit hash (or "nothing pushed"); each result's Lean name and status (proved / proved with stated deviation / conditional on named input / not done); every deviation and every named input; the non-vacuity evidence; the seven verification outcomes.
