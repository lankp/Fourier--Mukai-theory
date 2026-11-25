# Instructions for agents working in this repository

This file is read by every Claude session that works here, including the
parallel worker sessions of a swarm.  The rules are the ones `README.md` states
for the project; this file makes them operational.  If the two disagree,
`README.md` wins and this file should be fixed.

## What the project is

A Lean 4 formalization, on Mathlib, of

* **GL26**: Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic
  spaces* (arXiv:2609.01298; the target is the current manuscript, which is newer
  than the arXiv posting), and
* **LP26**: Lank–Pauwels, *Gluing weak approximability along recollements*
  (preprint).

The goal is all of GL26.  `results/COVERAGE.md` lists every numbered result of
both papers with its status in the tree.  Start there.

## Unpublished manuscripts: never commit them

The repository is **public**.  The current manuscripts of GL26 and LP26 are not.
Never commit their `.tex`, `.pdf` or `.bib`, or paste long passages of them into
files, commit messages or reports.  Refer to results by number **and**
TeX label (`Lemma 7.4, lem:morph_adj`); labels are stable across versions.  A
worker receives the TeX excerpt it needs in its task message.

## Building

The toolchain is pinned: Lean `v4.33.1` (`lean-toolchain`), Mathlib tag `v4.33.1`
(`lakefile.toml`, `lake-manifest.json`).

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get                      # Mathlib oleans; fast if present
lake build                              # FourierMukai, WeakApprox, StatementCheck
lake env lean FourierMukai/Prelim/Mates.lean   # one file
scripts/check_statements.sh             # statement surface vs. baseline
```

In a cloud session, the environment `fourier--mukai-theory` installs all of this
at start-up.  If `lean` is missing, see `results/SWARM.md` ("Environment").

`scripts/build.sh` is the path for a VM with a prebuilt read-only Mathlib and no
Lake; in a cloud session use Lake.

The project compiles with `autoImplicit = false`, `relaxedAutoImplicit = false`,
`maxSynthPendingDepth = 3`.  Do not override them in a file.

## Hard rules

1. **No `sorry` and no `axiom`** in anything you add.  The only `sorry`s in the
   tree are the nine targets in `FourierMukai/Paper/Statements.lean`.  A proof
   that is not finished is not committed.  Do not commit a "partial" file.
2. **What may be assumed** is exactly two things (see `results/STACKS_POLICY.md`):
   * a result of AxiomMath/Stacks, taken as a `Prop`-valued field of
     `RelativeFM.StacksInterface` (`FourierMukai/Scheme/StacksInput.lean`) with its
     tag, plus a row in `results/ASSUMPTIONS.md`;
   * Neeman, Acta Math. 233 (2024), Thm 3.2, direction "compact ⇒ perfect".
   Anything else is proved, or carried as an explicitly named hypothesis whose
   name says what it is.
3. **Statements are faithful.**  No hypothesis is `True`.  No result is reworded to
   fit what is available.  If a Lean statement is weaker than the paper's, its
   docstring names the gap.  If a rendering is false, prove it false in the tree
   rather than keep it as a target.  An interface whose functors are free fields
   does not imply geometric statements; see `Paper/InterfaceAudit.lean`.
4. **Do not change a pinned statement.**  `results/statement-baseline.txt` pins the
   headline declarations.  `scripts/check_statements.sh --update` is run only by
   the orchestrator, for a change it has checked against the manuscript and
   recorded in the commit message.
5. **Mathlib first.**  Before proving a categorical lemma, search Mathlib
   (`mateEquiv`, `conjugateEquiv`, `Adjunction.CommShift`, `Functor.IsTriangulated`,
   `ObjectProperty.triangEnvelope`, ...).  If Mathlib has it, prove the paper's
   form by reduction to Mathlib's and say so in the docstring.
6. **Never write under `.github/workflows/`.**  This repository's GitHub
   connection cannot.  Change `ci/ci.yml` and say in the commit message that the workflow
   must be updated by hand.

## Verification before you claim anything

A result is "proved" only after all of these, in order (`README.md`,
"Verification"):

1. the module compiles from the repository root, exit status 0;
2. the output contains no `error` (`#print axioms` prints even when a file fails);
3. no `sorryAx` anywhere in the output; flatten the wrapped
   `depends on axioms` lines before reading them; the set must be within
   `propext`, `Classical.choice`, `Quot.sound`;
4. read the proof as well as the statement;
5. `lake build` of the whole project passes (a single-file compile can read a
   stale `.olean`);
6. `scripts/check_statements.sh` still passes.

Report the outcome of each step.  If a step was skipped, say so.

## Conventions for new files

* Header: `/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under
  Apache 2.0 license as described in the file LICENSE. -/`, then imports, then a
  module docstring `/-! # ... -/` naming the paper, the result number **and**
  TeX label, what is proved, what is assumed, and how the Lean statement differs
  from the paper's (if it does).
* Namespace `RelativeFM` (and a sub-namespace for a section, as existing files do).
* Every declaration that renders a paper result gets a docstring beginning
  `**Lemma 7.4** (`lem:morph_adj`)`.
* Add the module to the root import file of its library (`FourierMukai.lean` or
  `WeakApprox.lean`).  Keep the list sorted where it is sorted.
* Add an `#print axioms` line for each headline result to `FourierMukai/Audit.lean`.
* Update the row in `results/COVERAGE.md`, and `results/ASSUMPTIONS.md` if you
  used a Stacks field.

## Git (no pull requests)

The maintainer has delegated merging to the orchestrator session: work reaches
`formalization` by direct push, without pull requests.

* The integration branch is `formalization`.  Only the **orchestrator** pushes to
  it, and only after running the six verification steps on the result of the
  merge.  Nobody force-pushes it or rewrites its history.
* A **worker** works on one branch, `wave<N>/<short-slug>`, branched from the
  latest `formalization`, and pushes only that branch, with
  `git -c push.negotiate=true push -u origin <branch>`.  It opens no PR.
* Touch only the files your task names, plus the root import line and
  `Audit.lean`.  If you need to change a shared file (`StacksInput.lean`,
  `Duality.lean`, `Statements.lean`, ...), stop and report instead.
* Commit messages say what was proved and what it depends on, in the style of
  the existing history.
* A worker's final report lists: results covered (number + label), files, the
  axiom sets printed, the six verification steps with outcomes, and any
  deviation from the paper's statement.  The orchestrator reads it, re-verifies,
  checks the statements against the manuscript, and merges or sends it back.

## Swarm protocol

The orchestration plan, the task queue and the current wave are in
`results/SWARM.md`.  A worker session:

1. reads this file, `results/SWARM.md` and the task message;
2. works only on its task, in the files its task names;
3. stops and reports (rather than improvising) if the task turns out to need
   an assumption outside rule 2, a change to a shared file, or a statement that
   differs from the paper's;
4. ends with a pushed branch and a final report, or with a written report of why
   nothing was pushed.
