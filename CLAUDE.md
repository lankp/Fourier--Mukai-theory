# Instructions for agents working in this repository

This file is read by every Claude session that works here, including the
parallel worker sessions of a swarm.  `README.md` is the short public summary; this
file holds the project's working rules.  If the two disagree, fix whichever is out of
date and say so in the commit message.

## What the project is

A Lean 4 formalization, on Mathlib, of

* **GL26**: Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic
  spaces* (arXiv:2609.01298; the target is the current manuscript, which is newer
  than the arXiv posting), and
* **LP26**: Lank–Pauwels, *Gluing weak approximability along recollements*
  (preprint).

The goal is both papers in full generality: **LP26 first** (with the parts of the
literature it needs), **then GL26** (maintainer, 26 November 2026).
`results/COVERAGE.md` lists every numbered result of both papers with its status in
the tree.  Start there.

**Full generality** (maintainer's standing instruction, 26 November 2026): the
whole repository aims at the results as stated in the current manuscripts, for
algebraic spaces, with `D_qc`, `Perf`, `D^b_coh`, `Lf^*`, `Rf_*`, `⊗^L` as in
GL26 §2.2.  The abstract interfaces (`Paper/DerivedSetup.lean`, `FMSetup`,
`StacksInterface`, the affine `D(A-Mod)` model) are the categorical engine, not the
target; a result proved only for an interface or an affine model is recorded as
such and is not the paper's result.  The geometric foundation is AxiomMath/Stacks,
imported as a Lake dependency (see `results/SWARM.md`, "Direction").

## Manuscripts

The repository is **public**.  The current GL26 and LP26 manuscripts are newer than
the arXiv postings and are **not stored in the repository** (they were removed from
the whole git history on 26 November 2026, when the maintainer made the repository
public).  The maintainer has given the current TeX of both papers to the orchestrator's
session; **unless the maintainer says otherwise, those files are unchanged** and current
(maintainer, 26 November 2026; the maintainer announces any new version).  Tasks that need
the text run where it is, in the orchestrator's container; a worker elsewhere that needs it
stops and reports.  If the orchestrator no longer has the files (a new orchestrator
session), it asks the maintainer to upload them again.
Never commit manuscript TeX or PDF, and never quote more than a statement's number,
TeX label or a short paraphrase in the repository, commit messages or anywhere public.
Refer to results by number **and** TeX label (`Lemma 7.4, lem:morph_adj`); labels are
stable across versions.  `results/COVERAGE.md` records the numbering of the current
manuscripts; when the maintainer provides a new version, the orchestrator re-checks
it against the new numbering.

## Building

The toolchain is pinned: Lean `v4.35.0` (`lean-toolchain`), Mathlib tag `v4.35.0`
(`lakefile.toml`, `lake-manifest.json`).

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get                      # Mathlib oleans; fast if present
lake build                              # FourierMukai, WeakApprox, StatementCheck
lake env lean FourierMukai/Prelim/Mates.lean   # one file
scripts/check_statements.sh             # statement surface vs. baseline
lake build Spaces                       # algebraic-space layer: also builds ~2 000 AxiomMath modules (~40 min) the first time
scripts/check_statements.sh --spaces    # pinned statements of Spaces
```

`lake build SpacesVerified` (full verification) compiles ~8 500 AxiomMath modules and
needs ~14 GB of memory (add swap on a 16 GB machine).  Only the worker whose task says so
(the `axiommath-verified` task) runs it and `scripts/check_statements.sh --verified`; other
workers do not.

In a cloud session, the environment `fourier--mukai-theory` installs all of this
at start-up.  If `lean` is missing, see `results/SWARM.md` ("Environment").

`scripts/build.sh` is the path for a VM with a prebuilt read-only Mathlib and no
Lake; in a cloud session use Lake.

The project compiles with `autoImplicit = false`, `relaxedAutoImplicit = false`,
`maxSynthPendingDepth = 3`.  Do not override them in a file.

## Hard rules

1. **No `sorry` and no `axiom`.**  The tree has none (since 26 November 2026) and
   must stay so.  A proof that is not finished is not committed.  Do not commit a
   "partial" file.  A target not yet proved is recorded in `results/COVERAGE.md`
   (or stated as a `def …Statement : Prop`), never as a theorem with `sorry`.
2. **What may be relied on** is exactly one thing (see `results/STACKS_POLICY.md`):
   AxiomMath/Stacks, a pinned Lake dependency.  In the algebraic-space library
   `Spaces`, import only the definition modules of
   `scripts/axiommath/spaces-imports.txt`; an AxiomMath theorem outside them is a
   tagged input (tag, AxiomMath declaration name, AxiomMath's statement verbatim) in
   `Spaces/AxiomMathInputs.lean` or in the `Inputs.lean` of the task's directory
   (`Spaces/<Area>/Inputs.lean`), discharged in `SpacesVerified` (by the orchestrator or the
   worker it assigns), where the final results are unconditional.  In the older layers
   a Stacks result is a `Prop` field of `RelativeFM.StacksInterface` with its tag and
   a row in `results/ASSUMPTIONS.md`.  **Neeman, Acta Math. 233 (2024), Theorem 3.2 is no
   longer an allowed assumption** (maintainer, 26 November 2026, including the
   direction "compact ⇒ perfect" that used to be allowed): what this project needs
   from it is formalized and verified here, and only that.  The inputs that still
   carry it (`CompactPerfectInput`, `SmallNeemanCompactToPerfectInput`,
   `Neeman_3_2_*` in `Scheme/Inputs.lean`, the 3.2(iii) field of
   `SupportedCategoryInput`) are open items to discharge, not permitted inputs.
   **Rule (maintainer, 26 November 2026): there are no assumptions and no unproven
   parts except AxiomMath's Stacks Project; every other result GL26 and LP26 need
   comes from Mathlib or is proved here.**  Do not add a named hypothesis that is not
   an AxiomMath theorem.  The named hypotheses still in the tree that are not
   AxiomMath theorems (`DerivedPseudofunctorInput`, `AffineSupportedSchemeComparisonInput`,
   the rest of `results/ASSUMPTIONS.md` §1b and `results/OPEN_INPUTS.md`) are open items:
   each is proved (from AxiomMath where it is a Stacks result) or the results that use it
   are deleted, and until then those results are recorded as not proved.
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

A result is "proved" only after all of these, in order (`README.md`, "Checking"):

1. the module compiles from the repository root, exit status 0;
2. the output contains no `error` (`#print axioms` prints even when a file fails);
3. no `sorryAx` anywhere in the output; flatten the wrapped
   `depends on axioms` lines before reading them; the set must be within
   `propext`, `Classical.choice`, `Quot.sound`;
4. read the proof as well as the statement;
5. **non-vacuity**: every hypothesis-carrying notion the statement relies on
   (a class, a structure, a `Prop` definition such as a compactness or
   generation predicate) is satisfiable.  Either cite an existing theorem that
   exhibits an instance, or prove one (an example object, or at least the zero
   object where that is meaningful).  A theorem whose hypotheses can never hold
   is not a proof of the paper's result;
6. `lake build` of the whole project passes (a single-file compile can read a
   stale `.olean`);
7. `scripts/check_statements.sh` still passes.

Report the outcome of each step.  If a step was skipped, say so.

Step 5 exists because of a real failure: the `Type`-valued `RelativeFM.IsCompact`
is uninhabited in every pretriangulated category
(`Prelim/CompactnessAudit.lean`), which made `lemma_2_5` and the first
`lemma_2_4` vacuous while every other check passed.  Compactness in this
project is `RelativeWeakApprox.IsCompactAb`.

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
  it, and only after running the seven verification steps on the result of the
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
  axiom sets printed, the seven verification steps with outcomes, and any
  deviation from the paper's statement.  The orchestrator reads it, re-verifies,
  checks the statements against the manuscript, and merges or sends it back.
* **After every wave** the orchestrator updates `README.md` (the module and line
  counts, the Status tables, "Next" and the Layout table; keep it short and plain) as
  well as `results/COVERAGE.md` and `results/SWARM.md`, so that the
  README always describes the tree as merged.  This is the maintainer's standing
  instruction.
* **Before a new wave starts**, every worker session of the previous wave has been
  merged (or its outcome recorded) and **archived**.  A wave is closed in this order:
  merge each branch, update `COVERAGE.md`, `SWARM.md` and `README.md`, archive the
  wave's workers, and only then launch the next wave.  Also a standing instruction
  of the maintainer.
* **To-do list** (maintainer, 26 November 2026): every result found to be not proved,
  conditional, or proved only in a restricted form (abstract, `Cat`, affine, interface)
  is a to-do in `results/TODO.md`, generated from `COVERAGE.md` by
  `python3 scripts/todo.py`.  Record a finding in `COVERAGE.md` (never edit `TODO.md` by
  hand) and regenerate.  To-dos are filled in order: LP26 first, then GL26.
* **Cleanliness first** (maintainer, 26 November 2026: cleanliness is a priority).  Before
  a new wave is launched, the repository is cleaned up and **every Markdown file is
  brought up to date** with the merged tree: README, `CLAUDE.md`, `results/*.md` (COVERAGE,
  ASSUMPTIONS, OPEN_INPUTS, STACKS_POLICY, VERIFICATION, the AxiomMath maps, SWARM) and
  `results/swarm/ORCHESTRATOR.md`; generated files regenerated (`scripts/todo.py`,
  `scripts/progress.py`); superseded files moved to `results/archive/`, finished briefs to
  `results/swarm/archive/`; scratch files, stale branches' leftovers and dead code removed.
  `python3 scripts/check_docs.py` must report no problem.  Wording stays short and plain.
* **Handoff** (maintainer, 26 November 2026): anything the orchestrator keeps outside the
  repository (scratchpad files, uploads, background processes, scheduled tasks, local
  subagents) that a new orchestrator session would need is shared with it.  Reusable tools go
  into `scripts/`; the rest is listed in `results/swarm/HANDOFF.md`, kept current whenever such
  an item starts, ends or changes; private items (the manuscripts, other private material) are
  never committed and are passed to the new session by session message.  A new orchestrator
  reads `HANDOFF.md` first.
* **Scratchpad** (maintainer, 26 November 2026).  *Privacy:* the scratchpad keeps private
  material private (manuscripts and anything derived from them, the maintainer's private
  files): never copied into the repository, a commit, a branch, a brief, a worker's message
  or any public place; readable only by the orchestrator; a local git copy that still
  reaches removed history is pruned (`git fetch --prune`, reflog expired).  *Clean-up:*
  before every handoff the scratchpad is cleaned: logs, probes, one-off scripts and copies of
  the manuscripts that the uploads supersede are deleted, reusable tools are moved into
  `scripts/`, and what stays is listed in `HANDOFF.md`.  *Read before a wave:* before starting
  a wave the orchestrator reads `HANDOFF.md` and the scratchpad (what is running, what is
  kept, what is private) and brings both up to date.
* **Robust long work** (maintainer, 27 November 2026).  The orchestrator's container is
  reclaimed when its session is idle, which kills its background builds and local subagents.
  So: (a) long builds (the AxiomMath / `SpacesVerified` build) run in a cloud worker, whose
  container stays up while it works; (b) while a build or a local subagent is running, the session
  that started it (orchestrator or worker) keeps itself active with foreground waits in slices
  of at most ten minutes instead of ending its turn (an idle session's container is reclaimed
  and its background builds die); (c) a task that needs the manuscripts may run as a
  cloud worker when the maintainer uploads the TeX to that worker's session (the orchestrator
  names the session; it never passes the TeX itself); otherwise it runs locally; (d) every
  worker, local or cloud, commits verified progress on its branch as it goes, so an
  interruption loses minutes, and a relaunched worker continues from its branch; (e) after a
  container restart (check `uptime` at the start of every turn and every scheduled check),
  first restore `swapon /home/user/.swapfile` and `sysctl -w vm.max_map_count=262144`
  (lost at each restart; without them large imports fail and big modules are killed), then
  relaunch what died; (f) a local subagent works in its own clone `/home/user/wt-<slug>`
  (`.lake/packages` symlinked to the main checkout's, `.lake/build` copied), pushes only its
  branch, and the clone is deleted after the merge; (g) one heavy build at a time per
  container: before a build that may compile AxiomMath modules, check
  `python3 -I scripts/axiommath/built.py`; a module killed for memory (exit 137) is rebuilt
  alone.
* **Model and effort per task** (maintainer, 27 November 2026: effectiveness first, quality
  over quantity).  Each task in a wave's plan names its model and effort.  Proofs, statements
  of paper results, anything read against the manuscripts, and anything whose failure costs
  hours: the strongest model (Opus), effort high.  Mechanical tasks that the objective checks
  fully guard (prunes, discharging tagged inputs by the declarations they name, docs and
  bookkeeping): Sonnet, effort medium, adopted only where a trial passes cleanly, and moved
  back to Opus on any rework.  The orchestrator and its local subagents run on the session's
  model.  Fewer tasks done well beat more tasks: a wave launches only what it can verify, and
  a task that fails verification is redone, not merged partially without record.
* **Archive before the next wave** (maintainer, 27 November 2026): the orchestrator archives
  every worker session of the completed wave (`archive_session`), and records it in
  `SWARM.md`, before it launches any session of the next wave.  A wave whose workers are not
  all archived is not closed.
* **Next wave** (maintainer, 26 November 2026): as soon as a wave is closed (and cleaned up,
  above), the
  orchestrator prepares the next one from the top of `results/TODO.md` (briefs in
  `results/swarm/wave<N>/`, a section in `SWARM.md`) and launches it, subject to the
  usage rule in `results/swarm/ORCHESTRATOR.md`.  It stops only when `TODO.md` is empty.

## Swarm protocol

The orchestration plan, the task queue and the current wave are in
`results/SWARM.md`.  A session taking over as orchestrator starts from
`results/swarm/ORCHESTRATOR.md`.  A worker session:

1. reads this file, `results/SWARM.md` and the task message;
2. works only on its task, in the files its task names;
3. stops and reports (rather than improvising) if the task turns out to need
   an assumption outside rule 2, a change to a shared file, or a statement that
   differs from the paper's;
4. ends with a pushed branch and a final report, or with a written report of why
   nothing was pushed.
