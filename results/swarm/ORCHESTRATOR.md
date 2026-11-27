# Orchestrator handoff

Current orchestrator session: `session_0111iGd9QDKToChKA2B4cz5n`

(A session that takes over replaces this id with its own, in a commit of its own.)

Read this if you are a Claude session taking over as the **orchestrator** of the
swarm that formalizes GL26 and LP26 in this repository (for example because the
previous orchestrator session ended).  Together with `CLAUDE.md`,
`results/SWARM.md`, `results/COVERAGE.md` and `results/ASSUMPTIONS.md` it is
everything you need; the previous orchestrator's conversation is not available
to you.

## Who decides what

* **Maintainer**: Pat Lank (GitHub `lankp`), an author of both papers.  The
  maintainer's standing instructions are below; follow them without asking again.
* **Orchestrator** (you): plans waves, launches worker sessions, verifies and
  merges their branches into `formalization`, keeps the documentation current.
* **Workers**: one cloud session per task, branch `wave<N>/<slug>`, no PRs.

## Standing instructions from the maintainer

1. Make all changes, edits and commits as needed; push directly to
   `formalization` (no pull requests), but only after the seven verification steps
   of `CLAUDE.md` pass on the merge result.
2. **Update `README.md` after every wave** (counts, Status table, "What is proved"
   tables, "What is open", Layout), together with `results/COVERAGE.md`,
   `results/SWARM.md`, `results/ASSUMPTIONS.md`, `results/archive/SCHEMES.md` as relevant.
3. **Archive every worker session of a wave once it is merged, before the next
   wave is launched.**
4. Prepare the next wave when the current one nears completion, and **launch it as soon as
   the current wave is closed** (maintainer, 26 November 2026): its tasks come from the top
   of `results/TODO.md` (`python3 scripts/todo.py` after updating `COVERAGE.md`), LP26
   before GL26; continue until `TODO.md` is empty.  **Before launching, archive** every worker session of the
   completed wave and record it in `SWARM.md` (maintainer, 27 November 2026), **and clean up**: every
   Markdown file updated to the merged tree, superseded files archived, generated files
   regenerated, `python3 scripts/check_docs.py` clean (CLAUDE.md, "Cleanliness first").  **If the 5-hour
   usage limit is near (status `allowed_warning`, or the window is already
   heavily used), do not launch; schedule the launch (`send_later`) for just
   after the next reset.**  Launch at most four workers at a time.
5. If the orchestrator session ends, a new orchestrator session continues.  An
   automatic successor is **not** possible: sessions started by a scheduled task,
   and worker sessions, do not get the session-management tools (`get_session`,
   `create_session`, `send_message`, `add_repo`), which was tested on 26 November
   2026.  So a new orchestrator is a session **the maintainer starts** on this
   repository with the message *"Take over as orchestrator: follow
   results/swarm/ORCHESTRATOR.md."*  That session replaces the id at the top of
   this file with its own (get_session with no argument), commits, and continues.
   The running orchestrator survives usage-limit stops and worker restarts on its
   own: scheduled messages (`send_later`) into it resume it after the reset.
6. **The repository is public; the manuscripts are not in it** (26 November 2026:
   the maintainer made it public; `manuscripts/` was removed from the entire history
   and every branch was force-pushed).  The maintainer uploaded the current TeX of both
   papers to this orchestrator session (LP26 `44b730a8-main.tex`, GL26 `46ab67e2-main.tex`
   in the session's uploads); **unless the maintainer says otherwise they are unchanged**,
   so do not ask again.  Run tasks that need the text here (local subagents), never commit
   or quote manuscript TeX.  If this session's uploads are gone (new orchestrator), ask the
   maintainer to upload them again.  When the maintainer announces a new version,
   re-check `results/COVERAGE.md` against its numbering.
7. GL26 is correct as stated in the current manuscript (the maintainer confirmed,
   for example, that Lemma B.10's displayed "(G,ζ) ⊣ (F,ξ)" is a typo for
   "(F,ξ) ⊣ (G,ζ)").  A Lean rendering that turns out false or vacuous is refuted
   in the tree; it does not mean the paper is wrong.

8. **Full generality** (26 November 2026): "focus the entire repo on proving
   results in their full generality as stated in GL26 and LP26 (LaTeX files, not on
   arXiv; algebraic spaces)."  Plan waves towards the geometric statements over
   algebraic spaces, built on AxiomMath/Stacks as a Lake dependency; see
   `results/SWARM.md`, "Direction".  Affine-model and interface-only work is done
   only where it feeds that.
9. **Neeman's affine weak approximability is to be proved, not assumed**
   (26 November 2026, for the next wave): LP26 is addressed with Neeman's weak
   approximability for affine schemes with support (Neeman 2024, Thm 3.2(iv), affine
   case `D_qc,V(I)(Spec A)`, `I` finitely generated) formalized and verified.  See
   `results/SWARM.md`, "Wave 5".

10. **Neeman 2024, Theorem 3.2 is not assumed** (26 November 2026): "the goal should
   include not assuming Neeman … Theorem 3.2 … compact implies perfect …  We should
   only formalize/verify what is needed from loc. cit. in this project."  CLAUDE.md
   rule 2 now allows AxiomMath/Stacks only; every remaining Neeman input is an open
   item.

11. **Only AxiomMath/Stacks is assumed** (26 November 2026): "The goal: to only
   assume Axiom's Stacks Project, every other result in GL26 and LP26 needed is from
   mathlib and proved on as needed basis."  Every named non-Stacks input in the tree
   is an open item; plan waves to prove or delete them, and report results that
   still take one as conditional.

12. **Worker effort** (26 November 2026, maintainer approved): launch workers that
   write or repair Lean proofs with `effort: "high"`, and reading, triage, mapping,
   documentation and mechanical refactor/prune workers with `effort: "medium"`
   (`create_session` parameter `effort`).  Applies to every future wave.

13. **Public progress page**: regenerate `results/PROGRESS.md` with
   `python3 scripts/progress.py` and `python3 scripts/todo.py` whenever a wave closes (and after any merge that
   changes `COVERAGE.md`, the baseline or the SWARM log); commit it with the docs.

## Infrastructure

* Repository: `lankp/Fourier--Mukai-theory` (lower-case alias
  `lankp/fourier--mukai-theory`), integration branch `formalization`.  In a new
  session: `add_repo` (owner `lankp`, repo `Fourier--Mukai-theory`, access
  `push`), then clone as it instructs.
* Cloud environment: `fourier--mukai-theory`, id `env_018GWtxMGwCU3sde5wadUMxL`.
  Its network allows GitHub release downloads, `releases.lean-lang.org`,
  `lakecache.blob.core.windows.net`, `cache.mathlib.org` (Mathlib v4.35.0 serves its olean cache there; added 26 Nov 2026) and `arxiv.org`; its setup script installs
  elan, Lean 4.33.1 and Mathlib's cache for a checkout named
  `Fourier--Mukai-theory` or `fourier--mukai-theory`.  If `lean` is missing, use
  the install commands in `results/swarm/archive/wave4/00-preamble.md`.  Do not call
  `elan toolchain install` (refused by the proxy).
* Launching a worker: `create_session` with `environment_id`
  `env_018GWtxMGwCU3sde5wadUMxL`, `source_url`
  `https://github.com/lankp/Fourier--Mukai-theory`, `source_revision`
  `formalization`, tags `fm-swarm` and `fm-wave<N>`, and a short prompt pointing
  to `results/swarm/wave<N>/00-preamble.md` and `results/swarm/wave<N>/<task>.md`
  (see the wave-3 and wave-4 launches in `results/SWARM.md`), plus any manuscript
  excerpt the task needs.  Tell workers not to call cloud-environment tools.
* Verifying a branch: `scripts/swarm/verify_branch.sh wave<N>/<slug>`.  It merges
  the branch onto `origin/formalization` locally, resolves import/audit-line
  conflicts by keeping both sides, and runs build, single-file compiles, the
  axiom audit and the statement check.  Then **you** do steps 4 and 5 by hand:
  read each headline statement against the manuscript, and check that every
  hypothesis-carrying notion is satisfiable.  Record the result in
  `results/COVERAGE.md` and the log in `results/SWARM.md`, then push with
  `git -c push.negotiate=true push origin HEAD:formalization` (fast-forward only).
* Watching for pushes: a `Monitor` on `git ls-remote origin 'refs/heads/wave<N>*'`.
* Workers stopped by the usage limit: send them a message to continue once the
  window has reset.

## Lessons that cost something to learn

* The `Type`-valued compactness `RelativeFM.IsCompact` is uninhabited; compactness
  is `RelativeWeakApprox.IsCompactAb` (`Prelim/CompactnessAudit.lean`).
* `StacksInterface.KoszulScalarSupportInput` is false for every nonzero ring
  (`Scheme/KoszulInputs.lean`); wave 4 repairs the endpoints that used it.
* Always check non-vacuity yourself; workers' reports have twice been right about
  everything except whether the hypotheses can hold.
* Merge conflicts in `FourierMukai.lean`, `FourierMukai/Audit.lean` and
  `results/ASSUMPTIONS.md` are routine (parallel appends); keep both sides.
* Shallow clones may need `--depth=200` to find merge bases.

## Handoff

Read [`HANDOFF.md`](HANDOFF.md) first: what the previous orchestrator kept outside the
repository (background builds, scheduled tasks, uploads, local clones) and how to redo it.
Keep it current; private items reach a successor only by session message.  Before starting
any wave, read `HANDOFF.md` and the scratchpad and bring both up to date; before any handoff,
clean the scratchpad (CLAUDE.md, "Scratchpad").

## Current state

See the end of `results/SWARM.md` (the log) and its current wave section.  At the
time of writing (26 November 2026, 19:20 UTC): waves 1–6 are merged and their workers
archived; `SpacesVerified` discharges every tagged input of `Spaces`
(`scripts/check_statements.sh --verified`); the README describes the merged tree.  Wave 7's
three Lean tasks were launched at 19:12 UTC (tag `fm-wave7`, sessions in `results/SWARM.md`);
`wave7/spaces-statements` ran as a local subagent with the GL26 TeX and is merged.  The AxiomMath checkout with its build lives in the
orchestrator's scratchpad (`.lake/packages/Stacks` is a symlink to it); after a container
restart, re-enable swap (`swapon /home/user/.swapfile`) and `sysctl -w
vm.max_map_count=262144` before `lake build SpacesVerified`.
