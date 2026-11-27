# Handoff: what the orchestrator has outside the repository

A new orchestrator session starts in a fresh container and sees only the repository.
Everything the current orchestrator keeps in its scratchpad, its uploads or in background
processes, and that a successor needs, is listed here (CLAUDE.md, "Handoff").  Private items
are never committed; they are passed to the successor by session message.  The manuscripts are
in the repository (`manuscripts/`).

Last updated: 27 November 2026, 23:20 UTC (wave 9: three tasks merged; verified running; pending items in `results/SWARM.md`).

## Running in the background

| what | where | how to redo it |
|---|---|---|
| hourly scheduled task "FM swarm: hourly wave check" | `trig_018gGiqMfFuTFks4J8LCQvp2`, fires into the orchestrator session | its prompt is the orchestration loop of `ORCHESTRATOR.md`; a successor creates its own (`create_trigger`) and deletes this one |
| wave 9 workers | sessions in `results/SWARM.md`, tag `fm-wave9` | cloud workers push their branches |

## Outside the repository, in the orchestrator's container

| what | where | for a new session |
|---|---|---|
| AxiomMath checkout with its build (~17 GB) | scratchpad; `.lake/packages/Stacks` is a symlink to it | `lake build Spaces` / `SpacesVerified` rebuilds it (hours; `SpacesVerified` needs ~14 GB of memory: swap, `vm.max_map_count=262144`) |
| other private material of the maintainer's (one directory, readable only by the orchestrator) | scratchpad | handed over by session message (`send_message`) to the new orchestrator, never through the repository |
| local subagent clones | `/home/user/wt-<slug>` | each pushes its branch; delete after merge |

## Scratchpad contents

After the clean-up of 26 November 2026 the scratchpad holds exactly: the AxiomMath checkout,
the build driver and log of the running AxiomMath build, and one private directory.  Logs,
probes, old repository copies and manuscript excerpts were deleted; reusable tools are in
`scripts/axiommath/`.  The local checkout's stale refs to the pre-rewrite history were pruned
and its reflog expired, so it no longer holds the removed manuscripts.

## Long work

The orchestrator's container is reclaimed when its session is idle (CLAUDE.md, "Robust long
work"): the AxiomMath / `SpacesVerified` build runs in the cloud worker `wave8/axiommath-verified`;
the scratchpad's own AxiomMath build was stopped (27 November, 03:15 UTC); its partial build in
the scratchpad checkout is kept as a fallback.

## Tools

Append-only merge conflicts (`Spaces.lean`, `Audit.lean`): `scripts/swarm/keep_both.py`.
AxiomMath closure check: `scripts/axiommath/built.py`; AxiomMath build: `scripts/axiommath/build.sh`.

## Container set-up after a restart

The container restarts often (twice on 26–27 November): files and uploads survive, but swap,
`vm.max_map_count` and running builds do not.  Restore them, and restart the AxiomMath build
(`scripts/axiommath/build.sh`; Lake skips what is built).  `swapon /home/user/.swapfile` (8 GB) and `sysctl -w vm.max_map_count=262144` before
`lake build SpacesVerified`.
