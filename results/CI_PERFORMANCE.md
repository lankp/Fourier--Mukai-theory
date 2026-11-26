# CI cost, and what would make it fast

The CI job takes about 2m35s, and most of that is moving Mathlib.  This note
records what has been measured, what has been tried, and what the two ways out
would actually cost.  Numbers are from the GitHub Actions API for this
repository; anything marked *estimate* is not measured.

## 1. Where the time goes

| step | run 4 (two jobs) | run 9 | run 10 | run 12 | run 13 |
|---|---|---|---|---|---|
| resolve dependencies | 90s + 77s | 91s | 97s | 72s | — |
| restore olean cache | 8s | 14s | 72s | 50s | 73s |
| get Mathlib cache | 4s | 5s | 5s | 3s | 119s |
| **build** | **2s** | **333s** | **3s** | 2s | 2s |
| axiom audit | 2s | 3s | 3s | 2s | 4s |
| statement check | 2s | 3s | 3s | 3s | 3s |
| linters (advisory) | 12s | 20s | 9s | 6s | 16s |
| cache save | 6s | 42s | 9s | 6s | 39s |
| **total** | 238s | 516s | 212s | **157s** | 265s |

Reading the columns: when the olean cache hits, the build is 2–3s and everything
else is setup and teardown.  Run 9 missed and compiled all 203 modules (333s);
run 13 shows what happens when the Mathlib clone has nowhere to happen — see
below.

## 2. What has been tried

| change | measured effect |
|---|---|
| fold the statement check into the build job | removed a duplicated `lake update` (77s) and cache fetch; run 12 is the result |
| cache `.lake/packages/*/.lake/build` as well as `.lake/build` | 1.9 GB instead of 47 MB; restore 50–73s instead of 8s, but build 333s → 2s on a hit |
| commit `lake-manifest.json` | resolution fixed; `lake update` becomes a no-op check |
| drop `lake update` because the manifest is committed | **worse**: 265s, because `lake update` was what cloned Mathlib; the clone moved into `lake exe cache get` (119s).  Reverted |
| `paths-ignore` for documentation-only pushes | not yet exercised, but it removes the cases that cost 4 minutes for nothing |

## 3. The floor of the current design

Run 12 is 157s.  Of that, 128s is moving Mathlib: `lake update`'s clone (72s) plus
the cache restore (50s) plus the save (6s).  A GitHub-hosted runner starts with an
empty disk every time, so those seconds are not compressible by editing steps —
they are the price of materialising about 1.5 GB of sources and 1.9 GB of oleans.

**Under 90 seconds is not reachable with a hosted runner.**  What follows is what
would be needed.

## 4. Option A: cache more (no infrastructure, one edit)

Cache `.lake` as a whole — sources and both build directories — and then the
clone disappears from the job.

* Sketch: `path: .lake`, plus a `lake update` kept only for the first run.
* Restore time follows the cache size at roughly 30–35 MB/s (47 MB → 8s,
  1.9 GB → 50–73s), so about 2.4 GB → **80–110s (estimate)**.
* Then `lake exe cache get` is a hash check, build 2s, checks 10s, save ~10s.
* Expected total **120–140s (estimate)**: better than 157s, not near 90s.
* Risks: `.lake/packages/mathlib` contains its git directory, which is large; the
  repository's cache budget is 10 GB and this would use about a quarter of it.

Worth one experiment.  It does not reach the target.

## 5. Option B: a prebuilt image

The idea: a container image with the toolchain, Mathlib's sources and the oleans
already inside, so a job starts with everything in place.

**Mathlib's published image is not usable as is.**  The Docker Hub repository
`leanprovercommunity/mathlib` has three tags; the newest, `latest` and `debian`
(407 MB), were last pushed **2024-08-20**, and `gitpod` (757 MB) 2024-08-20.  That
predates Lean 4.33.1 and the Mathlib revision `0df444a3` this repository pins, so
it would not match.  The image would have to be built here.

What that takes:

1. A `Dockerfile` following `lean-toolchain` and `lake-manifest.json`: install
   elan, copy `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, run
   `lake update` and `lake exe cache get` so that `.lake/packages/mathlib/.lake/build`
   and `~/.elan` are baked in.  Expect a **6–8 GB image** (Mathlib's `.lake` alone
   was 7.2 GB in this VM), so it needs a registry with layer caching.
2. A second workflow that rebuilds and pushes it whenever `lean-toolchain` or
   `lake-manifest.json` changes, tagged by the manifest revision:
   `ghcr.io/lankp/fourier-mukai-ci:0df444a3`.
3. The CI job gets `container: image: ghcr.io/lankp/fourier-mukai-ci:0df444a3`, a
   step to copy or hard-link the baked `.lake` into the workspace
   (`cp -al /opt/mathlib-cache/.lake .`), then `lake build`, the audit and the
   statement check.

**What it buys on a hosted runner: less than it looks.**  The runner still has to
pull the image, and pulling a 6–8 GB image costs at least as much as restoring a
2 GB cache — measured restore rates here are 30–35 MB/s, so **a cold pull is in
the same 2–4 minute range (estimate)**.  The image only wins when the layers are
already on the machine, which means a persistent Docker daemon — that is Option C
with extra steps.  What the image does buy, unconditionally, is simplicity: no
cache action, no clone, no cache key to get wrong.

## 6. Option C: a self-hosted runner

This is the one that gets under 90s, because the disk persists.

* **Machine**: 4–8 vCPU, 16 GB RAM, 60 GB SSD.  Mathlib's `.lake` is 7.2 GB, the
  toolchain a few GB, so 60 GB leaves room for two checkouts.
* **Register**: repository Settings → Actions → Runners → New self-hosted runner,
  then `./config.sh --url <repo> --token <token>` and `sudo ./svc.sh install` to
  run it as a service.  Label it, e.g. `lean`.
* **Workflow**: `runs-on: [self-hosted, linux, x64, lean]`, and keep the working
  copy between runs — either `actions/checkout` with `clean: false` in a fixed
  path, or no checkout action at all plus a `git fetch && git checkout` step.
  `lake update` and `lake build` are then incremental.
* **Expected timings (estimate)**: first run on a fresh machine 150s+, as now;
  after that, a push touching one module rebuilds that module and its dependents —
  tens of seconds — and a push touching no `.lean` file is skipped by
  `paths-ignore` anyway.
* **Maintenance**: toolchain and Mathlib updates (`lake update`, `lake exe cache
  get` when the pin moves), disk pruning, and the machine being up.  A small VM is
  in the tens of dollars a month.
* **Concurrency**: one runner runs one job; a queue forms if several pushes land
  together.  The existing `concurrency` group cancels superseded runs per branch,
  which mostly covers this.

### The security problem, and it is real here

GitHub's own documentation says, of self-hosted runners:

> We recommend that you only use self-hosted runners with private repositories.
> This is because forks of your public repository can potentially run dangerous
> code on your self-hosted runner machine by creating a pull request that executes
> the code in a workflow.

**This repository was public when this was written** (it has been private since 26 November 2026, while the manuscripts in `manuscripts/` are unpublished; the self-hosted-runner caution still applies if it is made public again).  A self-hosted runner attached to it would be
reachable by anyone who opens a pull request that runs a workflow on
`pull_request`.  Mitigations, in increasing order of safety:

* trigger only on `push` to `main`/`formalization` and on `workflow_dispatch`,
  never on `pull_request` — then a fork cannot queue a job on the runner;
* restrict the workflow with a label and an `if:` guard on the actor, so only your
  pushes run on it, and let fork PRs use the hosted runners;
* or make the repository private again, which is the configuration GitHub
  recommends and which removes the problem at the root.

Any of the first two works, but it has to be deliberate: the default
`pull_request` trigger in the current workflow is exactly the case the warning is
about.

## 7. Recommendation

1. Keep the current hosted job as the required check.  2m35s for a full build plus
   an independent statement check is not expensive, and it needs no maintenance.
2. If 2m35s is too slow, add Option A as one experiment (~2 min expected), since
   it costs one workflow edit and no infrastructure.
3. Go to Option C only if the number has to be under a minute.  Gate it to your
   own pushes, keep the hosted job as the gate for everything else, and treat the
   public-repository warning above as a requirement rather than a note.
4. Skip Option B unless Option C is in place; on its own it mostly relocates the
   same gigabytes.
