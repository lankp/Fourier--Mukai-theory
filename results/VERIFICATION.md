# Verification setup

What is run, where, and what each check does and does not establish.  The setup
follows [mattrobball/BridgelandStability](https://github.com/mattrobball/BridgelandStability):
a Lake build of the library against Mathlib's olean cache, plus a separate job
that checks the *statements* the project claims.

## 1. Two build paths over one set of sources

| path | command | runs where |
|---|---|---|
| Lake | `lake update && lake exe cache get && lake build` | CI, any writable checkout |
| script | `./scripts/build.sh` | the development VM: prebuilt read-only Mathlib on `LEAN_PATH`, no writable package directory, no Lake build |

Both compile the same 203 `.lean` files with the toolchain pinned in
`lean-toolchain` (Lean 4.33.1) and Mathlib pinned in `lakefile.toml`
(`v4.33.1`).  `scripts/build.sh` lists the modules in dependency order by hand,
so a new module must be added there as well as to `FourierMukai.lean`.

### Strict elaboration: `autoImplicit = false` is enforced

`lakefile.toml` carries the option block inherited from the AxiomMath/Stacks
configuration, and all three strictness options are now on:

```
autoImplicit = false
relaxedAutoImplicit = false
maxSynthPendingDepth = 3
```

`scripts/build.sh` passes the same three with `-D`, so the Lake path and the
offline path elaborate identically — which is the point of having both.

They were not always on.  When first enabled, the module list failed in 9 of 203
modules with `unknown universe level `u`` and `Unknown identifier `C``:

| module | errors | | module | errors |
|---|---|---|---|---|
| `AisleCoproducts` | 101 | | `SchemeFiniteCoverInduction` | 11 |
| `KProjectiveResolution` | 28 | | `AffineMain` | 4 |
| `ColimitHomologyM4` | 13 | | `IdealNeemanM1` | 3 |
| `WeakApprox/Closure` | 12 | | `NeemanFiniteSupportM4` | 2 |
| | | | `WeakApprox/Setup44Minimal` | 1 |

Isolated on `WeakApprox/Closure.lean`, `-DautoImplicit=false` alone reproduced
the 12 errors while `-DmaxSynthPendingDepth=3` alone gave none, so
`autoImplicit` was the cause rather than the other two options.

**One cause, in all nine.**  `universe` and `variable` commands are scoped to the
enclosing `namespace`/`section`.  Each of the nine files closes and reopens a
namespace with a new, partial prelude, so later blocks used level names and
variables that had gone out of scope and were silently re-bound as implicit
binders.  (This diagnosis is from member m6 of run `smww7domt`, which was asked
to look across all nine files after fixing one; it matched every file.)  The fix
restores the complete prelude in each reopened block: one or two `universe` lines
per block, plus three declarations that needed an explicit
`variable` (`{ι : Type ι}` in `ColimitHomologyM4`, `{P : Scheme.{u} → Prop}` in
`SchemeFiniteCoverInduction`) or explicit universe parameters
(`hasCoproduct_of_reflective.{uC, uD, v}`).  The whole change is 44 inserted and
10 deleted lines across the nine files; no proof, import or option inside a file
was touched.

**Why this cannot have changed a statement.**  Before touching anything, every
declaration in the nine modules was dumped with `#check @name` under
`set_option pp.all true` — 502 declarations, which prints the fully qualified
type with every implicit binder, instance argument and universe level.  After the
fix the dumps are **byte-identical**, not merely isomorphic: a bindered name that
moved, an instance that appeared, or a universe that merged would have shown in
the diff.  Then the full strict build was run over all 203 modules with zero
errors.  The scripts and the baseline dumps are the ones used for the earlier
measurement; the procedure is the one under "The protocol used for every claim"
below.

## 2. CI

The workflow is [`.github/workflows/ci.yml`](.github/workflows/ci.yml); it fires on
`push`, `pull_request` and `workflow_dispatch`.  [`ci/ci.yml`](ci/ci.yml) is a
byte-identical mirror kept for editing: the GitHub connection this project is
committed through cannot create or update a file under `.github/workflows/`
(it lacks the `workflows` permission), so a change made here has to be pasted
in.  Check that the two agree with

```bash
diff <(sed -n '/^name: CI/,$p' ci/ci.yml) .github/workflows/ci.yml
```

One job, `build-and-check`, in this order:

1. elan, `lake update`;
2. restore the olean cache — the project's `.lake/build` **and** the dependency
   build directories `.lake/packages/*/.lake/build`;
3. `lake exe cache get` (a hash check when the cache hit, a download otherwise);
4. `lake build` — `FourierMukai`, `WeakApprox`, `StatementCheck`;
5. `lake env lean FourierMukai/Audit.lean`, which prints every headline
   declaration's axiom set and fails if anything stops elaborating;
6. `scripts/check_statements.sh` — the blocking gate;
7. the linters, advisory;
8. upload of the re-elaborated statement surface.

The installed copy runs this single job — it was pasted in as commit `0cf48dc`
and went green as run 9, measured below.

### The single job, as it now runs

`CI` run 9 (commit `0cf48dc`, the paste of the folded workflow) and run 10
(commit `318364a`): both **success**, one job, every step green.

| step | run 9 (cache miss) | run 10 (cache hit) |
|---|---|---|
| Resolve dependencies | 91s | 97s |
| Restore olean cache | 14s | 72s |
| Get Mathlib cache | 5s | 5s |
| **Build** | **333s** | **3s** |
| Axiom audit | 3s | 3s |
| Check statements against the baseline | 3s | 3s |
| Linters (advisory) | 20s | 9s |
| Upload the re-elaborated surface | 1s | 1s |
| Post Restore olean cache (save) | 42s | 9s |
| **job total** | **516s** | **208s** |

Run 9 was slower than the two-job version it replaced (2m15s + 1m43s), and the
table shows why: the olean cache it restored did not let Lake skip the compile,
so it rebuilt all 203 modules and then saved a bigger cache.  Run 10 restored
that cache and `Build` fell to 3s, so the job is now **3m28s against 3m58s** for
the two jobs it replaced, with one `lake update` instead of two.

What the caches API shows, measured after run 9:

| entry | size | contents |
|---|---|---|
| created 15:31 (end of run 9) | 1.9 GB | `.lake/build` **and** `.lake/packages/*/.lake/build` |
| created 15:00 (earlier runs) | 47 MB | `.lake/build` only |

1.9 GB is GitHub's compressed size and the repository's whole cache footprint —
comfortably inside the 10 GB budget, so the caveat about the dependency cache
costing too much does not currently bite.  Restoring it costs 72s, which is the
price of the 330s it saves.

**The dominant cost is now `lake update` at about 95s**, because
`lake-manifest.json` was not committed and every run re-resolved Mathlib.  The
manifest is committed now (see below) and the step is gone from the mirror.

### `lake update`, kept on purpose

The manifest is committed, so `lake update` no longer does resolution work — but
it was removed once and put back, because it is what clones Mathlib.  The two
runs, same tree otherwise:

| step | run 12 (with `lake update`) | run 13 (without) |
|---|---|---|
| resolve dependencies | 72s | — |
| restore olean cache | 50s | 73s |
| get Mathlib cache | 3s | **119s** |
| build | 2s | 2s |
| axiom audit | 2s | 4s |
| statement check | 3s | 3s |
| linters (advisory) | 6s | 16s |
| cache save | 6s | 39s |
| **total** | **157s** | **265s** |

Without the step the clone happens inside `lake exe cache get`, which then costs
119s on top of the cache restore instead of 3s; the cache save also grew.  So the
step pays for itself and the mirror keeps it.

**This is the floor for this setup.**  Each run has to materialise about 1.5 GB of
Mathlib sources and 1.9 GB of oleans, and the steps that move them — cache
restore, clone, cache save — are 128s of run 12's 157s.  Getting under 90s needs
a machine that does not start from nothing each time: a self-hosted runner with a
persistent `.lake`, or a container image with Mathlib already built.  That is an
infrastructure decision, not a workflow tweak.

The statement check needs exactly the oleans the build produces.  A second job
bought a second `lake update`, a second Mathlib cache fetch and an artifact
hand-off, for no parallelism — the check always waits for the build.  Measured on
runs 3–6: 2m15s for the build job and 1m43s for the check job, of which roughly a
minute was that duplicated setup.

### What `paths-ignore` does and does not skip

Documentation-only pushes are skipped: `**.md`, `ci/**`, `attachments/**`,
`LICENSE`, `formalization.yaml`.  **`results/**` is not ignored**, because
`results/statement-baseline.txt` is the file the statement check compares
against — a push that changes only the baseline must still run the check, or the
baseline could be altered without anything noticing.

### What the first runs cost, as measured

`CI` run 4 (commit `b8269d4`, `push` to `formalization`) — and run 3, the same
commit on `main`:

| job | every step | result | time |
|---|---|---|---|
| `Lake build (Mathlib cache)` | resolve deps, olean cache, Mathlib cache, `lake build`, axiom audit, linters (advisory), upload oleans | **success** | 2m15s |
| `Independent statement check` | resolve deps, download oleans, Mathlib cache, check against the baseline, upload the re-elaborated surface | **success** | 1m43s |

Both green on both branches, and green again on runs 5 and 6 (commit `7bc29df`).
The step that matters in the second job is `scripts/check_statements.sh`: it exits
non-zero on any drift from `results/statement-baseline.txt` or on any `sorryAx`,
so a green step means the 17 pinned statements still match their recorded types
and axiom sets on a clean runner.

Runs 1 and 2 of the installed workflow were cancelled by hand mid-flight, and
runs on superseded commits are cancelled automatically by the `concurrency`
group (`${{ github.workflow }}-${{ github.ref }}`), which is the intended
behaviour for a repository that pushes both branches in lockstep.

The starter workflow `blank.yml`, which GitHub's template added and which echoed
"Hello, world!", has been deleted; it was reporting green on commits whose real
CI had not run.

### One caveat on the dependency cache

`.lake/packages/*/.lake/build` for Mathlib is several GB and counts against
GitHub's 10 GB per-repository cache budget.  If this repository approaches that
limit, dropping the second cache path costs one `lake exe cache get` and nothing
else — the build does not depend on the cache being there.

### Both jobs were also run locally before installation

The workflow was also executed end to end in a Lake copy of the tree on the
development VM:

| step | result |
|---|---|
| `lake update` | resolved Mathlib at `v4.33.1`, wrote `lake-manifest.json` |
| `lake exe cache get` | 8690 files downloaded and decompressed |
| `lake build` | **Build completed successfully (3979 jobs)** |
| `lake env lean FourierMukai/Audit.lean` | exit 0, zero errors, nine `sorryAx` |
| `scripts/check_statements.sh` | 17 declarations match the baseline |
| `lake exe runLinter` | unused-argument lints in `Scheme/Statements.lean` — advisory, as configured |

Coverage check: of the 202 modules listed in `scripts/build.sh`, 201 receive an
olean from `lake build`; the 202nd is `FourierMukai/Audit.lean`, which the
workflow compiles explicitly.  So the Lake path covers what the script path
covers.

`lake-manifest.json` is committed, pinning Mathlib at `0df444a3` (the `v4.33.1`
tag), so the resolution cannot drift between runs even though `lake update` still
runs -- it is there for the clone, which is the measured reason it stays.

**A known cost, since fixed.** This section used to end by noting that
`statement-check` re-ran `lake update` and `lake exe cache get`, roughly four
minutes of duplicated setup.  Both jobs are folded into one and the cache now
covers the dependency build directories; the numbers are in "The single job, as
it now runs" above.

## 3. The independent statement check

`StatementCheck.lean` prints, for each headline result, its full type (`#check`
with implicits) and its axiom set (`#print axioms`).
`scripts/check_statements.sh` re-elaborates that file, refuses any line
mentioning `sorryAx`, and diffs the output against
`results/statement-baseline.txt`:

```bash
scripts/check_statements.sh            # check against the baseline
scripts/check_statements.sh --update   # re-record after an intended change
```

17 declarations are pinned: GL26 Theorem 1.1 (affine, three variants), Lemmas
2.25 (six forms, including the no-proper-flat one), 2.26 and 5.4, LP Theorem 1.1
(two forms), and the four supported-base results.  All 17 print
`[propext, Classical.choice, Quot.sound]`; the last run recorded 17 axiom lines
and no `sorryAx`.

**What it establishes.**  That the statements have not drifted: a silently
weakened conclusion, a strengthened hypothesis, or a newly introduced axiom
fails the diff even when every proof still compiles.  This is the cheapest form
of the failure that has actually happened in this project — a docstring claiming
more than the type said, and a statement whose premise was invisible.

**What it does not establish.**  That the proofs are correct against a trusted
kernel.  BridgelandStability closes that gap with a generated `Challenge`
library (Mathlib-only import closure) replayed through `lean4export` and
`comparator`; the analogous step here needs a standalone challenge library whose
import closure is Mathlib alone, which the current statement layer does not yet
have — it imports the whole development by design.

## 4. The protocol used for every claim

1. compile the module from the repository root and check the **exit status**;
2. `grep` the output for `error` — `#print axioms` prints even when a file does
   not compile, so an audit line alone proves nothing (this is exactly how one
   non-compiling module was once accepted);
3. `grep` for `sorryAx`, and flatten every `depends on axioms` line before
   filtering, because they wrap across lines;
4. read the proof, not only the statement, where a gap could hide;
5. run the **full** `./scripts/build.sh` — a per-file compile can read a stale
   `.olean` and miss a name clash that the umbrella build catches.

A green build does not establish source fidelity either.  Fidelity is checked by
reading the paper: `results/AFFINE.md` carries one row per cited input,
`results/GL26_SCHEME_DEPENDENCE.md` carries the theorem-by-theorem audit against
`main-4.tex`, and the statement layer's docstrings name the results as printed.
