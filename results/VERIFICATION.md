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

## 2. CI jobs

The workflow is [`.github/workflows/ci.yml`](.github/workflows/ci.yml); it fires on
`push`, `pull_request` and `workflow_dispatch` for every branch.  [`ci/ci.yml`](ci/ci.yml)
is a byte-identical mirror kept for editing: the GitHub connection this project
is committed through cannot create or update a file under `.github/workflows/`
(it lacks the `workflows` permission), so a change made here has to be pasted
in.  Check that the two agree with

```bash
diff <(sed -n '/^name: CI/,$p' ci/ci.yml) .github/workflows/ci.yml
```

1. **`build`** — elan, `lake update`, `lake exe cache get`, `lake build`
   (`FourierMukai`, `WeakApprox`, `StatementCheck`), then
   `lake env lean FourierMukai/Audit.lean`, which prints the axiom set of every
   headline declaration.  Advisory (non-blocking) declaration and style linters.
2. **`statement-check`** — depends on `build`, reuses its oleans, and runs
   `scripts/check_statements.sh`.

### First run, on the installed workflow

Run 1 of `CI` (commit `4546aed`, `push` to `formalization`):

| job | every step | result |
|---|---|---|
| `Lake build (Mathlib cache)` | resolve deps, olean cache, Mathlib cache, `lake build`, axiom audit, linters (advisory), upload oleans | **success** |
| `Independent statement check` | cancelled by hand during "Resolve dependencies"; steps 5–7 skipped | cancelled |

So the build gate is proven in CI: the Lake build of the full tree, the
`FourierMukai/Audit.lean` axiom print, and the artifact upload all pass on a
GitHub runner.  The statement-check gate is proven locally (see below) but has
not yet run in CI.

The starter workflow `blank.yml`, which GitHub's template added and which
echoed "Hello, world!", has been deleted; it was reporting green on commits
whose real CI had not run.

### Both jobs were run locally before installation

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

`lake-manifest.json` is generated by `lake update` and is not committed.
Committing it would freeze the resolution and make the cache key stable, which
is what the BridgelandStability workflow does with its own.

**A known cost, not yet fixed.** `statement-check` re-runs `lake update` and
`lake exe cache get`, which is roughly four minutes of duplicated setup for the
Mathlib oleans the `build` job already downloaded — the cache action only covers
the project's own `.lake/build`.  Folding the statement check into the `build`
job, or caching `.lake/packages/*/.lake/build`, would remove it; both mean
editing the installed workflow by hand, so neither is done.

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
