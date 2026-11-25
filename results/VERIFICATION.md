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

### The `[leanOptions]` question, measured

`lakefile.toml` originally carried the option block inherited from the
AxiomMath/Stacks configuration, including

```
autoImplicit = false
relaxedAutoImplicit = false
maxSynthPendingDepth = 3
```

Those are **not** compatible with the current sources.  Running the full module
list with them:

```
lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
     -o <X>.olean <X>.lean
```

fails in 9 modules — `AisleCoproducts` (101 errors), `KProjectiveResolution`
(28), `ColimitHomologyM4` (13), `WeakApprox/Closure` (12),
`SchemeFiniteCoverInduction` (11), `AffineMain` (4), `IdealNeemanM1` (3),
`NeemanFiniteSupportM4` (2), `WeakApprox/Setup44Minimal` (1) — with errors of the
form `unknown universe level `u`` and `Unknown identifier `D``, which is what
`autoImplicit = false` produces when a declaration relies on Lean's automatic
implicit binders.  Isolating the options on `WeakApprox/Closure.lean`:
`-DautoImplicit=false` alone gives the same 12 errors, while
`-DmaxSynthPendingDepth=3` alone produces none.

Conclusion recorded in `lakefile.toml`: the two paths must elaborate the same
way, so the strict options are left off and the build runs with Lean's defaults.
Turning `autoImplicit = false` on is a mechanical clean-up across those 9
modules, not a build setting; it is not done here.

## 2. CI jobs

The workflow is [`ci/ci.yml`](ci/ci.yml); it must be installed at
`.github/workflows/ci.yml` (see the header of that file — the connection this
project is committed through has no `workflows` permission, so the move is a
manual step).

1. **`build`** — elan, `lake update`, `lake exe cache get`, `lake build`
   (`FourierMukai`, `WeakApprox`, `StatementCheck`), then
   `lake env lean FourierMukai/Audit.lean`, which prints the axiom set of every
   headline declaration.  Advisory (non-blocking) declaration and style linters.
2. **`statement-check`** — depends on `build`, reuses its oleans, and runs
   `scripts/check_statements.sh`.

`lake-manifest.json` is not committed; `lake update` generates it from
`lakefile.toml`.  Committing it would freeze the resolution and make the cache
key stable, which is what the BridgelandStability workflow does with its own.

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
