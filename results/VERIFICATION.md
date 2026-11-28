# Verification

What is checked before a result counts as proved, and where each check runs.  The earlier,
longer version of this file (CI history, the Lean 4.33 build paths) is in
[`archive/VERIFICATION-2026-11-26.md`](archive/VERIFICATION-2026-11-26.md).

## Libraries

| library | contents | build | where it runs |
|---|---|---|---|
| default (`FourierMukai`, `WeakApprox`, `StatementCheck`) | categorical results, LP26 §§2–4 and Theorem 1.1, the older affine and interface layers | `lake build` (~4 min with the Mathlib cache) | every session, CI |
| `Spaces` | algebraic spaces on AxiomMath's **definitions** (`scripts/axiommath/spaces-imports.txt`); every AxiomMath theorem used is a tagged hypothesis (`…Input : Prop`, AxiomMath's statement verbatim, with its Stacks tag) | `lake build Spaces` (~4 700 AxiomMath modules; ~1 h the first time) | every session |
| `SpacesVerified` | discharges each tagged hypothesis by the AxiomMath theorem it names, so the `Spaces` results hold with nothing assumed | `lake build SpacesVerified` (~14 600 AxiomMath modules, ~12 h, peak ~25 GB: 16 GB swap, `vm.max_map_count=262144`; the Proj/Chart/Twist cluster with `LEAN_NUM_THREADS=1`) | a dedicated cloud worker per wave (`wave<N>/verified`) |

Toolchain: Lean and Mathlib `v4.35.0`; AxiomMath/Stacks pinned at `f56a316`.  The project
compiles with `autoImplicit = false`, `relaxedAutoImplicit = false`, `maxSynthPendingDepth = 3`.

## The seven checks (CLAUDE.md)

A result is proved only after all of:

1. its module compiles, exit 0;
2. no `error` in the output;
3. no `sorryAx`; the flattened `#print axioms` sets (`Spaces/Audit.lean`, `FourierMukai/Audit.lean`)
   are within `propext`, `Classical.choice`, `Quot.sound`;
4. the statement is read against the manuscript (`manuscripts/`) and the proof is read;
5. **non-vacuity**: every hypothesis-carrying notion is shown satisfiable by an example;
6. the whole project builds;
7. the pinned statements still match (below).

Workers run them on their branch; the orchestrator re-runs 1–3 and 5–7 on the merge (the
`SpacesVerified` build only in the `verified` worker's container: it does not fit the
orchestrator's) and does step 4 itself.

## Pinned statements

`scripts/check_statements.sh` re-elaborates a file of `#check`s and `#print axioms` and compares
it with a recorded baseline, so a weakened statement or a new axiom fails even when every proof
compiles.  Only the orchestrator re-records a baseline (`--update`), for additions it has checked.

| command | file | baseline | pinned |
|---|---|---|---|
| `scripts/check_statements.sh` | `StatementCheck.lean` | `results/statement-baseline.txt` | 15 |
| `scripts/check_statements.sh --spaces` | `StatementCheckSpaces.lean` | `results/statement-baseline-spaces.txt` | 9 |
| `scripts/check_statements.sh --verified` | `StatementCheckVerified.lean` | `results/statement-baseline-verified.txt` | 98 recorded; 48 added in wave 9 (LP26's unconditional forms), to be re-recorded by `wave10/verified` |

## CI

`ci/ci.yml` mirrors the installed `.github/workflows/ci.yml` (which this repository's GitHub
connection cannot write): `lake build` and `scripts/check_statements.sh` on every push that
touches Lean.  `Spaces` and `SpacesVerified` are too large for CI and are checked as above.
