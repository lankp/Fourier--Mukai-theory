# Swarm plan

How parallel Claude sessions work on this repository, and the task queue.  The
rules every session follows are in `CLAUDE.md`; this file is the plan.

## Roles

* **Orchestrator**: one Claude session with the paper sources.  It picks tasks
  from the queue below, starts one worker session per task, sends each its task
  message (the rules, the files it may touch, and the TeX of the statements and
  proofs it needs), reads each worker's branch and report, runs the verification
  steps of `CLAUDE.md` itself on the merge, compares each Lean statement with the
  manuscript, and pushes the merge to `formalization`.  It updates
  `results/COVERAGE.md` and the log below when it merges.
* **Workers**: one cloud session per task, each in its own container, on its own
  branch `wave<N>/<slug>`, ending in a pushed branch and a final report.  No PRs.
* **Maintainer** (a human): has delegated merging to the orchestrator (25 November
  2026) and reads the orchestrator's report after each wave.

This replaces the earlier Ultramath arrangement (`README.md`, "How the work was
produced"), in which members wrote into `.ultramath/` and never committed.  Here a
worker commits to its own branch only, and the orchestrator's verified merge is
the unit of review.

## Choosing tasks

A task is ready when

1. every result its proof uses is P or C in `results/COVERAGE.md`, or is a
   Mathlib result, or is an allowed assumption (`CLAUDE.md`, rule 2);
2. it lives in new files, so that no two workers in a wave edit the same file;
3. its statement can be checked against the manuscript by reading it.

Waves are kept small (three to five workers).  Each worker is a full session, so
cost grows linearly with the wave, and shared files (`FourierMukai.lean`,
`Audit.lean`) are the only expected conflicts.

## Environment

Worker sessions run in the cloud environment `fourier--mukai-theory`, whose
network allows GitHub release downloads, `releases.lean-lang.org` and Mathlib's
cache host `lakecache.blob.core.windows.net`, and whose setup script installs
elan, the pinned toolchain and Mathlib's oleans.  elan's own toolchain download
is refused by the session proxy, so the setup script fetches the toolchain
archive with `curl` and unpacks it into `~/.elan/toolchains/` (that is all
`elan toolchain install` does).

## Wave 1: the categorical layer of §7, Appendix B, Appendix C and §2.1

All four tasks are Mathlib-only category theory, with no geometry and no
interface.  In wave 1, workers do **not** edit `results/COVERAGE.md`; the
orchestrator does that on merge.

| task | results (current numbering, TeX label) | new file | Mathlib to start from |
|---|---|---|---|
| `wave1/mates-calculus` | Lemma 7.4 `lem:morph_adj`; Lemma 7.6 `lem:taking_conjugates_is_taking_mates_twice`; Lemma 7.9 `lem:conjugates_are_functorial`; and the Hom-set square left open in `Prelim/Mates.lean` | `FourierMukai/Prelim/MatesCalculus.lean` | `mateEquiv`, `conjugateEquiv`, `conjugateEquiv_comp`, `mateEquiv_vcomp`/`hcomp` |
| `wave1/appendix-b` | Lemma B.4 `lem:equiv_transadj`; Lemma B.5 `lem:adj_and_equiv_in_trans`; Lemma B.7 `lem:transnat_is_trinat`; Lemma B.10 `lem:triadjoint_iff_adjoint` | `FourierMukai/Prelim/AppendixB.lean` | `Functor.CommShift`, `Adjunction.CommShift` (`Shift/Adjunction.lean`), `NatTrans.CommShift`, `Adjunction.isTriangulated_rightAdjoint` (`Triangulated/Adjunction.lean`, close to B.10) |
| `wave1/lemma-2-4` | Lemma 2.4 `lem:localizing_iff_cpt_gen` | `FourierMukai/Prelim/Lemma24.lean` | `Triangulated/LocalizingSubcategory.lean`; `Prelim/Lemma25.lean` (`SinglyCompactlyGenerated`, `IsLocalizingGenerator`) |
| `wave1/units` | Lemma C.1 `cmp:lem:units`; Lemma-Definition 7.10 `def:adj_equiv` (equivalence of the conditions, in `Cat`) | `FourierMukai/Prelim/AdjunctionUnits.lean` | `Adjunction.ofNatIsoRight`, `Functor.FullyFaithful`, `Bicategory.Adjunction` (`Bicategory/Adjunction/Basic.lean`) |

Out of wave 1 on purpose:

* Lemma 7.8 (`lem:mates_double_cat_iso`, double categories) and Lemma B.2
  (`lem:trans_is_2-cat`, a strict 2-category): they need double-category or
  strict-2-category infrastructure that Mathlib's bicategory library does not
  directly give, and nothing downstream uses them in that form.
* Lemma 7.17 (`lem:base_change_mates_pasting`): categorical in content, but it is
  stated over the base-change maps of `Scheme/Duality.lean`, a shared file.
  Wave 2.

## Wave 2

Launched once wave 1 (including 1b, the compactness re-rendering) is merged.  Four
tasks, each in new files except `wave2/trans-2cat`, which also owns
`Prelim/AppendixB.lean`.

| task | goal | new files | source |
|---|---|---|---|
| `wave2/regular-compact` | `IsCompactAb (ringObject A)` without Neeman's input, after settling in which model (`AffineD` vs `SmallAffineD`) the statement is meaningful; unconditional principal-support weak approximability as a corollary | `Scheme/RegularCompact.lean` | README "What is open" 1; `results/SCHEMES.md` |
| `wave2/jupper` | the last field of `AffineRecollementInput`: `jUpper` with `jStar ⊣ jUpper`, via the tensor–Hom reduction of `Scheme/AffineJUpperTensorHom.lean` | `Scheme/AffineJUpperConstruction.lean` | README "What is open" 2; GL26 Lemma A.4 (affine) |
| `wave2/trans-2cat` | Lemma B.2 (`Trans` is a 2-category over `Cat`), then B.4(5) as an adjunction in that bicategory, removing the B.4 deviation | `Prelim/TransTwoCategory.lean` (+ `Prelim/AppendixB.lean`) | GL26 App. B |
| `wave2/base-change-mates` | Lemmas 7.12 and 7.17, and the maps of 7.13–7.15, over abstract pseudofunctor data, so that they can later discharge fields of `Scheme/Duality.lean` | `Prelim/BaseChangeMates.lean` | GL26 §7.2 |

Done by the orchestrator between waves: the numbering cleanup (`dd45ef4`).

## Wave 3

Launched 25 November 2026 after wave 2 was merged.  Briefs in `results/swarm/wave3/`.

| task | goal | files |
|---|---|---|
| `wave3/fm-cube` | GL26 Lemmas 6.11, 10.1, 10.2 (`α^K`, `β^K`, and that they are mates) in six-functor form over the cube of Setup 2.20, from named inputs (flat base change, projection formula, monoidality, pseudofunctoriality) | new `Scheme/FMCube.lean` |
| `wave3/duality-wiring` | build `PullPushData` from `Scheme/Duality.lean`'s data and turn its 7.12-type coherence fields into theorems via `Prelim/BaseChangeMates.lean` | `Scheme/Duality.lean` + new files |
| `wave3/koszul-inputs` | prove the non-Stacks named inputs of the finite-support affine supported base | new files |
| `wave3/open-closed-glue` | discharge the completion hypothesis of `Scheme/OpenClosedGlue.lean`, towards weak approximability for qcqs schemes with support | new files |

## Wave 4 candidates

* a right adjoint of `Rj_*` without Stacks 0E55 (makes the affine recollement unconditional);
* GL26 Proposition 10.5 and Lemma 10.9 on top of `wave3/fm-cube` (10.5 needs Proposition 9.3 and Lemma 9.1, the latter a `Duality.lean` field);
* Lemma 7.8 (double categories) only if something downstream needs it.

## Log

| wave | task | session | merged as | outcome |
|---|---|---|---|---|
| 1 | `wave1/units` | `session_0111iGd6mLyx21wsZDAN46ta` | `611bba9` (merge of `3e2b208`) | C.1 and 7.10: P (C.1 (2), 7.10 in `Cat`); verified: build, audit 37 clean, statement check OK |
| 1 | `wave1/lemma-2-4` | `session_0111iGd8UAfu1fhMqf2yVMaq` | `22ecf48` (merge of `b0d3f63`) | Lemma 2.4: C (converse on Neeman's Bousfield triangles); verified: build, audit 31 clean, statement check OK |
| 1 | `wave1/appendix-b` | `session_0111iGd5Q2nuaHDR5zbDA1gd` | `7fa701b` (merge of `7ef8d66`, import conflict resolved by keeping both) | B.4, B.5, B.7, B.10: P; verified: build, audit 59 clean, statement check OK, hypotheses satisfiable |
| 1 | `wave1/mates-calculus` | `session_0111iGd55yqjemjonMmL7vdQ` | `e25c447` (merge of `0a93ce8`, import/audit conflict resolved by keeping both) | 7.2(1), 7.4, 7.6, 7.9: P in `Cat`; verified: build, audit 45 clean, statement check OK |
| 1b | `wave1b/compactness-09sn` | `session_0111iGd5kWqnDCBrK3MiDM4G` | `d4177b8` (merge of `1e6714e`) | merged: Lemma 2.5 P, Lemma 2.4 from Stacks 09SN; verified: build, audit 65 clean, statement check OK, non-vacuity shown. Task was: additive compactness for Lemmas 2.4/2.5 after `IsCompact` was found uninhabited (`fdea729`); Lemma 2.4's converse from Stacks 09SN |
| 2 | `wave2/regular-compact` | `session_0111iGd8gkx8KKuiS4T2BpnU` | `fe99a83` (merge of `92e0ca0`) | `IsCompactAb (ringObject A)` proved directly; D(A-Mod) and D_{V(f)} weakly approximable unconditionally; verified: build, audit 69 clean, statement check OK, non-vacuity shown |
| 2 | `wave2/jupper` | `session_0111iGd6ZSNTZ4tDzCc8YEFT` | `2f36bbb` (merge of `9b53b9b`, audit conflict resolved by keeping both) | affine recollement complete from Stacks 0E55; verified: build, audit 74 clean, statement check OK, non-vacuity (f = 0 instance; 0E55 a Stacks result) |
| 2 | `wave2/trans-2cat` | `session_0111iGd7v9afb51rwCpst8LU` | `2c3fee0` (merge of `3072a05`) | B.2 P (strict bicategory, forgetful strict pseudofunctor, uniqueness), B.4(5) honest; verified: build, audit 94 clean, statement check OK, non-vacuity shown |
| 2 | `wave2/base-change-mates` | `session_0111iGd8cvXVrvgCi69XkqVF` | `4beb203` (merge of `3805c22`) | 7.12, 7.17 P (abstract), 7.13–7.15 defined; verified: build, audit 82 clean, statement check OK, non-vacuity (`constPullPushData`) |
