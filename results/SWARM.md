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

## Wave 2 candidates

From `README.md`, "What is open", and the coverage map:

* the last adjunction of the affine recollement (`jStar ⊣ jUpper`, via the
  tensor–Hom adjunction on `RΓ_Z(A)`, Stacks 0A6R);
* Lemma 7.17 in the abstract form of `Scheme/Duality.lean`;
* correcting the stale numbering listed at the end of `results/COVERAGE.md`
  (`corollary_12_10Statement` → `corollary_12_4Statement` and docstrings);
* the remaining pieces of weak approximability for qcqs schemes with support
  (`results/SCHEMES.md`).

## Log

| wave | task | session | merged as | outcome |
|---|---|---|---|---|
| 1 | `wave1/units` | `session_0111iGd6mLyx21wsZDAN46ta` | `611bba9` (merge of `3e2b208`) | C.1 and 7.10: P (C.1 (2), 7.10 in `Cat`); verified: build, audit 37 clean, statement check OK |
| 1 | `wave1/lemma-2-4` | `session_0111iGd8UAfu1fhMqf2yVMaq` | `22ecf48` (merge of `b0d3f63`) | Lemma 2.4: C (converse on Neeman's Bousfield triangles); verified: build, audit 31 clean, statement check OK |
| 1 | `wave1/appendix-b` | `session_0111iGd5Q2nuaHDR5zbDA1gd` | `7fa701b` (merge of `7ef8d66`, import conflict resolved by keeping both) | B.4, B.5, B.7, B.10: P; verified: build, audit 59 clean, statement check OK, hypotheses satisfiable |
| 1 | `wave1/mates-calculus` | `session_0111iGd55yqjemjonMmL7vdQ` | `e25c447` (merge of `0a93ce8`, import/audit conflict resolved by keeping both) | 7.2(1), 7.4, 7.6, 7.9: P in `Cat`; verified: build, audit 45 clean, statement check OK |
| 1b | `wave1b/compactness-09sn` | `session_0111iGd5kWqnDCBrK3MiDM4G` | | started 25 Nov 2026: additive compactness for Lemmas 2.4/2.5 after `IsCompact` was found uninhabited (`fdea729`); Lemma 2.4's converse from Stacks 09SN |
