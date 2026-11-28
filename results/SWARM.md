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
  `results/COVERAGE.md` and the log below when it merges, and **updates `README.md`
  when a wave completes** (standing instruction of the maintainer; see `CLAUDE.md`,
  "Git").  It **archives every worker of a wave once that wave is merged, before the
  next wave is launched** (likewise a standing instruction).
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
| `wave2/regular-compact` | `IsCompactAb (ringObject A)` without Neeman's input, after settling in which model (`AffineD` vs `SmallAffineD`) the statement is meaningful; unconditional principal-support weak approximability as a corollary | `Scheme/RegularCompact.lean` | README "What is open" 1; `results/archive/SCHEMES.md` |
| `wave2/jupper` | the last field of `AffineRecollementInput`: `jUpper` with `jStar ⊣ jUpper`, via the tensor–Hom reduction of `Scheme/AffineJUpperTensorHom.lean` | `Scheme/AffineJUpperConstruction.lean` | README "What is open" 2; GL26 Lemma A.4 (affine) |
| `wave2/trans-2cat` | Lemma B.2 (`Trans` is a 2-category over `Cat`), then B.4(5) as an adjunction in that bicategory, removing the B.4 deviation | `Prelim/TransTwoCategory.lean` (+ `Prelim/AppendixB.lean`) | GL26 App. B |
| `wave2/base-change-mates` | Lemmas 7.12 and 7.17, and the maps of 7.13–7.15, over abstract pseudofunctor data, so that they can later discharge fields of `Scheme/Duality.lean` | `Prelim/BaseChangeMates.lean` | GL26 §7.2 |

Done by the orchestrator between waves: the numbering cleanup (`dd45ef4`).

## Wave 3

Launched 25 November 2026 after wave 2 was merged.  Briefs in `results/swarm/archive/wave3/`.

| task | goal | files |
|---|---|---|
| `wave3/fm-cube` | GL26 Lemmas 6.11, 10.1, 10.2 (`α^K`, `β^K`, and that they are mates) in six-functor form over the cube of Setup 2.20, from named inputs (flat base change, projection formula, monoidality, pseudofunctoriality) | new `Scheme/FMCube.lean` |
| `wave3/duality-wiring` | build `PullPushData` from `Scheme/Duality.lean`'s data and turn its 7.12-type coherence fields into theorems via `Prelim/BaseChangeMates.lean` | `Scheme/Duality.lean` + new files |
| `wave3/koszul-inputs` | prove the non-Stacks named inputs of the finite-support affine supported base | new files |
| `wave3/open-closed-glue` | discharge the completion hypothesis of `Scheme/OpenClosedGlue.lean`, towards weak approximability for qcqs schemes with support | new files |

## Direction: full generality (maintainer, 26 November 2026)

The maintainer directed that the whole repository now aims at GL26 and LP26 **in
their full generality as stated in the current manuscripts** (in `manuscripts/`):
algebraic spaces, `D_qc`, `Perf`, `D^b_coh`, `Lf^*`, `Rf_*`, `⊗^L` in the sense of
GL26 §2.2.  The abstract interfaces (`Paper/DerivedSetup.lean`, `FMSetup`,
`StacksInterface`, the affine `D(A-Mod)` model) are the categorical engine, not the
target.  The geometric foundation is **AxiomMath/Stacks** (kernel-checked,
`sorry`-free, Lean/Mathlib v4.35.0), imported as a Lake dependency, pinned at
`f56a316ddf7a930906d88b78d6f9a2668cffd0cf`.  It has algebraic spaces, `D(𝒪_X)` on
the small étale site, `D_QCoh`, perfect and pseudo-coherent objects, Stacks 0DKN
relative perfectness, compact generation of `D_qc` for qcqs spaces, duality for
spaces and Nagata compactification; 132 of the 150 Stacks tags the two papers cite
carry an AxiomMath `@[stacks]` attribute.  Its import closure for `D_qc` with
pushforward is about 7.4k modules (2.2M lines), and no olean cache is published, so
the orchestrator builds that slice once and distributes the oleans to workers.

Plan: (1) migrate to v4.35.0; (2) map the paper's notions to AxiomMath and audit
their fidelity; (3) build and distribute the AxiomMath slice; (4) a geometric layer
`FourierMukai/Spaces/` with GL26 §2.2's notions and the paper's headline results
stated over algebraic spaces (new pinned statements, checked against the
manuscript by the orchestrator); (5) prove them, section by section, using the
existing categorical engine.

## Wave 4 (re-planned for the direction above)

The wave-4 briefs prepared earlier (affine Koszul repair, open/closed non-vacuity
in the affine model, `R j` right adjoint, Stacks registration) are deferred to
`results/swarm/archive/deferred/`; `wave4/koszul-repair` was launched at 07:27 UTC and
stopped minutes later when the direction changed.  Briefs in `results/swarm/archive/wave4/`.

| task | goal | files |
|---|---|---|
| `wave4/axiommath-api-map` | map GL26 §2.2–2.4's notions and functors to AxiomMath declarations, with a fidelity verdict per definition; gaps; import-closure cost | `results/AXIOMMATH_MAP.md` |
| `wave4/axiommath-tag-map` | every Stacks tag cited in GL26/LP26 against AxiomMath: declaration, scope, spaces vs schemes, verdict; `S` rows of `ASSUMPTIONS.md` against AxiomMath | `results/AXIOMMATH_TAGS.md`, `scripts/axiommath/` |
| `wave4/toolchain-435` | migrate the tree to Lean/Mathlib v4.35.0 (no new dependency yet) | toolchain files, any `.lean` file the build needs |

Wave 4 closed 26 Nov 2026, 08:50 UTC: all branches merged, README updated, workers archived.
Environment: `cache.mathlib.org` added to the allowed hosts (Mathlib v4.35.0's cache).
AxiomMath build trial: the 67-module base slice builds in 90 s; the 8.9k-module
statement slice (T1) is building in the orchestrator session (about 4–5 h on 4 cores);
build products are about 0.6 MB per module without the `ir/*.setup.json` intermediates.

Wave 5 closed 26 Nov 2026, 12:45 UTC: neeman-3-2-inputs, neeman-affine-support,
neeman-prune and open-inputs merged and archived; `spaces-foundations` moves to wave 6
(the AxiomMath build is still running: `MilnorPatching.Relative` needs ~13.6 GB and
builds only with swap; workers cannot build AxiomMath themselves).

## Wave 5 (briefs in `results/swarm/archive/wave5/`)

**Maintainer's goal for wave 5 (26 November 2026):** besides the geometric layer,
LP26 is addressed with **Neeman's weak approximability for affine schemes with
support formalized and verified, not assumed**.  LP26's Corollary 1.2
(`cor:weak_approx_spaces`) combines Neeman 2024, Theorem 3.2(iv) (`D_qc,Z(X)` weakly
approximable for `X` qcqs and `Z` closed with quasi-compact complement) with the
induction principle for algebraic spaces; the affine case is the base.  State of the
tree: `D(A-Mod)` and `D_{V(f)}(A-Mod)` (principal support) are proved weakly
approximable unconditionally (`Scheme/RegularCompactEndpoints.lean`); the
finite-list case `V(f₁,…,fₙ)` goes through the refuted `KoszulScalarSupportInput`
(vacuous) and the open `KoszulPowerCoprodInput` and `KoszulDetectionInput` (Stacks
0A9A).  Wave-5 tasks for this goal:

| task | goal |
|---|---|
| `wave5/neeman-affine-support` | weak approximability of `D_{V(I)}(A-Mod)` for every finitely generated `I` (every finite list), with **no** named input: drop the refuted input (the deferred `koszul-repair` brief), prove `KoszulPowerCoprodInput`, and prove or import (AxiomMath 0A9A) `KoszulDetectionInput`; non-vacuity by an instance |
| `wave5/neeman-3-2-inputs` | maintainer, 26 Nov 2026: Neeman 2024 Thm 3.2 is no longer assumed; inventory its uses (`results/archive/NEEMAN_3_2.md`), prove what a GL26/LP26 path needs (first (i) compact ⇒ perfect for `D(A)`, both models, via compactness of the regular module and Stacks 09SR), unconditional corollaries in new files |
| `wave5/neeman-prune` | maintainer: discard what is not needed (`results/archive/NEEMAN_3_2.md` §4): endpoints take Stacks 09SR instead of the Neeman inputs (incl. the pinned `affine_theorem_1_1_neeman_only`), delete `Neeman_3_2_ii`, `NeemanPublishedWeakApproximation`, the 066S `NeemanAffineCompactModelInput` chain |
| `wave5/open-inputs` | maintainer: only AxiomMath/Stacks is assumed; triage every named non-Stacks input (Stacks / Mathlib / prove / delete / setup) into `results/OPEN_INPUTS.md`, with the shortest path to unconditional headlines and a task grouping for the next waves |
| `wave5/spaces-foundations` (after the AxiomMath bundle is published) | the algebraic-space layer `FourierMukai/Spaces/`: `D_qc`, `Perf`, `D^b_coh`, support; `Lf^*`, `Rf_*`, `⊗^L`; GL26's `f`-perfect and `f`-quasi-perfect; integral transforms `Φ_K`; all non-vacuous |
| `wave5/neeman-affine-transport` (after AxiomMath is imported) | transport it along AxiomMath's `D_qc(Spec A) ≃ D(A)` with supports matched: `D_qc,Z(Spec A)` weakly approximable for `Z` closed with quasi-compact complement, in AxiomMath's model — the base case of LP26 Cor 1.2 |

Then (wave 6 or later): Neeman's Theorem 3.2(iv) for qcqs schemes and LP26 Cor 1.2
for qcqs algebraic spaces by LP26 Theorem 1.1 and the induction principle (Stacks
08GL), all without assuming Neeman's result.

Other candidates (from the earlier plan, if they feed the geometric statements):
GL26 Proposition 10.5 and Lemma 10.9 on `Scheme/FMCube.lean`; `DerivedPseudofunctorInput`.

## Wave 6 (briefs in `results/swarm/archive/wave6/`; effort per ORCHESTRATOR.md item 12)

Planned from `results/OPEN_INPUTS.md`.  Affine-only versions of what AxiomMath proves
for spaces (0E55 coextension, `⊗^L` on `D(A-Mod)`) are **not** scheduled: the
geometric layer supersedes them.

| task | effort | goal |
|---|---|---|
| `wave6/vacuity-refutations` | high | prove F1 (`¬ HasCoproducts.{u+1} (AffineD A)`, `A` nontrivial), F2 (no compact `IsGenerator` in `D(ℤ)`), F3 (`QuasicoherentSerreInput (Spec ℤ)` false); then the orchestrator unpins/replaces the vacuous pinned endpoints |
| `wave6/lp26-paper-hypotheses` | high | LP26 Thm 1.1 with exactly the paper's hypotheses: compactly generated `t`-structures (AJS), BNP Cor 3.10(1), generator change |
| `wave6/spaces-foundations` | high | the algebraic-space layer on AxiomMath; **runs in the orchestrator container** (local subagent), because releases cannot be created from these sessions and worker containers cannot build AxiomMath (8.9k modules, ~6 h; `MilnorPatching.Relative` needs ~13.6 GB, i.e. swap). AxiomMath enters `lakefile.toml` only through a separate `Spaces` library outside `defaultTargets`, so workers' default `lake build` never compiles it. |
| `wave6/prune-dead-inputs` | medium | after vacuity-refutations: delete the triage's "delete" rows (keep `M4Unconditional`/`M6Unconditional`) |

**Wave 6 closed (26 November 2026).**  All five worker branches merged (Log); the
orchestrator then fixed `Tag09SRPaper` (09SR for triangulated categories) and landed
`SpacesVerified`, which discharges every tagged AxiomMath input of `Spaces`, so nothing in
the algebraic-space layer is assumed.  Workers archived.

## Wave 7 (closed 27 November 2026, workers archived; briefs in `results/swarm/archive/wave7/`)

The algebraic-space layer now assumes nothing, so wave 7 builds on it.  Three Lean tasks
run in parallel, each with its own directory and its own `Inputs.lean` for tagged AxiomMath
inputs (no shared file but `Spaces.lean` and `Spaces/Audit.lean`, both append-only).  The
AxiomMath theorem modules they cite are built in the orchestrator's container, so the
orchestrator can discharge their inputs in `SpacesVerified` at merge.

| task | effort | goal |
|---|---|---|
| `wave7/spaces-affine-base` (`session_0111iGd775NkFveWdRq8i6DW`) | high | LP26 Cor 1.2 affine base over AxiomMath's model: `D_{V(I)}(A-Mod) ≌ Spaces.DqcSupported (Spec A) V(I)` and transport of `NeemanAffineSupport.satisfiesPaperWA_of_fg` (OPEN_INPUTS 5.1) |
| `wave7/spaces-compact-generation` (`session_0111iGd895xp83khYFFveVy2`) | high | GL26 Lemma A.9 / Neeman 3.2(iii) over qcqs spaces from AxiomMath 0AEC, 0AED, 09M8, 09SR (replaces OPEN_INPUTS 2.10) |
| `wave7/spaces-base-change` (`session_0111iGd9Cxes2MsiML9Zjf5L`) | high | `PullPushData` for spaces (0D6D, 0D6E, 07A6; removes `DerivedPseudofunctorInput` for spaces) and GL26 Lemmas 7.12, 7.17, 6.11, 10.1 over spaces (08IR, 08IN, 08EU) |
| `wave7/spaces-statements` (local subagent in the orchestrator's container) | high | state GL26 1.2, 1.3, 1.6, 1.7, 6.18, 12.2, 12.3 over `Spaces`, replacing the `Paper/` interface targets; launched 26 Nov after the maintainer confirmed the current GL26 TeX is the one shared earlier, which is only in the orchestrator's session (not in the repository) |
| `wave7/prune-named-inputs` | medium | delete the conditional results whose named non-Stacks inputs are marked delete / being removed / false in `OPEN_INPUTS.md` (maintainer's rule: no assumptions or unproven parts except AxiomMath/Stacks); pinned ones listed for the orchestrator |

Order after wave 7: the qcqs induction for supported weak approximability over spaces
(LP26 Cor 1.2) once the affine base and Lemma A.9 are in; then GL26 §§3–6 over spaces.

## Wave 8 (closed 27 November 2026; briefs in `results/swarm/archive/wave8/`): LP26 in full generality

**Closed (27 November 2026, ~18:45 UTC):** every task merged; all 66 tagged AxiomMath inputs proved in `SpacesVerified`; workers archived.

Launches when wave 7 is closed and the repository cleaned up.  Order of need: the universe
bridge and the preferred class first, then §5, then Corollary 1.2.

| task | effort | goal |
|---|---|---|
| `wave8/universe-bridge` (`session_0111iGd7bQhnAomRu66CG3oJ`) | high | merged: LP26 Thm 1.1 and compactness at independent Hom / coproduct universes; non-vacuity on `D(𝒪_X)` |
| `wave8/neeman-approximability` (`session_0111iGd8kuVAzNdReRDjVzr4`) | high | merged (partial): Neeman equivalence abstractly; A.9 preferred class for `Z = \|X\|`; supported case open (supported 0GFI) |
| `wave8/lp26-section5` (local subagent, LP26 TeX; merged, partial) | high | done: LP26 Lemmas 5.5, 5.6, 5.7 and the standard `t`-structure over spaces.  Left: Def 5.3 (after universe-bridge), Lemma 5.9 (`wave8/lp26-lemma-5-9`), Prop 5.8 (`wave8/lp26-recollement`) |
| `wave8/lp26-lemma-5-9` (local, LP26 TeX; merged) | high | done: LP26 Lemma 5.9 (`lem:characterize_T-_c`) over algebraic spaces, both claims, for the standard `t`-structure; nine tagged inputs |
| `wave8/lp26-recollement` (local, manuscripts; merged) | high | done: GL26 Lemmas A.4 (recollement of `D_qc,W(X)`, built here) and A.6 over spaces; LP26 Def 5.3 and the W.A. part of Prop 5.8.  Open: the standard W.A. part of Prop 5.8 |
| `wave8/lp26-corollary-1-2` (local, LP26 TeX; merged) | high | done: LP26 Corollary 1.2 over qcqs algebraic spaces, W.A. and D_qc parts (pinned), without the quasi-finite-diagonal hypothesis.  Open: standard W.A., Noetherian coherence |
| `wave8/axiommath-verified` (`session_0111iGd8ChkAMsYSB2t9QoLz`; merged `85172a0`) | high | done: all 66 tagged inputs proved; LP26 §5, Cor 1.2, GL26 A.4, A.6, A.9, 6.11 unconditional; 12 h 20 min build, peak 25 GB with 16 GB swap. Was: build the full `SpacesVerified` closure in its own container (the orchestrator's is reclaimed when idle), then prove the 17 tagged AxiomMath inputs of wave 7 and the unconditional wave 7 headlines |
| `wave8/prune-pinned-vacuous` (`session_0111iGd6caNpP2YiJVNQW24x`) | medium | merged: the two vacuous `IsGenerator` endpoints and ~1 500 lines only they used deleted; baseline re-recorded (15 pins) |

The manuscripts are in `manuscripts/` (27 November 2026), so manuscript tasks need not run locally.

## Wave 9 (briefs in `results/swarm/archive/wave9/`): finish LP26

Launched 27 November 2026, 18:53 UTC, after wave 8 closed and its workers were archived.

| task | model, effort | goal |
|---|---|---|
| `wave9/lp26-standard-wa` (cloud, `session_0111iGd6PAyq17qjDSXGxPci`; merged, archived) | Opus, high | done: standard W.A. of LP26 Prop 5.8 and Cor 1.2 over spaces (`Spaces/LP26/StandardWA.lean`), no new input; verified: `lake build Spaces`, default build, audit 283 clean, both statement checks, non-vacuity (empty space, `Spec ℤ`).  `SpacesVerified` form at the end of the wave |
| `wave9/supported-0gfi` (cloud, `session_0111iGd5ogawHqMD6voe1Nm1`; merged, archived) | Opus, high | done: supported Stacks 0GFI (`Spaces/Supported/Detecting.lean`), GL26 Lemma A.9's preferred class for every support; 19 new tagged inputs, 18 definition modules added to the import list; verified: `lake build Spaces`, default build, audit 316 clean, both statement checks, non-vacuity (affine `h_{T₀}`).  Inputs discharged by `wave9/verified` |
| `wave9/lp26-noetherian-coherence` (cloud, `session_0111iGd6biYZJqTjkNaeCB5z`; merged `81a5ca9`, archived) | Opus, high | done: Cor 1.2's coherence clause for Noetherian `X` (`Spaces/LP26/Coherence.lean`; CHNS Ex. 10.1.2 proved here), and the preferred-class step of Lemma 5.9; 2 new tagged inputs; verified: `lake build Spaces`, default build, audit 327 clean, both statement checks, non-vacuity (`Spec ℤ`) |
| `wave9/verified` (cloud, `session_0111iGd73ttBiGqdq2N5NwFj`; merged `806e155`, archived) | Opus, high | the `SpacesVerified` forms of wave 9's results, new inputs discharged, `LocallySmall.{u}`; full AxiomMath build |

The first Sonnet trial (model rule) is the next mechanical task, not a proof task.

After wave 9, LP26 is complete up to the discharge of its AxiomMath inputs; GL26 follows.

**Closed** 28 November 2026, 12:30 UTC: `wave9/verified` merged (`806e155`): all wave 9 inputs discharged, LP26 complete.  Archived.  The `--verified` baseline update for its 48 new pins (additions only) is delegated to `wave10/verified` (message of 13:01 UTC).

## Wave 10: GL26 §2–3 over algebraic spaces (all tasks merged and archived; `wave10/verified` running)

Launched 28 November 2026, 00:52 UTC (maintainer's exception: `wave9/verified` still running), as cloud workers, all Opus, high; briefs in `results/swarm/wave10/`
(preamble `00-preamble.md`).  From the top of `results/TODO.md`, in dependency order:

| task | results | files |
|---|---|---|
| `wave10/gl26-conservativity` (`session_0111iGd9EqGEkn9JWtabwe1W`; archived; merged: 2.14, 2.15, 2.18; 3.2 for a given factorization, the rest in `wave10/verified`; 5 new inputs; verified: `lake build Spaces`, default build, audit 340 clean, both statement checks, non-vacuity (identity)) | Lemmas 2.14 (`lem:faithfully_flat_is_conservative`), 2.15 (`lem:zero_object_via_covers`), 2.18 (`lem:quasi-affine_via_diagonal`), 3.2 (`lem:quasi-affine_is_conservative`) | `Spaces/Conservative/` |
| `wave10/gl26-internal-hom` (`session_0111iGd62y3xTpdZRCZuCS3X`; archived; merged: `R𝓗om`, coherator; 2.10 (natural in `L`), 2.11, 2.16 (1); 2.16 (2) open; 3 new inputs, 3 modules added to the import list; verified: `lake build Spaces`, default build, audit 382 clean, both statement checks, non-vacuity (affine, zero objects)) | `RHom` over spaces; Lemmas 2.10 (`lem:rhom_tensor_morphism`), 2.11 (`lem:internal_hom`), 2.16 (`lem:gortz_wedhorn_internal_hom`) | `Spaces/InternalHom/` |
| `wave10/gl26-upper-shriek` (`session_0111iGd9NyeYUSKeFg71vUEW`; archived; merged: 2.22 for every compactification; 2.21, 2.23, 2.24 not attempted (AxiomMath results outside the `Spaces` closure): wave 11 `gl26-shriek-calculus`; 2 new inputs; verified: `lake build Spaces`, default build, audit 356 clean, both statement checks, non-vacuity (identity, trivial compactification)) | Lemmas 2.21–2.24 (`lem:neeman186`–`189`) | `Spaces/Duality/` |
| `wave10/verified` (`session_0111iGd9FCbVBJSawK1bbwZN`, launched 04:52 UTC 28 Nov; running) | the `SpacesVerified` forms of wave 10 and the general case of Lemma 3.2 (`results/swarm/wave10/verified.md`) | `SpacesVerified/` |

## Wave 11: GL26 §2 (rest) and §5 over algebraic spaces (launched 04:52 UTC 28 Nov)

Uses wave 10's conservativity, `RHom` and `f^×`.  Cloud workers, all Opus, high, at most four at a time (with the two `verified` builds): quasi-perfect and kernels first, then box generation, pullback-hom, shriek-calculus as slots free; briefs in `results/swarm/wave11/` (preamble `00-preamble.md`):

| task | results | files |
|---|---|---|
| `wave11/gl26-quasi-perfect` (`session_0111iGd8WjT87BZ5jJjBJ6ne`; archived; merged `54381a7`: 5.9, 5.3 (1)–(2); 5.3 (3) and 5.7 open (0D0S comparison; GL26 §3–4); 5 new inputs; verified: `lake build Spaces`, default build, audit 404 clean, both statement checks, non-vacuity (identity, zero object)) | Lemmas 5.3 (`lem:quasi-perfect_bounded`), 5.7 (`lem:f_perf_implies_perf_preserved`), 5.9 (`lem:neeman23lem5_3`) | `Spaces/QuasiPerfect/` |
| `wave11/gl26-box-generation` (`session_0111iGd5Y21q4AtiRceLY3ie`; merged `edce58a`, archived: 5.4 conditional on Lemma 3.2 for the projection, unconditional for `f₁` affine; 1 new input (08GE); verified: `lake build Spaces`, default build, audit 449 clean, both statement checks, non-vacuity (affine)) | Lemma 5.4 (`lem:neeman2023cor5_10`) | `Spaces/BoxGeneration/` |
| `wave11/gl26-kernels` (`session_0111iGd9YUfCZro4cSJK24uD`; archived; merged `b228f65`: 2.25, 2.26; no new inputs, 3 modules added to the import list; verified: `lake build Spaces`, default build, audit 424 clean, both statement checks, non-vacuity (identity, zero kernels)) | Lemmas 2.25 (`lem:funct_on_kernel`), 2.26 (`lem:convolution`) | `Spaces/Kernels/` |
| `wave11/gl26-pullback-hom` (`session_0111iGd8uUwHJAsLduyiRCZt`; merged `81a3d9b`, archived: 2.10 natural in `K`, `M`, `L`; 2.16 (2) stopped (inputs outside the `Spaces` closure), moved to `wave11/verified`; no new input; verified: `lake build Spaces`, default build, audit 458 clean, both statement checks, non-vacuity (zero object)) | Lemma 2.16 (2) (`lem:gortz_wedhorn_internal_hom2`): `ρ_f` invertible for `E` pseudo-coherent, `G ∈ D^+_qc`, `f` of finite Tor dimension, over spaces (from AxiomMath's ringed-space 0GM7 and affine case by étale descent); and Lemma 2.10's naturality in `K`, `M` | `Spaces/InternalHom/` |
| `wave11/gl26-shriek-calculus` (`session_0111iGd9ceBjn6Kwy76sLfgW`, launched 12:40 UTC) | Lemmas 2.21 (`lem:neeman186`), 2.23 (`lem:neeman188`), 2.24 (`lem:neeman189`), in `SpacesVerified` with the full build (their AxiomMath inputs lie outside the `Spaces` closure) | `SpacesVerified/Duality/` |
| `wave11/verified` (`session_0111iGd95VgvzQ7vFNT54Ex5`, launched 15:32 UTC) | the `SpacesVerified` forms of wave 11; Lemma 2.16 (2); Lemma 5.4 in general (after `wave10/verified`) | `SpacesVerified/` |

## Wave 12 (prepared): GL26 §§3–4 over algebraic spaces

Launched after wave 11's tasks are merged (or recorded) and archived, as cloud workers, all Opus,
high, at most four at a time; briefs in `results/swarm/wave12/` (preamble `00-preamble.md`):

| task | results | files |
|---|---|---|
| `wave12/gl26-points-perfectness` | Lemmas 3.1 (`lem:23`), 3.3 (`lem:34`), 3.4 (`lem:45`), 3.6 (`lem:61`), Proposition 3.12 (`prop:perfectness`) | `Spaces/Perfectness/` |
| `wave12/gl26-perfect-locality` | Lemmas 3.5 (`lem:perf_pullback_characterize`), 3.7, 3.8, 3.9 | `Spaces/PerfectLocality/` |
| `wave12/gl26-relative-perfect` | Lemmas 4.3, 4.4, Propositions 4.5, 4.6, Corollary 4.7, Theorem 4.8 (`thm:relative_perf_iff_smooth_locally`) | `Spaces/RelPerfect/` |

Then (wave 13): Lemma 5.7 (needs 3.12 and 4.3), §6 (Propositions 6.2, 6.8, Theorem 1.3).

Later waves: §9–10 (base change for adjoints, Theorems 10.13 / 1.6), §12 (the loci, Theorems
12.3, 12.9 / 1.2), §11 (Theorem 1.7, once Gorenstein morphisms and fibre genus are available).

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
| 3 | `wave3/duality-wiring` | `session_0111iGd7thGvestxwvBAa75L` | `c9e70fa` (merge of `2772f52`) | 7.12–7.17 for Duality.lean's maps from `DerivedPseudofunctorInput` (open, ledger 1b); verified: build, audit 111 clean, statement check OK, non-vacuity (`trivialInput`). started 25 Nov 2026, 20:48 UTC; stopped at 20:55 on the 5-hour usage limit; resumed 26 Nov 01:07 UTC |
| 3 | `wave3/koszul-inputs` | `session_0111iGd9g3poYVdXRe3zUiNo` | `ebcf8f5` (merge of `2096440`, audit and ledger conflicts resolved) | refuted `KoszulScalarSupportInput` (finite-support endpoints vacuous); proved two of the other inputs; verified: build, audit 121 clean, statement check OK. started 25 Nov 2026, 20:48 UTC; stopped at 20:55 on the 5-hour usage limit; resumed 26 Nov 01:07 UTC |
| 3 | `wave3/open-closed-glue` | `session_0111iGd6pPXkVdZh7E3aUHJS` | `c2cf3a3` (merge of `ef072ef`) | reduction: completion hypothesis replaced by package-free inputs; generator change proved; non-vacuity of the new inputs NOT established (queued for wave 4); verified: build, audit 116 clean, statement check OK. started 25 Nov 2026, 20:48 UTC; stopped at 20:55 on the 5-hour usage limit; resumed 26 Nov 01:07 UTC |
| 3 | `wave3/fm-cube` | `session_0111iGd7XkC9wt1eqC3VpBdh` | `3805c58` (merge of `fcc3e57`) | 6.11, 10.1 C (Stacks only), 10.2 P (abstract); verified: build, audit 101 clean, statement check OK, non-vacuity (`constFMCube`). started 25 Nov 2026, 20:48 UTC; stopped at 20:55 on the 5-hour usage limit; resumed 26 Nov 01:07 UTC |
| 4 | `wave4/koszul-repair` (old plan) | `session_0111iGd5EpQmrcMq2EVMYxSR` | — | launched 26 Nov 07:27 UTC under the earlier wave-4 plan, stopped at 07:30 when the maintainer set the full-generality direction; nothing pushed; archived. Brief in `results/swarm/archive/deferred/` |
| 4 | `wave4/axiommath-api-map` | `session_0111iGd7KmNg4hyA9gC1E4Hh` | `b50af08` (merge of `4af8b4f`) | `results/AXIOMMATH_MAP.md`: notions and functors faithful in the canonical model; gaps C.1–C.12; statement layer T1 = 8.9k AxiomMath modules, all named T3 = 16.6k. Documentation only; verified: one markdown file, no Lean changed. launched 07:39 UTC |
| 4 | `wave4/axiommath-tag-map` | `session_0111iGd5VH4ANnfPagE5ET8s` | `35f0c62d` (merge of `41dc007`) | `results/AXIOMMATH_TAGS.md`: 147 cited tags; 114 usable, 8 usable via untagged space-level declarations, 23 partial (mostly universe: site-level results at `{u,u,u}`), 2 schemes only, 0 absent; ASSUMPTIONS S rows cross-checked. Documentation and scripts only (local parsing, no network); verified: no Lean changed. launched 07:39 UTC |
| 4 | `wave4/toolchain-435` | `session_0111iGd75PvwesuGTUxJTGcP` | `a80e03e` (merge of `13bd116`) + baseline `7c8cf28` | tree on Lean/Mathlib v4.35.0; 18 `.lean` files, proofs only (`List.TFAE.out` now 1-based, renames, closing tactics); verified: build 9 min, audit 121 clean + the 9 targets, statement check OK after re-recording one pretty-printing drift (`Spec (CommRingCat.of A)` → `Spec ↧A`, same term). launched 07:39 UTC |
| 5 | `wave5/neeman-affine-support` | `session_0111iGd7GFY22r3kJrNYZauJ` | `88cb5b9` (merge of `5af4b8e`; conflicts in imports, Audit, ASSUMPTIONS resolved by the orchestrator) + baseline | **LP26 Cor 1.2 affine base = Neeman 3.2(iv) for `Spec A`, `V(I)`, `I` f.g., with no hypothesis** (`NeemanAffineSupport.satisfiesPaperWA_of_fg`, now pinned); refuted `KoszulScalarSupportInput` removed, Construction 7.3 and Koszul detection proved; three pinned declarations restated as authorized (they keep the proved `hAc`; the scheme forms keep the open `AffineSupportedSchemeComparisonInput`); verified: build, 9 modules compiled singly, audit 137 clean + 9 targets, statement check: exactly the 3 authorized entries, re-recorded, plus the new pin. | launched 26 Nov 08:34 UTC (5-hour window at `allowed_warning`, resets 11:00; weekly window at `allowed_warning`) |
| 5 | `wave5/neeman-3-2-inputs` | `session_0111iGd5q1UJafFAiSvAaNSe` | `2d3006c` (merge of `1a66a2c`) | Neeman 3.2(i) for `D(A)` in both models from Stacks 09SR (`compactPerfectInput`, `smallNeemanCompactToPerfectInput`), (ii) affine with no input; inventory `results/archive/NEEMAN_3_2.md` (neither paper cites (i)/(ii); (iii)–(iv) for schemes are on paper paths); verified: build, audit 127 clean + 9 targets, statement check OK, non-vacuity (examples over ℤ; 09SR antecedents shown). | launched 26 Nov 11:10 UTC (Neeman 3.2 no longer assumed); `neeman-affine-support` stopped on the 5-hour limit at 08:39 and was resumed at 11:10 |
| 5 | `wave5/neeman-prune` | `session_0111iGd9N3bRHZc6AEYH1o6J` | `1eb5001` (merge of `7a92091`) + baseline | Neeman 2024 Thm 3.2 inputs removed from the tree: `CompactPerfectInput`, `SmallNeemanCompactToPerfectInput`, `NeemanAffineCompactModelInput`, `Neeman_3_2_i/ii/iv`, `NeemanPublishedWeakApproximation` deleted, `Affine066S.lean` deleted; pinned `affine_theorem_1_1_neeman_only` → `affine_theorem_1_1_unconditional` with no input beyond the paper setup; small-Hom endpoints keep Stacks 09SR (small ⇒ large compactness lift unproved); verified: build, 13 modules singly, audit 142 clean + 9 targets, statement check: exactly the authorized diff, re-recorded. | launched 26 Nov 11:39 UTC |
| 5 | `wave5/open-inputs` | `session_0111iGd99W3B92SKghvVqXPu` | | launched 26 Nov 11:40 UTC |
| 6 | `wave6/vacuity-refutations` | `session_0111iGd9N18AtNr9JMXz2qgJ` | `b2c7530` (merge of `0009871` = `220fab5` cherry-picked onto the rewritten history) + baseline | F1 `¬ HasCoproducts.{u+1} (AffineD A)` for nontrivial `A` (two pinned endpoints vacuous → unpinned), F2 no compact `IsGenerator` in `D(ℤ)` (large and small; `SetupMainMinimal` empty at ℤ), F3 `QuasicoherentSerreInput (Spec ℤ)` false; verified: build, 4 modules singly, audit 160 clean + 9 targets, statement check (16 pins after unpinning). | launched 26 Nov 12:38 UTC, effort high (account now Max; 5-hour window `allowed`) |
| 6 | `wave6/lp26-paper-hypotheses` | `session_0111iGd8km4EQRgUkVzQZyHo` | merge of `687ae2c` (Audit conflict kept both) + pin | **LP26 Thm 1.1 with the paper's hypotheses** (`PaperHypothesesW6.theorem_1_1_paper`, pinned): recollement, `D_Z`, `D_U` weakly approximable, `G'` compact zero-detecting generator ⇒ (`D` WA ↔ `Hom(G',G'[n]) = 0`, `n ≫ 0`); only Stacks 09SR assumed; compactly generated `t`-structures proved (`CompactlyGeneratedTStructure`), BNP Cor 3.10(1) from 09SR; non-vacuity: zero and affine instances; verified: build, 4 modules singly, audit 169 clean + 9 targets, statement check (17 pins). Verify script hung on WeakApprox-only branches (empty module list): fixed. | launched 26 Nov 12:38 UTC, effort high |
| 6 | `wave6/prune-dead-inputs` | `session_0111iGd5ihxMTqsyaHh8y9DA` | `c34e606` (merge of `d0f2e1c`) | dead named inputs of `results/OPEN_INPUTS.md` deleted (33 files, −1704 lines; `AffineRecollementAssembly`, `AffineSetupInventory` removed); pins unchanged; verified: build, changed modules singly, audit 165 clean + 9 targets, statement check (17 pins). launched 13:11 UTC, effort medium |
| 6 | `wave6/spaces-foundations` | `session_0111iGd5Qzb48rxe9rDmcTe9` | merge of `394ee3a` (Spaces.lean imports conflict resolved) | **the algebraic-space layer**: `D`, `Dqc`, `Dbqc`, `DminusCoh`, `DbCoh`, `Perf`, support and `D_{qc,T}` on AxiomMath's definitions; `pull`, `push`, `tensor`, `Lf^* ⊣ Rf_*` (07A6); GL26 Def 4.1 `IsRelativelyPerfect`, Def 5.1 `IsQuasiPerfect`; integral transforms `Φ_K` over `S` and over a base space; four tagged inputs (06UQ, 08F4, 08F5, 08FA(1)) for `SpacesVerified`; non-vacuity (a space exists; zero object in every subcategory, f-perfect and f-quasi-perfect); five small AxiomMath proofs copied with attribution (Apache 2.0). Verified: `lake build Spaces` (no AxiomMath recompiled), audit 38 lines standard axioms, default build, both statement checks. Ran fine as a normal worker. | launched 26 Nov 15:58 UTC, effort high, as a normal worker on the definitions-only AxiomMath import (`9816a7d`) |
| 6 | `wave6/stacks-categorical` | `session_0111iGd5uAW7Bn1N8gQ4139v` | merge of `a83a4dd` | Stacks 09SR and 09SN **proved from AxiomMath** (`Spaces/Stacks/Tags.lean`, via bridges `IsCompactObject ↔ IsCompactAb`, weak generator ↔ `IsPaperGenerator`); **LP26 Thm 1.1 with the paper's hypotheses and no Stacks hypothesis** (`Spaces.Stacks.theorem_1_1`), GL26 Lemmas 2.4, 2.5 unconditional; 18 declarations, axioms standard; verified: `lake build Spaces` (no AxiomMath recompiled), 3 modules singly, default build, statement check. Deviation: repo `Tag09SRPaper` is stated for pretriangulated `C`, AxiomMath's 09SR needs `IsTriangulated` (all consumers triangulated). | launched 26 Nov 16:17 UTC, effort high: prove 09SR/09SN from AxiomMath (cheap categorical modules), unconditional LP26 Thm 1.1 and GL26 Lemma 2.4 |
| 6 | orchestrator: 09SR | (orchestrator) | `f5eaa44` | `Tag09SRPaper C` now takes `[IsTriangulated C]`, as AxiomMath's 09SR does (it was formally stronger than the tag); `tStructureEquivalent_of_inPreferredClass` gains the same instance; `Spaces.Stacks.tag09SRPaper` re-pinned (binder name only). Verified: default build, `lake build Spaces`, both statement checks, axioms standard. | 26 Nov |
| 6 | orchestrator: `SpacesVerified` | (orchestrator) | this commit | `SpacesVerified/Discharge.lean`: the four tagged inputs of `Spaces/AxiomMathInputs.lean` (06UQ, 08F4, 08F5, 08FA(1)) **proved** by the AxiomMath theorems they name; `D_qc(X)` triangulated and `Lf^*`, `⊗^L`, `Rf_*` on `D_qc` unconditional. Pinned in `StatementCheckVerified.lean` (`scripts/check_statements.sh --verified`, 5 declarations). Verified: `lake build SpacesVerified` (17 725 jobs, closure 8 524 AxiomMath modules all built), axioms standard, no `sorryAx`; default build, `lake build Spaces`, all three statement checks. | 26 Nov |
| 7 | `wave7/spaces-statements` (local) | (local subagent) | `02cb617`, merged; inputs discharged `60fc989` | GL26 Theorems 1.2, 1.3, 1.6, 10.13, 12.3, 12.9, Corollaries 6.18, 12.4, Lemma 12.2 stated over algebraic spaces; Theorem 1.7 not stated (Gorenstein, genus) | 26 Nov |
| 7 | `wave7/prune-named-inputs` | `session_0111iGd7AmsjhetGmmCxKaDV` | `5e8a373`, merged `fd253ec` | 86 declarations on the `IsGenerator` forms deleted; the two pinned vacuous endpoints remain (wave 8) | 27 Nov |
| 7 | `wave7/spaces-affine-base` | `session_0111iGd775NkFveWdRq8i6DW` | `e510ffb`, merged `fd253ec` | LP26 Cor 1.2 affine base over AxiomMath's algebraic spaces (tagged inputs 06Z0, 07TY, 021R) | 27 Nov |
| 7 | `wave7/spaces-compact-generation` | `session_0111iGd895xp83khYFFveVy2` | `be92093`, merged `fd253ec` | GL26 Lemma A.9 generation part over qcqs spaces (0AEC, 0AED, 0GFD, 08F3); preferred-class clause open (wave 8) | 27 Nov |
| 7 | `wave7/spaces-base-change` | `session_0111iGd9Cxes2MsiML9Zjf5L` | `438117f`, merged `fd253ec` | GL26 Lemmas 7.12, 7.13, 7.17 over spaces with no input; 6.11, 10.1 over spaces (08IR, 08IN) | 27 Nov |
