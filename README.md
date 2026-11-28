# Relative Fourier–Mukai theory for algebraic spaces, in Lean 4

A Lean 4 formalization of two papers:

* **LP26**: Pat Lank and Bregje Pauwels, *Gluing weak approximability along
  recollements*, preprint 2026;
* **GL26**: Elías Guisado Villalgordo and Pat Lank, *Relative Fourier–Mukai theory
  for algebraic spaces*, arXiv:2609.01298.

**Goal.** Both papers in full generality, as stated, over algebraic spaces.  The only
external input is the [AxiomMath formalization of the Stacks
Project](https://github.com/AxiomMath/Stacks) (a pinned Lake dependency); everything
else comes from Mathlib or is proved here.  **Order:** LP26 first, with the parts of
the literature it needs, then GL26.

306 Lean modules, about 74 000 lines, no `sorry`.  Every result depends only on the
axioms `propext`, `Classical.choice`, `Quot.sound`.  **Rule:** no assumptions and no
unproven parts except the Stacks Project as formalized by AxiomMath.

## Status

**LP26**

| result | status |
|---|---|
| §§2–4 (Lemmas 3.1, 3.3, 3.4, 3.5, 4.2, 4.3, 4.6, Proposition 4.8) | proved |
| Theorem 1.1 (`thm:glueing_weak_approx`) | proved, with the paper's hypotheses and nothing assumed (`Spaces.Stacks.theorem_1_1`); applies to the recollements of `D_qc,T(X)` |
| Corollary 1.2 (`cor:weak_approx_spaces`) | proved over qcqs algebraic spaces, nothing assumed: weak approximability and standard weak approximability of `D_qc,S(X)` and `D_qc(X)`, and coherence for Noetherian `X` |
| §5 (Definition 5.3, Lemmas 5.5–5.9, Proposition 5.8) | proved over algebraic spaces, nothing assumed |

**GL26**

| result | status |
|---|---|
| §2.2 over algebraic spaces: `D_qc`, `D^b_coh`, `Perf`, support, `Lf^* ⊣ Rf_*`, `⊗^L`, `R𝓗om`, `f^×`, `f^!`; Definitions 4.1, 5.1; integral transforms | defined (`Spaces/`) |
| Lemmas 2.3, 2.5 (triangulated categories) | proved |
| Lemmas 2.4, 6.11, 7.12, 7.17, A.4, A.6, A.9 | proved over algebraic spaces, nothing assumed |
| Lemma-Definition 7.13 | over abstract data (`Prelim/BaseChangeMates.lean`) |
| Lemmas 2.10, 2.11, 2.14, 2.15, 2.18, 2.22, 2.25, 2.26, 5.9; Lemma 2.16 (1); Lemma 5.3 (1)–(2) | proved over algebraic spaces from tagged AxiomMath theorems; their `SpacesVerified` forms are next (waves 10–11) |
| Lemma 3.2 | proved for a morphism given as open immersion then affine; the general case in `SpacesVerified` (wave 10) |
| Lemma 10.1 | proved over algebraic spaces from one flat-base-change hypothesis (open) |
| Lemmas 7.2, 7.4, 7.6, 7.9, 7.11, Lemma-Definition 7.10, Lemmas 10.2, B.2, B.4, B.5, B.7, B.10, C.1 | proved over abstract data or in `Cat`; the versions over spaces are to do |
| Lemmas 2.16 (2), 2.21, 2.23, 2.24, 5.4 | in progress (wave 11) |
| §§3–4 (Proposition 3.12, Theorem 4.8) | prepared (wave 12) |
| Theorems 1.2, 1.3, 1.6, 1.7 and the rest | open; Theorems 1.2, 1.3, 1.6 are stated over algebraic spaces (`Spaces/Statements/Main.lean`) |

Result by result: [`results/COVERAGE.md`](results/COVERAGE.md).  Everything not yet
proved in full generality is a to-do in [`results/TODO.md`](results/TODO.md) (generated),
filled wave by wave, LP26 first.  A generated summary:
[`results/PROGRESS.md`](results/PROGRESS.md).

## What is assumed

Only theorems of AxiomMath/Stacks, each used through a hypothesis that copies
AxiomMath's statement and names its Stacks tag.  The library `SpacesVerified`
replaces each such hypothesis by the AxiomMath theorem itself, so the results over
algebraic spaces are unconditional.  Neeman's Theorem 3.2 (Acta Math. 2024) is not
assumed; what the papers need from it is proved here.

Some results of the older layers (`FourierMukai/Scheme/`, `FourierMukai/Paper/`) still take a
named hypothesis that is not a Stacks theorem (for example `DerivedPseudofunctorInput`).
They are not counted as proved; they are being replaced by the versions over algebraic
spaces.  Ledger:
[`results/ASSUMPTIONS.md`](results/ASSUMPTIONS.md); open items:
[`results/OPEN_INPUTS.md`](results/OPEN_INPUTS.md); policy:
[`results/STACKS_POLICY.md`](results/STACKS_POLICY.md).

## Next

**LP26 is complete**: every numbered result is proved over algebraic spaces with nothing
assumed beyond AxiomMath/Stacks (28 November 2026).

**GL26 over algebraic spaces**, in dependency order: the rest of §2 (Lemmas 2.16 (2), 2.21,
2.23, 2.24) and §5 (wave 11), §§3–4 (wave 12), then §6, §§9–10, §12, §11.

## Checking

A result counts as proved only after seven checks: it compiles, the output has no
error, no `sorryAx`, the axioms are the three above, the proof is read, its hypotheses
are shown satisfiable, and the whole project builds.  The statements of the headline
results are pinned, so a weakened statement fails even if every proof compiles:

```bash
scripts/check_statements.sh              # 15 results (Mathlib only)
scripts/check_statements.sh --spaces     # 9 results (algebraic spaces)
scripts/check_statements.sh --verified   # 98 results recorded, 48 more to record (AxiomMath inputs discharged)
```

Details: [`results/VERIFICATION.md`](results/VERIFICATION.md).

## Building

Lean and Mathlib `v4.35.0`; AxiomMath/Stacks at `f56a316`.

```bash
lake exe cache get          # Mathlib
lake build                  # FourierMukai, WeakApprox (no AxiomMath)
lake build Spaces           # algebraic spaces (~4 700 AxiomMath modules, ~1 h the first time)
lake build SpacesVerified   # full verification (~14 600 AxiomMath modules, ~12 h, 16 GB of memory plus 16 GB swap)
```

## Layout

| path | contents |
|---|---|
| `WeakApprox/` | LP26 §§2–4 and Theorem 1.1 |
| `FourierMukai/Prelim/` | categorical results of GL26 §2.1, §7, Appendices B, C |
| `FourierMukai/Scheme/` | the affine layer (`D(A-Mod)`, perfect complexes, Neeman's affine results) |
| `FourierMukai/Paper/` | the earlier abstract interface and its targets |
| `Spaces/` | algebraic spaces on AxiomMath's definitions: LP26 Theorem 1.1, §5 and Corollary 1.2 (`Spaces/LP26/`); GL26's statements (`Statements/`), §2 (`Conservative/`, `InternalHom/`, `Duality/`, `Kernels/`), §5 (`QuasiPerfect/`), Appendix A (`Supported/`), base change |
| `SpacesVerified/` | the `Spaces` results with every AxiomMath input discharged: unconditional |
| `manuscripts/` | the current GL26 and LP26 manuscripts (TeX and PDF) |
| `results/` | coverage, assumptions, open items, the AxiomMath maps; `archive/` holds earlier reports |

## How the work is produced

By AI agents, checked before anything enters the tree.  Since 25 November 2026 a
coordinating Claude Code session splits the work into waves of independent tasks,
worker sessions prove them on their own branches, and the coordinator re-runs the
seven checks and reads each statement against the paper before merging into
`formalization` ([`results/SWARM.md`](results/SWARM.md)).  Earlier proofs came from
Ultramath, a team of model instances working on one problem at once, checked the
same way.  Corrections, including the agents' own mistakes, are recorded in the
commit messages and in the ledger.

## Licence

Apache 2.0; see [`LICENSE`](LICENSE).
