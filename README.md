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

281 Lean modules, about 70 000 lines, no `sorry`.  Every result depends only on the
axioms `propext`, `Classical.choice`, `Quot.sound`.  **Rule:** no assumptions and no
unproven parts except the Stacks Project as formalized by AxiomMath.

## Status

**LP26**

| result | status |
|---|---|
| §§2–4 (Lemmas 3.1, 3.3, 3.4, 3.5, 4.2, 4.3, 4.6, Proposition 4.8) | proved |
| Theorem 1.1 (`thm:glueing_weak_approx`) | proved, with the paper's hypotheses and nothing assumed (`Spaces.Stacks.theorem_1_1`) |
| Corollary 1.2 (`cor:weak_approx_spaces`) | proved over qcqs algebraic spaces: weak approximability of `D_qc,S(X)` and `D_qc(X)` with nothing assumed; the standard form and coherence for Noetherian `X` from AxiomMath inputs, whose proofs in `SpacesVerified` are in progress |
| §5 (Definition 5.3, Lemmas 5.5–5.9, Proposition 5.8) | proved over algebraic spaces; nothing assumed except for the standard part of Proposition 5.8 and the preferred-class form of Lemma 5.9 (AxiomMath inputs, `SpacesVerified` in progress) |

**GL26**

| result | status |
|---|---|
| §2.2 over algebraic spaces: `D_qc`, `D^b_coh`, `Perf`, support, `Lf^* ⊣ Rf_*`, `⊗^L`; Definitions 4.1, 5.1; integral transforms | defined (`Spaces/`), nothing assumed (`SpacesVerified/`) |
| Lemmas 2.3, 2.4, 2.5 | proved |
| Lemmas 7.12, 7.13, 7.17 | proved for algebraic spaces, nothing assumed |
| Lemmas 7.2, 7.4, 7.6, 7.9, 7.11, Lemma-Definition 7.10, Lemmas 10.2, B.2, B.4, B.5, B.7, B.10, C.1 | proved, over abstract data or in `Cat` |
| Lemmas A.4, A.6, A.9 (generation; preferred class for the whole space), 6.11 | proved over algebraic spaces, nothing assumed; Lemma A.9's preferred class for every support from AxiomMath inputs (`SpacesVerified` in progress) |
| Lemma 10.1 | proved over algebraic spaces from one flat-base-change hypothesis (open) |
| Lemmas 2.25, 2.26, 5.4, A.4 (affine case) | conditional on named inputs: not counted as proved; being redone over algebraic spaces |
| Theorems 1.2, 1.3, 1.6, 1.7 and the rest | open; being stated over algebraic spaces |

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

Some older results still take a named hypothesis that is not a Stacks theorem (for
example `DerivedPseudofunctorInput`, Lipman 3.6.2).  These are not counted as proved:
each hypothesis is being proved, from AxiomMath where it is a Stacks result, or the
result is removed.  Ledger:
[`results/ASSUMPTIONS.md`](results/ASSUMPTIONS.md); open items:
[`results/OPEN_INPUTS.md`](results/OPEN_INPUTS.md); policy:
[`results/STACKS_POLICY.md`](results/STACKS_POLICY.md).

## Next

1. **Finish LP26**: every result is proved over algebraic spaces; what remains is proving
   the wave 9 AxiomMath inputs in `SpacesVerified` (running).
2. **GL26 over algebraic spaces**, in dependency order: §2–3 (conservativity, internal Hom,
   duality: wave 10, prepared), then §§4–6, §§9–10, §12, §11.

## Checking

A result counts as proved only after seven checks: it compiles, the output has no
error, no `sorryAx`, the axioms are the three above, the proof is read, its hypotheses
are shown satisfiable, and the whole project builds.  The statements of the headline
results are pinned, so a weakened statement fails even if every proof compiles:

```bash
scripts/check_statements.sh              # 15 results (Mathlib only)
scripts/check_statements.sh --spaces     # 9 results (algebraic spaces)
scripts/check_statements.sh --verified   # 98 results (AxiomMath inputs discharged)
```

Details: [`results/VERIFICATION.md`](results/VERIFICATION.md).

## Building

Lean and Mathlib `v4.35.0`; AxiomMath/Stacks at `f56a316`.

```bash
lake exe cache get          # Mathlib
lake build                  # FourierMukai, WeakApprox (no AxiomMath)
lake build Spaces           # algebraic spaces (~2 000 AxiomMath modules, ~40 min the first time)
lake build SpacesVerified   # full verification (~14 600 AxiomMath modules, ~12 h, 16 GB of memory plus 16 GB swap)
```

## Layout

| path | contents |
|---|---|
| `WeakApprox/` | LP26 §§2–4 and Theorem 1.1 |
| `FourierMukai/Prelim/` | categorical results of GL26 §2.1, §7, Appendices B, C |
| `FourierMukai/Scheme/` | the affine layer (`D(A-Mod)`, perfect complexes, Neeman's affine results) |
| `FourierMukai/Paper/` | the earlier abstract interface and its targets |
| `Spaces/` | algebraic spaces on AxiomMath's definitions: LP26 Theorem 1.1, §5 and Corollary 1.2; GL26's statements, Lemmas 2.4, 2.5, 7.12–7.17, A.9, base change |
| `SpacesVerified/` | the AxiomMath theorems the `Spaces` layer uses |
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
