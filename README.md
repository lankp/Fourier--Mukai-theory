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

260 Lean modules, about 60 000 lines, no `sorry`.  Every result depends only on the
axioms `propext`, `Classical.choice`, `Quot.sound`.  **Rule:** no assumptions and no
unproven parts except the Stacks Project as formalized by AxiomMath.

## Status

**LP26**

| result | status |
|---|---|
| §§2–4 (Lemmas 3.1, 3.3, 3.4, 3.5, 4.2, 4.3, 4.6, Proposition 4.8) | proved |
| Theorem 1.1 (`thm:glueing_weak_approx`) | proved, with the paper's hypotheses and nothing assumed (`Spaces.Stacks.theorem_1_1`) |
| Corollary 1.2 (`cor:weak_approx_spaces`) | affine base case proved over algebraic spaces (AxiomMath inputs to discharge); the qcqs induction in progress |
| §5 (Definition 5.3, Lemmas 5.5–5.9, Proposition 5.8) | open |

**GL26**

| result | status |
|---|---|
| §2.2 over algebraic spaces: `D_qc`, `D^b_coh`, `Perf`, support, `Lf^* ⊣ Rf_*`, `⊗^L`; Definitions 4.1, 5.1; integral transforms | defined (`Spaces/`), nothing assumed (`SpacesVerified/`) |
| Lemmas 2.3, 2.4, 2.5 | proved |
| Lemmas 7.12, 7.13, 7.17 | proved for algebraic spaces, nothing assumed |
| Lemmas 7.2, 7.4, 7.6, 7.9, 7.11, Lemma-Definition 7.10, Lemmas 10.2, B.2, B.4, B.5, B.7, B.10, C.1 | proved, over abstract data or in `Cat` |
| Lemma A.9 (generation part), Lemmas 6.11, 10.1 | proved over algebraic spaces from AxiomMath theorems (being discharged); the preferred-class clause of A.9 is open |
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

1. **LP26 in full generality** (wave 8): LP26 Theorem 1.1 at AxiomMath's universes, the
   preferred-class clause of GL26 Lemma A.9 (Neeman's approximability, proved here), LP26 §5,
   then Corollary 1.2 over qcqs algebraic spaces; AxiomMath inputs of wave 7 discharged.
2. **GL26 over algebraic spaces**: prove the stated headline results, starting from §7 and
   the base-change cube.

## Checking

A result counts as proved only after seven checks: it compiles, the output has no
error, no `sorryAx`, the axioms are the three above, the proof is read, its hypotheses
are shown satisfiable, and the whole project builds.  The statements of the headline
results are pinned, so a weakened statement fails even if every proof compiles:

```bash
scripts/check_statements.sh              # 17 results (Mathlib only)
scripts/check_statements.sh --spaces     # 7 results (algebraic spaces)
scripts/check_statements.sh --verified   # 5 results (AxiomMath inputs discharged)
```

Details: [`results/VERIFICATION.md`](results/VERIFICATION.md).

## Building

Lean and Mathlib `v4.35.0`; AxiomMath/Stacks at `f56a316`.

```bash
lake exe cache get          # Mathlib
lake build                  # FourierMukai, WeakApprox (no AxiomMath)
lake build Spaces           # algebraic spaces (~2 000 AxiomMath modules, ~40 min the first time)
lake build SpacesVerified   # full verification (~8 500 AxiomMath modules, ~6 h, ~14 GB of memory)
```

## Layout

| path | contents |
|---|---|
| `WeakApprox/` | LP26 §§2–4 and Theorem 1.1 |
| `FourierMukai/Prelim/` | categorical results of GL26 §2.1, §7, Appendices B, C |
| `FourierMukai/Scheme/` | the affine layer (`D(A-Mod)`, perfect complexes, Neeman's affine results) |
| `FourierMukai/Paper/` | the earlier abstract interface and its targets |
| `Spaces/` | algebraic spaces on AxiomMath's definitions: LP26 Theorem 1.1, the affine base of Corollary 1.2; GL26's statements, Lemmas 2.4, 2.5, 7.12–7.17, A.9 (generation), base change |
| `SpacesVerified/` | the AxiomMath theorems the `Spaces` layer uses |
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
