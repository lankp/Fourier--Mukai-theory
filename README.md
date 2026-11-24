# FourierMukai: derived categories of algebraic spaces in Lean 4

This repository is a Lean 4 formalization of two papers on derived categories of
algebraic spaces:

1. **Elías Guisado Villalgordo, Pat Lank**, *Relative Fourier–Mukai theory for
   algebraic spaces* (arXiv:2609.01298).  The library `FourierMukai/` formalizes
   the triangulated-category and 2-categorical foundations of that paper
   (Section 2.1, Appendix B, and the mate calculus of Section 7), and states its
   main theorems over an interface for the geometric layer.
2. **Pat Lank, Bregje Pauwels**, *Gluing weak approximability along recollements*
   (November 2026).  The library `WeakApprox/` formalizes Sections 2 and 3 of that
   paper: the closure properties of `⟨H⟩^[a,b]`, the aisle lemma, the vanishing
   criteria, and the definition of weak approximation data.

## It builds on the Axiom Math formalization of the Stacks Project

The project is designed to build **on top of
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks)**, the Axiom Math
formalization of the Stacks Project, which is itself built on
[Mathlib](https://github.com/leanprover-community/mathlib4).  We are grateful to
the Axiom Math team and to the Stacks Project authors: the geometric prerequisites
of both papers (algebraic spaces, `D_qc`, perfect complexes, Grothendieck duality)
are taken from that library, and the build configuration here — `lean-toolchain`,
the `[leanOptions]` block, the Mathlib pin — is copied from it so that the two
libraries can be developed side by side.

* `lean-toolchain`: `leanprover/lean4:v4.35.0` (the toolchain of AxiomMath/Stacks).
* `lakefile.toml`: requires Mathlib at `v4.35.0` and `Stacks` from
  `https://github.com/AxiomMath/Stacks`.

## Building

With [elan](https://github.com/leanprover/elan) and Lake:

```bash
lake exe cache get   # Mathlib's compiled artifacts
lake build           # builds the libraries `FourierMukai` and `WeakApprox`
```

The Stacks library is large (about 63,000 modules); building it from source takes
a long time and a cache for it is still being prepared.  Both libraries here are
Mathlib-only at the moment, so `lake build FourierMukai WeakApprox` does not
require the Stacks modules to be compiled.

For development on a machine without the pinned toolchain, `scripts/build.sh`
compiles every module directly with the `lean` on `PATH`
(`LEAN_PATH="$LEAN_PATH:." lean -o <file>.olean <file>.lean`).

## Layout

| path | contents |
|---|---|
| `FourierMukai/Prelim/` | `Trinatural` (Definition B.9), Lemma 2.3(1)–(3), Lemma 2.3(2) triangulated/thick/localizing, Lemma 2.5, the mate bijection and Lemma 7.8(2) |
| `FourierMukai/Paper/` | the interface for `D_qc`, `f`-perfect and `f`-quasi-perfect complexes, the integral transform, the loci `FM`/`fm`, and the statements of the main theorems |
| `FourierMukai/Examples/` | a non-vacuous instantiation on Mathlib's derived category of an abelian category |
| `WeakApprox/` | `H[a,b]`, `Coprod`, `⟨H⟩^[a,b]`, weak approximation data, Lemmas 3.1, 3.3, and the start of Section 4 |
| `results/` | reports: the state of each formalization, the inventory of missing prerequisites, and the porting notes |
| `scripts/` | `build.sh` |

## Status

* `FourierMukai/Prelim/` and `WeakApprox/` are `sorry`-free; every declaration
  there depends only on `propext`, `Classical.choice` and `Quot.sound`
  (`FourierMukai/Audit.lean` prints the audit).
* `FourierMukai/Paper/Statements.lean` contains ten statements with `sorry`:
  Theorems 1.3, 1.2(1)–(2), 1.6, 12.3, 1.7, Lemmas 2.25, 2.26, 12.2 and
  Corollary 6.18 of the relative Fourier–Mukai paper.  They are formalization
  targets, not proved theorems.
* See [`results/REPORT.md`](results/REPORT.md),
  [`results/WEAK_APPROX.md`](results/WEAK_APPROX.md) and
  [`results/INTEGRATION.md`](results/INTEGRATION.md) for the details, and for the
  list of mathematical points in the papers that need attention.

## License

Apache 2.0; see `LICENSE`.
