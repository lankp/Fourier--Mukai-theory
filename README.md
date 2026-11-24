# GL26 in Lean: relative Fourier–Mukai theory for algebraic spaces

This repository is a Lean 4 formalization of

> **GL26** — Elías Guisado Villalgordo, Pat Lank, *Relative Fourier–Mukai theory
> for algebraic spaces*, arXiv:2609.01298 (2026).

The goal is to verify the paper's results in Lean, on top of the Axiom Math
formalization of the Stacks Project and Mathlib — see *Building* below.  The
formalization proceeds from the foundational sections outwards: the
triangulated-category and 2-categorical machinery of §2.1 and Appendix B, the mate
calculus of §7, the compact-object criterion of §2.1, and then the geometric
layer.

## What is verified

| GL26 | Lean |
|---|---|
| Definition B.9 (`Trinatural`), identity and vertical composition of trinatural transformations | `FourierMukai/Prelim/Triangulated.lean` |
| Lemma 2.3(1) (coproducts and cofactors), Lemma 2.3(2) (triangulated, thick, localizing), Lemma 2.3(3) (essential density) | `FourierMukai/Prelim/{Closure, Coproduct, Shift, EssentiallyDense, Thickness}.lean` |
| Lemma 2.5 (equivalences and compact objects) | `FourierMukai/Prelim/Lemma25.lean` |
| Lemma 7.1(2) (mate bijection) and Lemma 7.8(2) (mates of isomorphisms) | `FourierMukai/Prelim/Mates.lean` |
| Definition 4.1, Definition 5.1, the integral transform `Φ_K`, Definition 12.1 (`FM`, `fm`) | `FourierMukai/Paper/DerivedSetup.lean` |

Everything in `FourierMukai/Prelim/` is `sorry`-free and depends only on
`propext`, `Classical.choice` and `Quot.sound`; `FourierMukai/Audit.lean` prints
the audit.

`FourierMukai/Paper/Statements.lean` states the paper's main theorems —
Theorems 1.3, 1.2(1)–(2), 1.6, 12.3, 1.7, Lemmas 2.25, 2.26, 12.2 and
Corollary 6.18 — over an interface for the geometric layer (`D_qc` on algebraic
spaces, `f^×`, `f^!`).  They are formalization targets, not proved theorems; the
interface and the missing prerequisites are described in
[`results/REPORT.md`](results/REPORT.md).

## Other preprints verified along the way

GL26's methodology rests on three bodies of work that are not in the published
literature or in Mathlib, and their formalization is carried out here in the same
repository:

* **Lank–Pauwels**, *Gluing weak approximability along recollements*
  (November 2026), which GL26 cites for weak approximability of `D_qc` on
  algebraic spaces (Remark 2.6 and §12).  The library `WeakApprox/` verifies
  §2–§4 and **Theorem 1.1**: the closure properties of `⟨H⟩^[a,b]`
  (Lemma 3.1), the aisle lemma (Lemma 3.3), the iterated approximation
  (Lemma 3.4), the vanishing criterion (Lemma 3.5), the `Recollement`
  structure and the glued aisle (Lemma 4.2), Lemma 4.3, `P`-lifts and
  Lemma 4.6, Proposition 4.8, and both directions of Theorem 1.1 over Setup 4.4
  (`WeakApprox/Main.lean`).  Theorem 1.1 itself needs no unproved input; the
  remaining external ingredient of the paper is Stacks Tag 09SR (Ravenel–
  Neeman), used only to *derive* Setup 4.4, and `WeakApprox/NineSR.lean`
  records exactly what is and is not formalized of it.  Compactness is
  rendered over `AddCommGrpCat` in `WeakApprox/CompactAb.lean`, which is what
  makes Lemma 4.3(2) hold without an extra compactness hypothesis.  See
  [`results/WEAK_APPROX.md`](results/WEAK_APPROX.md).
* **Neeman**, *Triangulated categories with a single compact generator, and two
  Brown representability theorems* (Invent. Math. 2026) and **Canonaco–
  Haesemeyer–Neeman–Stellari**, *The passage among the subcategories of weakly
  approximable triangulated categories* (2024): cited in GL26 for the passage
  between equivalences on `D_qc`, `D^-_coh`, `D^b_coh` and `Perf` (Remark 2.6)
  and for the aisle facts used in `WeakApprox/`.
* **Neeman**, *An improvement on the base-change theorem and the functor `f^!`*
  (2023) and **Guisado Villalgordo–Lank–Manali Rahul–Pavic**, *Fiberwise criteria
  for Fourier–Mukai equivalences* (2025): cited throughout GL26's §2.4, §7–§10.

The status of each is recorded in the two reports above, including which
statements are assumed rather than proved.

## Building on the Axiom Math Stacks formalization

The project builds **on top of
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks)**, the Axiom Math
formalization of the Stacks Project, which is itself built on
[Mathlib](https://github.com/leanprover-community/mathlib4).  We thank the Axiom
Math team and the Stacks Project authors: the geometric prerequisites of GL26 —
algebraic spaces, `D_qc`, perfect complexes, Grothendieck duality — come from that
library, and the build configuration here (`lean-toolchain`, the `[leanOptions]`
block, the Mathlib pin) is copied from it so the two libraries can be developed
side by side.

* `lean-toolchain`: `leanprover/lean4:v4.35.0`.
* `lakefile.toml`: requires Mathlib at `v4.35.0` and `Stacks` from
  `https://github.com/AxiomMath/Stacks`.

With [elan](https://github.com/leanprover/elan) and Lake:

```bash
lake exe cache get   # Mathlib's compiled artifacts
lake build           # builds the libraries `FourierMukai` and `WeakApprox`
```

The Stacks library is large (about 63,000 modules) and its own cache is still
being prepared; both libraries here are Mathlib-only at present, so
`lake build FourierMukai WeakApprox` does not need the Stacks modules compiled.
For a machine without the pinned toolchain, `scripts/build.sh` compiles every
module with the `lean` on `PATH`.

## Layout

| path | contents |
|---|---|
| `FourierMukai/Prelim/` | the triangulated-category and 2-categorical foundations (see the table above) |
| `FourierMukai/Paper/` | the interface for the geometric layer, and the statements of the main theorems |
| `FourierMukai/Examples/` | a non-vacuous instantiation on Mathlib's derived category of an abelian category |
| `WeakApprox/` | the Lank–Pauwels preprint: §2–§4 |
| `results/` | reports: state of each formalization, missing prerequisites, porting notes |
| `scripts/build.sh` | the offline development build |

## License

Apache 2.0; see `LICENSE`.
