# GL26 in Lean: relative Fourier–Mukai theory for affine Noetherian schemes

This repository is a Lean 4 formalization of

> **GL26** — Elías Guisado Villalgordo, Pat Lank, *Relative Fourier–Mukai theory
> for algebraic spaces*, arXiv:2609.01298 (2026).

**Current scope: the affine base case.** The project verifies GL26 over an
affine Noetherian base scheme `S = Spec A`, on Mathlib alone.  The engine is the
gluing theorem of Lank–Pauwels (**LP Theorem 1.1**), whose categorical form is
verified here in full; the geometric layer is built for schemes, and the
affine case is where it is being completed.  The separated-base case and then
algebraic spaces are future targets — see [*Future targets*](#future-targets).

The verification chain for the affine case is tracked, row by row, in
[`results/AFFINE.md`](results/AFFINE.md).  Its end point is LP Theorem 1.1 for
the recollement `D_qc,Z(Spec A) ⟷ D_qc(Spec A) ⟷ D_qc(Spec A[1/f])` with **no
unproved input except Neeman's published theorem** (Acta Math. 233 (2024),
Theorem 3.2), which states that `D_qc,Z(X)` is weakly approximable for every
quasicompact quasiseparated scheme `X` and every closed `Z` with quasicompact
complement.

## What is verified

**Categorical layer** (`WeakApprox/`, scheme-agnostic, `sorry`-free):

| result | Lean |
|---|---|
| LP §2–§3: `⟨H⟩^[a,b]`, its closure properties (Lemma 3.1), the aisle lemma (3.3), iterated approximation (3.4), the vanishing criterion (3.5) | `WeakApprox/{Basic, Closure, Shift, Functoriality, HomVanishing, Aisle, Lemma34, Lemma35, Octahedron}.lean` |
| LP §4: the `Recollement` structure, the glued aisle (Lemma 4.2), Lemma 4.3 with its hypotheses reduced, `P`-lifts (Def. 4.5), Lemma 4.6, Proposition 4.8, Setup 4.4 reduced to its irreducible data | `WeakApprox/{Recollement, Lemma42, Lemma43, Lemma4323, Lemma433TStructure, PLift, Lemma46, Proposition48, Proposition48Paper, Setup44, Setup44Reduced, Setup44Minimal}.lean` |
| **LP Theorem 1.1**, both directions, from the minimal setup, with Stacks 09SR weakened to eventual vanishing between compacts | `WeakApprox/{Main, MainMinimal, EventualVanishing, CompactVanishing, NineSR}.lean` |
| compactness over `AddCommGrpCat` (the paper's notion), closed under biproducts | `WeakApprox/CompactAb.lean` |

**Scheme layer** (`FourierMukai/Scheme/`):

| result | Lean |
|---|---|
| `D(X) = D(X.Modules)`, cohomology sheaves, `D_qc(X)` as complexes with quasicoherent cohomology | `Derived.lean` |
| finite locally free sheaves, bounded vector-bundle complexes, `IsPerfect` (scheme-local 0BCJ model) | `Perfect.lean` |
| `j_! ⊣ j^* ⊣ j_*` for an open immersion, `j_!` and `j^*` exact, the derived recollement interface | `OpenImmersion.lean` |
| derived pushforward/pullback from Kan extensions; `RHom`, `⊗^L`, `f^×`, `f^!` interface with the projection formula and base change as a mate | `Duality.lean` |
| the ten GL26 targets over Noetherian schemes as `Prop`-valued statements, with no vacuous hypotheses | `Statements.lean` |
| the published inputs (Neeman, Bondal–Van den Bergh) as `Prop` templates with citations | `Inputs.lean` |

**Affine results** (the current focus):

| result | Lean |
|---|---|
| `Perf A`, `Db A`, `Dbcoh A` for a ring: closure under `0`, shifts, biproducts, cones, retracts; `Perf ⊆ D^b`; `Perf ⊆ D^b_coh` for Noetherian `A` | `PerfectRing.lean` |
| the affine dictionary `D(A-Mod) ≌ D(QCoh(Spec A))`, from a general derived-transport theorem for equivalences of abelian categories | `AffineDictionary.lean` |
| **LP Theorem 1.1 for `D(A-Mod)`**: weak approximability iff eventual self-vanishing of the generator | `Affine.lean` |
| **GL26 Lemma 2.25 for affine schemes**, proved: `Φ_{RΔ_*O} ≅ 𝟭`, with the projection formula, the tensor unit and the diagonal retractions as data | `AffineDiagonal.lean` |

Everything above is `sorry`-free and depends only on `propext`, `Classical.choice`
and `Quot.sound`; the audits are printed at the end of the modules that state the
main results.

## What is assumed

Only published theorems, each stated as a named `Prop`/`structure` field with a
citation, never as a `sorry`:

* **Neeman**, *Bounded `t`-structures on the category of perfect complexes*,
  Acta Math. 233 (2024), Theorem 3.2 — weak approximability, compact generation,
  compact = supported perfect, preferred `t`-structure, for qcqs schemes.
* **Bondal–Van den Bergh**, *Generators and representability of functors…*,
  Mosc. Math. J. 3 (2003), Theorem 3.1.1 and Lemma 3.3.8 — compacts are perfect,
  and eventual vanishing between them.
* Stacks tags for the individual facts still being formalized: 01LA
  (quasicoherence is a Serre property), 06Z0/36.3.5 (the two models of `D_qc`),
  09M1/0BCJ/08CM (perfect complexes), 08IN (projection formula), 00A6/00AB
  (exactness of `j_!`, `j^*`).

What is *not* claimed: the general scheme case, the separated case, algebraic
spaces, and GL26's Theorems 1.2–1.7 beyond their statements.

## Future targets

1. **Separated Noetherian schemes.**  The same chain over a separated base, where
   Guisado Villalgordo–Lank–Manali Rahul–Pavic, Theorem 6.11, is the scheme form
   of GL26 Theorem 10.13.
2. **Algebraic spaces**, which need the Stacks library for `D_qc` on algebraic
   spaces; at this toolchain that is a person-months port (see
   [`results/STACKS_PORTABILITY.md`](results/STACKS_PORTABILITY.md)).
3. The remaining GL26 targets (1.2, 1.3, 1.6, 1.7, 12.3, 2.26, 12.2, 6.18),
   which are stated over Noetherian schemes in `FourierMukai/Scheme/Statements.lean`.

The algebraic-space interface (`FourierMukai/Paper/DerivedSetup.lean`) and its
target file are kept as the record of what must remain true after the switch;
`FourierMukai/Paper/InterfaceAudit.lean` records a defect found in it — the
abstract `FMContext` does not imply Lemma 2.25, which is why the affine proof of
that lemma carries the projection formula and the diagonal identities as data.

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
  (`WeakApprox/Main.lean`).  Theorem 1.1 itself needs no unproved input, and
  Setup 4.4 is reduced to its irreducible hypotheses
  (`WeakApprox/Setup44Minimal.lean`): the normalization, the compactness and
  generation of the glued generator, the glued `t`-structure and condition (3)
  are all derived.  The remaining external ingredient of the paper is Stacks Tag
  09SR (Ravenel–Neeman), used only for condition (3), and
  `WeakApprox/NineSR.lean` records exactly what is and is not formalized of it.
  Weak approximability is also shown invariant under triangulated equivalences
  (`WeakApprox/EquivalenceInvariance.lean`).  Compactness is
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

## Building

The project is **Mathlib-only**.  It was originally laid out to sit on top of
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks), the Axiom Math
formalization of the Stacks Project, and the `[leanOptions]` block in
`lakefile.toml` is kept from that project's configuration because every module
here has been checked against it.  The Stacks requirement itself has been
dropped: porting that library to the toolchain used here is a person-months
programme ([`results/STACKS_PORTABILITY.md`](results/STACKS_PORTABILITY.md)),
so the geometric layer is built directly on Mathlib.

* `lean-toolchain`: `leanprover/lean4:v4.33.1`, the toolchain every module has
  actually been verified against.
* `lakefile.toml`: requires Mathlib at `v4.33.1`; no Stacks requirement.
* In the verification environment there is no Lake build: `/opt/mathlib` is a
  prebuilt read-only Mathlib on `LEAN_PATH`, and `scripts/build.sh` calls `lean`
  directly.  That script is the reproduced build; the Lake configuration is kept
  for users with a writable setup and is not exercised here.

With [elan](https://github.com/leanprover/elan) and Lake:

```bash
lake exe cache get   # Mathlib's compiled artifacts
lake build           # builds the libraries `FourierMukai` and `WeakApprox`
```

or, without Lake, `./scripts/build.sh`, which compiles every module in dependency
order with the `lean` on `PATH`.

## Layout

| path | contents |
|---|---|
| `WeakApprox/` | the Lank–Pauwels preprint: §2–§4 and Theorem 1.1, scheme-agnostic |
| `FourierMukai/Scheme/` | the scheme layer and the affine verification: `D(X)`, `D_qc`, `Perf`, open-immersion functors, duality interface, statement layer, and the affine theorems |
| `FourierMukai/Prelim/` | the triangulated-category and 2-categorical foundations used by both |
| `FourierMukai/Paper/` | the (superseded) algebraic-space interface, its targets, and the interface audit |
| `FourierMukai/Examples/` | a non-vacuous instantiation on Mathlib's derived category of an abelian category |
| `results/` | reports: `AFFINE.md` (the verification chain), `SCHEMES.md` (general scheme target), `MATHLIB_INVENTORY.md`, `STACKS_PORTABILITY.md`, `GL26_SCHEME_DEPENDENCE.md`, `WEAK_APPROX.md`, `REPORT.md` |
| `scripts/build.sh` | the offline development build |

## License

Apache 2.0; see `LICENSE`.
