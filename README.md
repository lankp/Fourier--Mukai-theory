# Relative Fourier–Mukai theory for algebraic spaces, in Lean 4

A Lean 4 formalization of

* **GL26**: Elías Guisado Villalgordo and Pat Lank, *Relative Fourier–Mukai
  theory for algebraic spaces*, arXiv:2609.01298, and
* **LP26**: Pat Lank and Bregje Pauwels, *Gluing weak approximability along
  recollements*, preprint 2026,

on Mathlib, together with the classical inputs the two papers use and Mathlib
does not have: perfect complexes for rings, quasicoherent cohomology through the
tilde functor, K-projective replacements, Le–Chen's splitting criterion, and the
exceptional functors of the affine recollement.

228 modules, about 57 000 lines.  There is no `sorry` except in nine declarations
that are deliberately left as targets; see [What is stated but not
proved](#what-is-stated-but-not-proved).

## Goal

**Verify GL26 completely, all of its results.**

That is the target, and nothing in the repository is a substitute for it.

**In full generality** (maintainer's standing instruction, 26 November 2026): the
results are to be proved as the current manuscripts state them, for algebraic
spaces, with `D_qc`, `Perf`, `D^b_coh`, `Lf^*`, `Rf_*`, `⊗^L` as in GL26 §2.2.  The
abstract interfaces and the affine `D(A-Mod)` model below are the categorical
engine; a result proved only there is recorded as such and is not the paper's
result.  The geometric foundation is
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks), imported as a Lake
dependency: its algebraic spaces, `D(𝒪_X)` on the small étale site, `D_QCoh`,
perfect and pseudo-coherent objects, `f^×`, compact generation and Nagata
compactification were mapped against GL26 and judged faithful
([`results/AXIOMMATH_MAP.md`](results/AXIOMMATH_MAP.md)), and 147 Stacks tags cited
by the two papers were checked against it
([`results/AXIOMMATH_TAGS.md`](results/AXIOMMATH_TAGS.md)).

The work goes in order.  The first part is weak approximability — the theorem of
LP26 and Neeman's theorem, with support — for quasi-compact quasi-separated
schemes, in the supported form `D_qc,Z(X)`.

## Status

| | |
|---|---|
| LP26, the whole categorical layer (Sections 2–4 and Theorem 1.1) | proved; **Theorem 1.1 with exactly the paper's hypotheses** (`PaperHypothesesW6.theorem_1_1_paper`, pinned, wave 6): only Stacks 09SR assumed; compactly generated `t`-structures and BNP Cor 3.10(1) proved |
| LP26 Theorem 1.1, affine case | the large-model endpoints `affine_theorem_1_1_unconditional`, `affine_theorem_1_1_stacks07LT` are **proved vacuous** for every nontrivial ring (`RefuteLargeCoproducts`: `¬ HasCoproducts.{u+1} (AffineD A)`, wave 6) and unpinned; the `IsGenerator` endpoints `SetupMainMinimal.theorem_1_1`, `affine_theorem_1_1_small` are proved vacuous at `ℤ` (`RefuteIntGenerator*`); LP26 Thm 1.1 stands as `PaperSetupMainMinimal.theorem_1_1` (zero-detecting generator), with the paper-hypotheses form in progress (wave 6) |
| GL26 Lemma 2.25 | proved from the inputs its own proof uses |
| GL26 Lemma 2.26 | proved in categorical form; affine wrapper proved |
| GL26 Lemma 5.4 | proved in six-functor form, modulo the cover square |
| GL26, categorical results of §2.1, §7 and Appendices B, C (Lemmas 2.3, 2.5, 7.2, 7.4, 7.6, 7.9, 7.11, Lemma-Def 7.10, B.2, B.4, B.5, B.7, B.10, C.1) | proved (some in `Cat` rather than an arbitrary 2-category) |
| GL26 Lemma 2.4 | proved from Stacks 09SN |
| GL26 Lemmas 7.12 and 7.17 | proved over abstract pseudofunctor data, and for `Scheme/Duality.lean`'s base-change maps from one named input (`DerivedPseudofunctorInput`, Lipman 3.6.2) |
| GL26 Lemmas 6.11, 10.1, 10.2 | 6.11 and 10.1 proved in six-functor form from Stacks 08IR, 08EU/08IN; 10.2 proved with no input |
| compactness of the regular module; weak approximability of `D(A-Mod)` and of `D_{V(f)}(A-Mod)` | proved, unconditionally |
| GL26 Lemma A.4, affine case (the recollement `D(A[1/f]) → D(A) → D_Z(A)`) | every field constructed, from Stacks 0E55 |
| LP26 Cor 1.2 affine base = Neeman 2024 Thm 3.2(iv) for `Spec A`, `V(I)`, `I` f.g. | **proved with no input** in `D(A-Mod)` (`NeemanAffineSupport.satisfiesPaperWA_of_fg`, wave 5) |
| Neeman 2024 Thm 3.2 | no longer assumed: (i) proved for `D(A)`; the Neeman inputs deleted from the tree (wave 5); (iii) for schemes/spaces open |
| weak approximability for qcqs schemes/spaces with support | open: transport of the affine base to AxiomMath's model, then the induction (wave 6+) |
| the remaining numbered results of GL26 | stated over Noetherian schemes, or over the abstract interface of `Paper/`, not proved; not yet stated over algebraic spaces |
| foundation for full generality | AxiomMath/Stacks mapped and audited against GL26 §2.2–2.4 (wave 4); toolchain migrated to Lean/Mathlib v4.35.0 to match it; the dependency and the algebraic-space layer `FourierMukai/Spaces/` are wave 5 |

The result-by-result status of both papers, in the numbering of the current
manuscripts, is in [`results/COVERAGE.md`](results/COVERAGE.md); the orchestration
of the work is in [`results/SWARM.md`](results/SWARM.md).

## What is proved

Everything in this section is free of `sorry` and depends only on `propext`,
`Classical.choice` and `Quot.sound`.  The audit is printed by
[`FourierMukai/Audit.lean`](FourierMukai/Audit.lean), and 17 headline
declarations are pinned in
[`results/statement-baseline.txt`](results/statement-baseline.txt).

### LP26, categorical layer (`WeakApprox/`)

| result | modules |
|---|---|
| the subcategory `⟨H⟩^[a,b]` and its closure properties (Lemma 3.1), the aisle lemma (3.3), iterated approximation (3.4), the vanishing criterion (3.5) | `Basic`, `Closure`, `Shift`, `Functoriality`, `HomVanishing`, `Aisle`, `Lemma34`, `Lemma35`, `Octahedron` |
| the `Recollement` structure, the glued aisle (Lemma 4.2), Lemma 4.3, `P`-lifts, Lemma 4.6, Proposition 4.8 | `Recollement`, `Lemma42`, `Lemma43`, `Lemma4323`, `Lemma433TStructure`, `PLift`, `Lemma46`, `Proposition48` |
| Theorem 1.1, both directions, from the reduced Setup 4.4 | `Main`, `MainMinimal`, `EventualVanishing`, `CompactVanishing`, `NineSR` |
| the zero-detection formulation the papers use | `PaperGeneratorM2`, `PaperLemma34M2`, `PaperSetup44M2`, `PaperMainMinimalM2` |
| compactness over `AddCommGrpCat`, and closure of compact objects under thick envelopes without AB4 | `CompactAb`, `CompactThick` |
| coproducts restricted to one aisle, so the LP proof needs no coproducts in the ambient category | `Scheme/AisleCoproducts` |

### Affine layer (`FourierMukai/Scheme/`)

| result | modules |
|---|---|
| `D(A-Mod) ≌ D(QCoh(Spec A))`, and the two models of `D_qc(Spec A)` from `tilde ⊣ RΓ` | `AffineDictionary`, `AffineQCoh` |
| `Perf A`: thick envelope, closure properties, `⊆ D^b`, `⊆ D^b_coh`; over a field `Perf k = D^b_coh k` | `PerfectRing`, `PerfectField` |
| bounded finite-projective models are perfect, over any commutative ring (066T) | `PerfectModel` |
| `Perf ≤ model ↔ model` is closed under retracts, and the model class is triangulated | `PerfectModelConverse` |
| Le–Chen 2.3: two out of three for split idempotents in a triangle | `LeChen` |
| the finite-free induction of 07LT, and `compact ⇒ Perf` | `CompactToPerfect` |
| perfect ⇒ compact (the thick half of 09M8), with compactness of the regular module now proved | `PerfectCompactThick`, `RegularCompact`, `RegularCompactEndpoints` |
| compactness of the regular module in `D(A-Mod)`, and unconditional weak approximability of `D(A-Mod)` and of `D_{V(f)}(A-Mod)` | `RegularCompact` (`ringObject_isCompactAb`), `RegularCompactEndpoints` (`affine_satisfiesPaperWA`, `principalSupported_satisfiesPaperWA`) |
| Spaltenstein's Theorem C, for any abelian category, and `AffineSpaltensteinInput A` for any commutative ring | `KProjectiveResolution`, `AffineBoundedAboveCoproducts`, `SpecialDirectLimits`, `Spaltenstein*`, `AffineSpaltenstein` |
| the Hovey route to the same replacement data | `ProjectiveModel`, `SmallObjectPresentable`, `GeneratingCofibrations` |
| 01LA(6) and 01IE extension closure, without cohomology | `QCohSerre`, `QCohSerreExtension`, `QCohSerreExtension01IE` |
| coproducts on `D(A-Mod)`: the universe decision, with `AffineD A ≌ SmallAffineD A H` | `AffineUniverse` |
| the affine recollement `D(A[1/f]) → D(A) → D_Z(A)` in the GL26/LP26 orientation, all fields, from Stacks 0E55 (a right adjoint of `Rj_*`); unconditionally when coextension of scalars is right exact | `AffineJUpperConstruction`, `AffineRecollement`, `AffineLocalCohomology`, `AffineLocalCohomologySupport`, `AffineGluing`, `AffineSupportedAssembly`, `AffineMixedZero`, `AffineIShriek`, `AffineSecondGluing`, `AffineRecollementAssembly` |
| LP26 Theorem 1.1, affine case | `AffineMain`, `SmallAffineAssembly`, `AffineUniverse`, `PerfectRingStacks` |

### GL26 results

| result | modules | what it takes as input |
|---|---|---|
| Lemma 2.25, `Φ_{RΔ_*O_Y} ≅ 𝟭` | `DiagonalIdentity`, `DiagonalFunctoriality`, `DiagonalDuality`, `Statements` | Stacks 08IN and functoriality of derived pullback and pushforward.  The tensor unit and the two diagonal retractions are derived rather than assumed, and the proper-flat hypothesis is proved unused |
| Lemma 2.26, convolution | `AffineConvolution`, `GL26OtherTargets` | the derived cube, Stacks 08IN and 08IR, and one monoidal compatibility, packaged as `CorrectedConvolutionData` |
| Lemma 5.4, the external tensor of compact generators generates the product | `Lemma54` | the cover square (flat base change, conservativity, the perfect/compact calculus).  The argument itself is proved in six-functor form |
| Neeman 3.2(iv), affine supported base | `PrincipalNeemanM1`, `IdealNeemanM1`, `AffineSupportedSchemeBaseM1` | for a principal closed support, nothing (compactness of the regular module is proved in `RegularCompact`); for finite `V(I)` and `IsAffine X`, named inputs, one of which is refuted (see "What is open") |

| Lemma 2.3, iso-loci of (tri)natural transformations | `Coproduct`, `Triangulated`, `Thickness`, `EssentiallyDense` | nothing |
| Lemma 2.4, `G` compactly generates iff `⟨G⟩‾ = T` | `Lemma24` | Stacks 09SN (`Stacks09SN`); the direction `⟨G⟩‾ = T ⇒` is unconditional |
| Lemma 2.5, equivalences detected on compacts | `Lemma25` | nothing (compactness is `IsCompactAb`; see `CompactnessAudit` for the earlier vacuous rendering) |
| Lemmas 7.2, 7.4, 7.6, 7.9, 7.11, Lemma-Definition 7.10, Lemma C.1 (mates, conjugates, adjoint equivalences, units) | `Mates`, `MatesCalculus`, `AdjunctionUnits` | nothing; in `Cat` (C.1 (1) in any bicategory) |
| Lemmas 7.12, 7.17 and the base-change maps of 7.13–7.15 | `BaseChangeMates` | nothing, over abstract pseudofunctor data (`PullPushData`) |
| Lemmas B.2, B.4, B.5, B.7, B.10 (the 2-categories `Trans`, `Triang`) | `TransTwoCategory`, `AppendixB` | nothing |
| Lemma A.4, affine case | `AffineJUpperConstruction` and the `AffineRecollement*` modules | Stacks 0E55; unconditional when coextension of scalars is right exact |

| Lemmas 6.11, 10.1, 10.2 (the base-change cube of Setup 2.20) | `FMCube` | 6.11: Stacks 08IR; 10.1: 08IR and 08EU/08IN; 10.2: nothing |
| Lemmas 7.12–7.17 for the base-change maps of `Duality.lean` | `DualityMates` | `DerivedPseudofunctorInput` (Lipman 3.6.2; GL26 Lemma 2.13), an open named input |

### What is stated but not proved

* [`FourierMukai/Paper/Statements.lean`](FourierMukai/Paper/Statements.lean)
  contains nine `sorry`s.  They are the remaining numbered results of GL26,
  written over an early abstract interface, and kept as targets; the audit prints
  them on purpose, and nothing on the affine path depends on them.  Lemma 2.25 is
  the exception in that file: it is proved, from the inputs its proof uses.
* [`FourierMukai/Scheme/Statements.lean`](FourierMukai/Scheme/Statements.lean) is
  a statement layer.  It gives the numbered results over Noetherian schemes as
  `Prop`-valued definitions, with the inputs each one needs left visible.

**GL26's Lemmas 2.25 and 2.26 are correct as stated in the paper, and both are
proved here** in the form that carries the inputs their proofs use (the projection
formula, the tensor unit, the diagonal identities, Tor-independent base change).
The files `Paper/InterfaceAudit.lean`, `Scheme/GL26OtherTargets.lean` and
`Scheme/ConvolutionCounterexample.lean` are about the Lean *interface*, not the
paper: they show that an interface whose derived functors are free fields cannot
imply these lemmas, which is why the Lean statements carry those inputs explicitly.

## Rules and assumptions

### What may be assumed

**The goal: AxiomMath's Stacks Project is the only assumption; every other result
GL26 and LP26 need comes from Mathlib or is proved here, as needed** (maintainer,
26 November 2026).  Named non-Stacks hypotheses that remain in the tree are open
items, not permitted inputs; a result that takes one is conditional.

One source, and nothing else: **AxiomMath/Stacks**, the formalization of the
Stacks Project at <https://github.com/AxiomMath/Stacks>.  Its results may be used
freely.  A Stacks result that Axiom has formalized counts as available; we do not
reprove it merely to avoid depending on it.

**Neeman**, *Bounded `t`-structures on the category of perfect complexes*, Acta
Math. 233 (2024), Theorem 3.2, was the second permitted source (direction "compact
implies perfect", large-Hom model).  Since 26 November 2026 it is **not** assumed
(maintainer's instruction): what the project needs from it is formalized and
verified here, and only that.  Its affine interfaces (`CompactPerfectInput`,
`SmallNeemanCompactToPerfectInput`, `Neeman_3_2_*`, the 066S module `Affine066S`)
were deleted on `wave5/neeman-prune`; the remaining uses (the 3.2(iii) field of
`SupportedCategoryInput`, the `CompactsArePerfect` fields of the scheme gluing
interfaces) are open items, listed under [What is open](#what-is-open).

Everything else is proved here.  The hypotheses that remain in the affine
endpoint are hypotheses of LP26 Theorem 1.1 by design, not gaps: the
`SetupMainMinimal` data, and one compact-generation identity.

### How a use of AxiomMath/Stacks is marked

A tag named only in prose is not a mark.  A use is marked in one of two ways.

* A `Prop`-valued field of `RelativeFM.StacksInterface`
  ([`FourierMukai/Scheme/StacksInput.lean`](FourierMukai/Scheme/StacksInput.lean)),
  taken as a hypothesis, so the dependency appears in the type of the theorem
  that uses it.
* A docstring naming the tag, when what is used is data rather than a
  proposition.

[`results/ASSUMPTIONS.md`](results/ASSUMPTIONS.md) is the ledger: one row per tag,
with status `P` proved here, `N` derived from a stated Neeman input, `S` supplied
by AxiomMath/Stacks, `R` bibliographic and not used.  The policy is in
[`results/STACKS_POLICY.md`](results/STACKS_POLICY.md).

**How AxiomMath is used.**  AxiomMath/Stacks is a Lake dependency, pinned at
`f56a316` (nothing is copied from it).  The algebraic-space library `Spaces` imports
only AxiomMath's definitions (`scripts/axiommath/spaces-imports.txt`); an AxiomMath
theorem it needs is a tagged input with AxiomMath's exact statement, and the library
`SpacesVerified` discharges every such input by the AxiomMath theorem itself, so the
results over algebraic spaces are unconditional and fully kernel-checked.  The Stacks
tags the two papers use, with the AxiomMath declaration for each, are listed in
[`results/AXIOMMATH_TAGS.md`](results/AXIOMMATH_TAGS.md).  Details:
[`results/STACKS_POLICY.md`](results/STACKS_POLICY.md).

### Generation is zero detection

Weak approximability is used in the form LP26 uses: `PaperWeakApproximationData`
with `IsPaperGenerator`, where a generator is an object whose vanishing detects
zero.  The stronger `IsGenerator` of the earlier interface is uninhabitable for
the regular module over `ℤ`, which is proved twice
(`Scheme/GeneratorCounterexampleM5.lean` for the ghost, and
`Scheme/AffineNeemanAssembly.lean` for the nonzero `Ext¹(ℤ/2, ℤ)`), so it must not
be required of the structure sheaf.  The LP26 chain is reproved under zero
detection in `WeakApprox/Paper*M2.lean`.  The old interface is still in the tree,
because the abstract statement of LP26 Theorem 1.1 is written over it, and
`PaperWeakApproximationData.ofStrong` records that the old data forgets to the new.

### Statements must be faithful

No target is stated over an interface that does not imply it, no hypothesis is
`True`, and no paper result is reworded to fit what is available.  When a Lean
statement is weaker than the paper's, the gap is named.  When a rendering is
false, it is refuted in the repository rather than kept as a target.

### Attribution

File headers read `Copyright (c) 2026 Formalization of Lank--Pauwels`.  The
second author of LP26 is Bregje Pauwels.  Code is under the Apache 2.0 licence.

## Verification

### Two build paths

| path | command | where |
|---|---|---|
| Lake, with Mathlib's olean cache | `lake exe cache get`, then `lake build` | CI, [`.github/workflows/ci.yml`](.github/workflows/ci.yml) |
| a script that calls `lean` in dependency order | `./scripts/build.sh` | the development VM, where Mathlib is prebuilt and read-only and there is no Lake package directory |

Both compile the same sources with the toolchain in `lean-toolchain` (Lean 4.35.0)
and Mathlib pinned in `lakefile.toml` and `lake-manifest.json` (tag `v4.35.0`).
Both use the same strict options: `autoImplicit = false`,
`relaxedAutoImplicit = false`, `maxSynthPendingDepth = 3`, the script passing them
with `-D` and the lakefile in `[leanOptions]`.

[`ci/ci.yml`](ci/ci.yml) is a byte-identical mirror of the installed workflow,
kept because this project's GitHub connection cannot write under
`.github/workflows/`.  A change to the workflow is made in the mirror and pasted
in by hand; `diff <(sed -n '/^name: CI/,$p' ci/ci.yml) .github/workflows/ci.yml`
checks that the two agree.

### CI

One job.  It restores an olean cache covering both `.lake/build` and
`.lake/packages/*/.lake/build`, runs `lake update` to clone Mathlib, fetches
Mathlib's oleans, builds, prints the axiom audit, runs the statement check, and
runs the linters (advisory).  Documentation-only pushes are skipped.
A run takes about 2 minutes 35 seconds, of which about 128 seconds is moving
Mathlib's sources and oleans into place.  Why `lake update` stays even though the
manifest is committed, and what it would take to get under 90 seconds — a bigger
cache, a prebuilt image, or a self-hosted runner — is in
[`results/CI_PERFORMANCE.md`](results/CI_PERFORMANCE.md); the answer is that a
hosted runner cannot do it.

### The independent statement check

[`StatementCheck.lean`](StatementCheck.lean) prints the type and the axiom set of
every headline result, and
[`scripts/check_statements.sh`](scripts/check_statements.sh) re-elaborates it,
refuses any line mentioning `sorryAx`, and diffs the output against
[`results/statement-baseline.txt`](results/statement-baseline.txt).

```bash
scripts/check_statements.sh            # check against the baseline
scripts/check_statements.sh --update   # re-record after an intended change
```

This catches a statement that has been weakened, a hypothesis that has been
strengthened, or an axiom that has appeared, even when every proof still compiles.
It does not check the proofs themselves against a trusted kernel; that would need
a standalone challenge library and a `comparator` run.

### The check applied to every claim in this repository

1. compile the module from the repository root and check the exit status;
2. search the output for `error`, because `#print axioms` prints even when a file
   does not compile;
3. search for `sorryAx`, and flatten the `depends on axioms` lines, which wrap,
   before reading them;
4. read the proof, not only the statement, where a gap could hide;
5. run the full `./scripts/build.sh`, because a single-file compile can read a
   stale `.olean` and miss a name clash that the full build catches.

## What is open

1. **Weak approximability for qcqs schemes with support.**  This is the first
   part of the goal.  The statement is `NeemanSupportedWeakApproximability X Z` in
   the repository's model of `D_qc`.  Of the four gluing inputs, supported
   excision is discharged from Stacks 08DF and isomorphism transport is proved;
   the open/closed glue is a reduction (`OpenClosedGlue`), and since wave 3 it no
   longer asks for a completion of two given approximation packages but for smaller,
   package-free inputs (`OpenClosedFrameInput`, `SupportedCategoryInput`:
   coproducts, Stacks 09SR, Neeman 3.2(iii), compact Hom vanishing), with headline
   `neemanSupported_of_qcqs_of_frameInput` (`Scheme/OpenClosedCompletion.lean`).
   **Whether those inputs are satisfiable is not yet shown**, in particular the
   coproduct input at the large Hom universe, so the qcqs headline is a reduction,
   not a proof; the affine supported
   base is proved unconditionally for a principal closed support
   (`principalSupported_satisfiesPaperWA`); the finite `V(I)` and `IsAffine X`
   forms take named inputs, and since wave 3 we know one of them,
   `KoszulScalarSupportInput`, is false for every nonzero ring
   (`KoszulInputs.not_koszulScalarSupportInput`), so those forms are vacuous until
   `FiniteKoszulM1.lean` is repaired (two of the other inputs,
   `IdealSupportedCoproductInput` and `IdealSupportedCompactnessInput`, are now
   proved).  What is left is those inputs and the
   satisfiability of the open/closed inputs (a concrete frame, and the right Hom
   universe for coproducts); compactness of the regular module is proved
   (`Scheme/RegularCompact.lean`).  The accounting is in
   [`results/SCHEMES.md`](results/SCHEMES.md).
2. **The affine recollement without Stacks 0E55.**  Every field of
   `AffineRecollementInput`, including `jUpper` with `jStar ⊣ jUpper`, is now
   constructed (`Scheme/AffineJUpperConstruction.lean`, by a Bousfield-localization
   argument that needs neither the tensor–Hom adjunction nor 0A6R), from a right
   adjoint of restriction of scalars `Rj_*` (Stacks 0E55, an allowed tagged input).
   What is left is that right adjoint without 0E55 (`RHom_A(A_f, -)` on unbounded
   complexes), and the identification of `jUpper` with `RHom(RΓ_Z A, -)`.
   `AffineJUpperCandidateRefuted` shows that the guess `jUpper = Rj_* Lj^*` is zero.
3. **The `SetupMainMinimal` data from ring data.**  `AffineSetupInventory.lean`
   packages what is left.  Neeman's preferred `t`-structure equivalence and the
   normalized weak approximation data do not by themselves give the literal aisle
   equalities that the Setup 4.4 fields ask for, so those have to be checked.
4. **066S without Neeman.**  It is derived from Neeman, which is enough for the
   endpoint, but not proved from scratch; the truncation induction fails because
   brutal truncation is not homotopy-functorial at the boundary
   (`Scheme/StupidTruncCounterexample.lean`).
5. **The rest of GL26, over algebraic spaces.**  The numbered results 1.2, 1.3,
   1.6, 1.7, 12.3, 12.2 and 6.18 are stated only over the abstract interface of
   `Paper/` (`theorem_12_3` even carries two `True` hypotheses, a rule violation
   that the restatement over spaces removes).  The plan: import AxiomMath, build
   the algebraic-space layer (`D_qc`, GL26's `f`-perfect and `f`-quasi-perfect,
   integral transforms `Φ_K`), state the headline results there, and prove them on
   the categorical engine.  What AxiomMath lacks is listed in
   [`results/AXIOMMATH_MAP.md`](results/AXIOMMATH_MAP.md), part C: integral
   transforms, weak approximability, Neeman's `f^!`, monoidality of `Lf^*` on
   `D_qc` (conditional there), the closed symmetric monoidal structure and the
   coherator on `D_qc`, `f^×` base change over non-affine bases, and a bridge
   between AxiomMath's compactness and `IsCompactAb`.
6. **Neeman 2024, Theorem 3.2, no longer assumed.**  Part (i) (compact ⇒
   perfect) is proved for `D(A-Mod)` with no input
   (`Stacks07LT.M4.perf_of_compact_unconditional`; the affine endpoint is
   `affine_theorem_1_1_unconditional`) and in the small-Hom model from Stacks
   09SR (`Scheme/Neeman32Inputs.lean`).  Still open: (iii) as the field of
   `SupportedCategoryInput` and (i) as the `CompactsArePerfect` fields of the
   scheme gluing interfaces, to come from AxiomMath's 09M8, 0AED, 0AEC, 09SR.
7. **Neeman's weak approximability for affine schemes with support, proved.**  The
   maintainer's goal for wave 5: `D_{V(I)}(A-Mod)` weakly approximable for every
   finitely generated `I` with no named input, then transported to AxiomMath's
   `D_qc,Z(Spec A)` as the base case of LP26 Corollary 1.2.

## Building

With Lake, as CI does:

```bash
lake exe cache get   # fetches the packages named in lake-manifest.json, and Mathlib's oleans
lake build           # FourierMukai, WeakApprox, StatementCheck
scripts/check_statements.sh
```

Without Lake, on the development VM where Mathlib is prebuilt and read-only on
`LEAN_PATH`:

```bash
./scripts/build.sh          # 202 modules, about five minutes on four cores
```

Or one module at a time:

```bash
LEAN_PATH="$LEAN_PATH:." lean -o FourierMukai/Scheme/AffineMain.olean \
  FourierMukai/Scheme/AffineMain.lean
```

Allow 300 seconds per module: the first `import Mathlib` in a process reads about
6 GB of oleans.

### Full verification (AxiomMath)

```bash
lake build Spaces           # GL26's notions on AxiomMath's definitions (~2 000 AxiomMath modules, ~40 min)
lake build SpacesVerified   # discharges the tagged AxiomMath inputs (~8 500 AxiomMath modules, ~6 h)
```

`SpacesVerified` needs about 14 GB of memory: one AxiomMath module
(`StacksFrontier.RingTheory.MilnorPatching.Relative`) peaks at ~13.6 GB, so add swap
on a 16 GB machine.  Neither library is a default target; `lake build` does not
compile AxiomMath.

## Layout

| path | contents |
|---|---|
| `WeakApprox/` | LP26: Sections 2–4 and Theorem 1.1, 45 modules |
| `FourierMukai/Scheme/` | the scheme and affine layer, the scheme-level statement layer, and the affine theorems, 153 modules |
| `FourierMukai/Prelim/` | triangulated-category and 2-categorical foundations, and the categorical results of GL26 §2.1, §7 and Appendices B, C, 15 modules |
| `FourierMukai/Paper/` | the early algebraic-space interface, its targets, and the interface audit |
| `FourierMukai/Examples/` | a non-vacuous instantiation on Mathlib's derived category |
| `Spaces/` | the algebraic-space layer on AxiomMath's definitions (GL26 §2.2 notions, integral transforms); tagged AxiomMath inputs in `Spaces/AxiomMathInputs.lean` |
| `SpacesVerified/` | discharge of the tagged AxiomMath inputs; the unconditional statements over algebraic spaces |
| `StatementCheck.lean` | the pinned statement surface, 17 declarations |
| `results/` | `AXIOMMATH_MAP.md` (GL26's notions and functors against AxiomMath/Stacks, with fidelity verdicts, gaps and build cost), `AXIOMMATH_TAGS.md` (every cited Stacks tag against AxiomMath), `AFFINE.md` (the verification chain, one row per cited input), `ASSUMPTIONS.md` (what is assumed and what would discharge it), `VERIFICATION.md` (the build and statement check, measured), `CI_PERFORMANCE.md` (where CI's time goes, and the three ways to cut it), `SCHEMES.md`, `GL26_SCHEME_DEPENDENCE.md`, `WEAK_APPROX.md`, `MATHLIB_INVENTORY.md`, `STACKS_POLICY.md`, `STACKS_PORTABILITY.md`, `REPORT.md`, `INTEGRATION.md` |
| `scripts/` | `build.sh`, `check_statements.sh`, `swarm/` (the orchestrator's branch verification), `axiommath/` (import-closure and tag-map scripts) |

## How the work was produced

Most of the proofs added after the initial infrastructure were produced by
**Ultramath**: several instances of the same model (`moonshotai/kimi-k3.1-pro`,
maximum reasoning effort) working one problem at once, each on a different
registered direction, in its own directory under `.ultramath/`, sharing findings
on a board.  Members never edit the repository and never commit; their output is
a directory of Lean files and a report.

Every submission was checked by the coordinating agent before it entered the tree,
by the procedure above: exit status, search for `error`, search for `sorryAx`, the
flattened axiom sets, the proof read, then the full build.  Rejections and
corrections are recorded in the commit messages and in
[`results/ASSUMPTIONS.md`](results/ASSUMPTIONS.md), including where the agent was
wrong: a module that did not compile was withdrawn after it had been accepted on
the strength of a printed audit, a mis-cited Stacks tag (0BFF, a formula for
abelian varieties) was removed after reading it at the source, a construction of
`iShriek` was downgraded from proved to conditional on an instance that fails for
`A = ℤ` and `f = 2`, and three times a member's reading of a paper corrected the
brief it had been given.

Since 25 November 2026 the work is organised as a swarm of Claude Code sessions
([`results/SWARM.md`](results/SWARM.md)): an orchestrator session splits the queue in
[`results/COVERAGE.md`](results/COVERAGE.md) into waves of independent tasks, each
worker session proves its task on its own branch, and the orchestrator re-runs the
seven checks of [`CLAUDE.md`](CLAUDE.md) (including non-vacuity of hypotheses) on
the merge, reads each statement against the manuscript, and only then merges into
`formalization`.  The task briefs are in [`results/swarm/`](results/swarm/).

## Provenance

Where a classical input was needed and a Stacks Project tag proves it, the tag is
cited with its number and its statement, and the proof is written against that
statement rather than against a textbook paraphrase: for example Tag 0AED (compact
if and only if perfect), Tag 09MB (eventual vanishing), Tag 0BCJ (perfect means
locally bounded finite locally free).  Where the tag is proved here instead, the
module says so and the ledger records it.  Where this project's own prose was
wrong and the Lean was right, the correction is recorded where it arose
(`results/AFFINE.md`, on the orientation of the recollement).

## Licence

Apache 2.0; see [`LICENSE`](LICENSE).
