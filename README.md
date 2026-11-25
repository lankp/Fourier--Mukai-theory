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

202 modules, about 50 000 lines.  There is no `sorry` except in nine declarations
that are deliberately left as targets; see [What is stated but not
proved](#what-is-stated-but-not-proved).

## Goal

**Verify GL26 completely, all of its results.**

That is the target, and nothing in the repository is a substitute for it.  The
work goes in order.  The first part is weak approximability — the theorem of
LP26 and Neeman's theorem, with support — for quasi-compact quasi-separated
schemes, in the supported form `D_qc,Z(X)`.

## Status

| | |
|---|---|
| LP26, the whole categorical layer (Sections 2–4 and Theorem 1.1) | proved, unconditionally |
| LP26 Theorem 1.1, affine case, with Neeman 3.2 as the only published input | proved |
| GL26 Lemma 2.25 | proved from the inputs its own proof uses |
| GL26 Lemma 2.26 | proved in categorical form; affine wrapper proved |
| GL26 Lemma 5.4 | proved in six-functor form, modulo the cover square |
| weak approximability for qcqs schemes with support | reduced to named inputs; three of the four gluing inputs are done |
| the remaining numbered results of GL26 | stated over Noetherian schemes, not proved |

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
| 066S from Neeman, hence `BoundedProjectiveModelConverseInput`, `Stacks07LTCompactModelInput` and `CompactPerfectInput` | `Affine066S` |
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
| Neeman 3.2(iv), affine supported base | `PrincipalNeemanM1`, `IdealNeemanM1`, `AffineSupportedSchemeBaseM1` | for a principal closed support, nothing (compactness of the regular module is proved in `RegularCompact`); for finite `V(I)` and `IsAffine X`, five named tagged inputs |

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

Two sources, and nothing else.

1. **AxiomMath/Stacks**, the formalization of the Stacks Project at
   <https://github.com/AxiomMath/Stacks>.  Its results may be used freely.  A
   Stacks result that Axiom has formalized counts as available; we do not reprove
   it merely to avoid depending on it.
2. **Neeman**, *Bounded `t`-structures on the category of perfect complexes*,
   Acta Math. 233 (2024), Theorem 3.2, and only in the direction "compact implies
   perfect", where a statement is made in the large-Hom model.

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

AxiomMath/Stacks cannot be imported here: it pins Lean and Mathlib 4.35.0 and
ships no build artifacts.  If it should enter Mathlib, the update is mechanical.
Each interface field is replaced by the imported declaration, its `S` row becomes
a `P` row, and the theorems that took the field lose that hypothesis.  No proof
here is written against Axiom's names, only against the statements recorded in the
interface.

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

Both compile the same sources with the toolchain in `lean-toolchain` (Lean 4.33.1)
and Mathlib pinned in `lakefile.toml` and `lake-manifest.json` (tag `v4.33.1`).
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
   the open/closed glue is a reduction (`OpenClosedGlue`); the affine supported
   base is proved unconditionally for a principal closed support
   (`principalSupported_satisfiesPaperWA`), and for finite `V(I)` and `IsAffine X`
   from five named tagged inputs.  What is left is those inputs and the completion
   that the open/closed glue asks for; compactness of the regular module is proved
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
5. **The rest of GL26.**  Beyond the affine case: separated Noetherian bases,
   then algebraic spaces, which need the Stacks library; and the numbered results
   1.2, 1.3, 1.6, 1.7, 12.3, 12.2 and 6.18.

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

## Layout

| path | contents |
|---|---|
| `WeakApprox/` | LP26: Sections 2–4 and Theorem 1.1, 45 modules |
| `FourierMukai/Scheme/` | the scheme and affine layer, the scheme-level statement layer, and the affine theorems, 146 modules |
| `FourierMukai/Prelim/` | triangulated-category and 2-categorical foundations |
| `FourierMukai/Paper/` | the early algebraic-space interface, its targets, and the interface audit |
| `FourierMukai/Examples/` | a non-vacuous instantiation on Mathlib's derived category |
| `StatementCheck.lean` | the pinned statement surface, 17 declarations |
| `results/` | `AFFINE.md` (the verification chain, one row per cited input), `ASSUMPTIONS.md` (what is assumed and what would discharge it), `VERIFICATION.md` (the build and statement check, measured), `CI_PERFORMANCE.md` (where CI's time goes, and the three ways to cut it), `SCHEMES.md`, `GL26_SCHEME_DEPENDENCE.md`, `WEAK_APPROX.md`, `MATHLIB_INVENTORY.md`, `STACKS_POLICY.md`, `STACKS_PORTABILITY.md`, `REPORT.md`, `INTEGRATION.md` |
| `scripts/` | `build.sh`, `check_statements.sh` |

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
