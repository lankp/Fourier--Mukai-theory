# Relative Fourier–Mukai theory for algebraic spaces, in Lean 4

A Lean 4 / Mathlib formalization of

* **GL26** — Elías Guisado Villalgordo, Pat Lank, *Relative Fourier–Mukai theory
  for algebraic spaces*, arXiv:2609.01298, and
* **LP** — Pat Lank, Bregje Pauwels, *Gluing weak approximability along
  recollements* (preprint, 2026),

together with the classical inputs the two papers need and Mathlib lacks: perfect
complexes for rings, quasicoherent cohomology through the tilde functor,
K-projective replacements, Le–Chen's splitting criterion, and the
exceptional-functor package of the affine recollement.

202 modules, about 50 000 lines, `sorry`-free except for nine declarations that are
deliberately left as specifications (see [What is stated, not
proved](#what-is-stated-not-proved)).  The GL26 statements are checked against the
25 November 2026 manuscript (`main-4.tex`, not the arXiv posting), theorem by
theorem in [`results/GL26_SCHEME_DEPENDENCE.md`](results/GL26_SCHEME_DEPENDENCE.md);
line references in `results/` name that file.

## Goals

1. **LP, in full.**  The whole categorical layer — §2–§4 and Theorem 1.1 — for an
   abstract recollement, with no scheme theory and no extra hypotheses.  Done.
2. **GL26's affine theorem on Neeman alone.**  The affine case of GL26 Theorem 1.1
   (equivalently LP Theorem 1.1 in `D_qc(Spec A)`) with Neeman's
   *Bounded t-structures on the category of perfect complexes* (Acta Math. 233
   (2024), Theorem 3.2) as the only published input, and everything else — 01LA,
   01IE, 01HV, 066S, 066T, 07LT, 09M1, 09M8, 09MB, 09SR, 0AED, 0BCJ, the
   Bondal–Van den Bergh inputs — either proved here or derived from Neeman.  Done,
   modulo the `SetupMainMinimal` data (see [What is open](#what-is-open)).
3. **GL26's numbered results over Noetherian schemes.**  Stated in a scheme-level
   statement layer; proved for Theorem 1.1 (affine case), Lemma 2.25, Lemma 2.26
   (categorical core, affine wrapper) and Lemma 5.4 (abstract six-functor form);
   the rest reduce to named residues.

Explicitly *not* goals, yet: algebraic spaces, `D_qc` for arbitrary schemes, and
Grothendieck duality in generality.  Mathlib has none of them, and porting the
AxiomMath/Stacks formalization to this toolchain is a person-months programme
([`results/STACKS_PORTABILITY.md`](results/STACKS_PORTABILITY.md)).

## What has been proved

Everything in this section is `sorry`-free and depends only on `propext`,
`Classical.choice`, `Quot.sound`.  The audits are printed by
[`FourierMukai/Audit.lean`](FourierMukai/Audit.lean) and at the end of the modules
that state the results, and 17 headline declarations are pinned in
[`results/statement-baseline.txt`](results/statement-baseline.txt).

### LP: gluing weak approximability — `WeakApprox/`

| result | module |
|---|---|
| `⟨H⟩^[a,b]` and its closure properties (Lemma 3.1), the aisle lemma (3.3), iterated approximation (3.4), the vanishing criterion (3.5) | `Basic`, `Closure`, `Shift`, `Functoriality`, `HomVanishing`, `Aisle`, `Lemma34`, `Lemma35`, `Octahedron` |
| the `Recollement` structure, the glued aisle (Lemma 4.2), Lemma 4.3, `P`-lifts, Lemma 4.6, Proposition 4.8 | `Recollement`, `Lemma42`, `Lemma43`, `Lemma4323`, `Lemma433TStructure`, `PLift`, `Lemma46`, `Proposition48` |
| **Theorem 1.1**, both directions, from the reduced Setup 4.4 | `Main`, `MainMinimal`, `EventualVanishing`, `CompactVanishing`, `NineSR` |
| the paper's zero-detection formulation, used throughout (`PaperWeakApproximationData`, `IsPaperGenerator`) | `PaperGeneratorM2`, `PaperLemma34M2`, `PaperSetup44M2`, `PaperMainMinimalM2` |
| compactness over `AddCommGrpCat` (the paper's notion), closed under biproducts | `CompactAb` |
| compact objects are closed under thick envelopes, by triangle two-out-of-three — no AB4 | `CompactThick` |
| coproducts localized to a fixed aisle, so the LP proof needs no ambient coproducts | `Scheme/AisleCoproducts` |

### The affine layer — `FourierMukai/Scheme/`

| result | module |
|---|---|
| `D(A-Mod) ≌ D(QCoh(Spec A))`, and the two models of `D_qc(Spec A)` from `tilde ⊣ RΓ` | `AffineDictionary`, `AffineQCoh` |
| `Perf A`: thick envelope, closure properties, `⊆ D^b`, `⊆ D^b_coh`; `Perf k = D^b_coh k` over a field | `PerfectRing`, `PerfectField` |
| bounded finite-projective models are perfect, for every commutative ring (066T) | `PerfectModel` |
| `Perf ≤ model ↔ model` retract-closed, with the model class triangulated | `PerfectModelConverse` |
| **Le–Chen 2.3**: two-out-of-three for split idempotents in a triangle | `LeChen` |
| **066S from Neeman**, hence `BoundedProjectiveModelConverseInput`, `Stacks07LTCompactModelInput`, `CompactPerfectInput` | `Affine066S` |
| 07LT's finite-free induction, and `compact ⇒ Perf` from its two residue fields | `CompactToPerfect` |
| perfect ⇒ compact up to compactness of the regular module (the thick half of 09M8) | `PerfectCompactThick` |
| **Spaltenstein's Theorem C**: `TheoremCInput` for arbitrary abelian `C`, and `AffineSpaltensteinInput A` for every commutative ring | `KProjectiveResolution`, `AffineBoundedAboveCoproducts`, `SpecialDirectLimits`, `Spaltenstein*`, `AffineSpaltenstein` |
| the Hovey model-structure route to the same replacement data | `ProjectiveModel`, `SmallObjectPresentable`, `GeneratingCofibrations` |
| **01LA(6) / 01IE** extension closure, proved without cohomology | `QCohSerre`, `QCohSerreExtension`, `QCohSerreExtension01IE` |
| coproducts on `D(A-Mod)`: the universe decision, with `AffineD A ≌ SmallAffineD A H` | `AffineUniverse` |
| the affine recollement `D(A[1/f]) → D(A) → D_Z(A)` in the GL26/LP orientation, **all fields but one** | `AffineRecollement`, `AffineLocalCohomology`, `AffineLocalCohomologySupport`, `AffineGluing`, `AffineSupportedAssembly`, `AffineMixedZero`, `AffineIShriek`, `AffineSecondGluing`, `AffineRecollementAssembly` |
| **GL26 Theorem 1.1**, affine, Neeman as the only published input | `AffineMain`, `SmallAffineAssembly`, `AffineUniverse`, `PerfectRingStacks` |

### GL26 results proved at the statement level

| result | module | what is assumed |
|---|---|---|
| **Lemma 2.25** `Φ_{RΔ_*O_Y} ≅ 𝟭` | `DiagonalIdentity`, `DiagonalFunctoriality`, `DiagonalDuality`, `Statements` | 08IN and functoriality; the tensor unit and the two diagonal retractions are *derived*, and the proper-flat hypothesis is proved unused | 
| **Lemma 2.26** (convolution) | `AffineConvolution`, `GL26OtherTargets` | the derived cube, 08IN, 08IR and a monoidal compatibility, packaged as `CorrectedConvolutionData` |
| **Lemma 5.4** (external tensor of compact generators generates) | `Lemma54` | the cover square (flat base change, conservativity, perfect/compact calculus); the argument itself is proved in six-functor form |
| **Theorem 1.1**, affine case | see above | Neeman 3.2 |
| **Neeman 3.2(iv)**: the affine supported base | `PrincipalNeemanM1`, `IdealNeemanM1`, `AffineSupportedSchemeBaseM1` | the principal closed support needs only `IsCompactAb (ringObject A)`; finite `V(I)` and `IsAffine X` need five named tagged inputs as well |

### What is stated, not proved

* [`FourierMukai/Paper/Statements.lean`](FourierMukai/Paper/Statements.lean) holds
  **nine** `sorry`s.  They are GL26's remaining numbered targets written over the
  superseded abstract `FMContext` interface, kept as specifications and printed
  deliberately by `FourierMukai/Audit.lean`.  Nothing on the affine path depends on
  them.  Lemma 2.25 is the exception: it is *proved* there from the inputs its own
  proof uses.
* [`FourierMukai/Scheme/Statements.lean`](FourierMukai/Scheme/Statements.lean) is a
  statement layer, not a proof layer: `Prop`-valued renderings of the numbered
  results over Noetherian schemes, with the residues named.

**A statement that omits an input is refuted here, not presented as the paper's
theorem.**  The bare renderings of Lemmas 2.25 and 2.26 — quantifying over a
`FMContext` whose derived functors are free fields — are *false*, and the
repository proves that (`Paper/InterfaceAudit.lean`,
`Scheme/GL26OtherTargets.lean`, `Scheme/ConvolutionCounterexample.lean`) while the
faithful forms are proved from the inputs the papers actually use.  The same
distinction has already caught two errors of this project's own prose: an earlier
version of `results/GL26_SCHEME_DEPENDENCE.md` said "Lemma 2.25 is false" on the
strength of one of those models, and the affine wrapper `affine_lemma_2_25` was
described as an affine *geometric* instance although it takes its derived data as
an argument.

## Related formalization

[**BridgelandStability**](https://github.com/mattrobball/BridgelandStability) — a
Lean 4 / Mathlib formalization of Bridgeland's *Stability conditions on
triangulated categories* — is the model for this repository's verification setup:
a Lake build against Mathlib's olean cache in CI, a linter pass, and a
`Challenge`/`comparator` step that checks the claimed statements independently of
the proofs.  The mathematics is unrelated (slicings and stability conditions
rather than Fourier–Mukai kernels), the engineering is not: same toolchain
generation, same cache strategy, same insistence that the statement surface be
auditable on its own.

## Verification

### Two build paths, one set of sources

| path | what it does | where it runs |
|---|---|---|
| `lake build` | Lake + `lake exe cache get`; builds `FourierMukai`, `WeakApprox`, `StatementCheck` | CI ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) |
| `./scripts/build.sh` | calls `lean` directly in dependency order, against a prebuilt read-only Mathlib on `LEAN_PATH` | the development VM, where there is no writable package directory |

Both use the same sources, the toolchain pinned by `lean-toolchain` (Lean
4.33.1) and Mathlib `v4.33.1` from `lakefile.toml`, and the same strict
elaboration options — `autoImplicit = false`, `relaxedAutoImplicit = false`,
`maxSynthPendingDepth = 3` — the script passing them with `-D` and the lakefile
in `[leanOptions]`.

### CI

The workflow is [`.github/workflows/ci.yml`](.github/workflows/ci.yml), live on
push; [`ci/ci.yml`](ci/ci.yml) is a byte-identical mirror kept for editing,
because this project's GitHub connection cannot itself write under
`.github/workflows/`.  Both jobs are green on a GitHub runner — the Lake build of
the whole tree with its axiom audit (2m15s), and the independent statement check
against the recorded baseline (1m43s).

[`ci/ci.yml`](ci/ci.yml) folds them into a single job and is waiting to be
pasted: one `lake update`, one cache restore that also covers
`.lake/packages/*/.lake/build`, then build, axiom audit, statement check and the
advisory linters in sequence, with documentation-only pushes skipped by
`paths-ignore`.  The installed copy still runs two jobs until that paste
happens.  What each step does:

1. **Lake build** — elan, `lake update`, `lake exe cache get`, `lake build`, then
   `lake env lean FourierMukai/Audit.lean`, which prints every headline
   declaration's axiom set and fails if anything stops elaborating.
2. **Independent statement check** — [below](#the-independent-statement-check).
3. **Linters**, advisory for now (`lake exe runLinter`, `lake exe lint-style`):
   the tree has not yet been brought up to Mathlib's linter standard.

### The independent statement check

[`StatementCheck.lean`](StatementCheck.lean) prints the *type* and the *axioms* of
every headline result.  [`scripts/check_statements.sh`](scripts/check_statements.sh)
re-elaborates that file and diffs the output against the recorded
[`results/statement-baseline.txt`](results/statement-baseline.txt), and refuses any
line mentioning `sorryAx`:

```bash
scripts/check_statements.sh            # check against the baseline
scripts/check_statements.sh --update   # re-record after an intended change
```

It currently covers 17 declarations — Theorem 1.1, Lemmas 2.25, 2.26, 5.4, LP
Theorem 1.1, the supported base, and the categorical lemmas behind them.  What
this establishes is that the **statements** have not drifted: a silently weakened
conclusion, a strengthened hypothesis, or a new axiom turns CI red even when every
proof still compiles.  What it does not establish is that the proofs are correct
against a trusted kernel — that is the `lean4export` + `comparator` step of the
BridgelandStability setup, and it is the natural next step here once a standalone
challenge library exists.  [`results/VERIFICATION.md`](results/VERIFICATION.md)
records the measured details: the strict `autoImplicit = false` block inherited
from AxiomMath/Stacks is now enforced on both build paths, nine modules were
given explicit binders to satisfy it, and the 502 declarations involved were
checked to have byte-identical elaborated signatures before and after.

### The protocol used for every claim in this repository

1. compile the module from the repository root and check the **exit status**;
2. `grep` the output for `error` — because `#print axioms` prints even when a file
   does not compile, so an audit line on its own proves nothing;
3. `grep` for `sorryAx`, and flatten every `depends on axioms` line (they wrap) to
   read the actual axiom set;
4. read the proof, not only the statement, where a gap could hide;
5. run the **full** `./scripts/build.sh` — a per-file compile can read a stale
   `.olean` and miss a name clash that the umbrella build catches.

## Rules and assumptions

### What may be assumed

**Two sources, and nothing else.**

1. **AxiomMath/Stacks** — the Axiom Math formalization of the Stacks Project,
   <https://github.com/AxiomMath/Stacks>.  Its formalization and results may be
   used freely here; a Stacks result that Axiom has formalized counts as available,
   and we do not re-prove it merely to avoid depending on it.
2. **Neeman**, *Bounded `t`-structures on the category of perfect complexes*, Acta
   Math. 233 (2024), Theorem 3.2 — and only in the direction *compact implies
   perfect*, where a statement is made for the large-Hom model.

Everything else is proved here.  In particular the endpoint's remaining hypotheses
are hypotheses of LP Theorem 1.1 by design, not gaps: the `SetupMainMinimal` data
and one compact-generation identity.

### How a use of AxiomMath/Stacks is marked

A tag mentioned in prose is not a mark.  A use is marked in one of two ways, and
both are checked:

* a `Prop`-valued field of `RelativeFM.StacksInterface`
  ([`FourierMukai/Scheme/StacksInput.lean`](FourierMukai/Scheme/StacksInput.lean))
  taken as a **hypothesis**, so the dependency appears in the theorem's type; or
* a docstring naming the tag, when the use is a data field rather than a
  proposition.

[`results/ASSUMPTIONS.md`](results/ASSUMPTIONS.md) is the ledger: one row per tag
with status `P` proved here, `N` derived from an explicit Neeman input, `S`
supplied by AxiomMath/Stacks, `R` bibliographic and not consumed.  The policy and
its rationale are in [`results/STACKS_POLICY.md`](results/STACKS_POLICY.md).

`AxiomMath/Stacks` **cannot be imported here**: it pins Lean `v4.35.0` and Mathlib
`v4.35.0` and ships no build artifacts.  If it enters Mathlib, the update is
mechanical: each `StacksInput` field is replaced by the imported declaration, its
`S` row becomes a `P` row, and the theorems that took the field lose that
hypothesis.  No proof is written against Axiom's *names*, only against the
statements recorded in the interface.

### Generation must be zero detection

Weak approximability is used in the form LP uses it — the paper's
`PaperWeakApproximationData` with `IsPaperGenerator`: a generator is one whose
vanishing detects zero.  The stronger `IsGenerator` used by the earlier
`WeakApproximationData` interface is **uninhabitable** for the regular module over
`ℤ`, and that is proved twice here (`Scheme/GeneratorCounterexampleM5.lean`: the
non-split `ℤ --2--> ℤ` gives a ghost; `Scheme/AffineNeemanAssembly.lean`: a nonzero
`Ext¹(ℤ/2, ℤ)`), so nothing may require it of the structure sheaf.  The LP chain is
therefore reproved under zero detection (`WeakApprox/Paper*M2.lean`), and the
affine endpoint and the supported-base results are stated in that form.  The old
`IsGenerator` interface is still in the tree — `WeakApprox/WeakApproximable.lean`,
`WeakApprox/MainMinimal.lean` — because the abstract LP theorem is stated over it;
`PaperWeakApproximationData.ofStrong` records that the old data forgets to the new,
so the zero-detection results are the stronger ones.

### Statements must be faithful

No target may be stated over an interface that does not imply it, no hypothesis may
be `True`, and a paper result is never reworded to fit what is available.  When the
Lean rendering of a result is weaker than the paper's, the gap is named (see
[What is stated, not proved](#what-is-stated-not-proved)); when a rendering is
simply false, it is refuted in-repo rather than kept as a target.

### Attribution

File headers read `Copyright (c) 2026 Formalization of Lank--Pauwels`; LP's second
author is Bregje Pauwels.  Code licence: Apache 2.0 (below).

## What is open

1. **The affine recollement's last adjunction.**  Every field of
   `AffineRecollementInput` is constructed except `jUpper` with
   `jStar ⊣ jUpper`.  The residue is one tensor–Hom adjunction on `RΓ_Z(A)`:
   `C ⊗^L (-) ⊣ RHom(C, -)` with `C = RΓ_Z(A)` (Stacks 0A6R), to which
   `AffineJUpperTensorHom` reduces `jStarAdj`.  For the record,
   `AffineJUpperCandidateRefuted` proves that the obvious guess
   `jUpper = Rj_* Lj^*` is *zero* and therefore wrong.
2. **The `SetupMainMinimal` data from ring data.**  `AffineSetupInventory.lean`
   packages what is left.  Its caveat: Neeman's preferred-`t`-structure equivalence
   and the normalized weak approximation data do not automatically give the
   *literal* aisle equalities that the Setup 4.4 fields ask for, so those must be
   checked rather than assumed to follow.
3. **066S unconditionally.**  It is derived from Neeman, which suffices for the
   endpoint, but not proved from scratch: the truncation induction fails because
   brutal truncation is not homotopy-functorial at the boundary
   (`Scheme/StupidTruncCounterexample.lean`).
4. **Neeman 3.2(iv) for schemes.**  Of the four gluing inputs, supported excision is
   discharged and isomorphism transport is proved; the open/closed glue is a
   reduction (`OpenClosedGlue`); the affine supported base is proved for a principal
   closed support from `IsCompactAb (ringObject A)` alone, and for finite `V(I)` and
   `IsAffine X` from that plus five named tagged inputs.  What is left there is those
   five statements and compactness of the regular module — not weak approximability.
   The accounting is in [`results/SCHEMES.md`](results/SCHEMES.md).
5. **Beyond the affine case.**  Separated Noetherian bases, then algebraic spaces,
   which need the Stacks library; and the remaining GL26 targets 1.2, 1.3, 1.6, 1.7,
   12.3, 12.2, 6.18.

## Building

### With Lake (the CI path)

```bash
lake update          # writes lake-manifest.json from lakefile.toml
lake exe cache get   # Mathlib's oleans
lake build           # FourierMukai, WeakApprox, StatementCheck
scripts/check_statements.sh
```

`lake-manifest.json` is not committed; the first `lake update` creates it, and
committing it afterwards freezes the resolution.  The `[leanOptions]` block is
inherited from the AxiomMath/Stacks build configuration and is enforced:
`autoImplicit = false`, `relaxedAutoImplicit = false`,
`maxSynthPendingDepth = 3`.  `scripts/build.sh` passes the same three with `-D`,
so the two paths elaborate identically; a module that relies on Lean's automatic
implicit binders fails both.

### Without Lake (the development VM)

`/opt/mathlib` is a prebuilt read-only Mathlib on `LEAN_PATH`:

```bash
./scripts/build.sh          # 202 modules, about five minutes on four cores
```

or one module at a time:

```bash
LEAN_PATH="$LEAN_PATH:." lean -o FourierMukai/Scheme/AffineMain.olean \
  FourierMukai/Scheme/AffineMain.lean
```

Allow at least 300 s per module: the first `import Mathlib` in a process reads
about 6 GB of oleans.

## Layout

| path | contents |
|---|---|
| `WeakApprox/` | the LP preprint: §2–§4 and Theorem 1.1 (45 modules) |
| `FourierMukai/Scheme/` | the scheme and affine layer: `D(X)`, `D_qc`, `Perf`, quasicoherent cohomology, K-projective replacements, the affine recollement, the affine theorems, the scheme-level statement layer (146 modules) |
| `FourierMukai/Prelim/` | triangulated-category and 2-categorical foundations |
| `FourierMukai/Paper/` | the superseded algebraic-space interface, its targets, and the interface audit |
| `FourierMukai/Examples/` | a non-vacuous instantiation on Mathlib's derived category |
| `StatementCheck.lean` | the pinned statement surface (17 declarations) |
| `results/` | `AFFINE.md` (the verification chain, one row per cited Stacks input), `ASSUMPTIONS.md` (what is assumed and what would discharge it), `VERIFICATION.md` (the build and statement-check setup, and what each establishes), `WEAK_APPROX.md`, `MATHLIB_INVENTORY.md`, `STACKS_PORTABILITY.md`, `STACKS_POLICY.md`, `GL26_SCHEME_DEPENDENCE.md`, `SCHEMES.md`, `REPORT.md`, `INTEGRATION.md` |
| `scripts/build.sh`, `scripts/check_statements.sh` | the offline build; the statement check |

## How the work was produced, and who checked it

Most of the proofs dated after the initial infrastructure were produced by
**Ultramath**: a swarm of identical model instances (`moonshotai/kimi-k3.1-pro`,
maximum reasoning effort) working one hard problem from different registered
directions, in separate directories under `.ultramath/`, sharing findings on a
board and submitting reports.  Members never edit the repository and never commit;
their output is a directory of Lean files plus a report.

**Every submission was checked by the coordinating agent before it entered the
tree**, by the protocol above — exit status, `grep error`, `grep sorryAx`, flattened
axiom lists, the proof read, then the full build.  Rejections and corrections are
recorded in the commit messages and in
[`results/ASSUMPTIONS.md`](results/ASSUMPTIONS.md), including where the agent was
wrong: a module that did not compile was withdrawn after it had been accepted on a
printed audit; a mis-cited Stacks tag (0BFF, a formula for abelian varieties) was
removed; a construction of `iShriek` was downgraded from "proved" to "conditional on
an instance that fails for `A = ℤ`, `f = 2`"; and three times a member's reading of a
paper corrected the briefing it had been given.  Nothing here is claimed on a
member's report alone.

## On provenance

Where a classical input was needed and a Stacks Project tag proves it, the tag is
cited with its number and its statement, and the proof here is written against that
statement rather than against a textbook paraphrase — for example Tag 0AED (compact
iff perfect), Tag 09MB (eventual vanishing), Tag 0BCJ (perfect = locally bounded
finite locally free).  Where the tag is *proved* here instead, the module says so
and the scoreboard records it.  The places where this project's own prose was wrong
and the Lean was right are recorded too: see `results/AFFINE.md` on the orientation
of the recollement, and `results/GL26_SCHEME_DEPENDENCE.md` on Lemma 2.25.

## License

Apache License 2.0; see [`LICENSE`](LICENSE).  File headers read
`Copyright (c) 2026 Formalization of Lank--Pauwels` and release under the same
licence.
