# Relative Fourier–Mukai theory in Lean

A Lean 4 formalization of

> **GL26** — Elías Guisado Villalgordo, Pat Lank, *Relative Fourier–Mukai theory
> for algebraic spaces*, arXiv:2609.01298 (2026),

together with the gluing theorem it rests on,

> **LP** — Pat Lank, Bregje Pauwels, *Gluing weak approximability along
> recollements* (2026),

and, where they are needed and not yet available in Mathlib, the classical inputs
those rest on: perfect complexes, quasicoherent cohomology, K-projective
resolutions, and the exceptional-functor package of the affine recollement.

**Scope: the affine base case.**  Everything here is aimed at `S = Spec A` with
`A` Noetherian, on Mathlib alone.  The separated-base case and then algebraic
spaces are future targets.

## The headline

The affine case of GL26 Theorem 1.1, with **Neeman's theorem as the only published
input**:

```lean
-- SmallAffineAssembly.lean
theorem affine_theorem_1_1_small_standard_neeman_only
    (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hgen : standardT.le 0 = Coprod (shiftTail (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) 0))
    (I : SmallNeemanCompactToPerfectInput A H) :
    SatisfiesWA (SmallAffineD A H) ↔ EventuallyHomZero S.G' S.G'
```

No Stacks 09SR, no coproduct package, no eventual-vanishing hypothesis.  The single
external input `I` is Neeman's `compact ⇒ perfect`; the vanishing is proved inside
the model.  The variant `affine_theorem_1_1_small_neeman_only` keeps a separate
standard-`t` hypothesis instead of the compact-generation field;
`replaceMiddleTStructure` (in the same module) rebuilds `SetupMainMinimal` with the
standard middle `t`-structure, which is what makes that hypothesis definitionally
free in the `_standard_` form.

**What "only Neeman" means precisely.**  Every other input that earlier versions of
this project cited — Stacks 01LA, 01IE, 01HV, 066S, 066T, 07LT, 09M1, 09M8, 09MB,
09SR, 0AED, 0BCJ, and the Bondal–Van den Bergh articles — is now either **proved
here** or **derived** from Neeman.  See [`results/ASSUMPTIONS.md`](results/ASSUMPTIONS.md)
for the inventory, which distinguishes what is proved, what is derived, and what is
genuinely open.

## What is proved

### Categorical layer — `WeakApprox/`

LP §2–§4 and **LP Theorem 1.1**, scheme-agnostic and `sorry`-free:

| result | module |
|---|---|
| `⟨H⟩^[a,b]` and its closure properties (Lemma 3.1), the aisle lemma (3.3), iterated approximation (3.4), the vanishing criterion (3.5) | `Basic`, `Closure`, `Shift`, `Functoriality`, `HomVanishing`, `Aisle`, `Lemma34`, `Lemma35`, `Octahedron` |
| the `Recollement` structure, the glued aisle (Lemma 4.2), Lemma 4.3, `P`-lifts, Lemma 4.6, Proposition 4.8 | `Recollement`, `Lemma42`, `Lemma43`, `Lemma4323`, `Lemma433TStructure`, `PLift`, `Lemma46`, `Proposition48` |
| **Theorem 1.1**, both directions, from the reduced Setup 4.4 | `Main`, `MainMinimal`, `EventualVanishing`, `CompactVanishing`, `NineSR` |
| compactness over `AddCommGrpCat` (the paper's notion), closed under biproducts | `CompactAb` |
| compact objects are closed under thick envelopes, by triangle two-out-of-three — no AB4 | `CompactThick` |
| coproducts localized to a fixed aisle, so the LP proof needs no ambient coproducts | `Scheme/AisleCoproducts` |

### Affine layer — `FourierMukai/Scheme/`

| result | module |
|---|---|
| `D(A-Mod) ≌ D(QCoh(Spec A))` | `AffineDictionary` |
| the two models of `D_qc(Spec A)`, constructed from `tilde ⊣ RΓ` | `AffineQCoh` |
| `Perf A`: thick envelope, closure properties, `⊆ D^b`, `⊆ D^b_coh`; `Perf k = D^b_coh k` over a field | `PerfectRing`, `PerfectField` |
| bounded finite-projective models are perfect, for every commutative ring (066T) | `PerfectModel` |
| `Perf ≤ model ↔ model` retract-closed, with the model class triangulated | `PerfectModelConverse` |
| **Le–Chen 2.3**: two-out-of-three for split idempotents in a triangle | `LeChen` |
| **066S derived from Neeman**, hence `BoundedProjectiveModelConverseInput`, `Stacks07LTCompactModelInput`, `CompactPerfectInput` | `Affine066S` |
| 07LT's finite-free induction, and `compact ⇒ Perf` from its two residue fields | `CompactToPerfect` |
| perfect ⇒ compact up to compactness of the regular module (the thick half of 09M8) | `PerfectCompactThick` |
| **Spaltenstein's Theorem C**: `TheoremCInput` for arbitrary abelian `C`, and `AffineSpaltensteinInput A` for every commutative ring | `KProjectiveResolution`, `AffineBoundedAboveCoproducts`, `SpecialDirectLimits`, `Spaltenstein*`, `AffineSpaltenstein` |
| the Hovey model-structure route to the same replacement data | `ProjectiveModel`, `SmallObjectPresentable`, `GeneratingCofibrations` |
| **01LA(6) / 01IE** extension closure, proved without cohomology | `QCohSerre`, `QCohSerreExtension`, `QCohSerreExtension01IE` |
| coproducts on `D(A-Mod)`: the universe decision, with `AffineD A ≌ SmallAffineD A H` | `AffineUniverse` |
| the affine recollement `D(A[1/f]) → D(A) → D_Z(A)` in the GL26/LP orientation, **all fields but one** | `AffineRecollement`, `AffineLocalCohomology`, `AffineLocalCohomologySupport`, `AffineGluing`, `AffineSupportedAssembly`, `AffineMixedZero`, `AffineIShriek`, `AffineSecondGluing`, `AffineRecollementAssembly` |
| **GL26 Lemma 2.25** for affine schemes: `Φ_{RΔ_*O} ≅ 𝟭` | `AffineDiagonal` |
| **GL26 Lemma 5.4** in abstract six-functor form: the external tensor of compact generators generates the fibre product | `Lemma54` |
| the ten GL26 targets over Noetherian schemes as `Prop`-valued statements | `Statements` |

Everything above is `sorry`-free and depends only on `propext`, `Classical.choice`
and `Quot.sound`; the audits are printed at the end of the modules that state the
results.

## What is assumed

**Neeman**, *Bounded `t`-structures on the category of perfect complexes*,
Acta Math. 233 (2024), Theorem 3.2 — specifically the direction *compact implies
perfect*, packaged as `SmallNeemanCompactToPerfectInput`.  Nothing else external is
assumed on the affine path.

Hypotheses that remain in the endpoint are hypotheses of LP Theorem 1.1 by design,
not gaps: the `SetupMainMinimal` data (the recollement, weak approximation on both
ends, the glued generator and its normalization, the aisle identities) and one
compact-generation identity.  Constructing that data from ring data is the work in
progress described below.

Two caveats worth stating plainly:

* **`FourierMukai/Paper/Statements.lean` still contains `sorry`s** — ten of them.
  They are the paper's targets stated over the superseded abstract `FMContext`
  interface, they are not used by anything on the affine path, and
  `FourierMukai/Audit.lean` prints them deliberately.  They are specifications,
  not gaps in proved theorems.
* **The GL26 statements in `FourierMukai/Scheme/Statements.lean` are statements,
  not proofs.**  Only Theorem 1.1 (affine case) and Lemmas 2.25 and 5.4 are
  proved.

## What is open

1. **The affine recollement's last adjunction.**  Every field of
   `AffineRecollementInput` is now constructed except `jUpper` together with
   `jStar ⊣ jUpper`.  The residue is one tensor–Hom adjunction on `RΓ_Z(A)`:
   `C ⊗^L (-) ⊣ RHom(C, -)` with `C = RΓ_Z(A)` (Stacks 0A6R), which
   `AffineJUpperTensorHom` reduces `jStarAdj` to.  For the record,
   `AffineJUpperCandidateRefuted` proves that the obvious guess `jUpper = Rj_* Lj^*`
   is *zero* and therefore wrong.
2. **The `SetupMainMinimal` data from ring data.**  After the recollement,
   `AffineSetupInventory.lean` packages what is left.  Note the caveat it raises:
   Neeman's preferred-`t`-structure equivalence and the normalized weak
   approximation data do not automatically give the *literal* aisle equalities the
   Setup 4.4 fields ask for, so those are to be checked rather than assumed to
   follow.
3. **066S unconditionally.**  It is derived from Neeman, which suffices for the
   endpoint, but not proved from scratch: the truncation induction fails because
   brutal truncation is not homotopy-functorial at the boundary.
4. Beyond the affine case: separated Noetherian bases, then algebraic spaces, which
   need the Stacks library (porting it to this toolchain is a person-months
   programme — see [`results/STACKS_PORTABILITY.md`](results/STACKS_PORTABILITY.md)),
   and the remaining GL26 targets 1.2, 1.3, 1.6, 1.7, 12.3, 2.26, 12.2, 6.18.

## Building

`/opt/mathlib` is a prebuilt read-only Mathlib on `LEAN_PATH`, and there is no Lake
build in this environment, so the reproduced build is a script:

```bash
./scripts/build.sh          # ~3 minutes, 100 modules, dependency order
```

or one module at a time:

```bash
LEAN_PATH="$LEAN_PATH:." lean -o FourierMukai/Scheme/AffineMain.olean \
  FourierMukai/Scheme/AffineMain.lean
```

Allow at least 300 s per module: the first `import Mathlib` in a process reads about
6 GB of oleans.  `lean-toolchain` pins `leanprover/lean4:v4.33.1` and `lakefile.toml`
pins Mathlib at `v4.33.1`; both are kept for users with a writable setup but are not
exercised here.

**Verification note.**  `#print axioms` prints even when a file has errors, so an
audit line is not evidence that anything compiled.  Check the exit status and grep
for `error` before believing a compile; the build script does both.

## Layout

| path | contents |
|---|---|
| `WeakApprox/` | the LP preprint: §2–§4 and Theorem 1.1, scheme-agnostic |
| `FourierMukai/Scheme/` | the scheme and affine layer: `D(X)`, `D_qc`, `Perf`, perfect complexes, quasicoherent cohomology, K-projective replacements, the affine recollement, and the affine theorems (59 modules) |
| `FourierMukai/Prelim/` | triangulated-category and 2-categorical foundations |
| `FourierMukai/Paper/` | the superseded algebraic-space interface, its targets, and the interface audit |
| `FourierMukai/Examples/` | a non-vacuous instantiation on Mathlib's derived category |
| `results/` | `AFFINE.md` (the 21-row verification chain), `ASSUMPTIONS.md` (what is assumed and what would discharge it), `WEAK_APPROX.md`, `MATHLIB_INVENTORY.md`, `STACKS_PORTABILITY.md`, `GL26_SCHEME_DEPENDENCE.md`, `SCHEMES.md`, `REPORT.md` |
| `scripts/build.sh` | the offline build |

## On provenance

Where a classical input was needed and a Stacks Project tag proves it, the tag is
cited with its number and its statement, and the proof here is written against that
statement rather than against a textbook paraphrase — for example Tag 0AED (compact
iff perfect), Tag 09MB (eventual vanishing), Tag 0BCJ (perfect = locally bounded
finite locally free).  Where the tag is *proved* here instead, the module says so
and the scoreboard records it.  The one place where this project's own earlier
prose was wrong and the Lean was right is recorded too, since it is the more
instructive case: see `results/AFFINE.md` on the orientation of the recollement.

## License

Apache 2.0; see `LICENSE`.
