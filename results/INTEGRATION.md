# Repository layout and the relation to AxiomMath/Stacks

This repository is laid out like [AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) and
builds on top of it:

| file | origin |
|---|---|
| `lean-toolchain` | copied from AxiomMath/Stacks (`leanprover/lean4:v4.35.0`) |
| `LICENSE` | copied from AxiomMath/Stacks (Apache 2.0) |
| `.gitignore` | adapted from AxiomMath/Stacks (plus the local development directories) |
| `lakefile.toml` | AxiomMath/Stacks' `[leanOptions]` block and Mathlib pin (`v4.35.0`), plus a `Stacks` requirement and the two libraries `FourierMukai`, `WeakApprox` |
| `formalization.yaml` | same schema as AxiomMath/Stacks' `formalization.yaml` |
| `README.md` | the goals of this project |

Official build: `lake exe cache get && lake build` with the pinned toolchain.  The two libraries
are Mathlib-only at the moment, so their build does not require the Stacks modules to be compiled;
the `Stacks` requirement is in place for the porting pass described below.  `scripts/build.sh`
remains the offline development path (it calls the `lean` on `PATH`).

The repository `lankp/Fourier--Mukai-theory` holds this development on the branches `main` and
`formalization` (the default branch is `formalization`).

---

# Grafting this development into `lankp/Fourier--Mukai-theory`

## What that repository is (verified 2026-11-24)

* `lankp/Fourier--Mukai-theory` is a **pure fork** of `AxiomMath/Stacks`: no
  commits beyond upstream, HEAD = `f56a316ddf` ("chore: seal sheafification def,
  and fix warnings (#19)", 2026-11-18), same `pushed_at` as the parent.
* `lean-toolchain`: `leanprover/lean4:v4.35.0`; Mathlib pinned to `v4.35.0`.
* `lakefile.toml` declares three libraries — `StacksCore`, `StacksFrontier`,
  `Stacks` — with these package-wide options:

  ```toml
  [leanOptions]
  pp.unicode.fun = true
  autoImplicit = false
  relaxedAutoImplicit = false
  maxSynthPendingDepth = 3
  weak.linter.flexible = true
  weak.linter.mathlibStandardSet = true
  weak.linter.style.header = false
  weak.linter.overlappingInstances = false
  ```

So the fork is the Stacks library, not a separate Fourier–Mukai project yet; the
intended move is to add this development as a fourth library on top of it.

### What the library already contains (verified by grepping the fork at HEAD)

I cloned the fork with `--depth 1` and searched it.  The geometric layer that
`FourierMukai/Paper/DerivedSetup.lean` only *interfaces* is largely there, under
these names:

| paper's object | declaration in `StacksFrontier` |
|---|---|
| algebraic spaces | `Space.IsAlgebraicSpace B S hS X` (predicate on an fppf presheaf), `Stacks.AlgebraicGeometry.AlgebraicSpaces` (the category), in `AlgebraicGeometry/Spaces/Category.lean` |
| `D_qc(X)` | `Stacks.DerivedQCoh.IsDQCoh` (predicate on `D(𝒪_X)`, `DerivedQCoh/Basic.lean`) |
| coherator `Q` | `Stacks.DerivedQCoh.derivedCoheratorOfScheme`, `derivedCoheratorSmallEtale` |
| perfect complexes | `Stacks.Cohomology.PerfectComplexes.IsPerfect` (`Topology/Sheaves/Cohomology/PerfectComplexes/Defs.lean:82`) |
| `f^!` | `Stacks.Duality.upperShriek`, `upperShriekDualityIso`, `upperShriekProperIso`, `properCompactification` |
| duality for spaces | `AlgebraicGeometry/Spaces/DerivedDuality`, `AlgebraicGeometry/Duality/` (twisted inverse image for closed immersions, blowups, dualising complexes) |

Also present and directly relevant: `DerivedQCoh/DerivedCoherator.lean`,
`DerivedQCoh/DualOfAPerfectComplex.lean`, `DerivedQCoh/RestrictionPerfectSupport.lean`,
`DerivedQCoh/QuasicoherentKFlatModel.lean`, `DerivedQCoh/AnyModel/`,
`DerivedQCoh/NoetherianExtension/`.

Caveat: all of this is in `StacksFrontier`, the tier the README describes as
AI-written and not yet human-reviewed.  Names and statements may move.  Treat the
table above as a map for the porting pass, and re-grep before relying on a name.

## Compatibility already checked

Every module here was recompiled with the fork's options

```bash
lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
     -o /tmp/t.olean <file>.lean
```

and all nine compile (this VM has Lean 4.33.1 / Mathlib 4.33.1, so this checks the
*options*, not the Mathlib version).  The Mathlib API surface used is small and
stable:

* `Mathlib.CategoryTheory.Triangulated.{Subcategory,Functor,Generators}`
* `Mathlib.CategoryTheory.MorphismProperty.Retract`
* `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`
* `Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms`
* `Mathlib.Algebra.Homology.DerivedCategory.Basic` (one example only)
* `Mathlib.CategoryTheory.Monoidal.Category`, `...Functor.FullyFaithful`,
  `...Adjunction.Basic`, `Mathlib.Topology.Basic` (interface file only)

The risk when moving is therefore Mathlib drift 4.33.1 → 4.35.0, not the
Stacks library.  Plan for one pass of `lake build FourierMukai` and small fixes.

## Steps

1. **Copy** `FourierMukai/` and `FourierMukai.lean` into the fork's root
   (next to `StacksCore/`, `StacksFrontier/`, `Stacks.lean`).  Do **not** put them
   inside `StacksCore/` or `StacksFrontier/`: those are separate libraries with
   their own roots and review process, and keeping `FourierMukai` separate makes
   upstream syncs conflict-free.
2. **Register the library** in `lakefile.toml`:

   ```toml
   defaultTargets = ["StacksCore", "StacksFrontier", "Stacks", "FourierMukai"]
   ...
   [[lean_lib]]
   name = "FourierMukai"
   roots = ["FourierMukai"]
   ```
3. **Build**: `lake exe cache get && lake build FourierMukai`.  Nothing in
   `FourierMukai/` imports `Stacks` yet, so this step is independent of the
   Stacks build (apart from Mathlib).
4. **Sync with upstream**: `git remote add upstream
   https://github.com/AxiomMath/Stacks` and rebase `main` on `upstream/main`.
   Because our files live in a new top-level directory and only `lakefile.toml`
   is edited, a rebase should be trivial.
5. **Replace the interface, module by module**, once the build is green.  The
   file `FourierMukai/Paper/DerivedSetup.lean` is a stopgap.  Mapping:

   | interface field | replace by |
   |---|---|
   | `Subcats.DbQc` | `Stacks.DerivedQCoh.IsDQCoh` plus a boundedness predicate (to be built; see `DerivedQCoh/EventualExtVanishing.lean` and `UniformExtVanishingLocallyFree.lean` for the available tools) |
   | `Subcats.Perf` | `Stacks.Cohomology.PerfectComplexes.IsPerfect` |
   | `Subcats.IsPseudocoherent`, `Dcoh` | `IsDQCoh` plus coherent cohomology; `IsPerfect ⟹ IsDQCoh` is `DerivedQCoh/KoszulSummandPerfect.lean` (`isDQCoh_of_isPerfect`) |
   | `MorphismContext.pull`, `.push`, `.adj` | the pullback/pushforward functors on `D(𝒪_X)` already used throughout `DerivedQCoh` (Stacks 07A6); the induced functors on `D_qc` are the `AnyModel` and `Inclusion` files |
   | `MorphismContext.tensorRight` | the monoidal structure on `D(𝒪_X)` from `Spaces/AbelianSheafMonoidal.lean`, `AbelianSheafDerivedTensor.lean` |
   | `MorphismContext.upperCross` | `Stacks.Duality.upperShriek` (with `upperShriekProperIso` giving `f^× = f^!` for proper `f`) |
   | `IsRelativelyPerfect`, `IsQuasiPerfect` | no Stacks tag: Definition 4.1 / 5.1 of the paper.  These become *definitions* on top of the above, not interface fields |
   | `FMSetup.fibreTransform` | still nothing: needs the fibre-product cube of Setup 2.20 over an arbitrary base change `t : T → S`, i.e. the base-change theory of §6 of the paper |

   After each replacement, delete the corresponding `Prop`-valued hypothesis from
   the interface and re-state the affected theorem — the statements in
   `Paper/Statements.lean` are written so that this is a local edit.

6. **Do not** put `sorry` in `StacksCore/`/`StacksFrontier/`.  The statements in
   `FourierMukai/Paper/Statements.lean` are formalization targets and stay
   `sorry`-carrying until proved; keep them in the new library.

## What is still missing from the fork for this paper

The Stacks library formalizes the Stacks Project, and Stacks does **not** contain
the paper's own contributions: relative perfectness (Definitions 4.1, 5.1 and
their theory), the fibre-wise criteria via mates (§7–§10), the openness results
(§12), or elliptic fibrations (§11).  Conversely, the paper uses
Grothendieck duality for algebraic spaces (Neeman's construction), weak
approximability, and Nagata compactification; the first two are not Stacks
chapters and must come from elsewhere.  See `results/REPORT.md` §5 for the full
inventory.
