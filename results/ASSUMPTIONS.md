# What is still assumed, and what would discharge it

**Goal.** The affine case of GL26 Theorem 1.1 with **Neeman, Acta Math. 233
(2024), Theorem 3.2 as the only published input**.  This file is the current
inventory of every other assumption, where it is made, and what would discharge
it.  It replaces the earlier append-only version: the labels below are stable.

The endpoint is

```
PerfectRingStacks.StacksGluing.affine_theorem_1_1_stacks07LT
    (S : SetupMainMinimal DZ (AffineD A) DU) (C : AffineDerivedCoproducts A DZ DU)
    (I : Stacks07LTCompactModelInput A) :
    SatisfiesWA (AffineD A) ↔ AffineEventualSelfVanishing S.G'
```

and, in the universe-correct small-Hom model,

```
AisleCoproducts.affine_theorem_1_1_small_noCoproducts
    (H : AffineSpaltensteinInput A) (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hT : S.tD = standard t-structure) (h09SR : Stacks09SR _) :
    SatisfiesWA (SmallAffineD A H) ↔ eventual self-vanishing of S.G'
```

## 1. The three open items

**(1) Stacks 066S, i.e. the residue of 07LT.**  `Perf A ≤ HasBoundedFiniteProjectiveModel A`.
Reduced twice and now in a good position:

* `Scheme/PerfectModelConverse.lean`: `Perf A ≤ model ↔ model.IsStableUnderRetracts`,
  with the model class proved closed under zero, isomorphisms, shifts, single
  finite-projective complexes and cones (explicit mapping-cone models), so
  triangulated.
* `Scheme/LeChen.lean`: **Le–Chen 2.3 is proved** (`LeChen.splitsWithin_third`):
  for a triangulated object property `T` and a morphism of distinguished triangles
  whose three components are idempotents, splitting of the first two within `T`
  gives splitting of the third.  No octahedral axiom is used.
* `Scheme/CompactToPerfect.lean`: the whole finite-free induction of 07LT, and
  `compact ⇒ Perf` follows from `FilteredFreeModelInput` + `FiniteFreeImprovementInput`.
  066S is **not** needed for that implication (the thick envelope absorbs the
  retract), only for the model form.

Residue: the truncation induction on a bounded finite-projective complex, using
that idempotents split in `R`-Mod at the bottom degree and `splitsWithin_third`
to cross the triangle `σ_{≥a+1}P → P → P^a`.  Concrete, bounded work.

**(2) Spaltenstein's Theorem C.**  `Scheme/SpaltensteinReplacement.lean`,
`TheoremCInput`: the canonical-truncation successor maps, exactness of the
sequential colimit on quasi-isomorphisms, and the filtration-colimit-to-`A`
quasi-isomorphism.  Everything else is proved:

* `Scheme/KProjectiveResolution.lean` + `AffineBoundedAboveCoproducts.lean`: the
  bounded-above case, for any abelian category with enough projectives;
* `Scheme/SpecialDirectLimits.lean`: an `ℕ`-indexed colimit of K-projectives with
  degreewise split monomorphisms is K-projective — no AB4, AB5, Mittag-Leffler
  or `lim¹` hypothesis, because an explicit telescope section kills the
  obstruction in that case;
* `Scheme/SpaltensteinStage.lean`, `SpaltensteinIteration.lean`,
  `SpaltensteinColimit.lean`: the cone stage with its homotopy and five-lemma
  quasi-isomorphism, and the countable induction using only bounded-above
  projective resolutions;
* `Scheme/ProjectiveModel.lean`, `SmallObjectPresentable.lean`,
  `GeneratingCofibrations.lean`: an alternative route, deriving replacement data
  from Hovey's projective model structure down to two inputs (Prop. 2.3.5 and
  sphere presentability), each a statement about a *set* of morphisms.

**Why it is still load-bearing, precisely.**  It is *not* needed for coproducts:
`Scheme/AisleCoproducts.lean` shows the LP proof only ever forms coproducts of
families lying in a fixed aisle, and those come from bounded-above resolutions.
But the universe decision (`Scheme/AffineUniverse.lean`) puts the endpoint in the
**small-Hom** derived category, `HasDerivedCategory.{u}`, whose *existence* is
what the replacement data supplies — `HasDerivedCategory.{u} (ModuleCat.{u} A)`
is not synthesizable on its own (checked directly).  So the dilemma is: large-Hom
model, where `HasAisleCoproducts` would need coproducts indexed by `Type (u+1)` in
a category of `u`-small modules (impossible); or small-Hom model, which exists
only given replacements.  Spaltenstein is therefore still on the critical path,
and `TheoremCInput` is the smallest form it has taken.

**(3) The affine recollement.**  `Scheme/AffineRecollement.lean`,
`AffineRecollementInput`.  `Scheme/AffineLocalCohomology.lean` builds `RΓ_Z` as
the degreewise cone of the localization unit, shifted by `-1`, proves it preserves
quasi-isomorphisms, descends it to `D(A)`, and proves three of the input's fields:
`Rj_* RΓ_Z ≅ 0`, `Lj^* RΓ_Z ≅ 0`, and `RΓ_Z X ≅ 0 ↔ X ∈ essIm Rj_*`.  No
injectives and no Noetherian hypothesis.  Missing: `RΓ_Z` landing in `AffineDZ`
(power-torsion support), its shift and triangulated structure, the adjunction to
the inclusion, `iShriek`, `jUpper`, and the two gluing triangles.

## 2. Assembly items (no open mathematics)

| item | why it is needed | where |
|---|---|---|
| `hT` | the middle `t`-structure of `SetupMainMinimal` must be identified with the standard one before `hasAisleCoproducts_standard` applies | stated as a hypothesis in `affine_theorem_1_1_small_noCoproducts` |
| transfer across `AffineD A ≌ SmallAffineD A H` | the existing affine inputs (recollement, generator data) live on the large-Hom model | `Scheme/AffineUniverse.lean` proves the equivalence; the transport with shift compatibility is not packaged |
| Stacks 09SR in this version | removed in `AffineMain.lean` by `CompactHomZeroAtTop`; not yet combined with the small-Hom endpoint | `Scheme/AffineMain.lean`, `Scheme/PerfectRingStacks.lean` |

## 3. Proved, previously assumed

| was | now |
|---|---|
| Stacks **01LA(6)** extension closure of quasicoherent sheaves, and **01IE** | **proved** (`Scheme/QCohSerreExtension01IE.lean`): the denominator-ideal argument, no cohomology; extension closure on every scheme and triangulated `D_qc` follow. Row 3 of `AFFINE.md` closed |
| Stacks **09MB** eventual Hom vanishing | **proved** for rings (`perf_eventuallyHomZero`), no input |
| Stacks **09M8**, perfect ⇒ compact | thick-envelope half proved (`WeakApprox/CompactThick.lean`, `Scheme/PerfectCompactThick.lean`); whole statement reduced to compactness of the regular module |
| Stacks **066T** (models are perfect) | **proved** for every commutative ring |
| Stacks **09SR** | removed from `affine_theorem_1_1_neeman_only` |
| Bondal–Van den Bergh | replaced by Stacks tags 0AED/09M8/0AEC/09SR/0BCJ/09MB throughout |
| the coproduct field of `AffineDerivedCoproducts` | no longer used by the LP chain: `Scheme/AisleCoproducts.lean` localizes coproducts to fixed aisles, and `theorem_1_1_of_middleAisleCoproducts` needs only those |
| the universe mismatch | **decided**: `HasCoproducts.{w} (ModuleCat.{u} A)` for `w` with `UnivLE.{w,u}`, and the small-Hom model where `HasCoproducts.{u}` of the derived category is expressible (`Scheme/AffineUniverse.lean`) |
| Stacks **01HV** (`tilde` is exact) | **proved**; `affineDerivedGammaInputOfTildeExact` fills the field |

## 4. Not on the affine path

The general-scheme layer: `AffineDerivedGammaInput` (06Z0/079W/08D4/01XB, the two
models of `D_qc`, `Scheme/AffineQCoh.lean`), `AffineAllSheavesBridgeInput`,
`DiagonalIdentityData` including 08IN (`Scheme/AffineDiagonal.lean`),
`VectorBundleCalculus` and `PerfectToDQCohInterface` (08CR/08CS),
`QuasicoherentStrongClosureInput`, `DQCohCoproductInput`, the duality interfaces in
`Scheme/Duality.lean`, and `CoverComparisonInput`/`ProductPerfectCompactInput` for
GL26 Lemma 5.4 (`Scheme/Lemma54.lean`, whose cover argument is proved in abstract
six-functor form).

## 5. The short version

With Neeman 3.2 allowed, the affine endpoint needs:

1. **066S** — a truncation induction on top of the proved Le–Chen 2.3;
2. **`TheoremCInput`** — the three comparisons left of Spaltenstein's Theorem C,
   needed because the endpoint lives in the small-Hom model;
3. **the recollement's remaining fields** — support, shift/triangulated structure,
   adjunction, `i⇕`, `i^*`, gluing triangles, with `RΓ_Z` already constructed.

Then `hT` and the transport across the equivalence are assembly.  Nothing else in
the tree blocks the affine statement.
