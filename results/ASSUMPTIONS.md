# What is still assumed, and what would discharge it

**Goal of this file.** The campaign target is: the affine case of GL26 Theorem 1.1
with **Neeman, Acta Math. 233 (2024), Theorem 3.2 as the only published input**.
This is the inventory of everything else that is currently assumed anywhere in the
tree, where it is assumed, and what would discharge it.  It supersedes the
"open" entries of [`AFFINE.md`](AFFINE.md) as the planning document.

The current endpoint is

```
PerfectRingStacks.StacksGluing.affine_theorem_1_1_stacks07LT
    (S : SetupMainMinimal DZ (AffineD A) DU)
    (C : AffineDerivedCoproducts A DZ DU)
    (I : Stacks07LTCompactModelInput A) :
    SatisfiesWA (AffineD A) ↔ AffineEventualSelfVanishing S.G'
```

so its assumptions are exactly `S`, `C`, `I`.  Everything else in the tree is
either proved or belongs to the general-scheme layer that the affine endpoint
does not touch.

## A. On the affine endpoint's path

| # | assumption | Lean name, file | what it says | discharge |
|---|---|---|---|---|
| A1 | Stacks **07LT**, hard direction | `Stacks07LTCompactModelInput.model_of_compact`, `Scheme/PerfectRingStacks.lean` | a compact object of `D(R)` has a bounded complex of finitely generated projective modules as a model | 07LT's own proof: truncate to `D^-(R)`, factor the identity through a bounded complex of frees, make the terms finite by induction, finish with **066S** (retract closure). `Scheme/PerfectModelConverse.lean` proves every step *after* 066S: `Perf A ≤ model ↔ model.IsStableUnderRetracts`. **Residue: 066S alone.** |
| A1' | 07LT's induction | `FourierMukai/Scheme/CompactToPerfect.lean` | the finite-free induction, the `DFinsupp` support extraction, the 07LR lifting step and the truncation-coproduct datum are now **proved**; `CompactToPerfectInput` (compact ⇒ `Perf`) follows from `FilteredFreeModelInput` together with `FiniteFreeImprovementInput` | construct those two inputs for a ring. The first is a free complex model with exhaustive bounded truncations having jointly surjective derived Hom maps, i.e. the same Spaltenstein-shaped dependency as A3; 066S is *not* needed for compact ⇒ `Perf` (only for the model form), since `Perf` is the thick envelope. Residue unchanged in status, but its induction is done. |
| A2 | Stacks **066S** | not assumed as a Lean hypothesis; it is the residue of A1 | a direct summand in `D(R)` of a strictly perfect complex is strictly perfect | reduced to one classical lemma: Le–Chen, *Karoubianness of a triangulated category*, J. Algebra 310 (2007), Proposition 2.3, in the form "in a triangle whose three components are idempotent, splitting of the two end components gives splitting of the middle". **Le–Chen 2.3 is now proved** (`Scheme/LeChen.lean`, `LeChen.splitsWithin_third`): for a triangulated object property `T` and a morphism of distinguished triangles whose three components are idempotents, splitting of the first two within `T` implies splitting of the third. The file also has `SplitsWithin`, strong splittings as biproduct decompositions, the biproduct-of-triangles construction (`biproductTriangle_distinguished`), `exists_biprod_map_of_comm` and `comp_eq_zero_of_distTriang`. `T`-images are constrained, which is the form 066S needs. No octahedral axiom is used — the source's Remark 2.4 and the proof agree on that.
The residue of 066S is now the **truncation induction**: split the idempotent on a bounded finite-projective complex by induction on its length, using that idempotents split in `R`-Mod at the bottom degree and `splitsWithin_third` to pass across the triangle `σ_{≥a+1}P → P → P^a`. Two earlier attempts produced nothing usable: `PerfectModelRetract.lean` (base cases only, never compiled) and a run that died on a type-coercion artifact in the assembly. |
| A3' | Spaltenstein, bounded above | `Scheme/KProjectiveResolution.lean`, `Scheme/AffineBoundedAboveCoproducts.lean` | a `KProjectiveResolution` for a complex strictly bounded above in degree `d`, for any abelian category with enough projectives, feeding `Scheme/DerivedCoproducts.lean`; coproducts of bounded-above families in `D(C)` follow | the unbounded case of Spaltenstein's Theorem C, which is the genuinely hard one (filtration plus Mittag-Leffler) |
| A3'' | the universe decision | `Scheme/AffineUniverse.lean` | **decided, and proved**: instead of `HasCoproducts.{u+1}` on a category of `u`-small modules (impossible), use the *small-Hom* derived category `SmallAffineD A H = DerivedCategory` at `HasDerivedCategory.{u}`, where the category is `Category.{u}` and `HasCoproducts.{u}` follows from K-projective replacement data plus coproducts in `ModuleCat`. Also `HasCoproducts.{w} (ModuleCat.{u} A)` for every `w` with `UnivLE.{w,u}`, `AffineD A ≌ SmallAffineD A H`, and `affine_theorem_1_1_small` proving LP Theorem 1.1 with the **unchanged** `SetupMainMinimal.theorem_1_1` and `v = u`, so `Coprod`, `IsCompactAb` and `WeakApproximationData` need no re-indexing | remaining: `AffineSpaltensteinInput` (A3), and packaging the transport of the existing affine inputs across `AffineD ≌ SmallAffineD` with shift compatibility |
| A3''' | Spaltenstein via a model structure | `Scheme/ProjectiveModel.lean`, `Scheme/SmallObjectPresentable.lean`, `Scheme/GeneratingCofibrations.lean` | K-projective replacement data is **derived** from cofibrant lifting, or from the RLP identity plus Mathlib's small-object argument; the ordinal preservation condition is discharged from cardinal presentability; Hovey's generating cofibrations are encoded with their smallness proved; and `hasCoproductsDerivedOfGeneratingCofibrations` feeds the existing `DerivedCoproducts` theorem | two named inputs, neither claimed: Hovey, *Model Categories*, Prop. 2.3.5 (`I.rlp = degreewiseEpiQuasiIso`) and presentability of the sphere objects (Hovey 2.3.2 for modules). Each is a statement about a *set* of morphisms, not about an arbitrary complex, so it is the most tractable form the obstruction has taken |
| A3 | coproducts on `D(A-Mod)` | `AffineDerivedCoproducts.hasCoproductsA`, `Scheme/Affine.lean` | `HasCoproducts.{u+1} (D(ModuleCat.{u} A))` | two independent obstructions: (i) **Spaltenstein** Theorem C, K-projective replacement for every complex — `Scheme/DerivedCoproducts.lean` already turns replacements into coproducts; (ii) a **universe** obstruction, since the field asks for a `Type (u+1)`-indexed coproduct in a category of `Type u`-small modules (`HasCoproducts.{0}` is synthesizable, `.{1}` is not). Needs either a Spaltenstein construction or a decision to index the categorical layer in the smaller universe. |
| A4' | `RΓ_Z` cone model | `Scheme/AffineLocalCohomology.lean` | the degreewise cone of the localization unit, shifted by `-1`, is proved to preserve quasi-isomorphisms and descends to `derivedFunctor : AffineD A ⥤ AffineD A`; three `AffineRecollementInput` fields are proved for it — `Rj_* RΓ_Z ≅ 0`, `Lj^* RΓ_Z ≅ 0`, and `RΓ_Z X ≅ 0 ↔ X ∈ essIm Rj_*` | no injectives, no Noetherian hypothesis. Still missing: `RΓ_Z` landing in `AffineDZ` (power-torsion support), its shift/triangulated structure, the adjunction to the inclusion, `iShriek`, `jUpper`, and the two gluing triangles |
| A4 | affine recollement | `AffineRecollementInput`, `Scheme/AffineRecollement.lean` | `j^×`, `RΓ_Z`, `i^*`, their exactness and adjunctions, the kernel characterization, the two mixed zero composites and both gluing triangles | the open/closed recollement for `Z = V(f)` is explicit, so no injective resolutions are needed: `RΓ_Z(K)` is the cone of `K → K ⊗_A A[1/f]` (degreewise, since `A[1/f]` is flat), `j^×` and `i^*` are the corresponding cone/adjunction functors. Currently being attempted. |
| A5 | `SetupMainMinimal`'s data | `WeakApprox/MainMinimal.lean`, 20 fields | recollement, three `t`-structures, `WeakApproximationData` on both ends, the glued generator `G'`, its compactness and generation, the normalization `m`, the three aisle identities | after A4, the fields are exactly Neeman 3.2(i)–(iv) applied to `Spec A` and to `Z = V(f)`: compacts are perfect (i), a compact generator exists (ii), the preferred `t`-structure and the aisle identities (iii), weak approximability of `D_qc,Z` (iv) — plus A1 for the compactness of the chosen generator. **This is assembly work, not new mathematics**, but it needs A3 to be stateable. |

## B. Reduced or proved, but still listed as inputs for compatibility

| item | Lean name | now |
|---|---|---|
| extension closure of quasicoherent sheaves (Stacks **01LA(6)**, **01IE**) | `QuasicoherentExtensionInput`, `Scheme/QCohSerre.lean` | **discharged**: `Scheme/QCohSerreExtension01IE.lean` proves 01IE (`AffineExtension.surjective_appTop`) and hence extension closure on every scheme and triangulated `D_qc`. 01LA(3) coproducts, biproducts and split extensions were already unconditional. |
| compact ⇒ perfect (Stacks **09M1**, **0AED**) | `CompactPerfectInput`, `Scheme/PerfectRing.lean` | split into `CompactToPerfectInput` (used) and `PerfectToCompactInput` (never used); the used half follows from 07LT's hard direction plus the proved filtration. |
| perfect ⇒ bounded model | `BoundedProjectiveModelConverseInput`, `Scheme/PerfectModel.lean` | equivalent to 066S by `Scheme/PerfectModelConverse.lean`. |
| eventual Hom vanishing (Stacks **09MB**) | `CompactHomZeroAtTop`, `Scheme/Inputs.lean` | **proved** for rings (`perf_eventuallyHomZero`); not on the affine path. |
| perfect ⇒ compact (Stacks **09M8**, the thick-envelope half) | `PerfectToCompactInput`, `Scheme/PerfectRingStacks.lean` | reduced to compactness of the regular module: `Perf A ≤ compactObjectProperty` whenever `IsCompactAb (ringObject A)` (`WeakApprox/CompactThick.lean` proves compact objects are closed under thick envelopes by triangle two-out-of-three, with no AB4; `Scheme/PerfectCompactThick.lean` derives `PerfectToCompactInput`). Not on the affine path. |
| Stacks **09SR** | `AffineStacks09SR`, `Scheme/Affine.lean` | removed from the current endpoint; only the older `affine_theorem_1_1` still carries it. |

## C. Not on the affine endpoint's path

These belong to the general-scheme layer and are not needed for the affine
statement: `AffineDerivedGammaInput` (Stacks 06Z0/079W/08D4/01XB, the two models
of `D_qc`; `Scheme/AffineQCoh.lean`), `AffineAllSheavesBridgeInput`
(`Scheme/PerfectModel.lean`), `DiagonalIdentityData` including 08IN
(`Scheme/AffineDiagonal.lean`), `VectorBundleCalculus` and
`PerfectToDQCohInterface` (08CR/08CS, `Scheme/Perfect.lean`),
`QuasicoherentStrongClosureInput` and `DQCohCoproductInput` (`Scheme/Derived.lean`,
superseded by the extension input), the duality interfaces in
`Scheme/Duality.lean` (`DerivedTensorHomData`, `PerfectDualityData`,
`UpperShriekBaseChangeData`, `BaseChangeCoherenceData`), and
`CoverComparisonInput` / `ProductPerfectCompactInput` for GL26 Lemma 5.4
(`Scheme/Lemma54.lean`).

## D. The short version

With Neeman 3.2 allowed, closing the affine case needs exactly three things:

1. **066S** — the only residue of 07LT (= A1 + A2);
2. the **explicit cone model** of `RΓ_Z`, `j^×`, `i^*` for a principal open, i.e.
   the affine recollement from ring data (= A4);
3. **coproducts on `D(A-Mod)`**, which needs Spaltenstein plus a universe decision
   (= A3).

Then A5 is assembly.  Nothing else in the tree blocks the affine statement.
