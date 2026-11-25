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
SmallAffineAssembly.affine_theorem_1_1_small_standard_neeman_only
    (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hgen : standardT.le 0 = Coprod (shiftTail (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) 0))
    (I : SmallNeemanCompactToPerfectInput A H) :
    SatisfiesWA (SmallAffineD A H) ↔ EventuallyHomZero S.G' S.G'
```

where `H : AffineSpaltensteinInput A` is **no longer an assumption** in the sense
of an unproved input: `AffineSpaltenstein.affineSpaltensteinInput A` inhabits it
for every commutative ring (see item (2) below).

## 0. The endpoint now exists

`Scheme/SmallAffineAssembly.lean` proves, in the universe-correct small-Hom model,

```
affine_theorem_1_1_small_neeman_only
    (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hT : S.tD = standard t-structure)
    (I : SmallNeemanCompactToPerfectInput A H) :
    SatisfiesWA (SmallAffineD A H) ↔ EventuallyHomZero S.G' S.G'
```

with **no Stacks 09SR, no coproduct package and no vanishing hypothesis**: the
external input `I` is exactly Neeman's `compact ⇒ perfect`, and the vanishing is
proved inside the small model (`smallPerf_eventuallyHomZero`).  The variant
`affine_theorem_1_1_small_standard_neeman_only` removes `hT` altogether by
rebuilding `SetupMainMinimal` with the standard middle `t`-structure
(`replaceMiddleTStructure`, which reproves only the compact-generation field, so
`hT` becomes `rfl`) and displays that single field as its remaining hypothesis.

What `S` still carries is what LP Theorem 1.1 takes as data by design: the
recollement, the weak approximation data on the two ends, the glued generator and
its normalization, and the aisle identities.  What remains open below is therefore
about *constructing* `S` from ring data, not about the theorem.

## 1. The three open items

**(1) Stacks 066S — no longer needed as an independent assumption.**
`Scheme/Affine066S.lean` derives it from Neeman alone: `NeemanAffineCompactModelInput`
instantiates Neeman 3.2(i) at the *literal* bounded finite-projective model
property, and then Y ∈ model ⇒ Y compact ⇒ X compact for a retract X of Y ⇒ X ∈
model, so the model class is retract-closed and `Perf A ≤ model` follows.  From
that: `Perf A ↔ model`, `BoundedProjectiveModelConverseInput`,
`BoundedProjectiveModelInput`, `Stacks07LTCompactModelInput`, and both
`CompactPerfectInput` and `CompactToPerfectInput`.  The tree therefore needs no
separate 066S hypothesis, only Neeman.

What is *not* done, and should not be claimed: 066S is not proved unconditionally.
The truncation induction that would do it fails, and the reason is now recorded
rather than guessed — brutal truncation is not homotopy-functorial at the boundary,
so the idempotent cannot simply be restricted to a subcomplex.  A genuine proof
needs the homotopy-idempotent lifting that `LeChen` does not supply.

Supporting infrastructure, all proved: `Scheme/LeChen.lean` (Le–Chen 2.3 for split
idempotents in a triangle), `Scheme/PerfectModelConverse.lean`
(`Perf ≤ model ↔ model retract-closed`, with the model class triangulated), and
`Scheme/CompactToPerfect.lean` (07LT's finite-free induction).

**(2) Spaltenstein's Theorem C — PROVED.**  `Scheme/SpaltensteinTheoremC.lean`
gives `theoremCInput : TheoremCInput C` for an arbitrary abelian category, all
three fields supplied: the canonical-truncation successor maps
(`SpaltensteinCanonicalTruncation.lean`), exact sequential colimits preserving
quasi-isomorphisms (`SpaltensteinSequentialComparisons.lean`), and the
filtration-colimit-to-`A` comparison, which is degreewise an isomorphism because
each evaluation diagram is eventually constant and therefore needs no exactness.
With `Scheme/AffineSpaltenstein.lean`, `affineSpaltensteinInput A` gives
`AffineSpaltensteinInput A` — unbounded K-projective replacement data — for
**every commutative ring**, using Mathlib's `AB5OfSize_of_univLE` for the AB5
instance.  Supporting work, all proved: the bounded-above case
(`KProjectiveResolution.lean`, `AffineBoundedAboveCoproducts.lean`), ℕ-indexed
split-mono colimits (`SpecialDirectLimits.lean`, no `lim¹` hypothesis), the cone
stage and countable induction (`SpaltensteinStage/Iteration/Colimit.lean`), and
the alternative Hovey route (`ProjectiveModel.lean`, `SmallObjectPresentable.lean`,
`GeneratingCofibrations.lean`).

**What this changes.**  Spaltenstein is no longer an assumption anywhere: the
small-Hom model `SmallAffineD A H` now exists unconditionally, since
`AffineSpaltensteinInput A` is inhabited for every commutative ring.  So the
endpoint's remaining hypotheses are the `SetupMainMinimal` data, the standard-`t`
identity (or the one compact-generation field), and Neeman's `compact ⇒ Perf` —
nothing else.

**(2b) The aisle equalities.**  `SetupMainMinimal` asks for three equalities of the
form `t.le 0 = Coprod (shiftTail G 0)`.  The ring form is **proved** for every
commutative ring: `Scheme/AisleGenRingGeneration.lean`,
`AisleGeneration.Ring.standard_le_zero_eq_coprod`,

```
(AffineD.standardTStructure A).le 0 = Coprod (shiftTail (ringObject A) 0)
```

The easy inclusion is aisle closure; the hard one replaces `X` by a complex strictly
bounded above in degree 0 and generates it by brutal truncation, free resolutions in
a single degree, bounded-above projective resolutions and a degreewise-split
telescope (nine modules, `Scheme/AisleGen*.lean`).  The supported case is analysed in
`Scheme/AffineSupportedAisle.lean` and `AffineSupportedCoprodLift.lean`, which reduce
it to one generation statement, and `Scheme/AffineKoszulGenerator.lean` supplies a
*perfect* supported generator (the cone of `f`).  Still open: the equalities for the
*specific* generators `G'⟦m⟧ ⊞ jShriek GU` and `iStar` of it.

**(3) The affine recollement.**  `Scheme/AffineRecollement.lean`,
`AffineRecollementInput`.  Substantial progress, all from ring data and without
injectives:

* `Scheme/AffineLocalCohomology.lean` builds `RΓ_Z` as the degreewise cone of the
  localization unit shifted by `-1`, proves it preserves quasi-isomorphisms,
  descends it to `D(A)`, and proves `Rj_* RΓ_Z ≅ 0`, `Lj^* RΓ_Z ≅ 0` and
  `RΓ_Z X ≅ 0 ↔ X ∈ essIm Rj_*`;
* `Scheme/AffineLocalCohomologySupport.lean` proves `RΓ_Z` lands in the supported
  subcategory (`derivedFunctor_isSupported`: every cohomology module is
  power-torsion, via `exists_pow_smul_of_one_tmul_eq_zero`), so `jStar` is an
  honest functor `AffineD A ⥤ AffineDZ A f`, with `jStarFactors` and, from the
  supported adjunction plus Mathlib's right-adjoint shift and triangulated
  theorems, `jStar_commShift`, `jStar_exact`, and via the comparison
  `derivedFunctor_commShift`, `derivedFunctor_exact`;
* `Scheme/AffineGluing.lean` constructs the mapping-cocone counit and connecting
  transformations and proves the associated triangle distinguished on every
  object;
* `Scheme/AffineSupportedAssembly.lean` supplies the four input fields
  `jShriekAdj`, `kernel`, `firstConnecting`, `first_distinguished` by concrete
  constructions, obtaining the supported adjunction from a Hom-bijection with
  orthogonality on the rotated triangle.  No Brown representability and no
  right-adjoint existence is assumed.

`Scheme/AffineMixedZero.lean` supplies `iShriek_jUpper` (`jUpper ⋙ iShriek ≅ 0`)
from the two adjunctions alone, via the general fact that if `F ⊣ G`, `F' ⊣ G'`
and `F ⋙ F' = 0` then `G' ⋙ G = 0` — so that field needs no explicit formulas.

`Scheme/AffineSecondGluing.lean` and `AffineSecondGluingAssembly.lean` construct the
second connecting morphism and prove the second triangle distinguished, purely
categorically: complete the counit, identify its cone with the open-image object by
right orthogonality and the kernel vanishing, and get naturality from injectivity on
precomposition together with uniqueness of maps out of an orthogonal triangle.
`AdjointInput.toAffineRecollementInput` then needs only `iShriek`, `iLowerAdj`,
`jUpper`, `jStarAdj` — everything else in `AffineRecollementInput` is constructed
from those four.

So the entire residue of the recollement is: **`jUpper` with `jStar ⊣ jUpper`, and
`iShriek` with `iLowerAdj`** — and, as the correction below explains, both are
instances of one closed structure rather than of two independent theorems.

**`iShriek` is NOT built — correction.**  `Scheme/AffineIShriek.lean` constructs
the right adjoint of derived restriction of scalars as *coextension* and proves the
adjunction, but only under the instance
`PreservesFiniteColimits (coextendScalars (A → A[1/f]))`, as its own docstring says
("a conditional special case, not a construction for an arbitrary localization").
That instance asks `Hom_A(A[1/f], -)` to be right exact, i.e. `A[1/f]` to be a
projective `A`-module; for `A = ℤ`, `f = 2` this fails, since `ℤ[1/2]` is
torsion-free of rank 1 and not free, hence not projective over the PID `ℤ` (the
last step is prose, not Lean).  So the coextension route does not give `iShriek`, and
an earlier version of this file wrongly said it did.

What `iShriek` actually is: `RHom_A(A[1/f], -)`, the total right derived functor of
coextension, which is the same derived-Hom machinery the `jUpper` adjunction needs.
So the recollement's residue is not two independent adjunctions but **one closed
structure**, consumed twice.

**Assembly and the exact residue.** `Scheme/AffineRecollementAssembly.lean` reduces
`AffineRecollementInput` to a structure with exactly seven fields — `iShriek`,
`iLowerAdj`, `jUpper`, `jStarAdj`, the iso-counit condition, `secondConnecting`,
`second_distinguished` — and fills the rest (local cohomology, the first triangle,
the mixed zero composite, and the four right-adjoint shift/exactness fields) from
what is landed, returning `AffineRecollement`.  `Scheme/AffineSupportedTStructure.lean`
constructs the standard `t`-structure on the supported category directly, via
induced `t`-structures and truncation/homology, so `tU` is no longer a Neeman
input.  `Scheme/AffineSetupInventory.lean` packages the post-recollement
`SetupMainMinimal` residue with standard `tD` and `tZ`.

**One caveat the inventory raises, which matters for the endpoint.**  Neeman's
preferred-`t`-structure equivalence and the normalized weak approximation data do
*not* automatically yield the literal aisle *equalities* that the
`SetupMainMinimal` fields ask for (`tD.le 0 = Coprod (...)` with a specific
generator).  So even with the recollement complete, those three aisle fields
remain to be checked rather than assumed to follow.

**`C = RΓ_Z(A)` is computed explicitly.**  `Scheme/AffineLocalCohomologyRingObject.lean`
identifies the ring object: `RΓ_Z(A[0]) ≅ Q(cone(A[0] → A_f[0])[-1])`, whose terms
vanish outside degrees 0 and 1, with the 0→1 differential equal to the negative
localization unit; it proves the distinguished triangle
`C → A[0] → Rj_*(A_f[0]) → C[1]`, that the derived cohomology is concentrated in
degrees 0 and 1, and the universal properties `H⁰ = ker(A → A_f)`,
`H¹ = coker`.  So `C` is a two-term complex, and `C ⊗^L X` is the localization
fibre once the exact derived tensor and its flat-extension comparison are available.

**`jUpper`: reduced to one tensor–Hom adjunction.**  `Scheme/AffineJUpperAdjoint.lean`
proves, given `jUpper` and `jStarAdj`, the adjoint triple, `IsIso jStarAdj.counit`
(from Mathlib's triple lemma and full faithfulness of the supported inclusion, not
assumed), `jUpper`'s full faithfulness, its `CommShift`, the adjunction's
`CommShift` and `IsTriangulated`.  It also rules out `jUpper = affineDZι`: that
would force every map from the open essential image into a supported object to
vanish.  `Scheme/AffineJUpperTensorHom.lean` gives the general reduction — if `E`
is fully faithful, `J ⊣` something with `J ⋙ E ≅ T` and `T ⊣ H`, then
`J ⊣ E ⋙ H` — so `jStarAdj` follows from a tensor–Hom adjunction with
`T = C ⊗^L (-)`, `H = RHom(C, -)` and `C = RΓ_Z(A)`, the comparison being Stacks
**0A6R**.  That single adjunction is what remains of `jUpper`.

**Dead end, recorded so it is not retried.** The natural guess `jUpper = Rj_* Lj^*`
on the supported category is *zero* for every `A`, `f`
(`Scheme/AffineJUpperCandidateRefuted.lean`, `tensorLocalizationCandidateIsoZero`),
so it cannot be `jUpper`: the counit would have to be an isomorphism and `jUpper`
fully faithful, which a zero functor into a nontrivial category cannot be —
witnessed by `ZMod 2` in degree 0 over `A = ℤ`, `f = 2`.  The RHom/coextend
formula (`Hom_A(A[1/f], -)` or `coextendScalars`) is still untested.  So `AffineRecollementInput` is
not yet inhabited, but eight of its fields are now theorems.

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

With Neeman 3.2 allowed, what the affine endpoint still needs is:

1. **One tensor–Hom adjunction.**  `C ⊗^L (-) ⊣ RHom(C, -)` for `C = RΓ_Z(A)`.
   `C` itself is computed (`Scheme/AffineLocalCohomologyRingObject.lean`: a two-term
   complex, degrees 0 and 1, differential the negative localization unit, with
   `H⁰ = ker` and `H¹ = coker`), and `Scheme/AffineJUpperTensorHom.lean` reduces
   `jStarAdj` to this adjunction given Stacks 0A6R.  Everything else in
   `AffineRecollementInput` is constructed.
2. **The two remaining aisle equalities**, i.e. the `tD`- and `tZ`-equalities for the
   *specific* generators `G'⟦m⟧ ⊞ jShriek GU` and `iStar` applied to it.  The ring
   form `t.le 0 = Coprod (shiftTail (ringObject A) 0)` is **proved**
   (`Scheme/AisleGenRingGeneration.lean`), and the supported case is reduced to one
   generation statement (`Scheme/AffineSupportedCoprodLift.lean`), with a perfect
   supported generator supplied by `Scheme/AffineKoszulGenerator.lean`.
3. **The `SetupMainMinimal` remainder** — weak approximation data on both ends, the
   glued generator and its normalization — which after (1) and (2) is Neeman input
   plus assembly, not open mathematics.

Two things that used to be on this list and are no longer: 066S (derived from
Neeman, `Scheme/Affine066S.lean`) and Spaltenstein's Theorem C (proved,
`Scheme/SpaltensteinTheoremC.lean`, `Scheme/AffineSpaltenstein.lean`).
