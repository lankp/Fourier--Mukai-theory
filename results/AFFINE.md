# Verifying LP Theorem 1.1 for an affine base scheme

**Target.** For `X = Spec A` with `A` Noetherian, `U = Spec A[1/f]` and
`Z = V(f)`, the recollement

  `D(U)  →  D(X)  →  D_Z(X)`

(note the orientation: the open category goes in the `D_Z` slot of the abstract
`Recollement`, the supported category in the `D_U` slot — see
`Scheme/AffineRecollement.lean` for why the reverse labelling is not the same
recollement) satisfies **LP Theorem 1.1** — `D_qc(X)` is weakly approximable if
and only if the chosen compact generator has eventually vanishing positive
self-Homs — with **Neeman's published theorem** (Acta Math. 233 (2024),
Theorem 3.2) as the only external homological input.  The affine dictionary
identifies this with the ring-level picture
`D_Z ⟷ D(A-Mod) ⟷ D(A[1/f]-Mod)`.

## The chain

Each row is one Lean module or one proof obligation.  "proved" means a theorem
with no residue; "proved from X" means no residue beyond the named input;
"cited" means a published theorem stated as a named hypothesis or field;
"open" means work still to be done.

| # | obligation | content | source | Lean | status |
|---|---|---|---|---|---|
| 1 | affine dictionary | `D(A-Mod) ≌ D(QCoh(Spec A))` | — | `Scheme/AffineDictionary.lean` (`affineDerivedEquivalence`) | proved |
| 2 | two models of `D_qc` | `D(A-Mod) ≌ D_qc(Spec A)` | Stacks 06Z0, 079W, 08D4+01XB | `Scheme/AffineQCoh.lean` (`affineRingCohomologyEquivalence`, `affineCohomologyComparisonOfInput`) | proved from `AffineDerivedGammaInput`; 01HV discharged (`affineDerivedGammaInputOfTildeExact`) |
| 3 | quasicoherence is Serre | extensions of quasicoherent sheaves are quasicoherent | Stacks 01LA(6), 01IE, 01LA(3) | `Scheme/QCohSerre.lean`, `Scheme/QCohSerreExtension.lean`, `Scheme/QCohSerreExtension01IE.lean`, `Scheme/Derived.lean` | **proved, no assumptions**: 01IE is a theorem (`AffineExtension.surjective_appTop`, via the denominator ideal, local lifts, quasicoherence of the kernel over `D(fg)`, quasi-compactness of `Spec R` and sheaf gluing), hence extension closure on every scheme and triangulated `D_qc`; kernels, cokernels, coproducts, biproducts and split extensions were already proved |
| 4 | `Perf` for rings | `Perf A` thick envelope; closure under `0`, shifts, biproducts, cones, retracts; `⊆ D^b`, `⊆ D^b_coh` (Noetherian) | — | `Scheme/PerfectRing.lean` | proved |
| 5 | perfect = bounded projectives | `Perf A` = bounded complexes of f.g. projectives | Stacks 07LT (= 0657 + 066S) | `Scheme/PerfectModel.lean`, `PerfectModelConverse.lean`, `LeChen.lean`, `CompactToPerfect.lean` | `model ⇒ Perf` **proved for every ring**; `Perf ⇒ model` reduced to retract closure of the model class, and that reduced further to **Le–Chen 2.3 (proved)** plus a truncation induction on a bounded complex.  Residue: that induction |
| 6 | compacts = perfect | compact objects of `D(A-Mod)` are `Perf A` | Stacks 09M1 (schemes, biconditional; affine case via 06Z0 and 07LT) or 0AED (algebraic spaces, with support) | `Scheme/PerfectRing.lean` (`CompactPerfectInput`), `PerfectRingStacks.lean` (`CompactToPerfectInput`), `CompactToPerfect.lean`, `PerfectCompactThick.lean` | **only `compact ⇒ Perf` is used**, and it follows from 07LT's compact-to-model half plus the proved filtration; the reverse implication is proved up to compactness of the regular module (`WeakApprox/CompactThick.lean`) and is never needed |
| 7 | `Perf` bridge | ring envelope vs scheme-local 0BCJ model at `Spec A` | Stacks 0BCJ / 08CM / 06Z0 | `Scheme/PerfectModel.lean` (`perf_iff_affineThickGenerated`, under `AffineAllSheavesBridgeInput` + row 3), `Scheme/PerfectField.lean` (`perf_eq_dbcoh`) | proved over a field; in general reduced to row 5 plus the 06Z0 coherence fields |
| 8 | affine recollement | `D(A[1/f]) → D(A) → D_Z(A)` as `WeakApprox.Recollement`, i.e. `D_Z` slot = open, `D_U` slot = `f`-power torsion | localization sequence (Gao–Psaroudakis 2.2(ii), BDS 2.3, Krause §4; no Stacks tag: 0BFF is unrelated) | `Scheme/AffineRecollement.lean` | proved, modulo the named `AffineRecollementInput` fields |
| 9 | open functors | `j_! ⊣ j^* ⊣ j_*`, exactness, derived recollement | Stacks 00A6, 00AB, 079W | `Scheme/OpenImmersion.lean` | proved |
| 10 | Setup 4.4 from ring data | the 20 fields for the affine recollement | LP §4 | `Scheme/Affine.lean`, `AffineUniverse.lean`, `AisleCoproducts.lean`, `AffineLocalCohomology.lean` | the **coproduct field is gone from the LP chain** (aisle-local coproducts, from bounded-above resolutions) and the **universe mismatch is decided** (small-Hom model).  Remaining: the recollement's functor fields (`RΓ_Z` support, shift/triangulated structure, adjunction, `i⇕`, `i^*`, gluing triangles) — `RΓ_Z` itself is built with three fields proved — plus the assembly items `hT` and the transport across `D ≌ D_small` |
| 11 | LP Theorem 1.1 (abstract) | the gluing theorem, minimal setup | LP Thm 1.1 | `WeakApprox/MainMinimal.lean` | proved |
| 12 | **affine Theorem 1.1** | `SatisfiesWA (D(A-Mod))` and the iff | rows 1–11 + row 6 | `Scheme/AffineMain.lean` (`affine_theorem_1_1_neeman_only`), `PerfectRingStacks.lean` (`affine_theorem_1_1_stacks07LT`), `AisleCoproducts.lean` (`affine_theorem_1_1_small_noCoproducts`), `AffineUniverse.lean` (`affine_theorem_1_1_small`) | proved modulo row 10 and the two assembly items; 09SR, the eventual-vanishing hypothesis (09MB) and the coproduct package are all out of the hypotheses, and the compact/perfect input is down to `compact ⇒ Perf` |
| 13 | GL26 Lemma 2.25 | `Φ_{RΔ_*O} ≅ 𝟭` for affine `Y → S` | GL26 §2.5, Stacks 08IN | `Scheme/AffineDiagonal.lean` (`affine_lemma_2_25`) | proved |
| 14 | weak approximability of `D_qc,Z(Spec A)` | the published input | Neeman, Acta 233 (2024) Thm 3.2 | `Scheme/Inputs.lean` | cited |
| 15 | **GL26 Lemma 5.4** | `Lg₁*P₁ ⊗^L Lg₂*P₂` compactly generates `D_qc(Y₁ ×_S Y₂)` when `P_i` generate | GL26 §5 (Neeman 2023 Cor. 5.10) | `Scheme/Lemma54.lean` | the whole cover argument **proved** in abstract six-functor form, in the paper's `IsPaperGenerator` (zero-detection) sense; residue is the cover square itself: flat base change, `Lt*` conservative, `Rh₂*` conservative (quasi-affine), and the perfect/compact calculus |
| 16 | Stacks 066S infrastructure | idempotents split; Le–Chen 2.3 in a triangle | Le–Chen, J. Algebra 310 (2007) Prop. 2.3 | `Scheme/LeChen.lean` | **proved**: `splitsWithin_third`, plus strong splittings, biproduct-of-triangles and `comp_eq_zero_of_distTriang`; no octahedral axiom |
| 17 | Stacks 09M8 infrastructure | perfect objects are compact | Stacks 09M8 | `WeakApprox/CompactThick.lean`, `Scheme/PerfectCompactThick.lean` | **proved up to compactness of the regular module**: compact objects are closed under thick envelopes, by two-out-of-three on a triangle with no AB4 |
| 18 | Spaltenstein infrastructure | K-projective replacements | Spaltenstein, Compositio Math. 65 (1988) Thm C | `Scheme/KProjectiveResolution.lean`, `AffineBoundedAboveCoproducts.lean`, `SpecialDirectLimits.lean`, `Spaltenstein{Stage,Iteration,Colimit,Replacement}.lean` | bounded-above case **proved**; ℕ-indexed split-mono colimits **proved**; the cone stage and countable induction **proved**; residue is `TheoremCInput`'s three comparisons |
| 19 | Hovey route to replacements | model structure on complexes | Hovey, *Model Categories*, Prop. 2.3.5 and 2.3.2 | `Scheme/ProjectiveModel.lean`, `SmallObjectPresentable.lean`, `GeneratingCofibrations.lean` | replacement data **derived** down to two inputs about a set of morphisms |
| 20 | aisle-local coproducts | the LP proof needs coproducts only inside a fixed aisle | — | `Scheme/AisleCoproducts.lean` | **proved**, and `hasAisleCoproducts_standard` supplies them from bounded-above resolutions, so no unbounded replacement is needed for coproducts |
| 21 | universe decision | where `HasCoproducts` of `D(A-Mod)` can be stated | — | `Scheme/AffineUniverse.lean` | **decided**: `HasCoproducts.{w} (ModuleCat.{u} A)` for `UnivLE.{w,u}`, and the small-Hom model `SmallAffineD` with `HasCoproducts.{u}`; `AffineD A ≌ SmallAffineD A H` |

## Row 10: history of the obstruction, and what actually blocks it now

> **Status update.** Two of the three obstructions recorded below have since been
> discharged, and the section is kept only because it states them precisely.
> **(a) is gone from the LP chain**: `Scheme/AisleCoproducts.lean` shows the proof
> only ever forms coproducts of families inside a fixed aisle, and
> `hasAisleCoproducts_standard` supplies those from bounded-above resolutions, so
> no ambient `HasCoproducts` is needed.  **(a') is decided**:
> `Scheme/AffineUniverse.lean` puts the endpoint in the small-Hom derived category
> where `HasCoproducts.{u}` is expressible, and proves `AffineD A ≌ SmallAffineD A H`
> so this is bookkeeping.
> What still blocks the row is the recollement's remaining functor fields, plus
> the two assembly items: `hT` (the middle `t`-structure is the standard one) and
> the transport of the old affine inputs across `D ≌ D_small`.

## Row 10 as originally diagnosed (historical)

Row 10 asks for `SetupMainMinimal (AffineD (Away A f)) (AffineD A) (AffineDZ A f)`.
Three of its twenty fields cannot be furnished at this toolchain, for two
independent reasons.

**(a) `HasCoproducts (AffineD A)` is missing from Mathlib.**  Checked directly:
`example (A : Type) [CommRing A] : HasCoproducts (AffineD A) := inferInstance`
fails.  `DerivedCategory C` is a localization of `HomotopyCategory C` at the
quasi-isomorphisms, and Mathlib 4.33.1 provides no colimit instance for it.
The two standard routes are not available either:

* `DerivedCategory/KProjective.lean` and `KInjective.lean` state only that
  `Qh` is bijective on Hom-sets *out of* (resp. *into*) a K-projective
  (K-injective) complex.  There is no equivalence `D(C) ≌ K(Proj C)` or
  `D(C) ≌ K(Inj C)`, so coproducts cannot be transported from the complex
  category.
* The injective route cannot produce coproducts in any case: K-injectives are
  closed under *products* (a map of complexes into a product is a family of
  maps), whereas `Hom(A, ∐ I_i) ≠ ∏ Hom(A, I_i)`, so coproducts of
  K-injectives need not be K-injective.

What is needed is a Spaltenstein-style replacement theorem (every complex has a
K-projective resolution), which is not in Mathlib; `Scheme/DerivedCoproducts.lean`
now proves everything downstream of it.  Until it exists, every field of
`SetupMainMinimal` that mentions `Coprod`, and `IsCompactAb` itself (it
quantifies over coproducts in `D`) — and hence `WeakApproximationData
(AffineD A)` and the `AffineDerivedCoproducts.hasCoproductsA` field — cannot
even be *stated*.  See (a') for the independent universe obstruction at the
exact size that row 10 asks for.

**(b) The aisle identities are Neeman-strength.**  The fields
`tD_compactlyGenerated : tD.le 0 = Coprod (shiftTail (G'⟦m⟧ ⊞ R.jShriek.obj GU) 0)`
(and its `tZ`, `tU` analogues) say that the aisle of the standard `t`-structure
is the colimit/extension closure of the shifts of the compact generator.  That is
the "compactly generated `t`-structure" theorem for `D(A-Mod)`, i.e. the content
of Neeman's theorem, not a ring-local computation.  They are hypotheses of LP
Theorem 1.1 by design (they enter the proof of the glued aisle and of
Proposition 4.8), so they cannot be produced from the ring data here.

**(c)** The two ends need `WeakApproximationData (AffineD (Away A f))` and
`WeakApproximationData (AffineDZ A f)`, i.e. weak approximability — and a
`t`-structure on the supported category `AffineDZ A f`, which is a full
subcategory of `AffineD A`.  Both are again Neeman-strength, and both are blocked
by (a) as well.

**(a') A second, independent obstruction at the exact size of the field.**  Row 10
asks for `HasCoproducts.{u+1} (AffineD A)` with `AffineD A = D(ModuleCat.{u} A)`.
A `Type (u+1)`-indexed coproduct of `Type u`-small modules need not stay `Type u`-small,
and indeed `HasCoproducts.{0} (ModuleCat.{0} A)` is synthesizable while
`HasCoproducts.{1} (ModuleCat.{0} A)` is not (checked directly).  So Spaltenstein
replacements would not by themselves close the field as written: either the
categorical layer must index its coproducts in the smaller universe, or the module
category must be resized with a comparison proved.  `Scheme/DerivedCoproducts.lean`
proves the replacement-free coproduct construction (degreewise coproducts of
K-projective complexes, no AB4 needed) and the reduction from a K-projective
replacement datum to `HasCoproducts` of the derived category, and
`Scheme/AffineCoproducts.lean` specializes both to `AffineD A`; neither claims the
field at universe `u+1`.

So the affine case cannot be *closed* by constructing the setup: what can be
closed is the theorem scheme `Setup 4.4 ⟹ LP Theorem 1.1 ⟹ weak approximability`,
which row 12 does, with the two independent Neeman-strength facts (approximability
and compacts = perfect) as the external input.  The next real advance is either

* a Mathlib contribution: `HasCoproducts (DerivedCategory C)` for abelian `C`
  with exact coproducts, via K-projective replacements (weeks, and independent of
  this project); or
* a reformulation of the endpoint that avoids `IsCompactAb`: state LP's
  hypotheses with `Perf`/thick-envelope compactness instead of
  coproduct-preservation of `Hom(G, -)`, and prove `Perf A` compact in that
  sense.  This is the cheaper route and would make rows 10–12 unconditional
  modulo rows 5–7.

## Row 3 is closed

`Scheme/QCohSerreExtension01IE.lean` proves Stacks 01IE without cohomology: for
`m ∈ Γ(F₃)` the ideal `I = {r | r·m lifts}` has an element outside every prime
(using local lifts on basic opens, quasi-compactness of `Spec R`, the
identification `F₁(D(fg)) = (Γ F₁)_fg` from quasicoherence of the kernel, and the
sheaf property of `F₂` to glue over a finite cover), so `I = ⊤` and `m` lifts.
Thus `AffineExtensionSurjectivityInput` is inhabited, extension closure holds on
every scheme, and `D_qc(X)` is triangulated.  Row 3 carries no assumption.

### History: how the residue was isolated

The section below records the reduction that led there, kept because it states
precisely which statement was the obstruction.

`Scheme/QCohSerreExtension.lean` closes the categorical side of Stacks 01IE.  The
one remaining statement is `AffineExtensionSurjectivityInput`: for a short exact
sequence of `O_{Spec R}`-modules whose *outer* terms are quasicoherent, global
sections are surjective on the right map.  That is exactly the assertion which
01IE's own proof reduces to (`0 → M₁ → M₂ → M₃ → 0` exact, where `M_i = Γ(F_i)`),
and the file proves the converse, so

  `AffineExtensionSurjectivityInput ↔ ∀ R, (quasiCoherent (Spec R)).IsClosedUnderExtensions`,

i.e. the residue is the affine case and nothing more.  From it:
extension closure on every scheme (`quasiCoherent_isClosedUnderExtensions`, via
the affine-local criterion and `X.isoSpec`), hence `QuasicoherentExtensionInput`
and triangulated `D_qc` (`isDQCohTriangulatedOfAffineExtensionSurjectivityInput`).
What 01IE's proof still needs, and this project does not have, is the
quasi-compact `D(f)`/`D(g)` patching: for `m ∈ Γ(F₃)`, the ideal
`I = {f | f·m lifts}` is shown to be all of `R` by lifting locally at each prime,
using quasi-compactness of `V(f)` and the sheaf property.  No cohomology is
needed, so this is a bounded piece of sheaf theory rather than a new theorem.

### The route that does not work



`Scheme/QCohSerre.lean` proves, unconditionally: quasicoherence is affine-local
(01BD), `tilde` is exact (00NX), quasicoherent sheaves are closed under kernels
and cokernels in the ambient category, affine global sections are exact on
sequences with quasicoherent outer terms, and the five-term weak-Serre lemma.
Consequently `QuasicoherentExtensionInput X` — the single field
`(quasiCoherent X).IsClosedUnderExtensions` — already gives `IsDQCoh X`
triangulated (`isDQCohTriangulatedOfExtension`), with the strong subobject and
quotient hypotheses no longer needed.

Extension closure itself is still open.  Recorded so it is not retried: the
`tilde`–`Γ` five-lemma route does **not** work.  On `Spec R` one can form the map
of short complexes `tildeΓ• → •`, whose rows are exact (the top one because `Γ`
is left exact and `tilde` exact) and whose outer vertical maps are isomorphisms
when the outer terms are quasicoherent; but the five lemma for short complexes
needs the *surjectivity* of `Γ B → Γ C` for the middle term, which is precisely
the missing content (it is the affine-cohomology-vanishing / horseshoe input, not
a consequence of left exactness of `Γ`).  What does work in that direction is the
mono half.  The honest route to 01LA is the horseshoe on a presentation
(Stacks 01LA's own proof): over a cover where both outer terms are cokernels of
maps of free modules, build a presentation of the middle term, which needs the
local lifting property of epis of sheaves of modules and a common refinement of
the two covers.

## Reduced forms

Reductions already in place, to be used rather than re-derived:

* **Aisle-local coproducts** (`Scheme/AisleCoproducts.lean`): the LP proof only
  ever forms coproducts of families inside a fixed aisle, and the standard
  `t`-structure supplies those from bounded-above resolutions, so no ambient
  `HasCoproducts` and no unbounded replacement is needed for them.
* **`CompactHomZeroAtTop`** (`WeakApprox/CompactVanishing.lean`): the §4 chain
  needs only eventual vanishing between compacts, which is *weaker* than Stacks
  09SR and is exactly Stacks Tag 09MB for qcqs schemes (via Tag 0AED).
* **Extension closure is proved**, so `D_qc(X)` is triangulated with no
  assumption: `Scheme/QCohSerreExtension01IE.lean` proves Stacks 01IE and
  `Scheme/QCohSerreExtension.lean` derives the rest.  The older
  `QuasicoherentSerreInput` (subobjects, quotients, extensions) and
  `QuasicoherentExtensionInput` are no longer needed and are kept only as
  interfaces.
* **`ringObject_eventuallyHomZero_self` + `perf_eventuallyHomZero`**
  (`Scheme/AffineMain.lean`): the ring form of Stacks Tag 09MB is *proved* for
  every commutative ring by transport along the thick envelope, so the only use
  of a compact/perfect theorem in row 12 is `compact ⇒ Perf` (row 6).

## Provenance of the compact/perfect and vanishing inputs

The two inputs that used to be cited to Bondal--Van den Bergh, *Generators and
representability of functors…*, Mosc. Math. J. 3 (2003), are now cited to Stacks
Project tags from Part 1, Chapter 36 (`derived` / `spaces-perfect`), which prove
the same statements with tag-numbered dependencies:

| what is needed | Stacks tag | statement |
|---|---|---|
| perfect objects are compact | **09M8** (Prop. 75.16.1) | a perfect object of `D(O_X)` is compact |
| a perfect compact generator exists | **0AEC** (Lemma 75.15.6) | `D_QCoh,T(O_X)` has a generator which is a perfect complex |
| the generator generates the compacts | **09SR** (Prop. 13.37.6) | a compact generator is a classical generator of the compacts |
| compacts are perfect (the hard direction) | **0AED** (Lemma 75.16.3) | an object of `D_QCoh,T(O_X)` is compact iff it is perfect as an object of `D(O_X)`; the proof uses 09M8, 0AEC and 09SR |
| perfect complexes are bounded | **0BCJ** (Lemma 36.35.2) / **08CM** | perfect = locally quasi-isomorphic to a bounded complex of finite locally free modules |
| eventual vanishing | **09MB** (Lemma 75.17.2) | for perfect `K` there are `a ≤ b` with `Hom(K,L) = 0` whenever `H^i(L) = 0` for `i ∈ [a,b]`, and `Ext^n(K,L) = 0` for all but finitely many `n` when `L` is bounded |

Read on 2026-11-24 at `https://stacks.math.columbia.edu/tag/<tag>`.  There `X` is
a quasi-compact quasi-separated algebraic space over a scheme, with `T ⊆ |X|`
closed and `|X| ∖ T` quasi-compact (`T = |X|` for the unsupported statement), so
every tag applies to Noetherian schemes after specialization, and to `Spec A`
through the affine dictionary.

Consequence for this project: row 6 (`CompactPerfectInput`) is Tag **09M1** for
schemes (Proposition 36.17.1, a biconditional whose affine case reduces through
06Z0 to 07LT) or Tag **0AED** for algebraic spaces with support, and the
eventual-vanishing hypothesis is Tag **09MB**.  For `X = Spec A` the vanishing
half is not cited at all — `perf_eventuallyHomZero` proves it for every
commutative ring — so the single remaining cited item on the affine path is
`compact ⇒ Perf`.

That implication is not even needed in its scheme form.  By Tag 07LT a compact
object of `D(R)` has a bounded complex of finite projective modules as a model
(Tag 0657), and `AffinePerfect.model_mem_perf` proves that any such model lies in
the thick envelope `Perf A`; `Scheme/PerfectRingStacks.lean` therefore derives
`compact ⇒ Perf` from the compact-to-model half of 07LT alone, and states the
affine endpoint with exactly that input
(`StacksGluing.affine_theorem_1_1_stacks07LT`).  The reverse implication
`Perf A ⇒ compact` is never used and is deliberately not assumed.
