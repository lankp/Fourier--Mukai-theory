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
| 3 | quasicoherence is Serre | extensions of quasicoherent sheaves are quasicoherent | Stacks 01LA | `Scheme/QCohSerre.lean`, `Scheme/Derived.lean` | kernels and cokernels **proved**; extension closure open, and it alone is what `D_qc` needs |
| 4 | `Perf` for rings | `Perf A` thick envelope; closure under `0`, shifts, biproducts, cones, retracts; `⊆ D^b`, `⊆ D^b_coh` (Noetherian) | — | `Scheme/PerfectRing.lean` | proved |
| 5 | perfect = bounded projectives | `Perf A` = bounded complexes of f.g. projectives | Stacks 066T/09M1 | `Scheme/PerfectModel.lean` | `Perf ⇒? model` open (`BoundedProjectiveModelConverseInput`); `model ⇒ Perf` **proved for every ring** |
| 6 | compacts = perfect | compact objects of `D(A-Mod)` are `Perf A` | Stacks 09M1 (schemes, biconditional; affine case via 06Z0 and 07LT) or 0AED (algebraic spaces, with support) | `Scheme/PerfectRing.lean` (`CompactPerfectInput`), `Scheme/PerfectRingStacks.lean` (`CompactToPerfectInput`) | cited, and **only the implication `compact ⇒ Perf` is ever used** |
| 7 | `Perf` bridge | ring envelope vs scheme-local 0BCJ model at `Spec A` | Stacks 0BCJ / 08CM / 06Z0 | `Scheme/PerfectModel.lean` (`perf_iff_affineThickGenerated`, under `AffineAllSheavesBridgeInput` + row 3), `Scheme/PerfectField.lean` (`perf_eq_dbcoh`) | proved over a field; in general reduced to row 5 plus the 06Z0 coherence fields |
| 8 | affine recollement | `D(A[1/f]) → D(A) → D_Z(A)` as `WeakApprox.Recollement`, i.e. `D_Z` slot = open, `D_U` slot = `f`-power torsion | localization sequence (Gao–Psaroudakis 2.2(ii), BDS 2.3, Krause §4, Stacks 0BFF) | `Scheme/AffineRecollement.lean` | proved, modulo the named `AffineRecollementInput` fields |
| 9 | open functors | `j_! ⊣ j^* ⊣ j_*`, exactness, derived recollement | Stacks 00A6, 00AB, 079W | `Scheme/OpenImmersion.lean` | proved |
| 10 | Setup 4.4 from ring data | the 20 fields for the affine recollement | LP §4 | `Scheme/Affine.lean` (partial) | open, and **not instantiable at this toolchain** — see below |
| 11 | LP Theorem 1.1 (abstract) | the gluing theorem, minimal setup | LP Thm 1.1 | `WeakApprox/MainMinimal.lean` | proved |
| 12 | **affine Theorem 1.1** | `SatisfiesWA (D(A-Mod))` and the iff | rows 1–11 + row 6 | `Scheme/AffineMain.lean` (`affine_theorem_1_1_neeman_only`), `Scheme/PerfectRingStacks.lean` (`StacksGluing.affine_theorem_1_1_stacks07LT`) | proved modulo row 10; 09SR and the eventual-vanishing hypothesis (Stacks 09MB) removed, and the row-6 input reduced to its `compact ⇒ Perf` half, itself derived from the compact-to-model half of 07LT |
| 13 | GL26 Lemma 2.25 | `Φ_{RΔ_*O} ≅ 𝟭` for affine `Y → S` | GL26 §2.5, Stacks 08IN | `Scheme/AffineDiagonal.lean` (`affine_lemma_2_25`) | proved |
| 14 | weak approximability of `D_qc,Z(Spec A)` | the published input | Neeman, Acta 233 (2024) Thm 3.2 | `Scheme/Inputs.lean` | cited |

## Row 10: why it is not instantiable here

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
K-projective resolution), which is not in Mathlib.  Until it exists, every field
of `SetupMainMinimal` that mentions `Coprod`, and `IsCompactAb` itself (it
quantifies over coproducts in `D`) — and hence `WeakApproximationData
(AffineD A)` and the `AffineDerivedCoproducts.hasCoproductsA` field — cannot
even be *stated*.

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

## Row 3: what is left, and one route that does not work

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

* **`CompactHomZeroAtTop`** (`WeakApprox/CompactVanishing.lean`): the §4 chain
  needs only eventual vanishing between compacts, which is *weaker* than Stacks
  09SR and is exactly Stacks Tag 09MB for qcqs schemes (via Tag 0AED).
* **`QuasicoherentExtensionInput`** (`Scheme/QCohSerre.lean`) is now the single
  obstruction to `D_qc` being triangulated; the older `QuasicoherentSerreInput`
  (subobjects, quotients, extensions) is stronger than needed.
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
