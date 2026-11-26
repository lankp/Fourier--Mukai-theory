# Mathlib 4.33.1 inventory for the scheme rehaul

## Method and bottom line

Every positive entry below is backed by a `#check` or a compiled example in this
file, using Lean 4.33.1 and the prebuilt `/opt/mathlib`.  `MISSING` means that no
implementation was found in this checkout by the explicit searches recorded at
the end; it is not a claim that no differently named future implementation could
exist.  There are **56 comparison rows: 34 present API groups and 22 missing
layers**.  These are interface counts, not estimates of proof difficulty.

The table corrects one statement in the existing `DerivedSetup.lean` docstring:
scheme étale sites *do* exist in this Mathlib (`Scheme.etaleTopology` and
`Scheme.smallEtaleTopology`), including an affine-small-site equivalence and
Grothendieck-abelian sheaf instances.  Algebraic spaces themselves, and the
quasicoherent/perfect/derived-geometric layer on either schemes or spaces, were
not found.

## Inventory

| # | Want | Mathlib name or MISSING | Evidence / qualification |
|---:|---|---|---|
| P1 | schemes and morphisms | `AlgebraicGeometry.Scheme`, `.Hom` | `#check` |
| P2 | (locally) Noetherian scheme | `IsLocallyNoetherian`, `IsNoetherian` | `#check`; global includes compactness |
| P3 | proper morphism | `IsProper` | `#check` |
| P4 | separated morphism | `IsSeparated` | `#check` |
| P5 | quasi-compact morphism | `QuasiCompact` (not `IsQuasiCompact`) | `#check` |
| P6 | quasi-separated morphism | `QuasiSeparated` | `#check` |
| P7 | open immersion | `IsOpenImmersion` | `#check` |
| P8 | closed immersion | `IsClosedImmersion` | `#check` |
| P9 | flat morphism | `Flat` | `#check` |
| P10 | all `O_X`-modules, abelian | `Scheme.Modules` | `#check`; `modules_abelian` below |
| P11 | quasicoherence predicate | `SheafOfModules.IsQuasicoherent`, `.isQuasicoherent` | `#check`; gives an `ObjectProperty` |
| P12 | affine `M ↦ M~`, affine QC equivalence | `tilde`, `tildeEquiv` | `#check`; also `isQuasicoherent_iff_isIso_fromTildeΓ` |
| P13 | local affine presentations of QC modules | `Scheme.Modules.exists_affineOpenCover_presentation` | `#check` |
| P14 | QC restriction along an open immersion | `Scheme.Modules.isQuasicoherent_restrictFunctor` | `#check` |
| P15 | locally free sheaves of modules | `SheafOfModules.IsLocallyFree` | `#check`; no finiteness/perfect-complex layer follows |
| P16 | underived module pullback | `Scheme.Modules.pullback` | `#check` |
| P17 | underived module pushforward | `Scheme.Modules.pushforward` | `#check` |
| P18 | underived pullback/pushforward adjunction | `Scheme.Modules.pullbackPushforwardAdjunction` | `#check`; proved again below |
| P19 | unbounded derived category of an abelian category | `DerivedCategory`, `HasDerivedCategory.standard` | `#check`; standard localization is a choice |
| P20 | localization from complexes/homotopy category | `DerivedCategory.Q`, `.Qh` | `#check` |
| P21 | shift, triangles, triangulated structure | `Pretriangulated.Triangle`; derived instances | `#check`; `derivedCategory_triangulated` below |
| P22 | bounded derived categories | `DerivedCategory.Plus`, `.Minus`, `.Bounded` | `#check` |
| P23 | canonical t-structure and cohomology | `DerivedCategory.TStructure.t`, `.homologyFunctor` | `#check`; t-structure example below |
| P24 | abstract total derived functors | `Functor.totalRightDerived`, `.totalLeftDerived` | `#check`; general localization API, not a geometric functor |
| P25 | right derived functor on `D^+` | `Functor.rightDerivedFunctorPlus` | `#check`; source TODO says its triangulatedness is not yet proved |
| P26 | individual classical right-derived functors | `Functor.rightDerived` | `#check`; needs injective resolutions |
| P27 | tensor of ordinary modules | `ModuleCat.monoidalCategory` | `#check` and compiled instance example |
| P28 | tensor of presheaves of modules | `PresheafOfModules.monoidalCategory` | `#check` |
| P29 | tensor of raw complexes | `HomologicalComplex.tensorObj`, `.monoidalCategory` | `#check`; compiled `ChainComplex (ModuleCat R) ℕ` example |
| P30 | global Ext groups | `Abelian.Ext` | `#check`; not a sheaf-valued derived internal Hom |
| P31 | site sheaf cohomology | `CategoryTheory.Sheaf.H`, `.H'` | `#check`; Ext-based, subject to its typeclass assumptions |
| P32 | Čech complex construction | `CategoryTheory.cechComplexFunctor` | `#check`; construction only, see M20 |
| P33 | big/small étale sites of a scheme | `Scheme.etaleTopology`, `.smallEtaleTopology` | `#check` |
| P34 | small-étale sheaves, Grothendieck abelian | `Scheme.AffineEtale.sheafEquiv`; `isGrothendieckAbelian_sheaf_smallEtaleTopology` | `#check` |
| M1 | QC sheaves as an abelian category | **MISSING: no ready instance** | failed `#synth Abelian (isQuasicoherent X.ringCatSheaf).FullSubcategory` |
| M2 | `X.Modules` Grothendieck abelian / enough injectives | **MISSING: no ready instances** | failed `#synth IsGrothendieckAbelian` and `#synth EnoughInjectives` |
| M3 | general scheme pullback preserves QC | **MISSING** | S1, S3; only the open-immersion wrapper P14 was found |
| M4 | affine/qcqs pushforward preserves QC | **MISSING** | S3 plus an explicit source TODO immediately before `isIso_fromTildeΓ_pushforward` |
| M5 | coherator / derived QC comparison | **MISSING** | S1, S2 |
| M6 | `D_qc(X)` / `D_qcoh(X)` | **MISSING** | S1, S2; `DerivedCategory X.Modules` is `D` of *all* modules, not a substitute |
| M7 | `D^b_coh`, coherent and pseudocoherent complexes | **MISSING in algebraic geometry** | S1; site-theoretic uses of “coherent sheaf” are unrelated |
| M8 | perfect / strictly perfect complexes, tor amplitude | **MISSING** | S1, S10; `Group.IsPerfect` is unrelated, and `SheafOfModules.IsLocallyFree` is only a starting point |
| M9 | `Perf(X)=D_qc(X)^c`, generation, geometric weak approximability | **MISSING as a scheme implementation** | S1, S2, S12; the project's abstract LP theory does not instantiate geometry |
| M10 | monoidal category of sheaves of modules | **MISSING: no ready instance** | failed `#synth MonoidalCategory X.Modules`; contrast P27/P28, S4 |
| M11 | derived tensor `⊗^L` on `D_qc(X)` | **MISSING** | S5; P29 is raw complexes and P24 is only a general machine |
| M12 | sheaf-valued `RHom` / derived internal Hom | **MISSING** | S5, S11; global `Abelian.Ext` P30 is different |
| M13 | unbounded geometric `Rf_*` on `D_qc` | **MISSING** | M2/M4/M6 plus S2/S5; P25 is only `D^+` of an already supplied abelian functor |
| M14 | geometric `Lf^*` and `Lf^* ⊣ Rf_*` | **MISSING** | S2/S5; P18 is underived |
| M15 | projection formula, tor-independent derived base change | **MISSING** | S7 found no relevant declaration |
| M16 | `f^×`, `f^!`, Grothendieck duality | **MISSING** | S2 found no implementation or declaration |
| M17 | ample / very ample line bundles | **MISSING** | S1, S13 found no relevant declaration |
| M18 | Nagata compactification | **MISSING** | S1/S2/S13 found no declaration |
| M19 | support and openness of perfect/pseudocoherent loci | **MISSING** | S1; no algebraic-geometry support/perfect-locus API found |
| M20 | Čech comparison computing sheaf cohomology or `Rf_*` | **MISSING** | P32 and S6: only the complex construction was found |
| M21 | geometric open/closed derived recollement with `j_!`, `i^!` | **MISSING** | S2/S5; abstract recollements in the project are not an instantiation |
| M22 | algebraic spaces | **MISSING** | S8 found no algebraic-space declaration in this checkout |

## Verdict (two sentences)

Scheme primitives and abstract homological algebra are genuinely reusable, but a
self-contained GL26 scheme layer is still blocked first by the QC/derived
infrastructure (QC as Grothendieck abelian with enough injectives and QC
functoriality; `D_qc`, `D_qcoh`, `Perf`, compact generation), then by monoidal
six-functor geometry (`⊗^L`, `RHom`, `Lf^*`, `Rf_*`, projection formula/base
change), and only afterwards by `f^!`, duality, support and ample/Nagata tools.
Restricting to Noetherian schemes removes the absent algebraic-space objects but
**none of the 21 scheme-level missing rows M1–M21**; assuming Neeman's published
weak-approximability result as a hypothesis can discharge an external geometric
proof obligation in M9, but supplies none of the definitions in which that
proposition and GL26's ten targets must be stated.

## Reproducible negative searches and probes

All paths below are under `/opt/mathlib/Mathlib`; `--glob '*.lean'` was used for
the recursive `rg` searches.  Matches were inspected, not merely counted.

* **S1** `rg -n -i 'perfect complex|strictly perfect|pseudocoherent|pseudo-coherent|coherent sheaf|def (DQc|DQCoh|Perf)|upperShriek|Nagata compactification|very ample|ample line bundle' .` — no relevant algebraic-geometry declaration; hits were unrelated notions (perfect fields, site coherence, etc.).
* **S2** `rg -n -i 'upper.?shriek|upperCross|dualizing|dualising|extraordinary inverse|Grothendieck duality|f\^!' AlgebraicGeometry Algebra/Homology/DerivedCategory Algebra/Category/ModuleCat/Sheaf` — no implementation hit.
* **S3** `rg -n 'isQuasicoherent.*(pullback|pushforward)|IsQuasicoherent.*(pullback|pushforward)' AlgebraicGeometry Algebra/Category/ModuleCat/Sheaf` — generic site lemmas and open restriction only.  In `AlgebraicGeometry/Modules/Tilde.lean`, the source TODO at the `isIso_fromTildeΓ_pushforward` block explicitly says to use the then-new affine QC criterion to show QC pushforward for affine morphisms; no such wrapper follows in the file.
* **S4** `rg -n -i 'tensor|Monoidal' AlgebraicGeometry/Modules Algebra/Category/ModuleCat/Sheaf` — no sheaf-of-modules tensor implementation; the positive presheaf construction is in `Algebra/Category/ModuleCat/Presheaf/Monoidal.lean`.
* **S5** `rg -n 'Monoidal.*DerivedCategory|DerivedCategory.*Monoidal|tensor.*DerivedCategory|derived.*tensor' Algebra CategoryTheory` — generic derivation/Tor material and raw complexes only, no `D_qc` tensor/derived geometric adjunction.
* **S6** `rg -n -i '(Cech|Čech).*(comparison|compute|isomorph|derived|cohomolog)|(comparison|compute|isomorph).*(Cech|Čech)' CategoryTheory/Sites/SheafCohomology` — only the Čech construction/header.
* **S7** `rg -n -i 'projection formula|tor.independent' AlgebraicGeometry Algebra/Homology/DerivedCategory Algebra/Category/ModuleCat/Sheaf` — no hits.
* **S8** `rg -n -i '\balgebraic spaces?\b' .` — no algebraic-space declaration found.  This does not contradict P33, which is about sites of schemes.
* **S9** `rg -n 'SheafOfModules.*(EnoughInjectives|IsGrothendieckAbelian)|EnoughInjectives.*SheafOfModules|IsGrothendieckAbelian.*SheafOfModules' .` — no hits.
* **S10** `rg -n '^(class|structure|def|abbrev) (.*\\.)?IsPerfect\\b|^class IsPerfect\\b' .` — exactly one declaration hit, `GroupTheory/IsPerfect.lean:41`; it is the group-theoretic notion, not a complex of sheaves.
* **S11** `rg -n '\\b(RHom|rHom|derivedHom|DerivedHom)\\b' AlgebraicGeometry Algebra/Homology` — no hits.
* **S12** `rg -n -i 'weakly approximable|weak approximability|compact objects.*perfect|perfect.*compact objects|compact generation.*scheme|coherator' .` — no hits.
* **S13** `rg -n -i '\\bample\\b|line.?bundle|Nagata|compactification' AlgebraicGeometry Algebra/Category/ModuleCat/Sheaf` — no hits; unlike S1 this also covers camelCase and does not truncate output.

The following negative typeclass probes were run separately with the same imports
(and `X : Scheme.{u}`); each failed to synthesize, rather than being inferred
from a simplification made for this audit:

```
#synth MonoidalCategory X.Modules
#synth EnoughInjectives X.Modules
#synth IsGrothendieckAbelian.{u} X.Modules
#synth Abelian (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory
```

Thus the failures M1, M2 and M10 are compiler-checked in addition to the source
searches.  A `#synth HasExt X.Modules` probe reached the typeclass heartbeat
limit; it is deliberately **not** counted as evidence of absence.
