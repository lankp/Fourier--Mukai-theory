> **Status.** The project's current focus is the **affine base case**; the
> verification chain is in [`results/AFFINE.md`](AFFINE.md).  This document
> describes the general Noetherian-scheme target, which comes after it, and the
> separated-base step before it.

# Refocus: GL26 for Noetherian schemes

**Decision.** The project is refocused from *quasi-compact quasi-separated
algebraic spaces* to **Noetherian schemes**. The categorical layer of
Lank–Pauwels is scheme-agnostic and stays as it is; the geometric layer of GL26
is rebuilt for schemes.

## Why this is the better target

* **The weak-approximability input becomes published.** For a quasicompact
  quasiseparated scheme `X` and `Z ⊆ X` closed with quasicompact complement,
  `D_qc,Z(X)` is weakly approximable — A. Neeman, *Bounded t-structures on the
  category of perfect complexes*, Acta Math. 233 (2024), no. 2, 239–284,
  Theorem 3.2(iv) (arXiv:2202.08861). The same theorem gives, in (i)–(iii), that
  the compacts of `D_qc,Z(X)` are the perfect complexes supported on `Z`, that a
  single compact generator exists, and the preferred standard `t`-structure.
  Eventual Hom vanishing between compacts is Stacks Tag 09MB (with compacts =
  perfect from Tag 0AED, and boundedness of perfect complexes from Tag 0BCJ). The algebraic-space version is LP, *Corollary 1.2*, which rests
  on Hall–Rydh's induction principle and is unpublished.  Note the class: qcqs,
  not Noetherian — Noetherian buys nothing extra for these inputs.
* **Two inputs of GL26 Remark 2.6 remain preprint-level**: coherence of
  `D_qc,Z(X)` (Neeman, arXiv:1806.06471, Example 5.4) and the passage between
  equivalences on `D_qc`, `D^-_coh`, `D^b_coh`, `Perf` (Canonaco–Haesemeyer–
  Neeman–Stellari, arXiv:2402.04605, Theorem B).  The scheme restriction removes
  the algebraic-space induction, not these.  See `FourierMukai/Scheme/Inputs.lean`
  for the exact statements, as `Prop`-valued templates.
* **The space-specific inputs disappear.** Nagata compactification for
  algebraic spaces, existence of quotients by finite groupoids, and the
  induction principle for algebraic spaces are replaced by the classical
  dévissage/Noetherian induction for schemes.
* **The categorical gluing is already proved here.** `WeakApprox/` proves LP's
  Theorem 1.1 with a single external input (`CompactHomZeroAtTop`, weaker than
  Stacks 09SR); it is stated for bare triangulated categories with a
  recollement, so it applies to `D_qc(X)` without change.

## Decided sequencing

**B'' now, A in parallel, B' medium term.**

* **B''** — affine Noetherian schemes first (`X = Spec A`, `A` Noetherian): the
  dictionary `D_qc(Spec A) ≃ D(A-Mod)`, perfect complexes for rings, and GL26's
  Lemma 2.25 (and one further target) proved in the affine model with the
  projection formula as data.  Run `smwuz1thx`.
* **A** — the scheme-level foundational layer in parallel (`D(X)`, `D_qc`,
  `Perf(X)`, open-immersion functors, `RHom`/`⊗^L`/`f^!` interfaces, and the
  scheme statement layer).  Run `smwuyku7t`.  The three blocking instances that
  A still needs (`EnoughInjectives X.Modules`, `MonoidalCategory X.Modules`,
  `QCoh` abelian) are the gate for anything beyond the interfaces.
* **B'** — separated Noetherian schemes, with GLMP25 Theorem 6.11 (preprint) as
  the scheme form of GL26 Theorem 10.13, once B'' and A have landed.

## First goal

GL26 **Theorem 1.3** (`E` is `f`-perfect ⟺ `E ⊗^L Lf^*A ∈ D^b_coh` for all
`A ∈ D^b_coh` ⟺ `E` is `f`-quasi-perfect) for `f : Y ⟶ X` a proper morphism of
Noetherian schemes, over the interface of `FourierMukai/Scheme/`.

Reaching it requires, in this order: `D_qc`, quasicoherence, `Perf`, `f_*`/`f^*`
with their derived counterparts, `⊗^L`, `RHom`, and the boundedness criterion
GL26 proves via compact generators. The remaining targets (1.2, 1.6, 1.7, 12.3,
2.25, 2.26, 12.2, 6.18) then follow the paper's own order.

## How much of GL26 the scheme route actually simplifies

The theorem-by-theorem audit is in
[`results/GL26_SCHEME_DEPENDENCE.md`](GL26_SCHEME_DEPENDENCE.md).  The headline
numbers:

* only **2 of the 10** targets use weak approximability at all (Theorem 1.2(1)
  through Theorem 12.9, and Remark 2.6/12.9 indirectly);
* **4 targets retain the genuinely new geometry** of GL26 — arbitrary Noetherian
  base change for relative perfectness and the three §12 openness/locus
  declarations;
* the scheme restriction deletes the étale-presentation and point/residual-space
  scaffolding, but not Grothendieck duality, relative dualizing complexes, mates,
  pseudocoherence, support arguments or arbitrary base change;
* restricting further to **separated** Noetherian schemes reuses more:
  Guisado Villalgordo–Lank–Manali Rahul–Pavic, Theorem 6.11 (preprint) is the
  scheme form of GL26 Theorem 10.13.

Consequence for the project's own work: Neeman's theorem proves scheme weak
approximability *directly*, so the completed `WeakApprox/` layer is not a
prerequisite for the scheme route — it is the abstract alternative, and the
thing the algebraic-space version needs.  That does not devalue it (it is a
proved theorem and it is what `FourierMukai/Scheme/WeakApprox.lean` instantiates
when a gluing proof is wanted), but the rehaul's value has to come from the
geometric layer and from GL26's own new mathematics, not from reusing the
categorical gluing.

## Module map (`FourierMukai/Scheme/`)

| module | content | status |
|---|---|---|
| `Derived.lean` | `D(X) := DerivedCategory (SheafOfModules X)`, cohomology sheaves, `IsDQCoh`, triangulated subcategory structure | to build |
| `QCoh.lean` | quasicoherence via the tilde functor on affine opens; `D_qc(Spec A) ≃ D(A-Mod)` | to build |
| `Perfect.lean` | vector bundles, `IsPerfect`, `Perf ⊆ D_qc`, `Perf = (D_qc)^c` (cited: Stacks 0AED / 09M8 / 09SR) | to build |
| `Functors.lean` | `f^*`, `f_*`, `j_!` on sheaves of modules; adjunctions; exactness for open immersions | to build |
| `Duality.lean` | `RHom`, `⊗^L`, `f^!`, projection formula, base change (interface + proved compatibilities) | to build |
| `Recollement.lean` | open/closed recollement of `D_qc`; feeds `WeakApprox.Recollement` | to build |
| `WeakApprox.lean` | `D_qc,Z(X)` weakly approximable: Neeman's theorem as the named input, glued by `WeakApprox/MainMinimal.lean` | in progress — see below |
| `Statements.lean` | the ten GL26 targets for Noetherian schemes, as `Prop`-valued definitions | to build |

### Scheme-level Neeman 3.2(iv): state of the four gluing inputs

The statement is `NeemanSupportedWeakApproximability X Z` in the repository's
`D_qc` model, with the `t`-structure pinned and compactness taken inside `D_qc X`.
Of its four inputs, three are now reductions rather than gaps:

* **Supported excision** — discharged from Stacks 08DF (`SchemeSupportedExcision`).
* **Isomorphism transport** — proved (`SchemeNeemanIsoTransport`).
* **Open/closed glue** — landed as a reduction (`OpenClosedGlue`): the LP gluing
  hypotheses are weakened from object equalities to isomorphisms and from
  `t`-structure equalities to bounded equivalences, using only zero-detection
  generation; the geometric theorem still takes a completion of the two endpoint
  approximation packages as an explicit hypothesis.
* **Affine supported base** — now in place at three strengths
  (`AffineSupportedBaseM1` … `AffineSupportedSchemeBaseM1`): the **principal**
  closed support `V(f)` is proved from nothing but
  `IsCompactAb (ringObject A)`; a finite list `V(f₁,…,fₙ)` and the exact
  `Spec A` / `IsAffine` statements are proved from that plus five named tagged
  inputs (`KoszulScalarSupportInput` 09IR, `IdealSupportedCoproductInput`,
  `IdealSupportedCompactnessInput`, `KoszulPowerCoprodInput`,
  `KoszulDetectionInput` 0A9A, and a supported module/scheme comparison).  No
  `IsGenerator` is used anywhere in that chain.

So the remaining work on this input is the five tagged statements themselves and
compactness of the regular module, not weak approximability.  Everything is
conditional as stated: the `IsAffine` theorem takes the five families over all
commutative rings and `IsCompactAb (ringObject A)` for each ring.

The old algebraic-space interface (`FourierMukai/Paper/DerivedSetup.lean`) and
targets (`FourierMukai/Paper/Statements.lean`) are kept until the scheme
versions replace them; they document what has to remain true after the rehaul.

## What Mathlib 4.33.1 gives, and what it does not

The measured inventory is in [`results/MATHLIB_INVENTORY.md`](MATHLIB_INVENTORY.md):
56 rows, 34 present, 22 missing, each backed by a `#check` or a recorded search.

Present and directly usable: schemes and the morphism classes (Noetherian,
proper, flat, separated, quasi-compact, quasi-separated, open and closed
immersions); `X.Modules` (abelian, with limits and colimits); a quasicoherence
predicate `SheafOfModules.IsQuasicoherent` with affine descriptions
(`tilde`, `tildeEquiv`, affine presentations, restriction along open
immersions); `SheafOfModules.IsLocallyFree`; underived pullback and pushforward
of modules with their adjunction; the general derived category (`DerivedCategory`,
`Q`, `Qh`, shifts, triangulation, `D^+`/`D^-`/`D^b`, the canonical
`t`-structure, `totalLeftDerived`/`totalRightDerived`, `rightDerivedFunctorPlus`,
`rightDerived`); tensor of modules, of presheaves of modules, and of raw
complexes; site sheaf cohomology, the Čech complex construction, and the big and
small étale sites of a scheme.

Missing, in dependency order:

1. **The three blocking instances.** `X.Modules` is not known to be Grothendieck
   abelian and has no `EnoughInjectives` instance; there is no monoidal structure
   on `X.Modules`; the quasicoherent modules are not known to form an abelian
   subcategory. Without the first of these there is no derived functor on
   unbounded complexes; without the second there is no `⊗^L`.
2. **QC functoriality**: general pullback and qcqs pushforward preserving
   quasicoherence, and the coherator.
3. **The derived geometric layer**: `D_qc`, `D_qcoh`, `D^b_coh`, `Perf`,
   `Perf = D_qc^c`, compact generation.
4. **The six-functor layer**: `Rf_*` and `Lf^*` on `D_qc` with the adjunction,
   `⊗^L`, `RHom`, the projection formula, tor-independent base change.
5. **`f^×`, `f^!`, duality, support, ample/very ample, Nagata compactification,
   the Čech comparison, and the open/closed recollement.**

Consequence for the plan: **the first goal is not Theorem 1.3.** It is item 1 —
`EnoughInjectives X.Modules` (equivalently, that sheaves of modules on a scheme
form a Grothendieck abelian category) and the monoidal structure on `X.Modules`.
Everything downstream, including the statement of Neeman's theorem, needs the
categories those instances provide. The affine/ring case is genuinely easier and
is a valid intermediate target: for `X = Spec A` everything reduces to `A-Mod`,
where Mathlib does have the abelian, monoidal and injective-envelope structure.

## A defect found in the current target layer

An earlier bare rendering quantified over an arbitrary `FMContext` and was
refuted: `FourierMukai/Paper/Statements.lean` used to state GL26's Lemma 2.25 as
`Nonempty (C.transform C.diagonalKernel ≅ 𝟭 D)` for an arbitrary `FMContext`.
That is **not a consequence of the interface**: `transform` is defined as
`push ∘ tensorRight K ∘ pull` and those are free structure fields, so
`FourierMukai/Paper/InterfaceAudit.lean` exhibits a legal `FMContext` on
`Type 0`, with every subcategory `True` and `push` constant at `PUnit`, for
which the bare statement is false.  The paper's proof uses the projection formula
(Stacks 08IN), the tensor unit, and `f'_1 ∘ Δ = f'_2 ∘ Δ = 𝟙`; those must be
**fields** of the interface, not consequences of it.  The current
`RelativeFM.lemma_2_25` and `RelativeFM.Noetherian.lemma_2_25Statement_proved`
take them explicitly and are proved; only the geometric discharge of those
inputs remains.

The same audit counts **7 vacuous `True` placeholders** in the targets (six
relative-perfectness hypotheses and `hell : True`).  Both points are
requirements on the scheme-level statement layer: no target may be stated over
an interface that does not imply it, and no hypothesis may be `True`.

**Resolution for Lemma 2.25 (later).**  GL26's Lemma 2.25 is correct, and the
defect above is exactly the defect of the interface: the paper's proof uses the
projection formula (08IN), the tensor unit and `f'_1 ∘ Δ = f'_2 ∘ Δ = 𝟙`, none of
which a free `FMContext` forces.  The scheme-level layer now carries the bare
rendering as `lemma_2_25BareStatement` (refuted, kept to record what the
interface fails to imply) and the faithful form as `lemma_2_25Statement`, which is
proved from `Lemma25DiagonalData` in `FourierMukai/Scheme/Statements.lean`.  So
Lemma 2.25 is no longer an open target; the open question is only the geometric
discharge of `Lemma25DiagonalData` from `Y → S`, which needs the derived layer
this section is about.

## Constraints and risks

* **Toolchain.** Everything is verified on Lean 4.33.1 with Mathlib at
  `/opt/mathlib`, which is read-only: there is no Lake build, and
  `lakefile.toml`'s pin (`v4.35.0` + AxiomMath/Stacks) is not reproducible here.
  The Stacks formalization cannot be imported, and porting it is not a shortcut:
  measured transitive import closures are 3,518 modules / 1.07M lines to reach
  "compact = perfect", 4,416 / 1.35M with generation and Ext vanishing, and
  7,679 / 2.31M for `f^!`; the estimate is 200--450 person-days for a literal
  port and 250--550 for the smallest package supplying compact generation,
  perfectness and Ext vanishing. See
  [`results/STACKS_PORTABILITY.md`](STACKS_PORTABILITY.md). The scheme layer is
  therefore built on Mathlib alone, and a definition spike of 10--20 person-days
  is the sensible first step.
* **The dominant cost is the geometric layer**, not the categorical part: `f^!`
  for schemes, and the compact-generation/perfectness comparison, are
  research-level formalizations even with the literature in hand.
* The rehaul is only worth it if the layer stops at what GL26's proofs use. The
  interface in `FourierMukai/Scheme/Duality.lean` is the contract: if a field is
  never used by a target statement, it does not belong there.
