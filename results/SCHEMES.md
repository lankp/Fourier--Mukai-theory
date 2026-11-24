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
  Eventual Hom vanishing between compacts is Bondal–Van den Bergh, *Generators
  and representability of functors…*, Mosc. Math. J. 3 (2003), Theorem 3.1.1 +
  Lemma 3.3.8. The algebraic-space version is LP, *Corollary 1.2*, which rests
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

## First goal

GL26 **Theorem 1.3** (`E` is `f`-perfect ⟺ `E ⊗^L Lf^*A ∈ D^b_coh` for all
`A ∈ D^b_coh` ⟺ `E` is `f`-quasi-perfect) for `f : Y ⟶ X` a proper morphism of
Noetherian schemes, over the interface of `FourierMukai/Scheme/`.

Reaching it requires, in this order: `D_qc`, quasicoherence, `Perf`, `f_*`/`f^*`
with their derived counterparts, `⊗^L`, `RHom`, and the boundedness criterion
GL26 proves via compact generators. The remaining targets (1.2, 1.6, 1.7, 12.3,
2.25, 2.26, 12.2, 6.18) then follow the paper's own order.

## Module map (`FourierMukai/Scheme/`)

| module | content | status |
|---|---|---|
| `Derived.lean` | `D(X) := DerivedCategory (SheafOfModules X)`, cohomology sheaves, `IsDQCoh`, triangulated subcategory structure | to build |
| `QCoh.lean` | quasicoherence via the tilde functor on affine opens; `D_qc(Spec A) ≃ D(A-Mod)` | to build |
| `Perfect.lean` | vector bundles, `IsPerfect`, `Perf ⊆ D_qc`, `Perf = (D_qc)^c` (cited: Bondal–Van den Bergh, Hall–Rydh) | to build |
| `Functors.lean` | `f^*`, `f_*`, `j_!` on sheaves of modules; adjunctions; exactness for open immersions | to build |
| `Duality.lean` | `RHom`, `⊗^L`, `f^!`, projection formula, base change (interface + proved compatibilities) | to build |
| `Recollement.lean` | open/closed recollement of `D_qc`; feeds `WeakApprox.Recollement` | to build |
| `WeakApprox.lean` | `D_qc,Z(X)` weakly approximable: Neeman's theorem as the named input, glued by `WeakApprox/MainMinimal.lean` | to build |
| `Statements.lean` | the ten GL26 targets for Noetherian schemes, as `Prop`-valued definitions | to build |

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

## Constraints and risks

* **Toolchain.** Everything is verified on Lean 4.33.1 with Mathlib at
  `/opt/mathlib`, which is read-only: there is no Lake build, and
  `lakefile.toml`'s pin (`v4.35.0` + AxiomMath/Stacks) is not reproducible here.
  The Stacks formalization cannot be imported (wrong toolchain, ~64k modules, no
  cache), so the scheme layer is built on Mathlib alone.
* **The dominant cost is the geometric layer**, not the categorical part: `f^!`
  for schemes, and the compact-generation/perfectness comparison, are
  research-level formalizations even with the literature in hand.
* The rehaul is only worth it if the layer stops at what GL26's proofs use. The
  interface in `FourierMukai/Scheme/Duality.lean` is the contract: if a field is
  never used by a target statement, it does not belong there.
