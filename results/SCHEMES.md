# Refocus: GL26 for Noetherian schemes

**Decision.** The project is refocused from *quasi-compact quasi-separated
algebraic spaces* to **Noetherian schemes**. The categorical layer of
Lank–Pauwels is scheme-agnostic and stays as it is; the geometric layer of GL26
is rebuilt for schemes.

## Why this is the better target

* **The weak-approximability input becomes published.** For a quasicompact
  quasiseparated scheme `X` and `Z ⊆ X` closed with quasicompact complement,
  `D_qc,Z(X)` is weakly approximable — Neeman, [5, Theorem 3.2(iv)] as quoted in
  arXiv:2505.09120. The algebraic-space version is LP, *Corollary 1.2*, which
  rests on Hall–Rydh's induction principle and is unpublished.
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

Verified present: `AlgebraicGeometry/Scheme`, `Modules/{Presheaf,Sheaf,Tilde}`
(sheaves of modules, the tilde functor), `Noetherian`, `Morphisms`,
`OpenImmersion`, `Sites`; `Algebra/Homology/DerivedCategory/Basic`
(`DerivedCategory`, `HasDerivedCategory`, `Q`, `Qh`, triangulated structure);
`CategoryTheory/Functor/Derived/*` and `CategoryTheory/Abelian/{Left,Right}Derived`.

Verified absent (as far as we have searched): a quasicoherence predicate for
sheaves of modules on a scheme, perfect complexes, `RHom`, derived tensor,
Grothendieck duality, K-injective/K-projective resolutions, ample line bundles.
These are exactly the modules above.

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
