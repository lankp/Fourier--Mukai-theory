# Verifying LP Theorem 1.1 for an affine base scheme

**Target.** For `X = Spec A` with `A` Noetherian, `U = Spec A[1/f]` and
`Z = V(f)`, the recollement

  `D_qc,Z(X)  ⟷  D_qc(X)  ⟷  D_qc(U)`

satisfies **LP Theorem 1.1** — `D_qc(X)` is weakly approximable if and only if
the chosen compact generator has eventually vanishing positive self-Homs — with
**no unproved input except Neeman's published theorem** (Acta Math. 233 (2024),
Theorem 3.2).  The affine dictionary identifies this with the ring-level picture
`D_Z ⟷ D(A-Mod) ⟷ D(A[1/f]-Mod)`.

## The chain

Each row is one Lean module or one proof obligation.  "proved" means a theorem
with no residue; "cited" means a published theorem stated as a named hypothesis
or field; "open" means work still to be done.

| # | obligation | content | source | Lean | status |
|---|---|---|---|---|---|
| 1 | affine dictionary | `D(A-Mod) ≌ D(QCoh(Spec A))` | — | `Scheme/AffineDictionary.lean` | proved |
| 2 | two models of `D_qc` | quasicoherent cohomology vs `D(QCoh)` for `Spec A` | Stacks 06Z0, 36.3.5 | `Scheme/AffineDictionary.lean` (`AffineCohomologyComparison`) | open |
| 3 | quasicoherence is Serre | extensions of quasicoherent sheaves are quasicoherent | Stacks 01LA | `Scheme/Derived.lean` (`QuasicoherentSerreInput`) | open |
| 4 | `Perf` for rings | `Perf A` thick envelope; `⊆ D^b`, `⊆ D^b_coh` (Noetherian) | — | `Scheme/PerfectRing.lean` | proved |
| 5 | perfect = bounded projectives | `Perf A` = bounded complexes of f.g. projectives | Stacks 09M1 / Neeman | `Scheme/PerfectRing.lean` (`BoundedProjectiveModelInput`) | open |
| 6 | compacts = perfect | compact objects of `D(A-Mod)` are `Perf A` | Bondal–Van den Bergh 3.1.1, Neeman | `Scheme/PerfectRing.lean` (`CompactPerfectInput`) | cited |
| 7 | `Perf` bridge | ring envelope vs scheme-local 0BCJ model at `Spec A` | Stacks 0BCJ / 08CM | `Scheme/Perfect.lean`, `PerfectRing.lean` | open |
| 8 | affine recollement | `D_Z ⟷ D(A) ⟷ D(A[1/f])` as `WeakApprox.Recollement` | localization sequence (Neeman; AJL) | — | open |
| 9 | open functors | `j_! ⊣ j^* ⊣ j_*`, exactness, derived recollement | Stacks 00A6, 00AB, 079W | `Scheme/OpenImmersion.lean` | proved |
| 10 | Setup 4.4 from ring data | the 20 fields for the affine recollement | LP §4 | `Scheme/Affine.lean` (partial) | open |
| 11 | LP Theorem 1.1 (abstract) | the gluing theorem, minimal setup | LP Thm 1.1 | `WeakApprox/MainMinimal.lean` | proved |
| 12 | **affine Theorem 1.1** | `SatisfiesWA (D(A-Mod))` and the iff | rows 1–11 + Neeman | `Scheme/Affine.lean` (`affine_theorem_1_1`) | proved modulo 10 |
| 13 | GL26 Lemma 2.25 | `Φ_{RΔ_*O} ≅ 𝟭` for affine `Y → S` | GL26 §2.5, Stacks 08IN | `Scheme/AffineDiagonal.lean` | proved |
| 14 | weak approximability of `D_qc,Z(Spec A)` | the published input | Neeman, Acta 233 (2024) Thm 3.2 | `Scheme/Inputs.lean` | cited |

## What "proved modulo 10" means

`affine_theorem_1_1` (`Scheme/Affine.lean`) already proves the equivalence of LP
Theorem 1.1 in the affine model `AffineD A = D(A-Mod)`, but it takes the LP setup
`SetupMainMinimal` as data.  Closing the verification means constructing that
setup from the ring data — rows 2, 3, 5, 7, 8, 10 — after which the only
remaining input is row 14, a published theorem.

## Reduced forms

Two reductions are already in place and should be used rather than re-derived:

* **`CompactHomZeroAtTop`** (`WeakApprox/CompactVanishing.lean`): the §4 chain
  needs only eventual vanishing between compacts, which is *weaker* than Stacks
  09SR and is exactly what Bondal–Van den Bergh supply for qcqs schemes.
* **`QuasicoherentSerreInput`** is the single obstruction to `D_qc` being
  triangulated; everything `t`-structural on `Dcq` waits on it.
