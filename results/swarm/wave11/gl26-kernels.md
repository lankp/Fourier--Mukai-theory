## Your task: `wave11/gl26-kernels` (Opus, effort: high)

Goal: GL26 Lemmas 2.25 and 2.26 over algebraic spaces, unconditionally (AxiomMath theorems as
tagged inputs only), with the integral transforms of `Spaces/IntegralTransform.lean`:

* **Lemma 2.25** (`lem:funct_on_kernel`): for `f : Y → S` proper flat of Noetherian spaces,
  `Φ_{RΔ_* 𝒪_Y} ≅ id` on `D_qc(Y)` (and the rest of the statement in the manuscript);
* **Lemma 2.26** (`lem:convolution`): `Φ_{K_2} ∘ Φ_{K_1} ≅ Φ_{K_2 ⋆ K_1}` on `D_qc`, with the
  manuscript's notation and hypotheses.

The scheme-layer versions (`Scheme/DiagonalIdentity.lean`, `Scheme/AffineConvolution.lean`) are
conditional on named inputs and are not the target; the proofs here use the projection formula
and flat (Tor-independent) base change from AxiomMath and the base-change cube of
`Spaces/BaseChange/`.  Statements and proofs: `manuscripts/GL26/main.tex`.  Files:
`Spaces/Kernels/` (new; own `Inputs.lean`, `NonVacuity.lean`), plus import lines in `Spaces.lean`
and `Spaces/Audit.lean`, and `scripts/axiommath/spaces-imports.txt`.  Commit verified pieces as
you go.  Seven verification steps; `lake build Spaces`; `scripts/check_statements.sh --spaces`.
Do not run `lake build SpacesVerified`.
