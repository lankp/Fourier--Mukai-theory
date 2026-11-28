## Your task: `wave12/gl26-relative-perfect` (Opus, effort: high)

Goal: GL26 §4 (`sec:relative_perfect`) over algebraic spaces, unconditionally (AxiomMath theorems
as tagged inputs only), on `IsRelativelyPerfect` (`Spaces/RelativePerfect.lean`, Definition 4.1
`def:relative_perf_stacks`; check it against the manuscript first and report any difference):

* **Remark 4.2** (`rmk:relative_perfects`) items used below;
* **Lemma 4.3** (`lem:finite_coh_dim_implies_restriction_to_bounded`): `Rf_* D^b_qc(Y) ⊆
  D^b_qc(X)` for `f` a morphism of qcqs spaces (needed by GL26 Lemma 5.7);
* **Lemma 4.4** (`lem:quasi_affine_reflects_boundedness`);
* **Propositions 4.5, 4.6** (`prop:relative_perfect_smooth_locality_ascent`, `..._descent`),
  **Corollary 4.7** (`cor:smooth_locally_f_perfect_implies_f_perfect`), **Theorem 4.8**
  (`thm:relative_perf_iff_smooth_locally`).

For Lemma 4.4 (quasi-affine `f`) the same constraint as Lemma 3.2 applies: the factorization of a
quasi-affine morphism is only available in `SpacesVerified`; prove the factorized form and report.
Flat base change (tor-independent squares) for spaces: AxiomMath, as in `Spaces/BaseChange/`.
Statements and proofs: `manuscripts/GL26/main.tex`.  Files: `Spaces/RelPerfect/` (new; own
`Inputs.lean`, `NonVacuity.lean`), plus import lines in `Spaces.lean`, `Spaces/Audit.lean`, and
`scripts/axiommath/spaces-imports.txt`.  Commit verified pieces as you go.  Seven verification
steps; `lake build Spaces`; `scripts/check_statements.sh --spaces`.  No `lake build SpacesVerified`.
