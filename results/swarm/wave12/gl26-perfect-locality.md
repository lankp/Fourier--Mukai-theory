## Your task: `wave12/gl26-perfect-locality` (Opus, effort: high)

Goal: GL26 §3's locality lemmas over algebraic spaces, unconditionally (AxiomMath theorems as
tagged inputs only):

* **Lemma 3.5** (`lem:perf_pullback_characterize`): perfect iff perfect on an étale presentation;
* **Lemma 3.7** (`lem:pseudocoherence_affine_faithfully_flat_cover`): pullback preserves
  pseudo-coherence and perfectness for Noetherian spaces, with the converse for faithfully flat
  `f` (use `Spaces/Conservative/Flat.lean`, Lemma 2.14);
* **Lemma 3.8** (`lem:pullback_is_perfect_iff_for_some_or_all_in_equivalence_class`) and
  **Lemma 3.9** (`lem:pullback_is_perfect_iff_closed_pt`): independence of the representative.

Statements and proofs: `manuscripts/GL26/main.tex`.  Files: `Spaces/PerfectLocality/` (new; own
`Inputs.lean`, `NonVacuity.lean`), plus import lines in `Spaces.lean`, `Spaces/Audit.lean`, and
`scripts/axiommath/spaces-imports.txt`.  Commit verified pieces as you go.  Seven verification
steps; `lake build Spaces`; `scripts/check_statements.sh --spaces`.  No `lake build SpacesVerified`.
