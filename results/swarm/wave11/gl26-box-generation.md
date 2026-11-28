## Your task: `wave11/gl26-box-generation` (Opus, effort: high)

Goal: **GL26 Lemma 5.4** (`lem:neeman2023cor5_10`) over algebraic spaces, unconditionally
(AxiomMath theorems as tagged inputs only): for `f_i : Y_i → S` morphisms of qcqs spaces and
compact generators `P_i` of `D_qc(Y_i)`, `Lg_1^* P_1 ⊗^L Lg_2^* P_2` compactly generates
`D_qc(Y_1 ×_S Y_2)`.  The scheme-layer `Scheme/Lemma54.lean` does the cover argument in
six-functor form with a residue (`CoverComparisonInput`); here prove it over spaces, using wave
10's conservativity results (`Spaces/Conservative/`: Lemmas 2.14, 3.2), compact generation of
`D_qc` (`Spaces/Supported/CompactGeneration.lean`) and flat base change from AxiomMath.

Statement and proof: `manuscripts/GL26/main.tex`.  Files: `Spaces/BoxGeneration/` (new; own
`Inputs.lean`, `NonVacuity.lean`), plus import lines in `Spaces.lean` and `Spaces/Audit.lean`,
and `scripts/axiommath/spaces-imports.txt`.  Commit verified pieces as you go.  Seven
verification steps; `lake build Spaces`; `scripts/check_statements.sh --spaces`.  Do not run
`lake build SpacesVerified`.
