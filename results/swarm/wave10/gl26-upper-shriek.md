## Your task: `wave10/gl26-upper-shriek` (Opus, effort: high)

Goal: GL26 §2's duality lemmas over algebraic spaces, unconditionally (AxiomMath theorems as
tagged inputs only).  `f^×` is the right adjoint of `Rf_*` on `D_qc`; `f^!` is defined on
`(Sp/S)_{Noeth,sep,fp}` by Nagata compactification, as in the manuscript.  AxiomMath has the
duality theory for spaces (`StacksFrontier/AlgebraicGeometry/Spaces/Duality*`) and Nagata
compactification: reuse its definitions.

In this order (commit each one verified):
* **Lemma 2.22** (`lem:neeman187`): for proper `f`, `f^× ≅ f^!` on `D_qc`;
* **Lemma 2.24** (`lem:neeman189`): the bifunctorial maps `χ(f,E,G)` (and the rest of the
  statement);
* **Lemma 2.21** (`lem:neeman186`): `ρ(f,g) : (g∘f)^! → f^! ∘ g^!` is an isomorphism under each
  of (1)–(4);
* **Lemma 2.23** (`lem:neeman188`): the base-change statement for a 2-fibered square.

Statements and proofs: `manuscripts/GL26/main.tex`.  If a statement needs a definition not yet
in `Spaces/` (the category `(Sp/S)_{Noeth,sep,fp}`, `f^!`), define it in your files and prove
it non-vacuous.  Files: `Spaces/Duality/` (new; own `Inputs.lean`, `NonVacuity.lean`), plus
import lines in `Spaces.lean` and `Spaces/Audit.lean`, and `scripts/axiommath/spaces-imports.txt`
for definition modules.  Seven verification steps; `lake build Spaces`;
`scripts/check_statements.sh --spaces`.  Do not run `lake build SpacesVerified`.  Partial is
fine if each merged lemma is complete: report what remains.
