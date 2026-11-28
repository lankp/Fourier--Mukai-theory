## Your task: `wave12/gl26-points-perfectness` (Opus, effort: high)

Goal: GL26 §3 (`sec:perfectness`), the pointwise characterization of perfectness over
algebraic spaces, unconditionally (AxiomMath theorems as tagged inputs only), with the
representatives of points of `Spaces/Statements/Notions.lean` (`Representative`, `Represents`):

* **Lemma 3.1** (`lem:23`), **Lemma 3.3** (`lem:34`), **Lemma 3.4** (`lem:45`), **Lemma 3.6**
  (`lem:61`);
* the definition of **finite flat dimension** (before `prop:perfectness`) and **Remark 3.10**
  (`rmk:topological_fact_for_stacks`) as needed;
* **Proposition 3.12** (`prop:perfectness`): for `X` qcqs and `E ∈ D^b_qc(X)` pseudo-coherent,
  all the equivalences of the manuscript.  (3) ⇒ (1) is what GL26 Lemma 5.7 needs.

Lemma 3.2 (`lem:quasi-affine_is_conservative`) is proved in `Spaces/Conservative/QuasiAffine.lean`
for a given factorization only (the general case is in `wave10/verified`); if you need it,
take the factorization as a hypothesis of an intermediate lemma, never as a new named input.
Statements and proofs: `manuscripts/GL26/main.tex`.  Files: `Spaces/Perfectness/` (new; own
`Inputs.lean`, `NonVacuity.lean`), plus import lines in `Spaces.lean`, `Spaces/Audit.lean`, and
`scripts/axiommath/spaces-imports.txt`.  Commit verified pieces as you go.  Seven verification
steps; `lake build Spaces`; `scripts/check_statements.sh --spaces`.  No `lake build SpacesVerified`.
