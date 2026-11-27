## Your task: `wave10/gl26-internal-hom` (Opus, effort: high)

Goal: the derived internal Hom of GL26 §2.2 over algebraic spaces, and three lemmas about it,
unconditionally (AxiomMath theorems as tagged inputs only):

* define `RHom` on `D(𝒪_X)` (AxiomMath has derived internal Hom for spaces: search
  `StacksFrontier/AlgebraicGeometry/Spaces/*InternalHom*`; reuse its definition, do not
  redefine) and the `D_qc` version `Q ∘ RHom ∘ (i × i)` of the paper (coherator `Q`, right
  adjoint of the inclusion `i`);
* **Lemma 2.10** (`lem:rhom_tensor_morphism`): for perfect `K`, the functorial isomorphism
  `K ⊗^L RHom(M,L) ≅ RHom(RHom(K,M), L)`;
* **Lemma 2.11** (`lem:internal_hom`): for `E, L ∈ D_qc(X)`, the canonical isomorphism of the
  manuscript;
* **Lemma 2.16** (`lem:gortz_wedhorn_internal_hom`): the canonical map
  `Lf^* RHom(E,G) → RHom(Lf^*E, Lf^*G)` for qcqs spaces, with the manuscript's hypotheses.

Statements and proofs: `manuscripts/GL26/main.tex`.  If `Q` (the coherator) is not in AxiomMath
for spaces, construct it (Stacks 08D6 / 0CQZ for spaces), or report.  Files: `Spaces/InternalHom/`
(new; own `Inputs.lean`, `NonVacuity.lean`), plus import lines in `Spaces.lean` and
`Spaces/Audit.lean`, and `scripts/axiommath/spaces-imports.txt` for definition modules.  Commit
verified pieces as you go.  Seven verification steps; `lake build Spaces`; `scripts/check_statements.sh
--spaces`.  Do not run `lake build SpacesVerified`.
