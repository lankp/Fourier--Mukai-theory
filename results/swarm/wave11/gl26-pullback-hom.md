## Your task: `wave11/gl26-pullback-hom` (Opus, effort: high)

Goal: complete GL26 Lemmas 2.16 and 2.10 over algebraic spaces (`Spaces/InternalHom/`, wave 10):

* **Lemma 2.16 (2)** (`lem:gortz_wedhorn_internal_hom2`): the canonical map
  `Lf^* R𝓗om(E, G) → R𝓗om(Lf^* E, Lf^* G)` is an isomorphism for `E` pseudo-coherent,
  `G ∈ D^+_qc(X)` and `f` of finite Tor dimension (manuscript's hypotheses).  Wave 10 reduced it
  to the invertibility of `ρ_f` (`lemma_2_16_pseudoCoherent_of_isIso`).  AxiomMath (`f56a316`)
  proves `ρ_f` invertible for ringed spaces (Stacks 0GM7), for affine morphisms of spaces, and in
  the base-change form of Stacks 0DKI(3); prove the case of a general morphism of spaces here
  (étale-local on `X` and `Y`, the formation of `R𝓗om` commuting with étale restriction).
* **Lemma 2.10** (`lem:rhom_tensor_morphism`): the isomorphism is natural in `K` and `M` as
  well (wave 10 has naturality in `L`).

Statements and proofs: `manuscripts/GL26/main.tex`.  Files: `Spaces/InternalHom/` (new files;
add to its `Inputs.lean` only tagged AxiomMath inputs), import lines in `Spaces.lean` and
`Spaces/Audit.lean`, `scripts/axiommath/spaces-imports.txt` for definition modules.  If an
AxiomMath result you need lies in a module whose closure contains `MilnorPatching.Relative`,
stop and report.  Commit verified pieces as you go.  Seven verification steps; `lake build
Spaces`; `scripts/check_statements.sh --spaces`.  Do not run `lake build SpacesVerified`.
