## Your task: `wave10/gl26-conservativity` (Opus, effort: high)

Goal: GL26 §2–3 conservativity results over algebraic spaces, unconditionally (AxiomMath
theorems as tagged inputs only), with `pull`, `push`, `Dqc` of `Spaces/Functors.lean` and
`Spaces/Categories.lean`:

* **Lemma 2.14** (`lem:faithfully_flat_is_conservative`): for faithfully flat `f : Y ⟶ X`,
  `Lf^*` is conservative on `D_qc(X)`.
* **Lemma 2.15** (`lem:zero_object_via_covers`): for qcqs `X` and `E ∈ D_qc(X)`, the four
  conditions (1)–(4) are equivalent.
* **Lemma 2.18** (`lem:quasi-affine_via_diagonal`): as stated in the manuscript.
* **Lemma 3.2** (`lem:quasi-affine_is_conservative`): for quasi-affine `f` of qcqs spaces,
  `Rf_*` is conservative on `D_qc(Y)` (use `IsQuasiAffineHom` of `Spaces/Statements/Notions.lean`).

Read the statements and proofs in `manuscripts/GL26/main.tex`; follow the paper's proofs,
reducing to AxiomMath (flat pullback, étale/smooth covers, `Rf_*` for affine morphisms,
quasi-coherent cohomology) and to Mathlib.  Files: `Spaces/Conservative/` (new; its own
`Inputs.lean` and `NonVacuity.lean`), plus the import lines in `Spaces.lean` and
`Spaces/Audit.lean`.  Add definition modules you need to `scripts/axiommath/spaces-imports.txt`
(check with `scripts/axiommath/built.py`).  Commit verified pieces as you go (one lemma at a
time is fine).  Seven verification steps; `lake build Spaces`; `scripts/check_statements.sh
--spaces`.  Do not run `lake build SpacesVerified`.
