## Your task: `wave7/spaces-affine-base` (effort: high)

Goal: the **base case of LP26 Corollary 1.2 over AxiomMath's model**: for a commutative ring
`A` and a finitely generated ideal `I`, `D_qc,V(I)(Spec A)` in the sense of `Spaces`
(`Spaces.DqcSupported` on the algebraic space of `Spec A`) is weakly approximable, with no
input beyond the AxiomMath theorems used (as tagged inputs, discharged at merge).  The tree proves this for `D_{V(I)}(A-Mod)` (`NeemanAffineSupport.satisfiesPaperWA_of_fg`,
wave 5); what is missing is the transport (`results/OPEN_INPUTS.md` row 5.1,
`AffineSupportedSchemeComparisonInput`).

Branch `wave7/spaces-affine-base` from `origin/formalization`.  Files: `Spaces/Affine/*.lean`
(namespace `RelativeFM.Spaces.Affine`), `Spaces/Affine/Inputs.lean` for tagged inputs,
`Spaces.lean` (one import line), `scripts/axiommath/spaces-imports.txt` (only definition
modules), `Spaces/Audit.lean` (append only).

1. Find in AxiomMath the equivalence `D(A-Mod) ≌ D_QCoh(Spec A)` (start from
   `StacksFrontier/AlgebraicGeometry/Spaces/AffineQuasicoherentDerivedEquivalence.lean` and
   Stacks 06Z0 / 0G9J in `results/AXIOMMATH_TAGS.md`), and the statement that it is
   triangulated and matches supports (cohomology supported on `V(I)` on both sides).  What
   is a theorem there becomes a tagged input in `Spaces/Affine/Inputs.lean`.
2. Construct the triangulated equivalence `D_{V(I)}(A-Mod) ≌ DqcSupported (Spec A) V(I)`
   and transport weak approximability (the tree has transport of `SatisfiesPaperWA` along
   triangulated equivalences; search `WeakApprox/` and `Scheme/` before writing one).
3. Headline: `**LP26 Corollary 1.2**, affine base` (TeX label from `results/COVERAGE.md`),
   conditional only on your tagged AxiomMath inputs.  Non-vacuity: `A = ℤ`, `I = (p)`.

Report every tagged input you add (tag, AxiomMath name, file), so the orchestrator can
discharge it.  The seven verification steps for `lake build Spaces`; default build and both
statement checks (`scripts/check_statements.sh`, `--spaces`) unaffected.
