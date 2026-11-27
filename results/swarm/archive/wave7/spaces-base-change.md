## Your task: `wave7/spaces-base-change` (effort: high)

Goal: **GL26 §7 and Lemmas 6.11, 10.1 for the base-change maps of algebraic spaces.**  The
tree proves Lemmas 7.12, 7.17 over abstract pull/push data (`Prelim/BaseChangeMates.lean`,
`PullPushData`) and 6.11, 10.1 over an abstract base-change cube (`Scheme/FMCube.lean`)
from Stacks 08IR, 08IN/08EU as fields.  Instantiate both for `Spaces`:

1. `PullPushData` for algebraic spaces from `Spaces.pull`, `Spaces.push`, `Lf^* ⊣ Rf_*`
   (07A6) and the composition isos `L(gf)^* ≅ Lf^*Lg^*` (0D6D), `R(gf)_* ≅ Rg_*Rf_*` (0D6E),
   all in the import list (`Spaces/AxiomMathInputs.lean`, docstring).  Check the coherence
   fields against AxiomMath (pseudofunctoriality); a coherence AxiomMath proves becomes a
   tagged input.  Then GL26 Lemmas 7.12 and 7.17 (TeX labels in `results/COVERAGE.md`) hold
   for spaces with no named non-Stacks input: this removes `DerivedPseudofunctorInput`
   (Lipman 3.6.2, GL26 Lemma 2.13) for spaces.
2. The base-change cube of Setup 2.20 for spaces, with flat (tor-independent) base change
   and the projection formula as tagged inputs from AxiomMath
   (`Spaces/SmallEtaleDerivedTorIndependentBaseChange`, `Spaces/SmallEtaleProjectionFormulaSnd`
   and neighbours, Stacks 08IR, 08IN, 08EU); then Lemmas 6.11, 10.1 over spaces.

Branch `wave7/spaces-base-change` from `origin/formalization`.  Files: `Spaces/BaseChange/*.lean`
(namespace `RelativeFM.Spaces.BaseChange`), `Spaces/BaseChange/Inputs.lean`, `Spaces.lean`
(one import line), `Spaces/Audit.lean` (append only).  Non-vacuity: the identity square, or
any square of affine schemes.  Report every tagged input you add.  Seven verification steps
for `lake build Spaces`; default build and both statement checks unaffected.
