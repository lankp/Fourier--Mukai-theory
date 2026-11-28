## Your task: `wave11/gl26-quasi-perfect` (Opus, effort: high)

Goal: GL26 §5's results on quasi-perfect objects over algebraic spaces, unconditionally
(AxiomMath theorems as tagged inputs only), on `Spaces/RelativePerfect.lean` (`IsQuasiPerfect`,
`IsRelativelyPerfect`) and wave 10's `RHom` (`Spaces/InternalHom/`) and `f^×`
(`Spaces/Duality/`):

* **Lemma 5.3** (`lem:quasi-perfect_bounded`): the three claims (tensoring with `Perf(Y)`;
  `RHom(E, f^× 𝒪_X) ∈ D^b_qc(Y)` for pseudo-coherent `E`; pseudo-coherence in the Noetherian case
  when `f^× 𝒪_X` has coherent cohomology);
* **Lemma 5.7** (`lem:f_perf_implies_perf_preserved`): for proper `f` of Noetherian spaces and
  pseudo-coherent `E`, `f`-perfect implies `f`-quasi-perfect;
* **Lemma 5.9** (`lem:neeman23lem5_3`): `Rf_* RHom(E, f^× P) ≅ RHom(Rf_* E, P)`.

Statements and proofs: `manuscripts/GL26/main.tex`.  Files: `Spaces/QuasiPerfect/` (new; own
`Inputs.lean`, `NonVacuity.lean`), plus import lines in `Spaces.lean` and `Spaces/Audit.lean`,
and `scripts/axiommath/spaces-imports.txt` for definition modules.  If wave 10's `RHom` or `f^×`
is not merged in the form you need, stop and report rather than redefine it.  Commit verified
pieces as you go.  Seven verification steps; `lake build Spaces`; `scripts/check_statements.sh
--spaces`.  Do not run `lake build SpacesVerified`.
