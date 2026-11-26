## Your task: `wave7/spaces-statements` (effort: high)

Goal: **state GL26's headline results over algebraic spaces**, faithfully, as `Prop`s on the
`Spaces` layer, so that they replace the interface targets of `FourierMukai/Paper/Statements.lean`
as the targets of the project.  Results (number and TeX label; `results/COVERAGE.md`):
Theorem 1.2 (1) = Theorem 12.9 (`thm:fm_locus_weak_approx`) and (2) = Corollary 12.4
(`cor:deform`), Theorem 1.3 = Propositions 6.2 + 6.8 (`thm:stacky_all_coincide`), Theorem 1.6 =
Theorem 10.13 (`thm:descent_ascent`), Theorem 1.7 = Proposition 11.4
(`thm:elliptic_fibration_autoequivalence`), Corollary 6.18
(`cor:noetherian_base_change_for_relative_perfectness`), Lemma 12.2
(`lem:independence_for_rep_with_ff_or_eq`), Theorem 12.3
(`thm:openness_for_equivalence_fullfaithful_dbcoh`).

The manuscript text is provided to this task **outside the repository** (its path is in your
task message).  Read the statements there.  Never copy TeX into the repository, a commit
message or any file you push; docstrings cite results by number and TeX label with at most a
short paraphrase.

Branch `wave7/spaces-statements` from `origin/formalization`.  Files: `Spaces/Statements/*.lean`
(namespace `RelativeFM.Spaces.Statements`), `Spaces.lean` (one import line), `Spaces/Audit.lean`
(append only).  Notions the statements need and `Spaces` lacks (proper, flat, the loci of
Theorem 1.2, base change of kernels, the relative product `Y₁ ×_S Y₂`, ...) go in
`Spaces/Statements/Notions.lean`, defined from AxiomMath's definitions (import list
`scripts/axiommath/spaces-imports.txt`; an AxiomMath definition module outside it: stop and
report).

1. Each result is a `def …Statement : Prop` (no `theorem` with `sorry`: the tree's only
   `sorry`s stay the nine of `Paper/Statements.lean`).  Hypotheses exactly the paper's; no
   `True` hypothesis; any difference (universe, a hypothesis made explicit, a convention) stated
   in the docstring.
2. Non-vacuity of every notion with hypotheses (step 5): an instance, e.g. the identity kernel
   over a point, `X = S`.
3. Where a statement is false as rendered, or the paper's statement needs a correction, stop and
   report rather than choose.
4. A table in the module docstring of `Spaces/Statements.lean` (or the first file): result,
   label, Lean name, the `Paper/Statements.lean` target it supersedes, and the gap if any.

Do not edit `Paper/Statements.lean`, the baselines or `results/*.md`; the orchestrator retires
the old targets and pins the new statements after checking them against the manuscript.
Verification: `lake build Spaces`, `scripts/check_statements.sh --spaces`, default `lake build`
and `scripts/check_statements.sh` unaffected; seven steps where they apply.
