/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.Statements.Notions
import Spaces.Statements.Main
import Spaces.Statements.Inputs
import Spaces.Statements.NonVacuity

/-!
# GL26's headline results stated over algebraic spaces

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), current
manuscript.  The headline results are stated as `Prop`s over the algebraic-space layer
(`Spaces/`, on AxiomMath/Stacks' definitions), with the paper's hypotheses, in namespace
`RelativeFM.Spaces.Statements`.  They are *targets*: nothing here proves them.  They supersede
the interface targets of `FourierMukai/Paper/Statements.lean`, whose abstract `FMSetup` and
`MorphismContext` do not tie the functors to any geometry (`Paper/InterfaceAudit.lean`) and
several of which carry `True` placeholder hypotheses.

* `Spaces/Statements/Notions.lean`: the vocabulary (Noetherian, proper, flat, finite type,
  quasi-affine; `|X|`, closed points, representatives; the cube of Setup 2.20, `L(t')^*K`,
  `Φ_{L(t')^*K}`; "fully faithful / an equivalence on `D_qc`, `D^b_coh`"; `fm(K)`, `FM(K)`).
* `Spaces/Statements/Main.lean`: the statements.
* `Spaces/Statements/Inputs.lean`, `Spaces/Statements/NonVacuity.lean`: non-vacuity of every
  hypothesis (CLAUDE.md step 5), with five tagged AxiomMath inputs used only there.

Each statement takes the base `(B, S, hS)` explicitly and `hZ : B.Contains (⊤_ Scheme)` (needed
by AxiomMath's notion of Noetherian algebraic space; always satisfied, AxiomMath's
`BigFppfSite.contains_terminal`).  GL26's base algebraic space is `S'`.

## The statements

| GL26 result | TeX label | Lean name | supersedes (`Paper/Statements.lean`) | gap |
|---|---|---|---|---|
| Theorem 1.2 (= Thm 12.9; `fm` clause = Thm 12.3 + Cor 12.4) | `thm:fm_locus` | `theorem_1_2Statement` | `theorem_1_2_open`, `theorem_1_2_baseChange` | none |
| Theorem 12.9 | `thm:fm_locus_weak_approx` | `theorem_12_9Statement` | `theorem_1_2_open`, `theorem_1_2_baseChange` | none |
| Corollary 12.4 | `cor:deform` | `corollary_12_4Statement` | `theorem_1_2_baseChange` (relatively perfect case) | none |
| Theorem 1.3 (= Props 6.2 + 6.8) | `thm:stacky_all_coincide` | `theorem_1_3Statement` | `theorem_1_3` | none |
| Theorem 1.6 | `introthm:descent_ascent` | `theorem_1_6Statement` | `theorem_1_6` | none |
| Theorem 10.13 | `thm:descent_ascent` | `theorem_10_13Statement` | `theorem_1_6` | none |
| Corollary 6.18 | `cor:noetherian_base_change_for_relative_perfectness` | `corollary_6_18Statement` | `corollary_6_18` | none |
| Lemma 12.2 | `lem:independence_for_rep_with_ff_or_eq` | `lemma_12_2Statement` | `lemma_12_2` | none |
| Theorem 12.3 | `thm:openness_for_equivalence_fullfaithful_dbcoh` | `theorem_12_3Statement` | `theorem_12_3` | none |
| Theorem 1.7 (= Prop 11.4) | `thm:elliptic_fibration_autoequivalence` | **not stated** | `theorem_1_7` (not superseded) | needs AxiomMath definitions outside the import list (Gorenstein morphisms of spaces, genus, geometric integrality of fibres, the ideal sheaf of the diagonal) |

"none" means: hypotheses and conclusion as in the manuscript, read through the conventions of
`Notions.lean` (AxiomMath's model of `|X|` and of its representatives; "on `D_qc`" and "on
`D^b_coh`" as restriction to full subcategories; Setup 2.20's unused `T` dropped where a result
does not mention it).  Each statement's docstring repeats its reading.
-/
