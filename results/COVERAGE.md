# Coverage: every numbered result of GL26 and LP26 against the tree

One row per numbered result (theorem, proposition, corollary, lemma, definition,
setup) of each paper, with the two remarks that the tree uses.  Numbers are those
of the **current manuscripts** (GL26 `main.tex` of 25 November 2026, LP26
`main.tex`, neither yet on arXiv; not stored in this public repository: ask the maintainer), which LaTeX would print; TeX labels are given
because they are stable across versions.

This map was produced by reading module headers, docstrings and the `results/`
ledgers, and by searching the tree for every label and number.  It records what
the tree **claims**.  Whether each claim compiles is checked separately by the
build (`lake build`, `scripts/check_statements.sh`); see the verification note at
the end.

## Status codes

| code | meaning |
|---|---|
| **P** | proved, `sorry`-free, with no hypotheses beyond the paper's (possibly in a categorical form of the statement) |
| **C** | proved, conditional on named inputs carried as structure fields or hypotheses |
| **H** | not proved; appears only as an interface field or hypothesis that other results consume |
| **T** | stated as a target (`...Statement : Prop` in `Scheme/Statements.lean`, or `sorry` in `Paper/Statements.lean`), not proved |
| **D** | a definition or setup, rendered as a Lean definition or structure |
| — | absent from the tree |

## GL26, *Relative Fourier–Mukai theory for algebraic spaces*

### Summary

| | P | C | H | T | D | — | total |
|---|---:|---:|---:|---:|---:|---:|---:|
| theorems, propositions, corollaries, lemmas | 16 | 7 | 15 | 14 | – | 64 | 116 |
| definitions, setups, lemma-definitions | 1 | – | – | – | 13 | 5 | 19 |

Sixteen results are proved outright (Lemmas 2.3, 2.5, 7.2, 7.4, 7.6, 7.9, 7.11, 7.12,
7.17, 10.2, B.2, B.4, B.5, B.7, B.10, C.1; 10.2 over abstract data; 7.12 and 7.17 over abstract pseudofunctor data; 7.4, 7.6, 7.9 and C.1 (2) in `Cat`), as is Lemma-Definition 7.10 (in `Cat`), five conditionally (Lemmas 2.4, 2.25, 2.26, 5.4, and A.4 in the
affine case).  Lemma 2.5 was briefly vacuous on 25 November 2026 and has been re-proved (see its row).  The 14 target rows are 10 distinct targets (1.2 = 12.9, 1.3 = 6.2 + 6.8,
1.6 = 10.13, 1.7 = 11.4), none proved.  Sections 3, 4, 6, 8, 9, 10, 11 and 12
have no proved result: everything there is a target, an interface field, or
absent.

### §1 Introduction

| # | label | status | where | note |
|---|---|---|---|---|
| Question 1.1 | `question:main` | – | | not a result; the repo's "GL26 Theorem 1.1" is LP26 Theorem 1.1, see below |
| Thm 1.2 | `thm:fm_locus` | T | `Scheme/Statements.lean` `theorem_1_2_openStatement`, `theorem_1_2_baseChangeStatement`; `Paper/Statements.lean` | `Scheme/GL26Theorem12Reduction.lean` proves the two assembly steps from named residues (Remark 2.7 preservation, canonical representative, openness of the relatively perfect locus, Thm 12.3) |
| Thm 1.3 | `thm:stacky_all_coincide` | T | `theorem_1_3Statement` | = Prop 6.2 + Prop 6.8 |
| Cor 1.4 | `cor:preservation` | — | | |
| Thm 1.5 | `introthm:base_change` | T (one direction) | via `corollary_6_18Statement` | the converse needs Thm 6.16, which is not stated |
| Thm 1.6 | `introthm:descent_ascent` | T | `theorem_1_6Statement` | = Thm 10.13 |
| Thm 1.7 | `thm:elliptic_fibration_autoequivalence` | T | `theorem_1_7Statement` | = Prop 11.4 |

### §2 Preliminaries

| # | label | status | where | note |
|---|---|---|---|---|
| Lem 2.3 | `lem:subcat_wher_nat_is_iso_is_closed_under_coprod_and_cofacts` | P | `Prelim/Coproduct.lean` (1), `Prelim/Triangulated.lean` + `Prelim/Thickness.lean` (2), `Prelim/EssentiallyDense.lean` (3) | (1) assumes only the one coproduct used |
| Lem 2.4 | `lem:localizing_iff_cpt_gen` | C (Stacks only) | `Prelim/Lemma24.lean` (`lemma_2_4`) | from the tagged Stacks input `Tag09SN` (`Prelim/Stacks09SN.lean`, AxiomMath's `exists_isHomotopyColimit_of_compactlyGenerated`) and `IsCompactAb G`; ⟨G⟩‾ = T ⇒ G generates is unconditional; "T compactly generated" not needed; Neeman's Bousfield localization no longer used |
| Lem 2.5 | `lem:equivalence_or_fully_faithful_via_compacts` | P | `Prelim/Lemma25.lean` (`lemma_2_5`), with "singly compactly generated" = `IsCompactAb G` ∧ localizing generation; `lemma_2_5_of_tag09SN` in the paper's zero-detection form, from 09SN.  Re-rendered 25 Nov 2026 after the earlier version was found vacuous (`Prelim/CompactnessAudit.lean`); hypotheses shown satisfiable (`singlyCompactlyGenerated_smallRingObject`) |
| Rmk 2.6 | `rmk:equivalences_induced` | H | `Scheme/Inputs.lean`, `GL26Theorem12Reduction.lean` | weak approximability (Neeman 3.2), coherence (Neeman), CHNS Thm B as proposition parameters |
| Rmk 2.7 | `rem:rel_perfect_is_free` | H | `TransformPreservationForcesRelativePerfect` | |
| Lem 2.8 | `lem:factor_residual_gerbes` | — | | algebraic spaces |
| Lem 2.9 | `lem:support_is_cohomological_for_finite_type_cohomology` | — | | |
| Lem 2.10 | `lem:rhom_tensor_morphism` | H | `Scheme/Duality.lean`, `Scheme/StacksInput.lean` | Stacks 08JJ |
| Lem 2.11 | `lem:internal_hom` | — | | |
| Lem 2.13 | `lem:spacey_Lipman_Hashimoto` | — | | |
| Lem 2.14 | `lem:faithfully_flat_is_conservative` | H | `CoverComparisonInput` (`Scheme/Lemma54.lean`) | part of the cover square |
| Lem 2.15 | `lem:zero_object_via_covers` | — | | possibly inside the Lemma 5.4 cover input; not named |
| Lem 2.16 | `lem:gortz_wedhorn_internal_hom` | H | `Scheme/Duality.lean` | |
| Lem 2.18 | `lem:quasi-affine_via_diagonal` | — | | |
| Lem 2.19 | `lem:quasi_affine_diagonal` | — | | |
| Setup 2.20 | `setup:fm_cube_pullback` | D | `FMSetup`, `BaseChange` (`Scheme/Statements.lean`, `Paper/DerivedSetup.lean`) | |
| Lem 2.21 | `lem:neeman186` | H | `Scheme/Duality.lean` | four invertibility cases as fields |
| Lem 2.22 | `lem:neeman187` | H | `Scheme/Duality.lean` | |
| Lem 2.23 | `lem:neeman188` | H | `Scheme/Duality.lean` | bounded-below and finite-tor cases |
| Lem 2.24 | `lem:neeman189` | H | `Scheme/Duality.lean` | |
| Lem 2.25 | `lem:funct_on_kernel` | C | `Scheme/DiagonalIdentity.lean`, `lemma_2_25Statement_proved` | from 08IN, the tensor unit and `f'ᵢ ∘ Δ = 𝟙` (`DiagonalIdentityData`); the bare interface form is refuted in `GL26OtherTargets.lean` |
| Lem 2.26 | `lem:convolution` | C | `Scheme/AffineConvolution.lean`, `lemma_2_26Statement_of_correction` | from `CorrectedConvolutionData` (07A4, 08IN, 08IR, 0D6D, 0D6E) |

### §3 Characterization of perfectness

| # | label | status | note |
|---|---|---|---|
| Lem 3.1 | `lem:23` | — | |
| Lem 3.2 | `lem:quasi-affine_is_conservative` | H | residue of Lemma 5.4 (`Rh₂*` conservative) |
| Lem 3.3 | `lem:34` | — | |
| Lem 3.4 | `lem:45` | — | |
| Lem 3.5 | `lem:perf_pullback_characterize` | — | |
| Lem 3.6 | `lem:61` | — | |
| Lem 3.7 | `lem:pseudocoherence_affine_faithfully_flat_cover` | — | |
| Lem 3.8 | `lem:pullback_is_perfect_iff_for_some_or_all_in_equivalence_class` | — | |
| Lem 3.9 | `lem:pullback_is_perfect_iff_closed_pt` | — | |
| Def 3.10 | | — | |
| Prop 3.12 | `prop:perfectness` | — | cited in a docstring only |

### §4 Relatively perfect complexes

| # | label | status | note |
|---|---|---|---|
| Def 4.1 | `def:relative_perf_stacks` | D (over algebraic spaces: `Spaces/RelativePerfect.lean` `IsRelativelyPerfect`, wave 6) | `IsRelativelyPerfect`, over the interface |
| Lem 4.3 | `lem:finite_coh_dim_implies_restriction_to_bounded` | — | |
| Lem 4.4 | `lem:quasi_affine_reflects_boundedness` | — | |
| Prop 4.5 | `prop:relative_perfect_smooth_locality_ascent` | — | |
| Prop 4.6 | `prop:relative_perfect_smooth_locality_descent` | — | |
| Cor 4.7 | `cor:smooth_locally_f_perfect_implies_f_perfect` | — | |
| Thm 4.8 | `thm:relative_perf_iff_smooth_locally` | — | |

### §5 Relatively quasi-perfect complexes

| # | label | status | note |
|---|---|---|---|
| Def 5.1 | `def:quasi_perf` | D (over algebraic spaces: `Spaces/RelativePerfect.lean` `IsQuasiPerfect`, wave 6) | `IsQuasiPerfect` |
| Lem 5.3 | `lem:quasi-perfect_bounded` | H | `Scheme/StacksInput.lean` |
| Lem 5.4 | `lem:neeman2023cor5_10` | C | `Scheme/Lemma54.lean`: the cover argument in six-functor form; residue is the cover square (flat base change, conservativity, perfect/compact calculus) |
| Prop 5.6 | `prop:preservation_of_perfect` | — | a lemma in the arXiv version |
| Lem 5.7 | `lem:f_perf_implies_perf_preserved` | — | |
| Lem 5.9 | `lem:neeman23lem5_3` | — | |
| Lem 5.10 | `lem:Ballard_relative_perf_implies_dual_is_such` | — | |
| Lem 5.11 | `lem:f-quasi-perfect_via_small_coproducts` | — | |
| Prop 5.12 | `prop:stacky_f_perf_gives_iso_between_uppershriek_and_pullback_up_to_tensor` | — | |
| Lem 5.13 | `lem:zero_iff_pushforward_zero` | — | |
| Lem 5.14 | `lem:upper_shriek_preserves_Dplusqc` | — | |
| Lem 5.15 | `lem:upper_shriek_coherent_cohomology` | — | |
| Prop 5.16 | `prop:ballard_quasi_perfect_involution` | — | |
| Thm 5.18 | `thm:adjoint_dqc_for_f-quasi-perfect` | — | |

### §6 Properness and base change

| # | label | status | note |
|---|---|---|---|
| Lem 6.1 | `lem:boundedness_via_coaisle` | — | cited in a docstring only |
| Prop 6.2 | `prop:stacky_all_coincide` | T | half of `theorem_1_3Statement` |
| Lem 6.5 | `lem:perfectness_via_coherence` | — | |
| Lem 6.7 | `lem:perfect_locus_open` | — | |
| Prop 6.8 | `prop:preservation_of_dbcoh` | T | half of `theorem_1_3Statement` |
| Lem 6.10 | `lem:fm_cube_locally_finite_tor_dimension` | — | |
| Lem 6.11 | `lem:fm_cube_flat_base_change_natural_isomorphism` | C (Stacks only) | `FMCube.lemma_6_11` (`Scheme/FMCube.lean`), six-functor form over the cube of Setup 2.20, from flat base change (Stacks 08IR) |
| Lem 6.12 | `lem:pushforward_coherent_support_is_image` | — | |
| Lem 6.13 | `lem:reflecting_bounded_pseudocoherence_perfectness_trivial_case` | — | |
| Lem 6.14 | `lem:induced_dbcoh_perf_preservation_upon_pullback_with_t_affine` | — | |
| Prop 6.15 | `prop:reflecting_bounded_pseudocoherence_perfectness` | — | |
| Thm 6.16 | `thm:bounded_pseudocoherence_perfectness_faithfully_flat_affine` | — | |
| Cor 6.18 | `cor:noetherian_base_change_for_relative_perfectness` | T | `corollary_6_18Statement` |

### §7 Mates in geometry

| # | label | status | note |
|---|---|---|---|
| Setup 7.1 | `setup:mates` | D | Mathlib adjunctions |
| Lem 7.2 | `lem:mates_bijection` | P | (2): `Prelim/Mates.lean`, definitionally Mathlib's `mateEquiv`; (1), the Hom-set square: `mates_hom_square` (`Prelim/MatesCalculus.lean`) |
| Def 7.3 | | D | `mate` in `Prelim/Mates.lean` |
| Lem 7.4 | `lem:morph_adj` | P (in `Cat`) | `lemma_7_4` (`Prelim/MatesCalculus.lean`), all four conditions as a `List.TFAE` |
| Lem 7.6 | `lem:taking_conjugates_is_taking_mates_twice` | P (in `Cat`) | `lemma_7_6`; it is Mathlib's `iterated_mateEquiv_conjugateEquiv` |
| Def 7.7 | `def:mates_double_cat` | — | |
| Lem 7.8 | `lem:mates_double_cat_iso` | — | `Prelim/Mates.lean` cites "Lemma 7.8(2)" for what is now 7.11 |
| Lem 7.9 | `lem:conjugates_are_functorial` | P (in `Cat`) | `lemma_7_9_id`, `lemma_7_9_comp`, from Mathlib's `conjugateEquiv_id`/`_comp`; does not use 7.8 |
| Lem-Def 7.10 | `def:adj_equiv` | P (in `Cat`) | `Prelim/AdjunctionUnits.lean` (`lemmaDef_7_10`); the footnote's "representably fully faithful ⇔ fully faithful" is proved (`representablyFullyFaithful_iff`) |
| Lem 7.11 | `lem:when_mate_correspondence_preserves_isos` | P | `isIso_mate`, `isIso_of_isIso_mate`, `isIso_mate_iff` |
| Lem 7.12 | `lem:pseudofunctoriality_isos_are_conjugate` | P (abstract) | `PullPushData.lemma_7_12` (`Prelim/BaseChangeMates.lean`), over abstract pseudofunctor data whose structure isos are conjugate (Lipman 3.6.2 / Lemma 2.13 as fields); wired into `Scheme/Duality.lean` by `Scheme/DualityMates.lean` (`DerivedPseudofunctorInput.lemma_7_12`; the coherence field `pushConjugate` is now proved for squares from that input) |
| Lem-Def 7.13 | `def:upper_star_lower_star_bc` | D | `theta`, `thetaLeftMate`, `lemma_7_13` (the two descriptions agree) in `Prelim/BaseChangeMates.lean`; `theta` in `Scheme/Duality.lean` |
| Def 7.14 | `def:lower_star_upper_cross_bc` | D | `xi`, with `isIso_xi` ⇔ `isIso_theta` (`Prelim/BaseChangeMates.lean`) |
| Lem-Def 7.15 | `def:upper_star_upper_cross_bc` | D | `beta`, `betaLeftMate`, `lemma_7_15` (the two descriptions agree) (`Prelim/BaseChangeMates.lean`) |
| Lem 7.17 | `lem:base_change_mates_pasting` | P (abstract) | `lemma_7_17_theta`, `lemma_7_17_xi` (`Prelim/BaseChangeMates.lean`), over the same abstract data; without Lemma 7.8, via Mathlib's `mateEquiv_vcomp`; for `Duality.lean`'s maps: `DerivedPseudofunctorInput.lemma_7_17_theta`, `lemma_7_17_lowerStarUpperCross` |
| Lem 7.19 | `lem:etale_presen_bc` | — | algebraic spaces |
| Lem 7.20 | `lem:characterize_tor-independence` | — | |
| Lem 7.21 | `lem:tor-independence_and_beta_pasting` | — | |

### §8 Derived reflexivity, §9 Base change for adjoints

| # | label | status | note |
|---|---|---|---|
| Def 8.1 | `def:homologically_reflexive` | — | |
| Lem 8.3 | `lem:derived_reflexive_by_covers` | — | |
| Lem 8.5 | `lem:involution_for_f_perfect` | — | |
| Lem 9.1 | `lem:base_change_relative_formula` | H | field of `DerivedMorphismData` |
| Lem 9.2 | `lem:base_change_relative_dualizing_complex` | — | |
| Prop 9.3 | `prop:right_adjoint_pullback` | — | |
| Cor 9.4 | `cor:relatively_perfect_y2_implies_right_adjoint_restrict_to_dbcoh` | — | |
| Lem 9.5 | `lem:left_adjoint` | — | |
| Prop 9.6 | `prop:left_adjoint_pullback` | — | |

### §10 Full faithfulness and equivalences, §11 Elliptic fibrations

| # | label | status | note |
|---|---|---|---|
| Lem 10.1 | `lem:fm_cube_pullback_natural_isomorphism` | C (Stacks only) | `FMCube.lemma_10_1`, from flat base change (08IR) and the projection formula (08EU/08IN) |
| Lem 10.2 | `lem:integral_transform_is_morphism_of_adjoints` | P (abstract) | `FMCube.lemma_10_2`: `mateEquiv (adj t₁) (adj t₂) α^K = β^K`, with no input, over abstract pull/push/tensor data |
| Prop 10.5 | `prop:pullbacks_is_a_morphism_of_adjoint_integral_transforms` | — | cited in a docstring only |
| Lem 10.9 | `lem:equivalences_induced` | H | `Scheme/Inputs.lean` |
| Prop 10.11 | `prop:descent` | — | |
| Prop 10.12 | `prop:ascending` | — | |
| Thm 10.13 | `thm:descent_ascent` | T | `theorem_1_6Statement`; for a separated base this is GLMP25 Thm 6.11 |
| Lem 11.1 | `lem:ideal_sheaf_relatively_perfect` | — | used as a hypothesis shape in `theorem_1_7Statement` |
| Prop 11.4 | `prop:derived_pullback_ideal_sheaf` | T | `theorem_1_7Statement` |

### §12 Openness of loci

| # | label | status | note |
|---|---|---|---|
| Def 12.1 | `def:fm_locus` | D | `FM`, `fm` |
| Lem 12.2 | `lem:independence_for_rep_with_ff_or_eq` | T | `lemma_12_2Statement` |
| Thm 12.3 | `thm:openness_for_equivalence_fullfaithful_dbcoh` | T | `theorem_12_3Statement` |
| Cor 12.4 | `cor:deform` | T | `corollary_12_4Statement` |
| Cor 12.5 | `cor:FM_partners_detects_surjectivity` | — | |
| Lem 12.7 | | — | |
| Prop 12.8 | `prop:relatively_perfect_locus` | H | residue of `GL26Theorem12Reduction.lean` (openness of `CanonicalRelativePerfectLocus`) |
| Thm 12.9 | `thm:fm_locus_weak_approx` | T | = Thm 1.2 |

### Appendices

| # | label | status | note |
|---|---|---|---|
| Lem A.1 | `lem:BNP_weak_version_for_glueing` | H | `Scheme/Inputs.lean` |
| Lem A.2 | `lem:support_for_pullback` | — | |
| Lem A.3 | `lem:support_for_pushforward` | — | |
| Lem A.4 | `lem:spacey_recollement` | C (affine; Stacks only) | `Scheme/AffineJUpperConstruction.lean` (`affineRecollementInputOfStacks0E55`): all fields of the affine recollement, from Stacks 0E55; unconditional when coextension of scalars is right exact (`affineRecollementInputOfExactCoextension`); `jUpper` is a chosen cone, isomorphic to `RHom(RΓ_Z A, -)` by uniqueness of adjoints (not formalized) |
| Lem A.6 | `lem:etale_nbhd_preferred_class_equivalences` | — | |
| Lem A.7 | `lem:pullback_compact_generator` | — | |
| Lem A.8 | `lem:etale_nbhd_preferred_class` | H | `Scheme/Inputs.lean` |
| Lem A.9 | `lem:preferred_eq_class` | H | `Scheme/Inputs.lean` |
| Def B.1 | `def:cat_with_trans` | D | Mathlib's `HasShift C ℤ` and `Functor.CommShift` stand in |
| Lem B.2 | `lem:trans_is_2-cat` | P | `Prelim/TransTwoCategory.lean`: `Trans.instBicategory` (strict, `Trans.instStrict`), `Trans.forget : StrictPseudofunctor TransCat Cat`, `lemma_B2_faithful`, `lemma_B2_unique` (the 2-cell data is determined by lying over `Cat`); translations are endofunctors (the paper's autoequivalences form a full sub-bicategory with the same structure) |
| Def B.3 | | — | |
| Lem B.4 | `lem:equiv_transadj` | P | `Trans.lemma_B4` (`Prelim/TransTwoCategory.lean`), all five conditions, (5) as a `Bicategory.Adjunction` in `Trans` (no deviation); universe-polymorphic unit/counit form `Trans.lemma_B4_unitCounit` (`Prelim/AppendixB.lean`) |
| Lem B.5 | `lem:adj_and_equiv_in_trans` | P | `Trans.lemma_B5_existsUnique` (T, T′ autoequivalences, as in the paper), `Trans.lemma_B5_equivalence`; left-adjoint variant not done |
| Def B.6 | `def:trinat_trans` | D | `Trinatural` (`Prelim/Triangulated.lean`) |
| Lem B.7 | `lem:transnat_is_trinat` | P | `lemma_B7`, `lemma_B7_natTrans` (also ⇔ Mathlib's `NatTrans.CommShift` ⇔ `RelativeFM.Trinatural`); triangulatedness of F, G not needed |
| Def B.8 | `def:triang` | D | Mathlib's pretriangulated categories and `Functor.IsTriangulated` |
| Def B.9 | | D | `Prelim/Triangulated.lean` cites "B.9" and "B.11" |
| Lem B.10 | `lem:triadjoint_iff_adjoint` | P | `lemma_B10_exists`, `lemma_B10_unique` (stronger: uniqueness of the whole `CommShift ℤ` from trinaturality of the unit), `lemma_B10_equivalence`; the manuscript's "(G,ζ) ⊣ (F,ξ)" is a typo for (F,ξ) ⊣ (G,ζ), confirmed by the author |
| Lem C.1 | `cmp:lem:units` | P | `Prelim/AdjunctionUnits.lean` (`lemma_C_1`, `Adjunction.twist`): (1) in any bicategory (`Bicategorical.twist`), (2) in `Cat`; the Aut(G)-torsor half of the remark after it is proved; transfer to `Triang` not proved |
| Def C.3 | `cmp:def:induced` | — | |

## LP26, *Gluing weak approximability along recollements*

All of §2–§4 and Theorem 1.1 are proved, scheme-agnostically, in `WeakApprox/`.
The geometric §5 is not; the tree records it in `results/WEAK_APPROX.md`.

| # | label | status | where / note |
|---|---|---|---|
| Thm 1.1 | `thm:glueing_weak_approx` | P | **with exactly the paper's hypotheses and no Stacks hypothesis**: `Spaces/Stacks/Corollaries.lean` `RelativeFM.Spaces.Stacks.theorem_1_1` (09SR proved from AxiomMath, wave 6); before that, `WeakApprox/Theorem11Paper.lean` `PaperHypothesesW6.theorem_1_1_paper` (pinned; only Stacks 09SR assumed; wave 6), from `PaperSetupMainMinimal.theorem_1_1`; compactly generated `t`-structures and BNP Cor 3.10(1) proved; non-vacuous (`Theorem11PaperNonVacuity`). The large-model affine endpoints are proved vacuous (`RefuteLargeCoproducts`) |
| Cor 1.2 | `cor:weak_approx_spaces` | H (affine base: P in the module model) | the affine base case = Neeman 2024 Thm 3.2(iv) for `Spec A`, `Z = V(I)`, `I` f.g., is proved with **no input** in `D(A-Mod)`: `NeemanAffineSupport.satisfiesPaperWA_of_fg` (wave 5, pinned); transport to AxiomMath's `D_qc,Z(Spec A)` and the induction over qcqs schemes/spaces are open |
| Def 2.1 | `def:weak_approx` | D | `WeakApproximationData`, `PaperWeakApproximationData` |
| Lem 3.1 | `lem:closures` | P | `Basic`, `Closure`, `Shift`, `Functoriality` |
| Lem 3.3 | `lem:aisle` | P | `Aisle` |
| Lem 3.4 | `lem:iterate` | P | `Lemma34`, `PaperLemma34M2` |
| Lem 3.5 | `lem:hom_vanishing` | P | `Lemma35`, `HomVanishing` |
| Setup 4.1 | `setup:recollement` | D | `Recollement` |
| Lem 4.2 | `lem:glued` | P | `Lemma42` |
| Lem 4.3 | `lem:normalize` | P | `Lemma43`, `Lemma4323`, `Lemma433TStructure` |
| Setup 4.4 | `setup:standing` | D | `Setup44`, `Setup44Minimal`, `PaperSetup44M2` |
| Def 4.5 | `def:lift` | D | `PLift` |
| Lem 4.6 | `lem:onecell` | P | `Lemma46`, `PaperLemma46M2` |
| Prop 4.8 | `prop:closure` | P | `Proposition48`, `Proposition48Paper` |
| Def 5.3 | `def:wa_spaces` | — | |
| Lem 5.5 | `lem:compact_ext_vanishing` | H | its categorical role is `WeakApprox/CompactVanishing.lean`; the `D_qc` statement is not proved |
| Lem 5.6 | `lem:perf_vanishing` | H | `Scheme/Inputs.lean` |
| Lem 5.7 | `lem:qcqs_open_pushforward` | — | |
| Prop 5.8 | `prop:A8` | — | the affine recollement (`AffineRecollement.lean`) is the input it uses |
| Lem 5.9 | `lem:characterize_T-_c` | — | |

## Numbering that disagreed with the current GL26 manuscript

Corrected on 25 November 2026: "GL26 Theorem 1.1" → LP26 Theorem 1.1 (README,
`StatementCheck.lean`, `Scheme/Affine.lean`, `VERIFICATION.md`); Corollary 12.10 →
12.4 for `cor:deform`, including the rename `corollary_12_10Statement` →
`corollary_12_4Statement` (not pinned); Theorems 6.2 and 11.4 → Propositions; the
mates file's 7.1/7.8 → 7.2/7.11; Definition B.11 → B.9.  `results/REPORT.md` is a
historical report and keeps the numbering of the version it was written against.

## Verification of this map

Produced on 25 November 2026 from commit `f7d14c0`, by label and number search
plus module headers.  A row marked P or C repeats the tree's own claim, checked
only as far as the following build of that commit goes (Lean 4.33.1, Mathlib
`v4.33.1` oleans from `lake exe cache get`, 4 cores):

| check | outcome |
|---|---|
| `lake build` (FourierMukai, WeakApprox, StatementCheck) | exit 0, 4 min 23 s; no errors, linter warnings only |
| `declaration uses 'sorry'` in the build | 9, all in `FourierMukai/Paper/Statements.lean` |
| `lake env lean FourierMukai/Audit.lean` | 34 audited declarations: 25 depend only on `propext`, `Classical.choice`, `Quot.sound`; 9 on `sorryAx`, exactly the nine targets of `Paper/Statements.lean` |
| `scripts/check_statements.sh` | OK, 17 declarations match the baseline, none depends on `sorryAx` |

The proofs behind the P and C rows were not re-read for this map.
