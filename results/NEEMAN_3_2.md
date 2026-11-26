# Neeman 2024, Theorem 3.2: inventory and discharge

Neeman, *Bounded `t`-structures on the category of perfect complexes*, Acta Math.
233 (2024), **Theorem 3.2**, for `X` a qcqs scheme and `Z ⊆ X` closed with
quasi-compact complement, `T = D_qc,Z(X)`:

* **(i)** compact objects of `T` are the perfect complexes supported on `Z`;
* **(ii)** `T` has a single compact generator;
* **(iii)** the (restricted) standard `t`-structure is in the preferred equivalence class;
* **(iv)** `T` is weakly approximable.

Since 26 November 2026 the project does not assume any part of it (maintainer).
This file lists every place the tree carries its content, what consumes it, and
what was done about it on branch `wave5/neeman-3-2-inputs` (task brief:
`results/swarm/wave5/neeman-3-2-inputs.md`).  Part (iv) is the task of
`wave5/neeman-affine-support`.

## 1. What the manuscripts actually use

| paper | result (number, label) | part of Thm 3.2 | scope |
|---|---|---|---|
| LP26 | Corollary 1.2 (`cor:weak_approx_spaces`), proof | (iii) and (iv) | the schematic locus `W` of an algebraic space (a qcqs scheme), and affine `V` in elementary distinguished squares, with support |
| LP26 | §1, motivating example | (iv) | none (citation) |
| GL26 | Lemma A.9 (`lem:preferred_eq_class`) | (iii) | qcqs schemes (schematic locus), then 09IT induction |

Parts (i) and (ii) are not cited by either paper.  They enter only inside the proofs
of (iii)/(iv) and in the tree's affine instances of LP26 Theorem 1.1
(`thm:glueing_weak_approx`), whose abstract form (`WeakApprox/`) uses none of
Thm 3.2.  The whole of (iii)+(iv) for non-affine schemes and for spaces is to come
from AxiomMath/Stacks (09M8, 0AEC, 0AED, 09SR, 09IT; see §4).

## 2. Inventory

"Model": **L** = large-Hom `AffineD A = D(A-Mod)` (Hom in `Type (u+1)`), **S** =
small-Hom `SmallAffineD A H`, **Sch** = scheme model `D_qc,Z(X)`, **C** = an
abstract category.  "Path": whether a consumer lies on the path to a GL26/LP26
result as stated in the manuscripts.

| declaration | file | part | model | consumers | path? | status after this branch |
|---|---|---|---|---|---|---|
| `CompactPerfectInput A` (structure, `compact_iff_perfect`) | `Scheme/PerfectRing.lean` | (i) ⇔ | L | `AffineMain` (`ringObject_isClassicalGeneratorOnCompacts_of_compactPerfectInput`, `affineCompactHomZeroAtTop_of_compactPerfectInput`, `satisfiesWA_of_neemanCompactPerfectInput`, **`affine_theorem_1_1_neeman_only`** (pinned in `statement-baseline.txt`), `ringObject_compact_of_compactPerfectInput`); `PerfectField` (`compact_iff_dbcoh_of_input`); `PerfectRingStacks` (`compactToPerfectInput_of_compactPerfectInput`); `AffineNeemanEndpointM3` (`compactPerfectInput_of_regularModule_compact`, output); `Affine066S` (`compactPerfectInput_of_neemanModel`, output) | affine instance of LP26 Thm 1.1 only | **discharged**: `Neeman32Inputs.compactPerfectInput A h09` |
| `CompactToPerfectInput A` (directed half) | `Scheme/PerfectRingStacks.lean` | (i) ⇒ | L | `PerfectRingStacks.affine_theorem_1_1_of_compactToPerfectInput`, `AffineNeemanEndpointM3.affine_regularGenerator_package`, `RegularCompact.affine_regularGenerator_package` | affine instance of Thm 1.1 | **discharged**: `Neeman32Inputs.compactToPerfectInput` |
| `SmallNeemanCompactToPerfectInput A H` | `Scheme/SmallAffineAssembly.lean` | (i) ⇒ | S | `SmallAffineAssembly` (`smallCompactHomZeroAtTop_of_neeman`, `affine_theorem_1_1_small_neeman_only`, `affine_theorem_1_1_small_standard_neeman_only`); `AffineCompactness` (`NeemanM1.isCompactAb_iff_smallPerf_of_neeman`); `M6Transport` (`smallAffine_neeman_3_2_i`, `affine_theorem_1_1_small_standard_of_compactProof`; `smallNeemanCompactToPerfectInput_of_large`, output); `SmallCompactToPerfectM5` (output of `..._of_boundedFactorization`); `AffineNeemanEndpointM3` (`small_compact_iff_smallPerf`, `small_affine_regularGenerator_package`) | affine instance of Thm 1.1 | **discharged**: `Neeman32Inputs.smallNeemanCompactToPerfectInput A H h09` |
| `Neeman_3_2_i C P` (template `Prop`) | `Scheme/Inputs.lean` | (i) ⇔ | C | `M6Transport.smallAffine_neeman_3_2_i` (output); `Affine066S.NeemanAffineCompactModelInput` | no | proved for `Perf`/`SmallPerf` in both affine models: `Neeman32Inputs.affine_neeman_3_2_i`, `smallAffine_neeman_3_2_i` |
| `AffinePerfect.NeemanAffineCompactModelInput A` = `Neeman_3_2_i (AffineD A) (HasBoundedFiniteProjectiveModel A)` | `Scheme/Affine066S.lean` | (i) with literal bounded-projective "perfect" | L | `Affine066S` (066S retract closure, `compactPerfectInput_of_neemanModel`, ...), `M6Transport.neemanAffineCompactModelInput_*` (outputs) | no (the tree's `Perf` is the thick envelope; only 066S-comparison uses it) | **open, not needed**: needs Stacks 066S (retract closure of bounded finite-projective models); recommend leaving as dead code or deleting |
| `Neeman_3_2_ii C` = `∃ G, IsCompactAb G ∧ IsGenerator G` | `Scheme/Inputs.lean` | (ii) | C | none | no | **false rendering for rings**: `IsGenerator` (morphism separation) fails for `ℤ[0]` (`GeneratorCounterexampleM5`); the paper's (ii) is `IsCompactAb ∧ IsPaperGenerator`, proved affine: `Neeman32Inputs.affine_neeman_3_2_ii`, `NeemanM1.smallRingObject_isCompactAb` + `smallRingObject_isPaperGenerator`. Recommend deleting the template |
| `Neeman_3_2_iv C` = `SatisfiesWA C` | `Scheme/Inputs.lean` | (iv) | C | `SchemeWeakApproxStatement`, `SchemeNeemanConsumerAudit` (legacy bridges to `SatisfiesPaperWA`) | via the bridges only | not mine (`neeman-affine-support`); affine unsupported (iv) proved (`AffineNeemanEndpointM3.small_affine_neeman_3_2_iii_iv_base`, `RegularCompact.affine_satisfiesPaperWA`) |
| `NeemanPublishedWeakApproximation C` = `SatisfiesWA C` | `Scheme/WeakApprox.lean` | (iv) | C | `weakApprox_of_neeman` | no | legacy; recommend deleting |
| `OpenClosedCompletionW3.SupportedCategoryInput.neeman_3_2_iii` | `Scheme/OpenClosedCompletion.lean` | (iii) | Sch, `D_qc,Z(X)` | `compact_open_closed_glue_of_frameInput`, `neemanSupported_of_qcqs_of_frameInput` (Audit l.156) | **yes**: scheme (iv) by induction, toward LP26 Cor 1.2 / GL26 Lemma A.9 | **open, scheme level**: needs `D_qc,Z` of schemes; record for the AxiomMath tasks (0AEC + 09SR + 0AED give the compact generator and compacts; (iii) is GL26 Lemma A.9's input, proved affine unsupported: `RegularCompact.affine_standard_inPreferredClass`, `AffineNeemanEndpointM3.small_affine_inPreferredClass`) |
| `SupportedCategoryInput.tag_09SR`, `.compactHomZeroAtTop` | same | 09SR; (i)+09MB | Sch | same | yes | `tag_09SR` is an allowed Stacks input; `compactHomZeroAtTop` (Stacks 09MB with 0AED) is Stacks-level |
| scheme-level targets `NeemanWeakApproximability`, `NeemanSupportedWeakApproximability`, `NeemanSupportedCoverInput`, `SupportedNeemanOpenClosedCompletion`, `NeemanCompactSupportedCoverInput`, `DqcSupportedNeemanOpenClosed*` | `SchemeWeakApproxStatement`, `SchemeNeemanFiniteCoverAssembly`, `OpenClosedGlue`, `SchemeSupportedTwoOpen` | (iv) as a *conclusion*; (i)–(iii) inside completion packages | Sch | `neemanSupported_of_qcqs_*` | yes | (iv) is the goal there, not an input; the packages are Stacks/scheme inputs for `neeman-affine-support` and the AxiomMath tasks |
| ASSUMPTIONS rows 066S, 07LR/07LT, 09M1/0AED, 0AEC (marked N) | `results/ASSUMPTIONS.md` §4 | (i), (ii) | L, S | as above | — | 09M1/0AED and 07LT (compact ⇒ `Perf`) and 0AEC (affine generator) updated; 066S stays N (open, off-path) |

`Neeman_coherent_example_5_4` (`Scheme/Inputs.lean`) is Neeman's Example 5.4, not
Thm 3.2; it is outside this inventory.

## 3. What this branch proves (`FourierMukai/Scheme/Neeman32Inputs.lean`)

Route: **Ravenel–Neeman via Stacks 09SR**, the allowed tagged input, as the
existing `Prop` `OpenClosedCompletionW3.Tag09SRPaper` (AxiomMath/Stacks
`CategoryTheory.Pretriangulated.isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated`).
In `SmallAffineD A H` its antecedents are proved: `u`-small coproducts
(`smallAffineHasCoproducts`), `A[0]` compact (`NeemanM1.smallRingObject_isCompactAb`),
`A[0]` zero-detecting (`NeemanGeneratorM5.Paper.smallRingObject_isPaperGenerator`);
its conclusion is literally `SmallPerf`.  For `AffineD A`, 09SR cannot be applied
directly (`HasCoproducts.{u+1} (AffineD A)` is not available), so a compact object
is moved to the canonical small model by
`SmallHomM5.isCompactAb_of_equivalence_large_to_small` (proved) and `Perf` comes
back along `CapstoneM6.smallPerf_affineQhComparison_iff` (proved).  The direct
route (compact ⇒ retract of a finite stage of a K-projective cell model) was not
taken: its packages `SmallFilteredFreeModelInput`, `SmallFiniteFreeImprovementInput`
are not inhabited in the tree.

| declaration | statement | hypotheses |
|---|---|---|
| `smallPerf_of_isCompactAb`, `smallNeemanCompactToPerfectInput` | (i) ⇒, S model | `h09 : Tag09SRPaper (SmallAffineD A H)` |
| `smallAffine_neeman_3_2_i` | (i) ⇔, S model | same |
| `perf_of_isCompactAb`, `compactToPerfectInput`, `compactPerfectInput` | (i) ⇒ / ⇔, L model | `h09 : Tag09SRPaper (CanonicalSmallAffineD A)` |
| `affine_neeman_3_2_i` | (i) ⇔ as `Neeman_3_2_i (AffineD A) (Perf A)` | same |
| `affine_neeman_3_2_ii` | (ii), paper form (`IsCompactAb ∧ IsPaperGenerator`) | none |
| `ringObject_isClassicalGeneratorOnCompacts` | (ii)+09SR: `A[0]` classically generates compacts | `h09` |
| `affine_theorem_1_1_of_tag09SR`, `satisfiesWA_of_tag09SR` | `affine_theorem_1_1_neeman_only` and its reverse half with `CompactPerfectInput` discharged | as the originals, with `h09` for `I` |
| `affine_theorem_1_1_small_of_tag09SR`, `affine_theorem_1_1_small_standard_of_tag09SR` | the small endpoints with `SmallNeemanCompactToPerfectInput` discharged | as the originals, with `h09` for `I` |
| `affineCompactHomZeroAtTop`, `smallCompactHomZeroAtTop` | compact Hom vanishing at the top | `h09` |
| `affine_regularGenerator_package`, `small_affine_regularGenerator_package` | WA + preferred class + compact ⇔ perfect | `h09` |
| `compact_iff_dbcoh` | over a field, compact ⇔ `D^b` with finite-dimensional cohomology | `h09` |

(iii) in the affine models was already proved unconditionally
(`RegularCompact.affine_standard_inPreferredClass`,
`AffineNeemanEndpointM3.small_affine_inPreferredClass`); nothing to add.

## 4. Recommendations

* The orchestrator can now replace the hypothesis `I : CompactPerfectInput A` of
  the pinned `affine_theorem_1_1_neeman_only` by `h09`, and likewise in the other
  consumers of §2; the corollaries above show the substitution typechecks.
* Delete (or keep as dead code, marked) `Neeman_3_2_ii` (false rendering),
  `NeemanPublishedWeakApproximation` and `NeemanAffineCompactModelInput`'s
  role as an input (only 066S needs it, and no paper path needs 066S).
* Scheme level: `SupportedCategoryInput.neeman_3_2_iii` is the only Thm 3.2 item
  on a paper path still carried as a non-Stacks input; it is to be proved from
  AxiomMath (0AEC compact generator, 0AED, 09SR) for `D_qc,Z(X)`, following the
  affine proof `NeemanPreferredM6.inPreferredClass_of_compactlyGenerated`.
