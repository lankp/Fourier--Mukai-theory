# D3: the AxiomMath Stacks checkout and the cost of using it at Lean 4.33.1

## Verdict

**Do not treat the checkout as a cheap drop-in justification for refocusing this project while it is
pinned to Lean 4.33.1.** The *source* evidence for the scheme route is nevertheless strong:
`09M1` (compacts are perfect), `09IS` (a perfect generator), `09M4` (eventual Ext vanishing), the
Noetherian case `09T4` (the derived coherator equivalence), and `0ATY` (the upper-shriek
pseudofunctor) all have named scheme-level declarations. Thus the restriction to Noetherian
schemes is mathematically well supported, and `09T4` is a genuine Noetherian simplification, not
just a stronger hypothesis copy-pasted onto a qcqs proof.

The obstruction is reuse. The raw transitive import closure delivering compact = perfect has 3,518
Stacks modules / 1,074,899 lines and 21 distinct directly imported Mathlib source paths absent from
4.33.1; the useful package compact = perfect + perfect generator + Ext windows has 4,416 modules /
1,347,554 lines. Missing paths include real derived-functor and Grothendieck-abelian infrastructure,
not merely renames. On the present image the toolchain gap is a hard operational blocker; calling
it “mostly mechanical” would hide those substantive backports. If a Lean 4.35.0 environment with
compiled Stacks artifacts is permitted, the conclusion changes: using that environment is much
more credible than either a 4.33.1 backport or a new algebraic-space development.

There is no replacement here for the LP layer: exact searches over all `StacksCore` and
`StacksFrontier` Lean files found **0** occurrences of `weakly approximable`,
`weak approximability`, or `weak approximation`, and no declaration named `Recollement` or
`recollement`. The geometric support/recollement triangles noted below are inputs to such an
argument, not weak approximability itself.

## Scope, provenance, and method

The audit is of local commit `f56a316ddf7a930906d88b78d6f9a2668cffd0cf`, read textually from
`.git/refs/heads/main` (no git command). Its `lake-manifest.json` pins Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` (`inputRev = v4.35.0`). There are 64,213 `.lean`
files under `StacksCore` and `StacksFrontier` (445 and 63,768 respectively), counted by
`rg --files ... -g '*.lean' | wc -l`. No source was built or modified.

The declaration names below were read at the indicated lines using `rg -n` and `sed`. The stated
hypotheses and qualifications were read in the actual declaration/docstring, not inferred from the
file name. The checkout's README says that all proofs are kernel-checked, there is no `sorry`, and
`StacksFrontier` is agent-written and not human-reviewed; `formalization.yaml` self-assesses zero
sorries and the three standard axioms. **Those are upstream assurances, not an independent check in
this VM.** A targeted search for `:= sorry`, `sorryAx`, `admit`, and `axiom` declarations in the
source files listed below returned no match, but this cannot substitute for elaborating their import
closure.

Closure counts were computed by the accompanying read-only `portability.py`: it strips nested Lean
comments, parses `import`/`public import`, follows only Stacks source modules, and counts lines and
unique directly mentioned Mathlib modules. It resolved every Stacks import. A Mathlib module is
marked absent when the corresponding `.lean` path is absent under `/opt/mathlib/Mathlib`; this is a
source-path test, not a claim that every declaration in that module is conceptually absent. The raw
closure is an upper bound on a dependency-pruned port, and over-eager imports can inflate it. It is
the right cost measure for using the existing source *unchanged*.

## What exists for schemes

Paths are relative to the checkout root. “Any model” refers to the chosen `HasDerivedCategory` model.
All entries except base API are in `StacksFrontier`, hence have the review qualification above.

| wanted input | module and exact declaration | source status and qualification |
|---|---|---|
| `D_qc` objects | `StacksFrontier/AlgebraicGeometry/DerivedQCoh/Basic.lean`, `Stacks.DerivedQCoh.IsDQCoh` (line 113) | Defined: all cohomology sheaves quasicoherent. This is a predicate, not the whole six-functor package. |
| `D(QCoh) ≌ D_qc`, Noetherian | `.../DerivedQCoh/NoetherianExtension/Equivalence.lean`, `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isNoetherian` (124), `derivedCoherator_isoInv_of_isNoetherian` (143) | **[Stacks 09T4]**, standard derived model. The companion `noetherianAffineOpenPushforwardCompatible` discharges the general `09T6` compatibility via `09T3`; this is the real Noetherian specialization. |
| perfect objects | `.../Topology/Sheaves/Cohomology/PerfectComplexes/Defs.lean`, `Stacks.Cohomology.PerfectComplexes.IsPerfectComplex` (59), `IsPerfect` (82) | **[Stacks 08CM]**, ringed-space definition by local strictly perfect models; no `Perf` six-functor suite is implied by this definition alone. |
| triangulated structure on perf | `.../PerfectComplexes/TriangulatedSubcategory.lean`, `Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect` (84) | **[Stacks 08CR, 0FDG]**, any derived model. `DirectSummands.lean` only proves the split-triangle two-out-of-three statement; full retract thickness `08CS` is elsewhere and must not be inferred from its file name. |
| compacts = perfect | `.../Duality/CompactGeneration/CompactPerfectTag.lean`, `Stacks.Duality.isCompactObject_eq_isPerfect` (48); objectwise form in `CompactPerfect.lean`, `isCompactObject_iff_isPerfect` (661) | **[Stacks 09M1]**, qcqs schemes, any derived model; both directions have no extra geometric hypothesis in the final declaration. |
| compact generation | `.../Duality/CompactGeneration/QcqsCompactGeneration.lean`, `Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory` (955) | qcqs compact generation of `D_qc`; this is separate from weak approximability. |
| a perfect compact generator | `.../DerivedQCoh/PerfectGeneratorInduction.lean`, `Stacks.DerivedQCoh.AnyModel.hasPerfectGenerator_of_qcqs` (416), `exists_isPerfect_isZero_iff_forall_hom_eq_zero` (432) | **[Stacks 09IS]**, Bondal–Van den Bergh, qcqs. `AnyModel/PerfectGeneratorAnyModel.lean` transports the result to an arbitrary chosen derived model. |
| eventual vanishing | `.../Duality/DetectingBoundednessOfAPerfectComplex.lean`, `Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_qcqs` (147), `finite_setOf_not_subsingleton_hom_shift_of_isPerfect_qcqs` (164) | **[Stacks 09M4(1),(2)]**, qcqs. Part (2) needs a perfect source and a bounded `D_qc` target and gives finiteness of nonvanishing degrees. With `09M1` supplying perfectness/boundedness of compacts, this is directly relevant to `CompactHomZeroAtTop`. |
| support/gluing triangle | `.../DerivedQCoh/SupportedDerivedModules.lean`, `Stacks.DerivedQCoh.exists_derivedRestrict_triangle` (424) | A distinguished unit triangle for open restriction, with third vertex supported on the closed support difference. It requires the named derived direct-image model and support hypotheses; it is a geometric ingredient, not an abstract recollement package. |
| coherator and its adjunction | `.../DerivedQCoh/CoheratorQuasiInverse.lean`, `Stacks.DerivedQCoh.derivedCoheratorAdjunction` (298), `derivedCoherator_isoInv` (361); `DerivedCoherator.lean`, `derivedCoheratorOfScheme` | Existence is for arbitrary schemes. The general comparison-equivalence file takes `AffineOpenPushforwardCompatible`; use the Noetherian `09T4` entry above for the discharged version. |
| `f^!` and pseudofunctoriality | `.../Duality/Compactification/ShriekPseudofunctor/Pseudofunctor.lean`, `Stacks.Duality.upperShriekPseudofunctor` (183), `exists_upperShriekPseudofunctor` (222) | **[Stacks 0ATY]**, on `D⁺_QCoh`, over Noetherian `S`, for separated finite-type schemes `FTS S`; uses Nagata compactification (`0F41`). This is not an unbounded `f^!` on every scheme morphism. |
| Tor-independent base change | `.../Duality/TwistedInverseImage/TorIndependentBaseChangeIsIso.lean`, `Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent` (344) | **[Stacks 0A9K]**, the pushforward/right-adjoint mate is invertible under the stated Tor-independence hypotheses. |
| flat base change for `f^!` | `.../Duality/UpperShriekFlatBaseChange.lean`, `Stacks.Duality.upperShriekBaseChangeMap` (168), `isIso_upperShriekBaseChangeMap_app` (180) | **[Stacks 0E9U]**, on `D⁺_QCoh`, for a flat cartesian square in `FTS S`; compactification hypotheses are explicit. |

Primary source links for checking the mathematical labels are
[08CM](https://stacks.math.columbia.edu/tag/08CM),
[09M1](https://stacks.math.columbia.edu/tag/09M1),
[09IS](https://stacks.math.columbia.edu/tag/09IS),
[09M4](https://stacks.math.columbia.edu/tag/09M4),
[09T4](https://stacks.math.columbia.edu/tag/09T4),
[0ATY](https://stacks.math.columbia.edu/tag/0ATY),
[0A9K](https://stacks.math.columbia.edu/tag/0A9K), and
[0E9U](https://stacks.math.columbia.edu/tag/0E9U). The exact source declaration `09M1` is also
visible upstream at
https://github.com/AxiomMath/Stacks/blob/f56a316ddf7a930906d88b78d6f9a2668cffd0cf/StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/CompactPerfectTag.lean#L48 .

## Measured import closures

“Missing paths” is the number of unique directly mentioned `Mathlib.*` module paths absent in the
4.33.1 source tree, not the number of mathematical theorems missing. Roots are named so the counts
can be reproduced rather than compared to an arbitrary directory size.

| target / roots | Stacks modules | lines | missing Mathlib paths |
|---|---:|---:|---:|
| perfect definition: `PerfectComplexes/Defs.lean` | 31 | 7,665 | 4 |
| elementary perf API: `Defs`, `BasicProperties`, `MappingCone`, `DirectSummands` | 52 | 13,841 | 4 |
| support triangle: `DerivedQCoh/SupportedDerivedModules.lean` | 1,831 | 559,821 | 18 |
| Noetherian coherator equivalence: `NoetherianExtension/Equivalence.lean` | 2,255 | 689,516 | 20 |
| Ext windows: `Duality/DetectingBoundednessOfAPerfectComplex.lean` | 2,462 | 753,849 | 20 |
| compact = perfect: `CompactGeneration/CompactPerfectTag.lean` | 3,518 | 1,074,899 | 21 |
| Tor-independent base change: `TwistedInverseImage/TorIndependentBaseChangeMap.lean` | 3,851 | 1,183,017 | 21 |
| weak-approx geometric inputs: `CompactPerfectTag` + `PerfectGeneratorAnyModel` + `DetectingBoundednessOfAPerfectComplex` | 4,416 | 1,347,554 | 21 |
| upper-shriek pseudofunctor: `Compactification/ShriekPseudofunctor/Pseudofunctor.lean` | 7,679 | 2,310,604 | 27 |

The compact-generation root alone (`QcqsCompactGeneration.lean`) measures 3,505 modules / 1,071,774
lines / 21 missing paths. Thus extracting only compact = perfect rather than the whole generator
development does not make a dramatic difference: the common infrastructure dominates.

## What the 4.33.1 gap contains

The `#check` commands below are active evidence for the base API that *is* present:
schemes and ringed spaces, scheme modules and sheaf modules, quasicoherence, open restriction,
pushforward, standard derived categories and homology, and total right-derived functors. The file
also parses `module`/`public import` successfully at 4.33.1, so module syntax alone is not the main
porting problem.

There is no active `#check CategoryTheory.IsCompactObject` here for a reason: the Stacks definition
is local to `StacksFrontier/CategoryTheory/Triangulated/CompactObjects/ThickSubcategory.lean` (line
106), and `ObjectProperty.IsWeakTriangulatedGenerator` is local to
`CategoryTheory/Triangulated/Generators.lean` (line 512). These classes travel with the Stacks port;
they should not be misreported as independently missing Mathlib concepts.

Spot checks against both `/opt/mathlib` and upstream primary sources give:

| v4.35 import seen in Stacks | 4.33.1 finding | kind of work |
|---|---|---|
| `Mathlib.Order.Int.ConditionallyCompleteOrder`, `Order.Int.LeastGreatest`, `Order.SuccPred.Int`, `Order.SuccPred.Nat` | Material exists under `Mathlib/Data/Int/...` and `Mathlib/Data/Nat/SuccPred.lean`; upstream also has the old path [Data.Int.ConditionallyCompleteOrder](https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.33.1/Mathlib/Data/Int/ConditionallyCompleteOrder.lean) | Mechanical path/API rename. |
| `Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated` | No local file or `IsTriangulated`/`CommShift` declaration in current `RightDerived*.lean`; v4.33.1 URL returns 404. [v4.35 source](https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.35.0/Mathlib/CategoryTheory/Functor/Derived/RightDerivedTriangulated.lean) proves `CategoryTheory.Functor.isTriangulated_of_leftExtension` | Real new proof/API to backport, although the file itself is small. |
| `Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift` and `LeftDerivedTriangulated` | No local file; v4.33.1 `RightDerivedCommShift` returns 404; [v4.35 source](https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.35.0/Mathlib/CategoryTheory/Functor/Derived/RightDerivedCommShift.lean) has the shift structures and coherence proofs | Real derived-functor infrastructure, not a rename. |
| `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules` (and `PresheafOfModules`) | Neither local file nor a local `IsGrothendieckAbelian` instance in sheaf-module files; v4.33.1 URL returns 404. [v4.35 source](https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.35.0/Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/SheafOfModules.lean) supplies the small-site instance | Substantive gateway to K-injective/unbounded-derived arguments, even though its proof is short once presheaf AB5/separator facts exist. |
| `Std.Tactic.BVDecide.Normalize.Prop` | Absent at both `/opt/lean/lib/lean/...` and the installed Batteries candidate path | Additional toolchain/Std mismatch, independent of Mathlib renames. |

The weak-input closure has exactly 21 such missing Mathlib paths; the pseudofunctor closure has 27.
Many others look like module splits and should be triaged individually rather than counted as 21 large
research problems. Conversely, the three categories above are sufficient to refute the claim that
the entire gap is cosmetic.

## Smallest useful subtree and concrete effort

**Spike first:** `PerfectComplexes/Defs.lean`, then `BasicProperties`, `MappingCone`,
`TriangulatedSubcategory`, and `DirectSummands`. Its raw closure is 31 modules / 7,665 lines for the
definition alone and 52 modules / 13,841 lines for the elementary package. It gives a genuine
ringed-space `IsPerfect` and triangulated closure, but **not** compact = perfect, full thickness,
compact generation, or weak approximability. Budget **10–20 person-days for the definition spike**
and **25–50 person-days total for the elementary package**, including replacement of the four absent
Mathlib paths and elaboration fixes. This estimate was not build-tested and assumes an expert already
familiar with Mathlib's derived-category API.

**Smallest subtree that answers the key compactness question:** `CompactPerfectTag.lean`, whose final
statement is exactly the qcqs equality of compact and perfect object properties. Its raw 3,518-module
closure makes a literal 4.33.1 port approximately **200–450 person-days**. **Do not start this as a
“small subtree port”; it is a person-months programme.** The smallest package supplying all three
weak-approx geometry inputs (compact = perfect, a perfect generator, and Ext windows) is the measured
4,416-module union and is approximately **250–550 person-days**. These ranges assume a sustained
2,000–5,000 imported/debugged lines per person-day after the first API adaptations, plus time for the
real derived-functor/Grothendieck additions; extensive pruning could reduce them, but then it is a
re-engineering project requiring a new audit, not the measured port.

For comparison, the Noetherian coherator alone is an estimated **150–350 person-days** by the same
literal-closure model, and the `0ATY` pseudofunctor closure is **500–1,200 person-days**. These are
planning estimates, not proved lower bounds or claims that new formalization must duplicate those
lines. They are intended to rule out the incorrect “copy a handful of files in a week” estimate.
The defensible cheap alternatives are (i) keep the geometric statements as cited hypotheses, or
(ii) change the execution environment to one that can consume compiled Lean 4.35 Mathlib/Stacks
artifacts and assess integration separately. Option (ii) was not built or benchmarked here.