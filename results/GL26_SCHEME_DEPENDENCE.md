# D4: GL26 theorem-by-theorem dependence, schemes versus algebraic spaces

## Verdict

**Neeman's scheme theorem does not make the Noetherian-scheme version of GL26
mostly categorical.**  It supplies exactly the weak-approximability hypothesis,
compact generation, compacts `= Perf`, and the preferred `t`-structure class.
Only **2 of the 10** Lean targets use weak approximability.  Four targets still
contain the new geometric work of GL26: arbitrary Noetherian base change for
relative perfectness and the three §12 openness/locus declarations.  Restricting
to schemes usefully deletes étale-presentation and point/residual-space
scaffolding, but it does not delete Grothendieck duality, relative dualizing
complexes, mates, pseudocoherence, support arguments, or arbitrary base change.

Weak approximability itself needs only qcqs schemes, not Noetherian schemes;
Noetherianness buys coherence, finite cohomology, and the duality setting used
elsewhere.  It does not finish Remark 2.6: that argument also invokes
coherence of `D_qc` and CHNS Theorem B, identified explicitly below.

A narrower retreat to **separated** Noetherian schemes would reuse more:
Guisado Villalgordo--Lank--Manali Rahul--Pavic (GLMP25), Theorem 6.11, is the
scheme version of GL26 Theorem 10.13.  That is an arXiv preprint, not a journal
publication, and it assumes a separated base.  "Noetherian schemes" without
separatedness still needs the later base-change/duality assembly.

There is also a project-cost consequence: Neeman's theorem proves scheme weak
approximability **directly**.  The scheme restriction removes the algebraic-space
application of Lank--Pauwels gluing rather than making that completed work the
main next step.  LP can still be used as an abstract alternative, but is not a
prerequisite for the published scheme input.

## Quantitative summary

| audit item | count | evidence |
|---|---:|---|
| targets in `FourierMukai/Paper/Statements.lean` | 10 | declarations read individually |
| targets whose paper proof uses weak approximability | 2 | `theorem_1_2_open`, `theorem_1_2_baseChange`; `main.tex` 7497, 7563 |
| targets not using weak approximability | 8 | in particular the alternative at `main.tex` 6683--6686 |
| targets involving GL26's new arbitrary-base-change/openness packages | 4 | Corollary 6.18, Theorem 12.3, Theorem 12.9(1),(2) |
| targets stated almost verbatim in the earlier scheme preprint | 1 | Theorem 10.13 = GLMP25 Theorem 6.11, **separated base only** |
| `True` placeholders in those targets | 7 | six relative-perfectness placeholders and `hell : True` |
| direct Hall--Rydh-induction calls in the ten proof sketches | 0 | `main.tex` 575 is only the general thick-subcategory remark |
| space-specific proof packages removed or shortened | 6 | grouping made explicit below; this is an audit partition, not six independent theorems |

The six packages are (1) small-étale-site/presentation descent, (2) field-class
representatives and residual spaces/gerbes, (3) the quasi-affine-diagonal lemmas,
(4) the algebraic-space weak-approximability induction, (5) the preferred-class
induction through Stacks 09IT, and (6) the algebraic-space Nagata background for
`f^!`.  Only (4)--(5) replace substantive external theorem dependencies;
(1)--(3) mostly shorten proofs.  Item (6) does **not** eliminate
Grothendieck duality, nor scheme Nagata compactification if one chooses to build
`f^!` for arbitrary separated finite-type morphisms.  The morphisms in the main
proper-flat setup are proper, so their `f^! = f^×` comparison remains essential.

## Status key and sources actually checked

* **(a)** means a scheme-level statement or close ingredient exists in a named
  source.  It does not mean that its Lean formalization already exists.
* **(b)** means a specifically algebraic-space construction disappears or is
  replaced by an easier Zariski/point argument.
* **(c)** means that the exact conclusion, or substantial assembly toward it,
  remains after scheme restriction.  This is not a claim that GL26 fails to prove
  it: GL26's own proof is a blueprint.  It means that Neeman's scheme theorem and
  the earlier scheme preprint do not make the task disappear.

The primary sources below were fetched and their statements read.  The local
`rg` searches were over `FourierMukai/Paper/*.lean` and GL26 `main.tex`; the
specific proof ranges are included in the table.

| key | source and exact location | publication status and used statement |
|---|---|---|
| N24 | Amnon Neeman, *Bounded `t`-structures on the category of perfect complexes*, Acta Math. 233(2) (2024), 239--284, **Theorem 3.2(i)--(iv)**, https://arxiv.org/html/2202.08861v4#S3.Thmtheorem2 | Published. For qcqs `X` and closed `Z` with qc complement: compacts are supported perfect complexes; one compact generator exists; preferred class; `D_qc,Z(X)` weakly approximable. Take `Z=X` for a Noetherian scheme. |
| CHNS24 | Canonaco--Haesemeyer--Neeman--Stellari, *The passage among the subcategories of weakly approximable triangulated categories*, **Theorem B**, https://arxiv.org/html/2402.04605v1#Sx1.ThmthmInt2 | arXiv preprint used by GL26 Remark 2.6: triangulated equivalences restrict between the indicated intrinsic subcategories, with the relevant implication using coherence. |
| N18 | Amnon Neeman, *The categories `T^c` and `T^b_c` determine each other*, **Example 5.4**, https://arxiv.org/html/1806.06471v2#S5.Thmtheorem4 | Preprint cited here as a companion to N24: for a qcqs coherent scheme and `Z` with qc-open complement, `D_qc,Z(X)` is coherent and weakly approximable. Noetherian schemes are coherent. |
| AJLS23 | Alonso Tarrío--Jeremías López--Sancho de Salas, *Relative perfect complexes*, Math. Z. 304 (2023), 42, **Theorem 4.3**, https://arxiv.org/html/2112.09680v4#S4.Thmtheorem3, DOI 10.1007/s00209-023-03294-7 | Published. For a quasi-proper morphism, bounded pseudocoherent `E`: `f`-perfect iff `Rf_*(E⊗P)` is perfect for all perfect `P`; also gives its fibre criterion. Proper morphisms of Noetherian schemes are quasi-proper. |
| GLMP25 | Guisado Villalgordo--Lank--Manali Rahul--Pavic, *Fiberwise criteria for Fourier--Mukai equivalences*, **Theorem 6.11**, https://arxiv.org/html/2512.16503v5#S6.Thmtheorem11; **Lemma 3.4**, `#S3.Thmtheorem4`; **Proposition 5.4**, `#S5.Thmtheorem4`; **Proposition 6.5**, `#S6.Thmtheorem5` | arXiv preprint 2512.16503v5. Gives the fibre criterion on a **separated Noetherian scheme**, affine base change for relative perfectness, adjoint kernels, and mate compatibility. |
| N23 | Amnon Neeman, *An improvement on the base-change theorem and the functor `f^!`*, Bull. Iranian Math. Soc. 49 (2023), 25, **Theorem 1.8(6)--(9), Construction 9.4, Corollary 5.10**, https://arxiv.org/abs/1406.7599, DOI 10.1007/s41980-023-00768-6 | Published; source used by GL26 §2.4 for `f^!`, `f^×` and their relations. Its existence already covers the scheme setting, but its full pseudofunctor/coherence package is still required. |
| HLS09 | Hernández Ruipérez--López Martín--Sancho de Salas, *Relative integral functors for singular fibrations and singular partners*, JEMS 11 (2009), 597--625, **Proposition 2.16 and §3.4.1**, DOI 10.4171/JEMS/162 | Published fibre-level input used explicitly by GL26 at `main.tex` 7128. The global elliptic-fibration conclusion also uses the corrected fibre criterion, not this citation alone. |

Further scheme-compatible references used by the proofs:

* Stacks **75.20.1 (08IN)**, https://stacks.math.columbia.edu/tag/08IN: projection
  formula for qcqs morphisms of algebraic spaces, in particular schemes.
* Stacks **75.20.4 (08IR)**, https://stacks.math.columbia.edu/tag/08IR:
  Tor-independent base change on unbounded `D_qc`.
* Stacks **75.8.1 (08GK)**, https://stacks.math.columbia.edu/tag/08GK: proper
  support gives bounded coherent derived pushforward under the stated Noetherian
  and finite-type hypotheses.
* Stacks **75.16.1 (09M8)**, https://stacks.math.columbia.edu/tag/09M8:
  compact objects of `D_qc` are perfect (also covered for schemes by N24).
* Stacks **75.29.3--75.29.4 (0GFH/0GFI)**, https://stacks.math.columbia.edu/tag/0GFH
  and https://stacks.math.columbia.edu/tag/0GFI: boundedness detected by Hom
  vanishing from a perfect generator. Their algebraic-space proofs use an
  induction principle; GL26 also gives a preferred-class alternative. Only direct
  GL26 calls were counted as Hall--Rydh uses above.
* Stacks **86.5.1 (0E5I)**, https://stacks.math.columbia.edu/tag/0E5I: proper-flat
  base change for the right adjoint when the base change is between affine
  schemes; GL26's étale localization is used precisely to get to this input.
* Janina C. Letz, *Local to global principles for generation time over
  commutative Noetherian rings*, HHA 23(2) (2021), 165--182,
  **Proposition 2.5**, DOI 10.4310/HHA.2021.v23.n2.a10: the local perfect-generation
  locus used by GL26 Lemma 6.7. This replaces neither global relative perfectness
  nor the pushforward/support argument.

## The ten targets and Definition 12.1 / `FMContext`

The "scheme input" column answers (a); the next two columns answer (b) and (c).
Labels such as Proposition 10.5 refer to GL26 itself, not to earlier literature.

| target | geometric inputs in the actual proof | (a) scheme source | (b) disappears/simplifies | (c) what remains |
|---|---|---|---|---|
| `theorem_1_3` (Thm 1.3) | Proper coherent pushforward, projection formula, pseudocoherent tensor/RHom, relative duals, compact generation and Hom-boundedness; `prop:stacky_all_coincide`, `lem:boundedness_via_coaisle`, `thm:adjoint_dqc_for_f-quasi-perfect` (`main.tex` 2753--3035). | **AJLS23 Theorem 4.3** supplies the central `f`-perfect/`f`-quasi-perfect equivalence for schemes; N24(i),(ii), 08GK, 08IN, 0GFH/I cover the supporting inputs. | The affine étale presentation in 2831--2890 and the residual-space argument in 2976--3035 disappear. One can cite AJLS rather than port the space-specific duality proof of the central equivalence. | The middle `D^b_coh` characterization still needs coherent closure and the closed-point-to-perfect argument; this is small assembly, not an immediate restatement of AJLS(1)⇔(3). |
| `corollary_6_18` (Cor 6.18) | Quasi-affine base change, compact-generator pullback, boundedness under covers, reflection after faithfully flat/field base change, Theorem 6.16; proof at 3382--3398 and dependencies at 3182--3380. | **GLMP25 Lemma 3.4** is the **affine** base-change result; AJLS23 §3 supplies transverse-square ingredients. | No presentation of `T` is needed at 3390; affine Zariski covers replace it. The quasi-affine-diagonal wrapper is simpler. | **Arbitrary** Noetherian `t`, not just affine `t`, is explicitly described by GL26 as new at `main.tex` 414--415. The exact global theorem and its localization/reflection argument remain. Properness and bounded pseudocoherence cannot be dropped. |
| `theorem_12_3` (Thm 12.3) | Right-adjoint kernel `RHom(K,(f')^!O)`, Proposition 10.5 unit/counit mates, compact generators and their pullback, bounded coherent support, closedness of proper maps, fibre-zero detection; proof at 7215--7258. | N24(i),(ii), 08GK, 08IN/IR, N23, and GLMP25 Proposition 6.5 (affine mate compatibility) are scheme ingredients. | The representative-independence wrapper becomes ordinary residue-field reasoning. | The support-of-unit/counit-cones openness argument is not in GLMP25 and does not follow from Neeman weak approximability. Relative duals and Proposition 10.5 are still substantive; **no weak-approximability is needed for this relatively perfect case**. |
| `theorem_1_2_open` (Thm 12.9(1)) | Proposition 12.8 openness of the relative-perfect locus, Remark 2.6 to force an equivalence kernel to be relatively perfect, Theorem 12.3, and base change for relative perfectness; proof at 7370--7548. | **N24(iv)** replaces the space weak-approximability input; Letz Proposition 2.5 is the local perfect-locus input; N24(i)--(iii) covers generation and preferred class. **CHNS24 Theorem B + N18 Example 5.4** supply the still-needed coherence/equivalence restriction. | Remark 2.6 no longer needs Lank's algebraic-space Corollary 1.2. Étale-open-image reasoning for the base locus becomes Zariski reasoning. | Proposition 12.8, the preprint-level CHNS/N18 restriction, GL26's preservation arguments, and the relatively perfect support theorem all remain. This is one of exactly two targets using weak approximability. |
| `theorem_1_2_baseChange` (Thm 12.9(2)) | Everything in the previous row, plus Corollary 12.10, Corollary 6.18, and reflection along residue-field extensions; proof at 7550--7573. | N24(iv), CHNS24/N18, and GLMP25's affine ascent/descent are partial scheme inputs. | Residue-field maps replace algebraic-space point representatives. | Both arbitrary base change for relative perfectness and the second use of Remark 2.6 at 7563 remain, including the preprint-level CHNS/N18 restriction. GL26 Corollary 12.10 alone assumes relative perfectness, so it cannot be used as a shortcut for arbitrary kernels. |
| `lemma_12_2` | Propositions 10.10/10.12 ascent/descent, adjoint base change, preservation/reflection of relative perfectness, common field extensions; proof at 7162--7213. | Follows from **GLMP25 Theorem 6.11** on a separated base; its condition (3) uses arbitrary fields. | Residual gerbes and equivalence classes of field morphisms disappear. | On a general, possibly non-separated Noetherian base one still needs the duality/base-change package and proof of representative independence. It is a corollary of the older theorem only after imposing separatedness. |
| `theorem_1_6` (Thm 10.13) | Left/right adjoint kernels, Proposition 10.5 and Remark 10.6 mates, compact generation, support at closed points, relative-perfect base change; proof at 6172--6878. | **GLMP25 Theorem 6.11** is essentially the same theorem on a separated Noetherian scheme, including both full faithfulness and equivalence and stronger affine/field formulations. | All residual-space and presentation scaffolding can be avoided by citing the scheme precursor. | Without separatedness, the later assembly remains. Weak approximability is **not** required: `main.tex` 6683--6686 explicitly replaces it by generation plus relative perfectness. |
| `lemma_2_25` | Projection formula, tensor unit, functoriality of derived push/pull, and both projection–diagonal composites being identities; proof at 1514--1533. | **Stacks 08IN**, together with standard pseudofunctoriality; no algebraic-space-only result is needed. | Only the site wrapper is simplified. | The projection formula and diagonal identities are genuine data. They are absent from the current abstract `FMContext`, as the countermodel below proves. |
| `lemma_2_26` | Projection formula, Tor-independent base change (flatness supplies Tor independence), monoidality and pseudofunctoriality, and compatibility of the triple fibre product; proof at 1546--1563. | **Stacks 08IN and 08IR**; Huybrechts, *Fourier–Mukai Transforms in Algebraic Geometry*, Proposition 5.10, is the classical scheme computation. | Nothing substantive beyond étale wrappers. | The natural-isomorphism coherence and triple-product diagram remain. The Lean `conv` is currently an arbitrary function and the three contexts are unrelated, so the statement needs additional fields/hypotheses. |
| `theorem_1_7` (Thm 11.4) | Lemma 11.1 relative perfectness of the diagonal ideal, Proposition 11.3 pullback of that ideal, relative adjoints, Theorem 10.13, and **HLS09 Proposition 2.16/§3.4.1** on geometric fibres; proof at 6885--7130. | HLS09 supplies the singular elliptic-fibre autoequivalence; GLMP25 Theorem 6.11 gives the separated-scheme ascent step. | The fibres were already schemes in GL26's definition. Restriction affects the global space, not the hard fibrewise curve argument. | Coherent relative dualizing complexes, ideal-sheaf base change, and the corrected global criterion remain. General non-separated bases are outside the old theorem. No weak-approximability shortcut is needed here. |
| Definition 12.1 / `FMContext` | Fibre products, derived categories and functors, residue-field base change of kernels, and the actual identification of `fibreTransform` with the pulled-back integral transform. | These are definitions over schemes as well; N24 says nothing at the definitional level. | A scheme point has its canonical residue field, avoiding the space's equivalence-class definition. | `D_qc`, `Perf`, bounded pseudocoherence, pull/push/tensor and their compatibility do not become definable by Neeman's theorem. The current `FMContext` has no triangle, exactness, adjunction, `RHom` or `f^!` fields; `FMSetup.fibreTransform` is arbitrary. |

Two statement mismatches matter independently of schemes.  First, the Lean
`theorem_1_6` quantifies over every `p : X.Base` and tests ordinary full
faithfulness of each fibre functor, whereas GL26 Theorem 10.13 concerns closed
points and `D^b_coh` (and separately full faithfulness/equivalence).  Second,
`theorem_1_7` takes an arbitrary `idealDiag` and `hell : True`; it contains no
elliptic-fibration or diagonal-ideal condition.  These are specification issues,
not missing mathematical references.

## What actually vanishes—and what does not

1. **Neeman's published package really helps.** N24(iv) replaces Lank's
   algebraic-space weak approximability, and N24(i)--(iii) also replaces the
   compact-generation and preferred-class citations. It is a stronger improvement
   than a bare `D_qc(X)` weak-approximability hypothesis.
2. **The expensive categorical Rosetta stone stays.** `f^!`, `f^×`, `RHom`,
   relative dualizing complexes, proper coherent pushforward, derived tensor,
   Tor base change, and pseudocoherence are used throughout §§6--12. Switching
   from étale to Zariski sites does not prove these theorems.
3. **Space-specific induction is limited, not the whole story.** GL26's preferred
   class proof at `main.tex` 7983--7993 explicitly invokes N24(iii) followed by
   Stacks 09IT; this induction disappears for schemes. The recollement/support
   lemmas in the same appendix do not all disappear. Hall--Rydh is not a direct
   ingredient of the ten proof sketches, and no quotient-existence theorem is
   invoked there.
4. **The older scheme theorem is narrower in two ways.** GLMP25 assumes a
   separated base and proves the relatively perfect fibre criterion, not GL26's
   arbitrary-base-change Corollary 6.18 or the openness results of §12. There is
   no legitimate inference "Neeman + GLMP25 = all of GL26 for arbitrary
   Noetherian schemes".
5. **The present Lean interface must be repaired before estimating proofs.**
   Seven hypotheses are `True`; `FMContext` lacks the projection formula and all
   dualizing/mates data. `constantContext` below is a valid `FMContext` for which
   Lemma 2.25 is false. Thus the ten unproved declarations are targets of mixed
   faithfulness, not a reliable ten-item work breakdown.

## Practical scoping recommendation

On this dependency evidence, **refocus to Noetherian schemes is a legitimate
infrastructure simplification, but not a near-feasibility argument for GL26**.
It replaces several algebraic-space inputs by precise published scheme theorems
and shortens the proofs; it does not turn the ten targets into applications of LP.
If the objective is an early meaningful theorem, the relatively perfect criterion
for a **separated** Noetherian base (GLMP25 Theorem 6.11), or the elementary
functoriality lemmas with a strengthened interface, is much better scoped than
Theorem 1.2.  The latter still packages nearly the whole theory: relative
perfectness, arbitrary base change, duality, mates, support, and the
weak-approximability/coherence equivalence machinery.

## Lean verification policy

No assertion is made here that Mathlib already contains scheme `D_qc`, `Perf`,
`f^!`, or the geometric hypotheses. The `#check`s below verify only the existing
abstract interface in this project's `DerivedSetup`. All unproved literature and
GL26 inputs are collected as `Prop` fields (not global axioms). The countermodel
is fully proved. The searches used were local `rg` searches on `main.tex` and
`FourierMukai/Paper/Statements.lean`, plus the primary-source URLs above; no
Mathlib-inventory claim is inferred from those literature searches.