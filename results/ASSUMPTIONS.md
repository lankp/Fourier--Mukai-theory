# Assumption ledger: AxiomMath/Stacks + Neeman

## 1. Contract and terminology

The only permitted external mathematical inputs are the **tagged Stacks
interface** and **Neeman, Acta Math. 233 (2024), Theorem 3.2**. The interface is
`FourierMukai/Scheme/StacksInput.lean`, in `RelativeFM.StacksInterface`; its
fields record exact statements and tag numbers from AxiomMath/Stacks. See also
`results/STACKS_INTERFACE.md`.

**Policy (see [`STACKS_POLICY.md`](STACKS_POLICY.md)).**  The formalization and results
of AxiomMath/Stacks may be used **freely**; a Stacks result that Axiom has formalized
counts as available and is not re-proved here merely to avoid depending on it.  Every
use is marked, and a proved result already here is kept, since replacing a proof by an
assumption would make the development depend on more.

AxiomMath/Stacks is **read, not imported**: `.scratch/stacks` uses Lean/Mathlib
4.35.0 and has no build artifacts, while this VM has Lean 4.33.1, read-only
Mathlib 4.33.1, and no Lake. Thus “assume Stacks” means supplying a `Prop`-valued
interface field, not adding an `axiom` or pretending an import works.  If Axiom's
repository is added to Mathlib or Lean, these fields become imports and the theorems
taking them lose the hypothesis. All other
literature results used below must be proved here. In particular, Spaltenstein
and Le--Chen 2.3 are formalized, not extra allowances; CHNS and other preprints
mentioned in older notes are not extra assumptions either.

Here **P** means proved in the stated scope, **N** means derived from an explicit
Neeman 3.2 input, **S** means supplied by the tagged interface if that layer is
used, and **R** means a bibliographic reference not consumed by a current proof.
Conditional theorems are not constructions from ring data until their inputs are
inhabited. Proved code uses only `propext`, `Classical.choice`, and `Quot.sound`;
no new global axioms are allowed.

## 1b. Named hypotheses outside the contract (not assumed)

These inputs appear as hypotheses of conditional theorems.  They are **not**
permitted assumptions: a theorem that takes one is recorded as conditional (C in
`results/COVERAGE.md`), and the input stays open until it is proved here.

| input | Lean name | used by | source | to discharge |
|---|---|---|---|---|
| Pseudofunctoriality of `L(-)^*` and `R(-)_*` as a family indexed by morphisms, with conjugate composition and unit isomorphisms | `DerivedPseudofunctorInput S` (`Scheme/DualityMates.lean`) | GL26 Lemmas 7.12–7.17 for `Duality.lean`'s base-change maps (`DerivedPseudofunctorInput.lemma_7_12`, `coherence`, `lemma_7_15`, `lemma_7_17_*`) | Lipman 2009, (3.6.2); GL26 Lemma 2.13 (`lem:spacey_Lipman_Hashimoto`) | construct `L(-)^*`, `R(-)_*` on the scheme model as pseudofunctors and prove (3.6.2) |
| Bousfield localization at a compact object: every `E` sits in a triangle `S → E → R → S⟦1⟧` with `S ∈ ⟨G⟩‾` and `R` right orthogonal to the shifts of `G` | `HasBousfieldTriangles G` (`Prelim/Lemma24.lean`) | only the secondary route `isLocalizingGenerator_of_isPaperGenerator`, `isPaperGenerator_iff_isLocalizingGenerator`; **no longer used by the headline GL26 Lemma 2.4** (`lemma_2_4` now uses Stacks 09SN, see §4).  `CompactBousfieldLocalization C` was deleted (it was stated with the refuted `Type`-valued `IsCompact`, hence trivially true; `Prelim/CompactnessAudit.lean`) | Neeman, *Triangulated categories* (2001), Rmk 1.16, Thm 1.17, Prop 9.1.19 | not needed for GL26 Lemma 2.4; Brown representability if the route is wanted |

## 2. The affine endpoint and what is actually proved

The universe-correct endpoint in `Scheme/SmallAffineAssembly.lean` is

```lean
RelativeFM.affine_theorem_1_1_small_standard_neeman_only
    (S : SetupMainMinimal DZ (SmallAffineD A H) DU)
    (hgen : standardT.le 0 =
      Coprod (shiftTail (S.G'⟦S.m⟧ ⊞ S.R.jShriek.obj S.GU) 0))
    (I : SmallNeemanCompactToPerfectInput A H) :
    SatisfiesWA (SmallAffineD A H) ↔ EventuallyHomZero S.G' S.G'
```

`H` can be `RelativeFM.Spaltenstein.affineSpaltensteinInput A`; it is not an
open assumption. `I` is Neeman 3.2(i), compact implies perfect. This formulation
uses no Stacks 09SR, ambient derived-coproduct package, or separate Hom-vanishing
hypothesis. It is nevertheless **not yet an unconditional construction from a
ring**: `S` and `hgen` still contain geometric and setup data.

| Proved result | Scope and remaining input |
|---|---|
| LP gluing Theorem 1.1 | Abstract development in `WeakApprox/` and `SmallAffineAssembly.lean`; only its displayed hypotheses. |
| Spaltenstein Theorem C and the small-Hom model | Unbounded K-projective replacements over every commutative ring; `SmallAffineD A H` and its equivalence with `AffineD A`. No literature input. |
| Standard ring generation | `standardT.le 0 = Coprod (shiftTail (ringObject A) 0)`, via `AisleGeneration.Ring.standard_le_zero_eq_coprod`. No input. |
| Specific-generator identities | `SpecificM3.concrete_tD_and_tZ_compactlyGenerated`: **both** standard-aisle identities, for `G' = ringObject A`, `m = 0` and `GU` the perfect supported generator, `R = I.toRecollement`. Unconditional: no large-coproduct package and no Stacks input is consumed. |
| Quasicoherent closure | 01IE patching, extension closure, triangulated `D_qc`, and the elementary kernel/cokernel/coproduct results in `QCohSerre*.lean`. No input for these statements. |
| Perfect modules and affine vanishing | Thick-envelope and boundedness calculus; model implies `Perf A`; Le--Chen 2.3; `perf_eventuallyHomZero` and its small-model analogue. Compact-to-`Perf` and 066S-style retract closure use only Neeman 3.2(i). |
| Perfect-to-compact reduction | Only thick-envelope closure is proved (`PerfectCompactThick.lean`). Compactness of the regular module is not thereby proved, and the small endpoint does not need it. |
| Local cohomology and most of the recollement | Concrete `RΓ_Z`, support, open adjunction, `iShriek`, kernel, mixed zero and both triangles. `C = RΓ_Z(A)` is the explicit two-term cone with `H⁰ = ker`, `H¹ = coker`. The last adjunction is below. |
| Affine diagonal and product generation | Lemma 2.25's categorical computation and Lemma 5.4's abstract cover argument, conditional on their explicit geometric data (`DiagonalIdentity.lean`, `AffineDiagonal.lean`, `Lemma54.lean`).  The two diagonal retraction identities are themselves derived from comparison data for derived pullback/pushforward and `Δ ≫ prᵢ = 𝟙`, in `DiagonalFunctoriality.lean`. |
| Convolution | Lemma 2.26's categorical core, corrected statement bridge and affine wrapper (`AffineConvolution.lean`), conditional on a derived cube with projection formulas, tensor compatibilities and an invertible 08IR mate. |

## 2b. Neeman's weak approximability: what is now proved

The campaign now *proves* Neeman's weak approximability instead of citing it, in the
paper's own zero-detection formulation.

**Proved, with no external input.**

| component | module |
|---|---|
| `PaperWeakApproximationData` — `WeakApproximationData` with `IsGenerator` replaced by the paper's `IsPaperGenerator` — and **LP Theorem 1.1 reproved** under zero detection throughout, including the two-stage approximation and Lemma 4.3(2) by retract/shift/left-adjoint transport of zero detection | `WeakApprox/Paper*M2.lean` (7 modules) |
| the approximation triangles, any bound `N ≥ 1` | `Scheme/NeemanApproximation.lean` |
| zero detection of the regular module, every commutative ring | `Scheme/NeemanPreferred.lean`, `Scheme/PaperGeneratorM5.lean` |
| the preferred `t`-structure, and the two aisle formulations agree | `Scheme/NeemanPreferred.lean` |
| generator bounds, in the large- and small-Hom models | `Scheme/NeemanGeneratorBoundsM5.lean` |
| compactness of `A[0]` and **perfect ⇒ compact** | `Scheme/AffineCompactness.lean` |
| **compact ⇒ bounded above** (Stacks 07LT's first paragraph) | `Scheme/CompactBoundedAbove.lean` |
| **the affine base case of Neeman 3.2(iii)–(iv)**, unconditionally for every commutative ring: `SatisfiesPaperWA` and `InPreferredClass` in the small-Hom model | `Scheme/AffineNeemanEndpointM3.lean` |
| the same package transported to the all-sheaves `D_qc(Spec A)` model, by generic equivalence-invariance lemmas | `Scheme/SchemeNeemanTransport.lean` |
| closed-support infrastructure for `Z ⊆ X`: support `= V(I)`, Serre closure, triangulated supported category with induced `t`-structure, supported `H⁰` cover and triangle, principal Koszul factorization | `Scheme/NeemanFiniteSupportM4.lean`, `PrincipalChainM4`, `PrincipalKoszulM4`, `IdealKoszulM4`, `DerivedSingleM4`, `ColimitHomologyM4` |

**`compact ⇒ perfect` is proved, unconditionally.**  `Scheme/M4Unconditional.lean`:

```
compactToPerfectInput_unconditional : CompactToPerfectInput A
perf_of_compact_unconditional {X : AffineD A} : IsCompactAb X → Perf A X
```

for every commutative ring, with no external input.  The chain, each link landed:
compact ⇒ bounded above (`CompactBoundedAbove`, Stacks 07LT's first paragraph, via the
truncation diagonal and an AB4 exact-coproduct transport); free resolutions with the
07LR Hom lift, the biproduct refinement and arbitrary-upper-bound transport
(`CompactToPerfectBoundedFree`, with 05T7(1) proved); the finite-free refinement
(`M4Improvement`: finite-support basis tails, a finite-free kernel of `tailMap`, a
K-projective coproduct epimorphism, `Shrink` enlargement, the short-exact improvement
triangle).  Two members reached the capstone independently.

The **model form** of 07LT is separate and still conditional: 066S's retract closure is
a named hypothesis in `model_of_compact_of_stableUnderRetracts_unconditional`.  It is
not needed for compact ⇒ `Perf`, because `Perf` is the thick envelope and absorbs the
retract.

**Consequences.**  The affine case of Neeman's weak approximability now has no unproved
input: `AffineNeemanEndpointM3.small_affine_neeman_3_2_iii_iv_base` was already
unconditional, and `Scheme/SmallAffineBridgeM5.lean`, `SmallHomTransportM5.lean` and
`SmallCompactToPerfectM5.lean` carry compactness and perfection between the large- and
small-Hom models (`Perf ↔ SmallPerf`, the equivalence triangulated), with
`SmallNeemanCompactToPerfectInput` constructed from a named factorization input.
`Scheme/SchemeNeemanTransport.lean` transports the package to the all-sheaves
`D_qc(Spec A)` model.

**What is not proved.**  066S's model form (retract closure of the bounded
finite-projective class, amplitude ≥ 2), where
`Scheme/StupidTruncCounterexample.lean` proves the naive truncation route cannot work
and `Scheme/Affine066SRetracts.lean` covers strict idempotents and one degree.  The
closed-support case `Z ⊊ X` is infrastructure only: the finite tensor Koszul `B_n`, the
supported coproduct `H⁰` assembly, the compact zero-detection generator there, and
`SatisfiesWA` are outstanding.  The scheme case beyond `X` affine is a reduction
(`Scheme/SchemeGluingReduction.lean`), not a theorem — Mathlib has no scheme-level
`D_qc` construction, which is the obstacle to stating it at all.

**A constraint discovered on the way, which changes the target.**  For `A = ℤ` the
regular module is **not** `IsGenerator` — `Scheme/GeneratorCounterexampleM5.lean` uses
the non-split injection `ℤ --2--> ℤ` and `Scheme/AffineNeemanAssembly.lean` uses a
nonzero `Ext¹(ℤ/2, ℤ)` class, two independent proofs — so no `WeakApproximationData`
with `G = ringObject` exists, and the original `G_generates` field had to be replaced
by the paper's zero detection.  That repair is the `Paper*M2` development above.

`D(A-Mod) ≌ D(QCoh(Spec A))` is proved in `AffineDictionary.lean`. The stronger
comparison with the **all-sheaves quasicoherent-cohomology** model is conditional
on `AffineDerivedGammaInput` or `AffineCohomologyComparison`; the small ring-valued
endpoint does not use it.

## 3. Stacks assumptions and the remaining work

**Active recollement assumptions.**

* **0A6R: assume.** Its normalized natural Čech comparison has the orientation
  required by `AffineJUpperTensorHom.e : jStar ⋙ affineDZι ≅ T`.
* **Derived tensor/RHom data: construct it, or assume it explicitly.** It is a
  separate input to `AffineCechTensorData.tensorHom`, whereas 0A6R is
  `AffineStacksInput.tag_0A6R`. The tensor data also includes the natural
  augmentation `cechToId`, which must be constructed before stating 0A6R's
  normalization. Together these give `jUpper` and `jStar ⊣ jUpper`; shift,
  exactness and full-faithfulness consequences are already proved in
  `AffineJUpperAdjoint.lean`. In particular, **0A6R is not the tensor--Hom
  adjunction**. The wrong candidate `Rj_* Lj^*` is proved zero in
  `AffineJUpperCandidateRefuted.lean`.

For the ordinary all-sheaves comparison, direct **06Z0** is the shortest allowed
route. The stronger `AffineDerivedGammaInput` route uses 06Z0/079W/08D4/01XB;
01HV is already proved. Other GL26 layers use the tags in the census only when
their proofs actually invoke those fields. Existing cheap proofs (01IE, 066T,
Spaltenstein, ring generation and vanishing) should not be replaced by stronger
assumptions.

**Open or incomplete.**

1. Construct/instantiate `DerivedTensorHomData`, the Čech augmentation
   `cechToId`, and the 0A6R comparison to finish the sole remaining concrete
   recollement adjunction.
2. Construct the remaining approximation, normalization, glued-generator and
   large/small transport data from ring data and Neeman. An abstract
   `SetupMainMinimal` argument is not such a construction.
3. Prove the other GL26 targets against corrected interfaces. The old ten
   `sorry`s in `FourierMukai/Paper/Statements.lean` are superseded specifications,
   not dependencies of the affine endpoint.

A Neeman-free proof of all of 066S remains optional; its affine consequence is
already N. Full scheme/algebraic-space GL26 is outside the affine-base claim.

## 4. Census of every tag cited in the original Lean sources

The original census covers `FourierMukai/**/*.lean` and `WeakApprox/*.lean` (57
tags). Hybrid rows are deliberate: an affine consequence does not prove a whole
general Stacks tag. New interface/companion-module tags follow this table.

| Tags | Status and exact scope |
|---|---|
| 0096, 00A6, 00AB, 00NX, 01BD | P: the cited sheaf-level pullback/extension-by-zero, associated-sheaf, and affine-local quasicoherence facts. Derived functors are separate. |
| 01HV, 01IE | P: exact affine `tilde`; affine extension patching and its extension-closure/triangulated consequences. |
| 01LA, 01LB | P for active coproduct/kernel/cokernel/extension closure; S only for stronger uninstantiated legacy interfaces. Arbitrary subobject/quotient instances are not claimed. |
| 01C6 | P for elementary finite-locally-free facts; S for the remaining vector-bundle calculus fields. |
| 0657, 066R, 066T | P in the module-model development: definitions/elementary retract facts and model implies `Perf A`. |
| 066S | N for affine retract closure. No unconditional full-tag proof is claimed. |
| 07LR, 07LT | P for finite-free induction lemmas; N for compact-to-model/`Perf` used by the endpoint. The two 07LR input packages are not silently inhabited. Reverse perfect-to-compact does not follow. |
| 09M1, 0AED | N in the affine ring model (`compactPerfectInput_of_neemanModel`); S for general supported schemes/spaces. The small endpoint uses only compact-to-perfect. |
| 09M8 | P for the thick-envelope reduction only; S if full perfect-to-compact is required. |
| 09MB | P for the perfect-pair affine ring form used here; S for the general amplitude statement. |
| 09SR | P for abstract reductions, absent from the small affine endpoint; S for a geometric instance that really needs classical generation. |
| 0AEC | N for the compact-generator package from Neeman 3.2(ii); S for another geometric instance. No independent construction is asserted. |
| 08CM, 0BCJ | P for proved ring boundedness/model facts; S for the general scheme-local characterization and all-sheaves bridge. Definitions of perfectness are not silently identified. |
| 0GFH, 0GFI | S for general GL26 boundedness criteria; R for the affine ring-vanishing proof, which proves only its stated special case. |
| 06Z0 | S for the actual all-sheaves `D_qc` comparison/coherence. The separate ordinary QCoh equivalence is P without it. |
| 079W, 08D4, 01XB | S for `AffineDerivedGammaInput`; R for the small ring endpoint. |
| 07A6 | P for concrete affine scalar restriction/extension; S for general geometric derived pull/push. |
| 0BFF | **R, and the citation was wrong.** 0BFF is Lemma 39.9.7, the formula `[n]^*L = L^(n(n+1)/2) (x) ([-1]^*L)^(n(n-1)/2)` for abelian varieties; it has nothing to do with the localization sequence. The citation has been removed from `AffineRecollement.lean` and `AFFINE.md`, and the sources for the recollement are Gao--Psaroudakis 2.2(ii), Balmer--Dell'Ambrogio--Sanders 2.3 and Krause section 4. The power-torsion and localization-vanishing facts are proved here independently of any tag. |
| 08D5, 08DQ | R: an alternative proof of eventual vanishing documented in `Scheme/Inputs.lean`, not an affine dependency. |
| 094A, 09SP | R now; S only if the Brown-representability/09SR route is instantiated. |
| 09SN | **S, active** (25 Nov 2026): see the 09SN/090Z rows below; used by GL26 Lemmas 2.4 and 2.5. |
| 08IN, 08IR | P for abstract computations/mates once data is supplied; S for the geometric projection formula and Tor-independent base change. |
| 08CR, 08CS, 0FPU, 0FPV | S for general perfect-thickness and vector-bundle dual/tensor interfaces. Ring analogues do not inhabit these scheme structures. |
| 08J9, 08JJ, 0E55, 0E5D | S for the perfect-duality and exceptional-functor interface fields; categorical consequences after those inputs are P. |
| 08H4 | S: derived pullback preserves pseudocoherence via `PullbackStacksInput`; its occurrence in `Scheme/Statements.lean` alone proves no target. |
| 09IY, 07TZ, 09TF | S for future GL26 proofs; currently specification-only in `Scheme/Statements.lean`. |
| 0BY7, 0BY9, 0FD2, 0FW1, 0A26 | S for the elliptic-fibration target; currently specification-only. |
| 0A6R | **S, active:** normalized local-cohomology/Čech-tensor comparison, not the derived tensor--Hom adjunction. |
| 07A4, 0D6D, 0D6E | New in `AffineConvolution.lean`: P for the categorical convolution; S for geometric pullback--tensor and pseudofunctoriality data used to build its cube. |
| 08IR (`FMCube.lean`) | **S, as named `Prop`s** `RelativeFM.FMCube.FlatBaseChangeLeft`, `FlatBaseChangeRight`: invertibility of the base change map `θ_□` (GL26 Lemma-Definition 7.13) for the two faces `Y₁₂T = Y₁₂ ×_{Y₁} Y₁T`, `Y₁₂T = Y₁₂ ×_{Y₂} Y₂T` of the cube of GL26 Setup 2.20 (Tor-independent since `f'₂`, `f'₁` are flat). Hypotheses of GL26 Lemmas 6.11 (`Right`) and 10.1 (`Left`); Lemma 10.2 uses neither. |
| 08EU, 08IN (`FMCube.lean`) | **S, as a named `Prop`** `RelativeFM.FMCube.ProjectionFormula`: the projection map `R t'_*E ⊗ K ⟶ R t'_*(E ⊗ L t'^*K)`, defined as the mate of monoidality (`TensorPullPushData.projMap`), is invertible. Hypothesis of GL26 Lemma 10.1 only. |

### Additional tagged-interface fields and alternative inputs

These were not in the original 57-tag census.

| Tags | Status and exact scope |
|---|---|
| 0E56 | S: quantitative bounded-below statement for `f^×`, with uniform bound loss `N`; boundedness of `f^× O_X` is a special case. |
| 0A8A | S: `RHom(K,L)` has quasicoherent cohomology under either the pseudocoherent/`D^+_qc` or perfect/`D_qc` alternative. |
| 04LX, 08JB | S: étale-chart site identification and invertibility of derived-`RHom` restriction. 04M1/04M3 are subsidiary references in 04LX, not extra fields. Not used by the small LP endpoint. |
| 0A6H, 0D0S | S: global 0A6H(1),(2), excluding clauses (3),(4); and coherent bounded-below cohomology of `RHom`, respectively. |
| 08H6 | S: derived pullback preserves perfectness, companion to 08H4 in `PullbackStacksInput`. |
| 08F5, 0FPQ | S for 08F5: derived tensor preserves quasicoherent cohomology. 0FPQ records construction provenance, not an independent `Prop` field. |
| 0A8Z | S only for the alternative complex-level internal-Hom/tensor adjunction; unnecessary if the derived package is built directly. |
| 08J8 (08DI on ringed spaces) | S if derived tensor--Hom is taken from Stacks. The categorical adapter proves internal currying from this adjunction, so currying is not another assumption. |
| 09IR, 0A9A, 09M1 (affine supported base) | S: the affine supported base consumes `KoszulScalarSupportInput` (tagged 09IR), `KoszulDetectionInput` (0A9A: finite Koszul zero detection; no AxiomMath declaration name recorded yet) and `IdealSupportedCompactnessInput` (09M1 form), plus three named inputs that are not Stacks results -- `IdealSupportedCoproductInput` (supported direct sums), `KoszulPowerCoprodInput` (Neeman, Construction 7.3, finite-power envelope) and `AffineSupportedSchemeComparisonInput` (supported module/scheme comparison). **Status (`Scheme/KoszulInputs.lean`):** `KoszulScalarSupportInput` is **refuted** for every nontrivial ring (`KoszulInputs.not_koszulScalarSupportInput`: its `mem_le_zero` field quantifies over all perfect `X`, and fails for `a = 0`, `X = A[0]⟦-1⟧`), so every theorem taking `hS` is vacuous outside the zero ring. The true replacements are proved there (`scalarConeData_isSupported`, all perfect `X`; `scalarConeData_le_zero`, for `X ≤ 0`), and wiring them into `FiniteKoszulM1.koszulListData` needs a change to that shared file. `IdealSupportedCoproductInput` and `IdealSupportedCompactnessInput` are **proved** for every finite list (`idealSupportedCoproductInput`, `idealSupportedCompactnessInput`), so they are no longer assumptions. Still open: `KoszulPowerCoprodInput`, `KoszulDetectionInput`, `AffineSupportedSchemeComparisonInput`. The **principal** closed support `V(f)` needs none of them (`PrincipalNeemanM1`). |
| 09SR (open/closed glue, wave 3) | S, carried as the `Prop` `RelativeFM.OpenClosedCompletionW3.Tag09SRPaper` (a field of `SupportedCategoryInput`), not yet moved into `RelativeFM.StacksInterface`: `RelativeFM.OpenClosedCompletionW3.Tag09SRPaper C` (`Scheme/OpenClosedCompletion.lean`), Stacks 09SR (2) ⇒ (1) for one generator: with small coproducts, a compact zero-detecting object classically generates the compacts. AxiomMath/Stacks `CategoryTheory.Pretriangulated.isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated` (`StacksFrontier/CategoryTheory/Triangulated/CompactObjects/CompactGenerators.lean`), with `IsCompactObject.{v}` read as `IsCompactAb` and `IsWeakTriangulatedGenerator (singleton E)` as `IsPaperGenerator E` (the comparison is not proved here). Unlike the older `Stacks09SR` it uses zero detection, not `IsGenerator`. Taken as the `tag_09SR` field of `SupportedCategoryInput`, a named hypothesis, because `StacksInput.lean` is shared; the orchestrator may move it into `StacksInterface`. The same structure carries **Neeman 2024 Thm 3.2(iii)** (`neeman_3_2_iii`: the restricted standard `t`-structure is in the preferred class), which is not a Stacks result and not the allowed direction of Thm 3.2, so it is a named non-Stacks input (affine `AffineD` analogue proved: `RegularCompact.affine_standard_inPreferredClass`). |
| 090Z | Definition, not an assumption: `RelativeFM.StacksInterface.IsHomotopyColimit` (`Prelim/Stacks09SN.lean`), verbatim from AxiomMath/Stacks `CategoryTheory.Pretriangulated.IsHomotopyColimit` (`StacksFrontier/CategoryTheory/Triangulated/HomotopyColimit.lean`). |
| 09SN | S: `RelativeFM.StacksInterface.Tag09SN D` (`Prelim/Stacks09SN.lean`), verbatim from AxiomMath/Stacks `CategoryTheory.Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated` (`StacksFrontier/CategoryTheory/Triangulated/CompactObjects/CellStructure.lean`) with `IsCompactObject.{v}` replaced by `RelativeWeakApprox.IsCompactAb` (same notion: the `AddCommGrpCat` coproduct is the direct sum; the comparison of the two predicates is not proved here).  Taken as a hypothesis by `StacksInterface.isLocalizingGenerator_of_tag09SN`, GL26 Lemma 2.4 `RelativeFM.lemma_2_4`, `singlyCompactlyGenerated_iff`, `lemma_2_5_of_tag09SN`, and `singlyCompactlyGenerated_smallRingObject`.  `RelativeFM.lemma_2_5` itself does not take it. |

## 5. Verification

From the repository root run `./scripts/build.sh`, or compile one module with

```bash
LEAN_PATH="$LEAN_PATH:." lean -o FourierMukai/Scheme/<Module>.olean \
  FourierMukai/Scheme/<Module>.lean
```

Allow at least 300 seconds. Check the exit status and grep for `error`:
`#print axioms` prints even after errors. Audits belong in the defining module;
only a full build detects stale `.olean` files and duplicate umbrella names.
