# Assumption ledger: AxiomMath/Stacks + Neeman

## 1. Contract and terminology

The only permitted external mathematical inputs are the **tagged Stacks
interface** and **Neeman, Acta Math. 233 (2024), Theorem 3.2**. The interface is
`FourierMukai/Scheme/StacksInput.lean`, in `RelativeFM.StacksInterface`; its
fields record exact statements and tag numbers from AxiomMath/Stacks. See also
`results/STACKS_INTERFACE.md`.

AxiomMath/Stacks is **read, not imported**: `.scratch/stacks` uses Lean/Mathlib
4.35.0 and has no build artifacts, while this VM has Lean 4.33.1, read-only
Mathlib 4.33.1, and no Lake. Thus “assume Stacks” means supplying a `Prop`-valued
interface field, not adding an `axiom` or pretending an import works. All other
literature results used below must be proved here. In particular, Spaltenstein
and Le--Chen 2.3 are formalized, not extra allowances; CHNS and other preprints
mentioned in older notes are not extra assumptions either.

Here **P** means proved in the stated scope, **N** means derived from an explicit
Neeman 3.2 input, **S** means supplied by the tagged interface if that layer is
used, and **R** means a bibliographic reference not consumed by a current proof.
Conditional theorems are not constructions from ring data until their inputs are
inhabited. Proved code uses only `propext`, `Classical.choice`, and `Quot.sound`;
no new global axioms are allowed.

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
| Affine diagonal and product generation | Lemma 2.25's categorical computation and Lemma 5.4's abstract cover argument, conditional on their explicit geometric data (`AffineDiagonal.lean`, `Lemma54.lean`). |
| Convolution | Lemma 2.26's categorical core, corrected statement bridge and affine wrapper (`AffineConvolution.lean`), conditional on a derived cube with projection formulas, tensor compatibilities and an invertible 08IR mate. |

## 2b. What of Neeman is now proved (weak approximability)

The campaign now aims to *prove* Neeman's weak approximability rather than cite it.
Progress, all `P` (no external input):

| Neeman 3.2 component | status |
|---|---|
| the approximation triangles | **proved**: `Scheme/NeemanApproximation.lean`, `exists_approximation_triangle` — for `F` in the standard aisle of `D(A-Mod)` there is a distinguished triangle `E → F → D → E⟦1⟧` with `E ∈ ⟨A⟩^[-1,1]` and `D ∈ t^{≤-1}`; any bound `N ≥ 1` by monotonicity |
| zero detection (generation) | **proved**: `ringObject_isPaperGenerator`, `Scheme/NeemanPreferred.lean` and `Scheme/PaperGeneratorM5.lean`, for every commutative ring, by projective lifts to cycles |
| the preferred `t`-structure | **proved modulo compactness of `A[0]`**: `standard_inPreferredClass`, plus `le_zero_eq_coprod_compactInAisle` showing the two aisle formulations agree (no counterexample) |
| the generator bounds | **proved**: `Scheme/NeemanGeneratorBoundsM5.lean`, in both the large-Hom and small-Hom models |
| compactness of `A[0]` | open; this is what `PerfectToCompactInput` still lacks |
| scheme case | reduced, not proved: `Scheme/SchemeGluingReduction.lean` proves the gluing steps from `SetupMainMinimal` + compact Hom vanishing and notes that LP's Corollary 1.2 cites Neeman for schemes rather than proving it by gluing |

**A constraint discovered on the way, which changes the target.**  For `A = ℤ` the
regular module is **not** `IsGenerator`: `Scheme/GeneratorCounterexampleM5.lean`
exhibits the non-split injection `ℤ --2--> ℤ`, whose connecting map is a nonzero
ghost out of the shifts of `ℤ`; and consequently no `WeakApproximationData` on
`SmallAffineD ℤ` can have `G = smallRingObject`.  So LP's structure *as formalised*
cannot be inhabited by the regular module: either the generator must be a different
object, or the `G_generates` field must be weakened to the paper's zero detection
(`IsPaperGenerator`), which is what Neeman and LP actually use and what survives for
the regular module.  This is the sharpest open design question in the project.

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
| 094A, 09SN, 09SP | R now; S only if the Brown-representability/09SR route is instantiated. |
| 08IN, 08IR | P for abstract computations/mates once data is supplied; S for the geometric projection formula and Tor-independent base change. |
| 08CR, 08CS, 0FPU, 0FPV | S for general perfect-thickness and vector-bundle dual/tensor interfaces. Ring analogues do not inhabit these scheme structures. |
| 08J9, 08JJ, 0E55, 0E5D | S for the perfect-duality and exceptional-functor interface fields; categorical consequences after those inputs are P. |
| 08H4 | S: derived pullback preserves pseudocoherence via `PullbackStacksInput`; its occurrence in `Scheme/Statements.lean` alone proves no target. |
| 09IY, 07TZ, 09TF | S for future GL26 proofs; currently specification-only in `Scheme/Statements.lean`. |
| 0BY7, 0BY9, 0FD2, 0FW1, 0A26 | S for the elliptic-fibration target; currently specification-only. |
| 0A6R | **S, active:** normalized local-cohomology/Čech-tensor comparison, not the derived tensor--Hom adjunction. |
| 07A4, 0D6D, 0D6E | New in `AffineConvolution.lean`: P for the categorical convolution; S for geometric pullback--tensor and pseudofunctoriality data used to build its cube. |

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

## 5. Verification

From the repository root run `./scripts/build.sh`, or compile one module with

```bash
LEAN_PATH="$LEAN_PATH:." lean -o FourierMukai/Scheme/<Module>.olean \
  FourierMukai/Scheme/<Module>.lean
```

Allow at least 300 seconds. Check the exit status and grep for `error`:
`#print axioms` prints even after errors. Audits belong in the defining module;
only a full build detects stale `.olean` files and duplicate umbrella names.
