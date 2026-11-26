# Open inputs: triage of every named hypothesis in the tree

Task `wave5/open-inputs` (brief: `results/swarm/archive/wave5/open-inputs.md`), written on
26 November 2026 against `origin/formalization` at `a65ef98`.  Reading only: no Lean
was changed and nothing was built.  Every row was checked against the Lean
definition (fields as written, not the docstring); consumers were found by scanning
the signatures (the part before `:=`) of every `theorem`/`lemma`/`def` in
`FourierMukai/` and `WeakApprox/`.  In the consumer column, **[P]** marks a
declaration pinned in `results/statement-baseline.txt` and **[A]** one with a
`#print axioms` line in `FourierMukai/Audit.lean`.

**Maintainer's goal (26 Nov 2026).** AxiomMath's Stacks Project is the only
assumption; everything else GL26/LP26 need comes from Mathlib or is proved here.

**Wave 6 (`wave6/prune-dead-inputs`).**  The rows marked **delete** were acted on;
each such row now ends with its outcome ("deleted (wave 6)" or "kept: reason").

## Verdicts used

| verdict | meaning |
|---|---|
| **Stacks** | a Stacks result; the AxiomMath declaration is named (from `results/AXIOMMATH_TAGS.md`, or from a search of AxiomMath/Stacks at `f56a316` for tags the papers do not cite), with how the repository's rendering compares |
| **Mathlib** | Mathlib has it; the declaration is named |
| **prove** | on a GL26/LP26 path and neither of the above.  Size S < 200 lines, M < 1000, L more.  **now** = can be done in the affine/abstract model today; **AX** = only after the algebraic-space layer (AxiomMath import, `wave5/spaces-foundations`) |
| **proved** | already inhabited in the tree with no hypothesis (the closing declaration is named).  Nothing to prove; the structure can be inlined or kept |
| **delete** | no GL26/LP26 path needs it, or it is false or vacuous (refutation named, or the argument given when the refutation is not yet in the tree) |
| **setup** | not an assumption: the paper's own hypothesis or setup data (or an interface that stands for the paper's objects until the spaces layer replaces it) |
| **being removed** | a Neeman 2024 Thm 3.2 input that `wave5/neeman-prune` is removing; listed for completeness |

**Model warning, which applies to every `AX` row.**  The repository has its own
scheme-level model (`Dqc X`, `DqcSupported X Z`, `SchemeD X`: Mathlib's
`DerivedCategory X.Modules` on the Zariski site).  AxiomMath's model is different
(`D(𝒪_X)` on the small étale site, `QcohDerived`).  A Stacks field stated in the
repository's model is discharged by AxiomMath only after a model comparison, which
nobody has proposed to build.  The plan in `results/SWARM.md` ("Direction") restates
the results in AxiomMath's model instead.  So for the scheme-level rows below the
realistic verdict is "restate in AxiomMath's model, then delete the repo row", and
the size estimates are for that restatement.

## 0. Items that look false or vacuous as stated (read first)

These were found during the triage.  **F1–F3 are now proved in the tree** (wave 6,
`Scheme/RefuteLargeCoproducts.lean`, `RefuteIntGenerator.lean`,
`RefuteIntGeneratorSmall.lean`, `RefuteQCohSerre.lean`); the two F1 endpoints were unpinned.

* **F1. `HasCoproducts.{u+1} (AffineD A)` is false for every nonzero ring `A`.**
  So `AffineDerivedCoproducts A DZ DU` (field `hasCoproductsA`) has no instance, and
  every theorem taking it is vacuous for `A ≠ 0`.  That includes the **pinned**
  `RelativeFM.affine_theorem_1_1_neeman_only` and
  `RelativeFM.StacksGluing.affine_theorem_1_1_stacks07LT`, the audited
  `Neeman32Inputs.affine_theorem_1_1_of_tag09SR` (the `neeman-prune` replacement of
  the first one), `AffineGluingInput`, and the instance-argument lemmas in
  `AffineSupportedCoprodLift.lean` and `AffineKoszulGenerator.lean:209`.
  *Argument.* Let `k = A/𝔪` and let `I : Type (u+1)` have cardinality greater than
  every `u`-small cardinal (for example `I = Cardinal.{u}`).  If `C = ∐_{I} A[0]`
  existed, then `Hom(C, k[0]) ≅ ∏_{I} k`, which is not `u`-small.  But `AffineD A` is
  locally `u`-small: by Spaltenstein (`AffineSpaltensteinInput`, proved) `C` has a
  K-projective replacement by `u`-small modules, so `Hom(C, k[0])` is a quotient of a
  `u`-small set (the tree already has `locallySmallDerivedCategoryOfKProjectiveReplacementData`).
  Formalizing this is S.  The small-Hom model `SmallAffineD` is not affected.
* **F2. `D(ℤ)` has no compact object that is `IsGenerator`** (shifts separate
  morphisms).  So `WeakApproximationData (AffineD ℤ)` and
  `WeakApproximationData (SmallAffineD ℤ H)` are empty, `SatisfiesWA (D(ℤ))` is false,
  and `SetupMainMinimal DZ D DU` is empty whenever `D ≃ D(ℤ)`.  The tree proves only
  the special case `G ≠ ringObject ℤ` (`weakApproximationData_int_G_ne_ringObject`,
  `no_weakApproximationData_ringObject_int`).
  *Argument.* A compact `G` is perfect (`compactToPerfectInput_unconditional`).  Over
  ℤ it is a finite sum of shifts of `ℤ` and of `ℤ/q^e`.  Pick a prime `p` not dividing
  any of these `q`.  The nonzero class `φ : ℤ/p → ℤ[1]` is a ghost for `G`: every
  composite `G[n] → ℤ/p → ℤ[1]` lands in `Ext¹(ℤ,ℤ) = 0`, or factors through
  `Hom(ℤ/q^e, ℤ/p) = 0` or `Ext¹(ℤ/q^e, ℤ/p) = 0`.  Formalizing this is S–M.
  Consequence: every `IsGenerator`-based endpoint is satisfiable at most for rings
  like fields.  These are the **pinned** `RelativeWeakApprox.SetupMainMinimal.theorem_1_1`,
  `RelativeFM.affine_theorem_1_1_small` and the two F1 endpoints.  The paper's
  "compact generator" is zero detection (`IsPaperGenerator`), which the `Paper*`
  forms already use.
* **F3. `QuasicoherentSerreInput X` and `QuasicoherentStrongClosureInput X` are false
  for `X = Spec ℤ`.**  Their `subobjects` and `quotients` fields claim that
  quasi-coherent modules are closed under arbitrary `𝒪_X`-submodules and quotients.
  For `U = D(2)`, `j_!𝒪_U ⊂ 𝒪_X` is not quasi-coherent: its stalk at `(2)` is 0 but its
  generic stalk is not.  Neither is `𝒪_X / j_!𝒪_U`.  Stacks 01LA asserts only kernels,
  cokernels and extensions.  The extension-only route (`QuasicoherentExtensionInput`,
  proved) has replaced them.
* **F4. Contentless as stated (inhabited trivially).**  `CompactsArePerfect C`: its
  `Perf` is a free field, so `Perf := IsCompactAb` inhabits it.  The same holds for
  `SchemePerfectStacksInput.tag_09M1` = `PerfectCompactStatement H compact`, where
  `compact` is a free `ObjectProperty`.  Neither is false, but neither carries the
  Stacks content it is named after (the AxiomMath cross-check already notes 09M1).
* **F5. Already known and refuted in the tree:** `Neeman_3_2_ii` (`IsGenerator`
  rendering, `GeneratorCounterexampleM5`); `RegularModuleApproximationInput.generates`
  (`no_weakApproximationData_ringObject_int`); the deleted `KoszulScalarSupportInput`.
* **F6. Risk in `wave5/neeman-prune` (not a false statement).**  `CompactPerfectInput A`
  is inhabited **with no hypothesis at all** in the large model:
  `compactPerfectInput_of_separateInputs A (M4Unconditional.compactToPerfectInput_unconditional A) (perfectToCompactInput A)`.
  That is stronger than the 09SR route (`Neeman32Inputs.compactPerfectInput A h09`)
  which the prune brief prescribes.  The prune brief's step 3 deletes producers of
  Neeman inputs in `M4Unconditional.lean` and `M6Unconditional.lean`; these
  unconditional proofs should be kept.

## 1. Stacks-interface fields and tagged `Prop`s

`Scheme/StacksInput.lean` and the tagged `Prop`s elsewhere.  All the signatures in
`StacksInput.lean` (`InternalHomSignature`, `UpperCrossSignature`,
`EtaleRestrictionSignature`, `ProjectionFormulaSignature`, …) have **free** categories,
functors and `Prop`s such as `qcqs`, so a field states its tag only once the signature
is instantiated with AxiomMath's objects.  The fields in rows 1.1–1.7 feed **no**
headline result: their only consumers are lemmas inside `StacksInput.lean`.

| # | name (file) | what it says (Lean) | consumers / headline | verdict |
|---|---|---|---|---|
| 1.1 | `StacksInput` (`StacksInput.lean`) | fields `tag_07A6` (`qcqs → pull ⊣ push`), `tag_0E55` (`qcqs → push ⊣ upperCross`), `tag_0E56` (uniform `N` bound for `f^×` on `D^+`), `tag_0A8A` (`RHom` preserves `D_qc` in two cases), `tag_04LX` (localization is an equivalence), `tag_08JB` (`RHom` commutes with restriction), `tag_0A6H` (global 0A6H(1),(2)), `tag_0D0S` (`RHom(D⁻_coh, D⁺_coh) ⊆ D⁺_coh`) | `upperCross_maps_boundedBelow`, `rhom_mem_dqCoh_and_locallyBoundedBelow` (same file); no headline | **Stacks**: 07A6 `DerivedPullbackOfToposHom.derivedAdjunction`; 0E55 `Space.isLeftAdjoint_quasicoherentDerivedPushforward` (repo **stronger**: it names the adjoint); 0E56 `Space.quasicoherentDerivedRightAdjoint_boundedBelow` (same); 0A8A `Space.qcohDerived_smallEtaleDerivedSheafHom` (same); 04LX `Space.smallEtaleRingedEquivalenceOverChart` (same); 08JB untagged `Space.smallEtaleDerivedSheafHomEtaleRestrictionIso` (AxiomMath gives an iso; the repo asks `IsIso` of its own map); 0A6H **schemes only** in AxiomMath, while the repo uses it on a space; 0D0S AxiomMath **weaker**.  All only after instantiation |
| 1.2 | `MorphismStacksInput` (`StacksInput.lean`) | `tag_07A4 : IsIso pullTensor`; `tag_08IN : qcqs → IsIso projectionFormula`; `tag_08IR : qcqs → torIndependent → IsIso comparison` | none outside the file | **Stacks**: 07A4 untagged `Space.smallEtaleDerivedPullbackTensorIso` (the tagged one is at `{u,u,u}` and does not apply to spaces); 08IN `Space.isIso_smallEtaleProjectionFormulaMap`; 08IR `Space.isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent`.  Same after instantiation, once the repo's maps are identified with AxiomMath's |
| 1.3 | `PerfectStacksInput` (`StacksInput.lean`) | `tag_08J9` (currying iso), `tag_08JJ` (double dual and dual-tensor isos for perfect objects), `tag_08J9_08JJ_rhomTensor` (GL26 Lemma 2.10's map iso for perfect `K`) | `toPerfectDualityData` (same file) | **Stacks** for 08JJ (untagged `Space.smallEtaleDerivedBidualIso`, `…SheafHomIsoTensorDual`).  08J9: AxiomMath has it only at `{u,u,u}`, **not for spaces** (gap C.5 in `AXIOMMATH_MAP.md`).  The third field is GL26 **Lemma 2.10** (`lem:rhom_tensor_morphism`), so it is **prove** (S, AX), not a Stacks field |
| 1.4 | `AffineHomStacksInput` (`StacksInput.lean`) | `tag_0A6H_3a`, `tag_0A6H_3b`: the `RHom`/`tilde` comparison is iso for pseudo-coherent `K` with bounded-below `L`, resp. for perfect `K` | none | **Stacks** 0A6H(3): `isIso_affineDerivedTildeHomComparison_of_isPseudoCoherent`, `affinePerfectDerivedSheafHomIso`; same once `comparison` is AxiomMath's.  Off path |
| 1.5 | `AffineComparisonStacksInput` (`StacksInput.lean`) | `tag_06Z0 : Nonempty (AffineCohomologyComparison A)` (`D(QCoh(Spec A)) ≌ D_QCoh` as an equivalence of plain categories) | `comparison`, `ringCohomologyEquivalence` (same file) | **Stacks** 06Z0 `derivedGlobalSectionsQuasicoherent_isEquivalence`, but in AxiomMath's model; the repo's target is Mathlib's `DerivedCategory (Spec A).Modules`.  Off the pinned path |
| 1.6 | `PullbackStacksInput` (`StacksInput.lean`) | `tag_08H4`, `tag_08H6`: `qcqs →` `Lf^*` preserves pseudo-coherence, resp. perfectness | none | **Stacks**, untagged for spaces `Space.isPseudoCoherent_smallEtaleDerivedModulePullback`, `Space.isPerfect_smallEtaleDerivedModulePullback`.  The repo is weaker (it adds `qcqs`) |
| 1.7 | `TensorStacksInput` (`StacksInput.lean`) | `tag_08F5`: `⊗^L` preserves `D_qc` | none | **Stacks** 08F5 `Space.qcohDerived_smallEtaleDerivedTensor` (same after instantiation) |
| 1.8 | `SchemePerfectStacksInput` (`StacksInput.lean`) | `tag_08CR` (2-of-3 for perfect objects), `tag_08CS` (retracts of perfect objects are perfect), `tag_09M1` = `PerfectCompactStatement H compact` with a **free** `compact` | `toPerfectThicknessInterface`, `toPerfectCompactInterface` | **Stacks** for 08CR (`PerfectComplexTriangles.isPerfect_obj₂_of_distinguished`) and 08CS (`TorAmplitude.isPerfect_of_biprod`; summand rather than retract).  The repo's `IsPerfect` lives on its own `SchemeD X` (different model).  `tag_09M1` is **contentless** (F4).  Off path: **delete**, then restate on AxiomMath's `IsPerfect` when needed **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 1.9 | `AffineStacksInput` / `Tag0A6R` / `AffineCechTensorData` (`StacksInput.lean`) | there is `e : RΓ_Z ≅ RΓ_Z(A) ⊗^L (-)` with `e ≫ cechToId = counit`, for a free `tensorHom` and `cechToId` | `cechIso`, `jStarAdj`, `jUpperConsequences` (same file) | **delete**: it was the 0A6R route to `jUpper`, superseded by `affineRecollementInputOfIShriek` (wave 2).  If it is ever wanted: Stacks 0A6R `LocalCohomology.CechFormula.localCohomologyCechIso` (AxiomMath is stronger: any finite generating family) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 1.10 | `AffineCech.ComparisonInput` (`AffineDerivedTensorHom.lean`) | `tag_0A6R : Nonempty (RΓ_Z ≅ T.tensorLeft (RΓ_Z A))` | `adjointInput`, `toAffineRecollementInput`, `toRecollement*` (same file) | **delete** (same superseded route as 1.9) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** The superseding route `affineRecollementInputOfIShriek` is kept. |
| 1.11 | `AffineOpenRightAdjointStacksInput f iShriek` (`AffineDerivedTensorHom.lean`) | `tag_0E55 : Nonempty (derivedRestrictionScalars A f ⊣ iShriek)` | **[A]** `affineRecollementInputOfStacks0E55` → GL26 **Lemma A.4** (`lem:spacey_recollement`), affine case | **prove (M, now)**.  The right adjoint of `Rj_*` is derived coextension `RHom_A(A_f, -)`.  It exists for every ring by K-projective replacement of `A_f` (Spaltenstein is proved; `KProjHomComplex.lean` has the Hom complex).  This makes Lemma A.4 (affine) unconditional.  Alternative: Stacks 0E55 (`Space.isLeftAdjoint_quasicoherentDerivedPushforward`) plus the affine dictionary, which is longer |
| 1.12 | `AffineDerivedClosedStacksInput A` (`AffineDerivedTensorHom.lean`) and `SymmetricMonoidalClosedInput D` (`DerivedTensorHomClosed.lean`) | there exist a monoidal structure on `AffineD A`, a symmetric structure, `rhom` and all adjunctions `tensorLeft E ⊣ rhom E` | `affineDerivedTensorHomData`, `derivedTensorHomDataOfInput` | **prove (M–L, now)** in the affine model: `⊗^L` and `RHom` on `D(A-Mod)` via K-projective (or K-flat) replacements.  **Mathlib** has no derived tensor (`archive/MATHLIB_INVENTORY.md` M11).  It is needed for the affine forms of GL26 Lemmas 2.25 and 2.26 (rows 6.9, 6.12).  For spaces it is AxiomMath's 06YU/08J8 (gap C.5) |
| 1.13 | `Tag09SN D` (`Prelim/Stacks09SN.lean`) | for compact `E i` whose shifts detect zero, every `X` is a homotopy colimit of a sequence of cells built from coproducts of shifts of the `E i` | **[A]** `lemma_2_4`, `singlyCompactlyGenerated_iff`, `lemma_2_5_of_tag09SN`, `isLocalizingGenerator_of_tag09SN` → GL26 **Lemma 2.4** (`lem:localizing_iff_cpt_gen`), Lemma 2.5 (zero-detection form) | **Stacks** 09SN `Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated`.  Same statement **modulo** `IsCompactObject.{v}` vs `IsCompactAb`; that bridge is **prove (S–M, AX)** (gap C.10) |
| 1.14 | `Tag09SRPaper C` (`OpenClosedCompletion.lean`) | for triangulated `C` (`[IsTriangulated C]`, as AxiomMath's 09SR; added 26 Nov 2026): `HasCoproducts.{v} C → ∀ G, IsCompactAb G → IsPaperGenerator G → IsClassicalGeneratorOnCompacts G` | **[A]** all of `Neeman32Inputs` (compact ⇒ perfect, affine Thm 1.1 endpoints); field of `SupportedCategoryInput`; the same shape is the explicit hypothesis of **[P]** `PaperSetupMainMinimal.theorem_1_1` (LP26 **Thm 1.1**) | **Stacks** 09SR `ObjectProperty.isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated`.  The repo is **weaker** (one direction, one generator), modulo the bridges `IsCompactAb ↔ IsCompactObject` and `IsPaperGenerator G ↔ IsWeakTriangulatedGenerator {G}` (**prove S–M, AX**; C.10) |
| 1.15 | `Stacks09SR C` (`Scheme/WeakApprox.lean`) and `AffineStacks09SR A` (`Affine.lean`) | as 1.14, with `IsGenerator` instead of `IsPaperGenerator` | **[P]** `affine_theorem_1_1_small`; `affine_theorem_1_1` and three more in `Affine.lean`; `weakApprox_dqcX_*`; the same shape is the hypothesis of **[P]** `SetupMainMinimal.theorem_1_1` | **Stacks** (follows from 1.14, since `IsGenerator ⇒ IsPaperGenerator`), but **delete** together with the `IsGenerator` layer (F2) **→ wave 6: `AffineStacks09SR` deleted with its consumers in `Affine.lean`; `Stacks09SR` kept**: the pinned `affine_theorem_1_1_small` takes it (the pinned `SetupMainMinimal.theorem_1_1` takes the same shape inline) (and `RefuteIntGeneratorSmall.lean` refutes the hypotheses of the former).  Removing it is the orchestrator's baseline call. |
| 1.16 | `StacksSupportedExcisionInput` (`SchemeSupportedExcision.lean`) | `tag_08DF`: for `Z ⊆ U` there is a `SupportedExcisionDatum` (triangulated equivalence `D_qc,Z(U) ≌ D_qc,Z(X)` compatible with cohomology) | **[A]** `neemanSupported_of_qcqs_of_frameInput` (scheme Neeman 3.2(iv), toward LP26 **Cor 1.2**) | **Stacks** 08DF `PushforwardRestriction.isIso_derivedOpenPushforward_restrictionUnit_app_of_supported` (and `…extensionByZero…`).  Packaging differs: assembling the datum from AxiomMath's isos is **prove (S–M, AX)**, in AxiomMath's model |
| 1.17 | `FMCube.FlatBaseChangeLeft`, `FlatBaseChangeRight` (`FMCube.lean`) | `IsIso (P.theta C.sq₁)`, resp. `IsIso (P.theta C.sq₂)` | **[A]** `lemma_6_11`, `lemma_10_1`, `lemma_10_2_iso` → GL26 **Lemmas 6.11, 10.1** | **Stacks** 08IR `Space.isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent`, after instantiating `TensorPullPushData` (C.1, C.6) and identifying `θ` with AxiomMath's map (flat ⇒ Tor-independent) |
| 1.18 | `FMCube.ProjectionFormula` (`FMCube.lean`) | `∀ K, IsIso (P.projMap C.t' K)` (`projMap` is the mate of monoidality) | **[A]** `lemma_10_1`, `lemma_10_2_iso` → GL26 **Lemma 10.1** | **Stacks** 08IN `Space.isIso_smallEtaleProjectionFormulaMap` (08EU for schemes), once `projMap` is identified with AxiomMath's map (prove S, AX) |
| 1.19 | `Stacks07LTCompactModelInput A` (`PerfectRingStacks.lean`) | every compact `X : AffineD A` has a `BoundedFiniteProjectiveModel` | **[P]** `affine_theorem_1_1_stacks07LT`; `affineCompactHomZeroAtTop_of_stacks07LT`, … | **Stacks** 07LT `StacksDraft.Perfect.isPerfect_iff_isCompactObject` (`StacksFrontier/Homology/Perfect/Characterizing.lean`; `…_max` variant for module universes above the ring), with "perfect" read as a bounded finite-projective model (Stacks 0656), not checked here.  In the tree it is conditional on 066S retract closure (`stacks07LTCompactModelInput_of_stableUnderRetracts_unconditional`).  The pinned consumer is vacuous (F1): **delete** with it **→ kept (wave 6)**: it is *proved* (`Stacks07LT.M4.stacks07LTCompactModelInput_of_stableUnderRetracts_unconditional`, `CapstoneM6.stacks07LTCompactModelInput_of_retracts_unconditional`, both conditional only on 066S retract closure) and is used by `RefuteLargeCoproducts.lean`.  Its consumers that also took `AffineDerivedCoproducts` (`affine_theorem_1_1_stacks07LT`, ...) were deleted. |
| 1.20 | `DQCohCoproductInput X ι` (`Scheme/Derived.lean`) | `Derived X` has `ι`-coproducts, `quasiCoherent X` is closed under them, `H^n` preserves them | `isDQCohClosedUnderCoproductsOfInput` only | **Stacks** (01LA/01LB and cohomology of coproducts in `D(𝒪_X)`), true; off path; repo model.  **delete** (restate in AxiomMath's model if needed) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |

## 2. Neeman 2024 Theorem 3.2 inputs (being removed by `wave5/neeman-prune`)

| # | name (file) | what it says | consumers / headline | verdict |
|---|---|---|---|---|
| 2.1 | `CompactPerfectInput A` (`PerfectRing.lean`) | `∀ X, IsCompactAb X ↔ Perf A X` in `AffineD A` | **[P]** `affine_theorem_1_1_neeman_only` (vacuous by F1); `AffineMain`, `PerfectField`, … | **being removed** (→ `h09`); in fact **proved** with no input (F6) |
| 2.2 | `CompactToPerfectInput A` (`PerfectRingStacks.lean`) | `IsCompactAb X → Perf A X` | `affine_regularGenerator_package`, … | **proved**: `M4Unconditional.compactToPerfectInput_unconditional` (also `M6Unconditional`) |
| 2.3 | `PerfectToCompactInput A` (`PerfectRingStacks.lean`) | `Perf A X → IsCompactAb X` | `compactPerfectInput_of_separateInputs`, … | **proved**: `RegularCompactEndpoints.perfectToCompactInput` |
| 2.4 | `SmallNeemanCompactToPerfectInput A H` (`SmallAffineAssembly.lean`) | `IsCompactAb X → SmallPerf A H X` in `SmallAffineD A H` | `affine_theorem_1_1_small_*neeman_only`, … | **being removed** (→ `h09`, Stacks 09SR).  The alternative with no input would be `smallNeemanCompactToPerfectInput_of_large` plus the open small→large compactness lift `liftCompact` (prove, S–M, now) |
| 2.5 | `Neeman_3_2_i C P` (`Inputs.lean`) | `∀ P, IsCompactAb P ↔ PerfectSupported P` (a template) | outputs only (`affine_neeman_3_2_i` **[A]**) | **being removed** (template).  As an output it is proved for `Perf`/`SmallPerf` |
| 2.6 | `Neeman_3_2_ii C` (`Inputs.lean`) | `∃ G, IsCompactAb G ∧ IsGenerator G` | none | **being removed**; false rendering (F5) |
| 2.7 | `Neeman_3_2_iv C`, `NeemanPublishedWeakApproximation C` (`Inputs.lean`, `WeakApprox.lean`) | `SatisfiesWA C` | legacy bridges in `SchemeNeemanConsumerAudit`, `SchemeWeakApproxStatement`; `weakApprox_of_neeman` | **being removed**; uses the `IsGenerator` form (F2) |
| 2.8 | `Neeman_coherent_example_5_4 C P` (`Inputs.lean`) | `Neeman_3_2_iv C ∧ P` | `paperWA_and_coherent_of_legacy…` only | **delete**.  The paper need it stands for, the **coherence clause of LP26 Cor 1.2** (`cor:weak_approx_spaces`), is proved in LP26 from Lemma 5.9 and the CHNS criterion: **prove (M, AX)**, listed as 6.20 **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 2.9 | `AffinePerfect.NeemanAffineCompactModelInput A` (`Affine066S.lean`) | `Neeman_3_2_i (AffineD A) (HasBoundedFiniteProjectiveModel A)` | the 066S chain (`M6*`, `Affine066S`) | **being removed** (no paper path needs 066S).  If ever wanted: Stacks 066S `StacksDraft.Perfect.isPerfect_of_biproduct` |
| 2.10 | `SupportedCategoryInput.neeman_3_2_iii` (`OpenClosedCompletion.lean`) | for qcqs `X`, `Z` with qc complement: `InPreferredClass (dqcSupportedStandardTStructure X Z)` | **[A]** `compact_open_closed_glue_of_frameInput`, `neemanSupported_of_qcqs_of_frameInput` → LP26 **Cor 1.2**, GL26 **Lemma A.9** (`lem:preferred_eq_class`) | **prove (M, AX)**: GL26 Lemma A.9 / Neeman (iii), from 0AEC (`Space.exists_isPerfect_generator…`) + 0AED + 09SR, following the affine proof `NeemanPreferredM6.inPreferredClass_of_compactlyGenerated`.  Not a permitted input.  The other fields of the structure are row 5.6 |
| 2.11 | `CompactsArePerfect C` (`Scheme/WeakApprox.lean`) and `DqcOpenClosedGluingInput.perfectX/U/Z` (`PaperTwoOpenGluing.lean`) | `Perf : ObjectProperty C` (free) with `IsCompactAb G ↔ Perf G` | `PerfectHomZeroAtTop`, `toPaperSchemeOpenClosedDerived` | **delete**: contentless (F4) and labelled Neeman 3.2(i).  Where the content is needed: Stacks 0AED `Space.isCompactObject_iff_isPerfect_of_supported` **→ deleted (wave 6, `wave6/prune-dead-inputs`).** `CompactsArePerfect` and the `perfectX/U/Z` fields of `SchemeOpenClosedDerived`, `PaperSchemeOpenClosedDerived`, `PaperSchemeOpenClosedSeed` are gone; `PerfectHomZeroAtTop` and its consumers deleted; the conjunct `I.perfectX.Perf W.G` dropped from the conclusions of `SchemeGluingM2.exists_standardData_of_compactHomZeroAtTop` and `PaperSchemeOpenClosedDerived.exists_paperData_of_compactHomZeroAtTop`. |

## 3. Compact ⇒ perfect machinery and module models (affine)

| # | name (file) | what it says | consumers | verdict |
|---|---|---|---|---|
| 3.1 | `Stacks07LTBoundedFactorizationInput A` (`CompactToPerfect.lean`) | compact `X` is a retract of an object with a bounded finite-projective model | 07LT chain | **proved**: `stacks07LTBoundedFactorizationInput_unconditional` (`M4Unconditional`, `M6Unconditional`) |
| 3.2 | `FiniteFreeImprovementInput A` (`CompactToPerfect.lean`) | the finite-below bound of a bounded free factorization can be raised by one | 07LT chain | **proved**: `M4Improvement.finiteFreeImprovementInputM4` |
| 3.3 | `BoundedFreeInductionInput A` (`CompactToPerfect.lean`) | `initial` factorization + `FiniteFreeImprovementInput` | 07LT chain | **proved** (`boundedFreeInductionInput_of_finiteFreeImprovement` with 3.2; `…_of_boundedAbove`) |
| 3.4 | `BoundedAboveFreeResolutionInput A` (`CompactToPerfectBoundedFree.lean`) | free resolutions of bounded-above complexes, preserving the upper bound | 07LT chain | **proved**: `boundedAboveFreeResolutionInput` |
| 3.5 | `FilteredFreeModelInput A` (`CompactToPerfect.lean`) | compact objects have filtered free cell models | `affine_theorem_1_1_of_filteredFreeModels` | **delete** (an alternative route, never inhabited, superseded by 3.1–3.4) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 3.6 | `SmallFiniteFreeImprovementInput`, `SmallBoundedFreeInductionInput`, `SmallFilteredFreeModelInput`, `SmallStacks07LTBoundedFactorizationInput` (`SmallCompactToPerfectM5.lean`) | small-model copies of 3.1–3.5 | `smallNeemanCompactToPerfectInput_of_boundedFactorization`, … | **delete** (not inhabited; the small model is served by 09SR, or by the lift in 2.4) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 3.7 | `BoundedProjectiveModelInput A`, `BoundedProjectiveModelConverseInput A` (`PerfectRing.lean`, `PerfectModel.lean`) | `Perf A X ↔ ∃ bounded finite-projective model`, resp. `⇒` | `boundedProjectiveModelInput_of_*` | **delete** (066S comparison, off path; NEEMAN_3_2.md).  It is Stacks 066S/0656 if ever needed **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 3.8 | `RegularModuleApproximationInput A` (`AffineNeemanAssembly.lean`) | `bound`, `compact`, `generates : IsGenerator (ringObject A)`, approximation triangles | `toWeakApproximationData`, `satisfiesWA`, `satisfiesStandardWA` | **delete**: `generates` is false for ℤ (F5); the paper form is `RegularCompact.affine_satisfiesPaperWA` **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 3.9 | `AffineSpaltensteinInput A` = `KProjectiveReplacementData (ModuleCat A)` (`AffineCoproducts.lean`, `DerivedCoproducts.lean`) | every object of `D(A-Mod)` has a K-projective resolution | 98 declarations (model parameter `H`) | **proved**: `Spaltenstein.affineSpaltensteinInput` (also `TheoremCInput` → `theoremCInput`, `SequentialColimitQuasiIsoInput` → `sequentialColimitQuasiIsoInput`).  `H` is a model choice, not an assumption |
| 3.10 | `TheoremCInput C`, `SequentialColimitQuasiIsoInput C`, `CanonicalTruncationData` (`Spaltenstein*.lean`) | Spaltenstein's Theorem C ingredients for an abelian `C` | `replacementOfInput`, … | **proved** for module categories (`theoremCInput`, `sequentialColimitQuasiIsoInput`, `canonicalTruncation`).  Generic `C`: setup |
| 3.11 | `DerivedFreeCoproductData A ι` (`PrincipalH0CoverM1.lean`) | the derived coproduct of copies of `A[0]` is `A^{(ι)}[0]`, compatibly with injections | `derivedFreeCoproductData` | **proved** (`derivedFreeCoproductData`) |
| 3.12 | `AffineDerivedGammaInput A` (`AffineQCoh.lean`) | `RΓ : D((Spec A).Modules) ⥤ D(A)` with `tilde ⊣ RΓ`, unit and counit (on `D_qc`) quasi-isos; `tildeExact` | **[A]** `neemanWeakApproximability_spec` (two copies: `FinalStatementCrosscheck`, `RegularCompactEndpoints`); `SchemeNeemanAffineInstance` | **Stacks** 06Z0 (079W, 08D4, 01XB; 01HV is proved), but in the **repo's** Mathlib model, where AxiomMath does not apply directly.  **prove (L)** in that model, or **delete** once `wave5/neeman-affine-transport` restates the scheme results in AxiomMath's model (recommended) |
| 3.13 | `AffineAllSheavesBridgeInput` (`PerfectModel.lean`) | an `AffineCohomologyComparison` plus commShift, triangulated, and the image of `A[0]` | `perf_iff_affineThickGenerated` | **delete** (off path; the same 06Z0 model issue as 3.12) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 3.14 | `AffineCohomologyComparison A` (`AffineDictionary.lean`) | a plain equivalence `D(QCoh(Spec A)) ≌ D_QCoh` | `affineDerivedCohomologyEquivalence` | data carrier of 06Z0 (rows 1.5, 3.12); same verdict as 3.12 |

## 4. Affine recollement and affine setups

| # | name (file) | what it says | consumers | verdict |
|---|---|---|---|---|
| 4.1 | `AffineRecollementInput A f` (`AffineRecollement.lean`) | `iShriek`, `jStar`, `jUpper` with their adjunctions, iso counit, kernel description, `jUpper ⋙ iShriek ≅ 0`, the two gluing triangles | **[A]** `affineRecollementInputOfIShriek`, `…OfStacks0E55`, `…OfExactCoextension` → GL26 **Lemma A.4** (affine), LP26 **Prop 5.8** input | **setup** (it is the recollement), built from one input: row 1.11.  Becomes **proved** once 1.11 is proved |
| 4.2 | `RemainingInput`, `AdjointInput` (`AffineRecollementAssembly.lean`, `AffineSecondGluingAssembly.lean`) | intermediate packages (`iShriek`, `jUpper`, adjunctions, second triangle) | `toAffineRecollementInput` | **delete** (superseded by `affineRecollementInputOfIShriek`) **→ wave 6: `RemainingInput` deleted (module `AffineRecollementAssembly.lean` removed); `AdjointInput` kept**: `affineRecollementInputOfIShriek` (the superseding route) constructs it (`adjointInputOfIShriek`) and uses `AdjointInput.toAffineRecollementInput`, so it is an intermediate structure, not an input. |
| 4.3 | `AffineDerivedCoproducts A DZ DU` (`Affine.lean`) | `HasCoproducts.{u+1}` on `DZ`, `AffineD A`, `DU` | **[P]** `affine_theorem_1_1_neeman_only`, **[P]** `affine_theorem_1_1_stacks07LT`, **[A]** `affine_theorem_1_1_of_tag09SR`, … | **delete**: uninhabited for `A ≠ 0` (F1) **→ wave 6: every consumer deleted; the structure is kept only as the object of the refutation** `VacuityF1.isEmpty_affineDerivedCoproducts` (`RefuteLargeCoproducts.lean`). |
| 4.4 | `SmallAffineDerivedCoproducts A H DZ DU` (`AffineUniverse.lean`) | `HasCoproducts.{u}` on `DZ`, `SmallAffineD A H`, `DU` | **[P]** `affine_theorem_1_1_small` | middle field **proved** (`smallAffineHasCoproducts`, `smallAffineDerivedCoproductsOfSpaltenstein`); `DZ`, `DU` fields **setup** (LP26: compactly generated categories have small coproducts) |
| 4.5 | `AffineGluingInput` (`Affine.lean`) | `AffineDerivedCoproducts`, `SetupMainMinimal`, `AffineStacks09SR`, eventual vanishing | `satisfiesWA_of_affineDictionary` | **delete** (F1, F2) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 4.6 | `StandardSetupInput R` (`AffineSetupInventory.lean`) | `SetupMainMinimal`-shaped fields over `AffineD A` with `G'_generates : IsGenerator G'` and `WeakApproximationData` | none outside its file | **delete** (F2; the paper data is `SpecificM3.concrete_tD_and_tZ_compactlyGenerated` plus the `Paper*` setups) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** (module `AffineSetupInventory.lean` removed). |

## 5. Scheme-level gluing (the repository's scheme model)

All in the repo's model (see the model warning).  Targets: LP26 **Cor 1.2**
(`cor:weak_approx_spaces`), i.e. Neeman 3.2(iv) for qcqs schemes and then for spaces.

| # | name (file) | what it says | consumers / headline | verdict |
|---|---|---|---|---|
| 5.1 | `AffineSupportedSchemeComparisonInput A I` (`AffineSupportedSchemeBaseM1.lean`) | a triangulated equivalence `D_{V(I)}(A-Mod) ≌ DqcSupported (Spec A) (V(I))` taking the standard `t`-structure to the restricted one | **[P]** `neemanSupported_of_qc_closedComplement`, **[P]** `neemanSupportedWeakApproximability_of_isAffine` (LP26 Cor 1.2, affine base) | **prove (L)** in the repo's model: 06Z0 there (row 3.12) plus support matching.  Or (recommended) **delete** after `wave5/neeman-affine-transport` proves the same base case in AxiomMath's model, where `D(A) ≃ D_QCoh(Spec A)` is 06Z0 (`derivedGlobalSectionsQuasicoherent_isEquivalence`) and support matching is M.  **This is the only open input of the pinned scheme forms** |
| 5.2 | `NeemanSupportedCoverInput`, `NeemanCompactSupportedCoverInput` (`SchemeNeemanFiniteCoverAssembly.lean`, `OpenClosedGlue.lean`) | the four induction steps for `NeemanSupportedWeakApproximability`: affine base, iso transport, excision, open/closed gluing | `neemanSupported_of_qcqs_*` | **setup** (an induction interface; that the four steps imply the result is proved).  Fields: `of_isAffine` = 5.1; `of_iso` **proved** (`neemanSupportedWeakApproximability_of_iso`); `excision` = 1.16; `open_closed_glue` = 5.6 + 5.7 |
| 5.3 | `SupportedOpenCoverInductionData Q`, `CompactSupportedOpenCoverInductionData Q`, `OpenCoverInductionData P` (`SchemeSupportedFiniteCoverInduction.lean`, `OpenClosedGlue.lean`, `SchemeFiniteCoverInduction.lean`) | generic induction steps for a property `Q` of closed subsets / `P` of schemes | `toSetInductionData`, `of_twoOpenGluing` | **setup** (an induction principle with proved conclusion).  For spaces it is replaced by AxiomMath 09IT `Space.qcqs_induction_on_enlargement` (Stacks) |
| 5.4 | `NeemanOpenClosedCompletionInput`, `NeemanCompactOpenClosedCompletionInput` (`OpenClosedGlue.lean`) | for all WA data on the two ends, a seed and its completion exist | `open_closed_glue_of_completionInput`, … | **delete** (superseded by 5.6 + 5.7, wave 3) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 5.5 | `DqcOpenClosedGluingInput g` (`PaperTwoOpenGluing.lean`) | `PaperSetupMainMinimal` over `Dqc`, three `CompactsArePerfect`, a support predicate equal to `ker j^*` | `toPaperSchemeOpenClosedDerived` | **delete** (off the pinned path; contentless fields, F4) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 5.6 | `SupportedCategoryInput` (`OpenClosedCompletion.lean`) | for qcqs `X`, `Z` with qc complement: `HasCoproducts.{u+1} (DqcSupported X Z)`, `Tag09SRPaper`, Neeman 3.2(iii), `CompactHomZeroAtTop` | **[A]** `compact_open_closed_glue_of_frameInput`, `neemanSupported_of_qcqs_of_frameInput` | per field: `coproducts` **Stacks** (`D_qc,Z` closed under coproducts; AxiomMath's `SupportedDirectSums` file under 0A9A), in AxiomMath's model; `tag_09SR` **Stacks** (1.14); `neeman_3_2_iii` **prove** (2.10); `compactHomZeroAtTop` = LP26 **Lemma 5.6** (`lem:perf_vanishing`) with 0AED: **prove (S–M, AX)** (row 6.19).  Move `tag_09SR` into `StacksInterface` (an orchestrator decision) |
| 5.7 | `OpenClosedFrameInput` (`OpenClosedCompletion.lean`) | for qcqs `X`, qc open `V`, `Z`: an `OpenClosedFrame` (recollement `D_{Z∖V} → D_Z → D_{V,Z∩V}`, compact zero-detecting `G'`, `GU`, compactly generated `tD`, `tZ`, `tU`, normalization `m`) | **[A]** same two | **prove (L, AX)**: recollement = GL26 **Lemma A.4** / LP26 **Prop 5.8** for spaces; generators = Stacks 0AEC; compactly generated `t`-structures = Alonso–Jeremías–Souto (not Stacks; prove M); normalization `m` = LP26 **Lemma 4.3(1)** (proved as `lemma_4_3_1_paper` modulo `BNP310Input`, row 6.17) |
| 5.8 | `CompactHomZeroAtTop C` (`Inputs.lean`, `WeakApprox/CompactVanishing.lean`) | `∀` compact `X, Y`: `Hom(X, Y[n]) = 0` for `n ≫ 0` | hypothesis of `satisfiesPaperWA_of_compactHomZeroAtTop`, `exists_paperData` **[A]**, 30+ more | a property, not an input.  For `D_qc,Z(X)` it is LP26 **Lemma 5.6**: **prove (S–M, AX)** (row 6.19).  Affine: **proved** (`Neeman32Inputs.smallCompactHomZeroAtTop` from `h09`; large model with no input via 2.1) |
| 5.9 | `PerfectCompactStatement` (`Perfect.lean`) | `∀ E ∈ D_qc, compact E ↔ IsPerfect E`, `compact` free | `SchemePerfectStacksInput.tag_09M1` | **delete** (F4) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** (with `PerfectCompactInterface`). |

## 6. GL26 six-functor data (abstract interfaces with geometric content)

These structures carry functors as **free fields**, so a theorem over them is a
categorical statement (`Paper/InterfaceAudit.lean`).  Each is discharged only by
instantiating it with the paper's functors on `D_qc` of algebraic spaces (AX).  Gap
numbers C.n refer to `results/AXIOMMATH_MAP.md`.

| # | name (file) | what it says | consumers / headline | verdict |
|---|---|---|---|---|
| 6.1 | `PullPushData S` (`Prelim/BaseChangeMates.lean`) | `pull`, `push`, `pull ⊣ push`, unit/composition isos with associativity and unitality, conjugacy of the pull and push composition isos (Lipman (3.6.2)) | **[A]** `lemma_7_12`, `lemma_7_13`, `lemma_7_15`, `lemma_7_17_*` → GL26 **7.12–7.17** (abstract) | **setup** (the abstract form of the paper's pseudofunctor); non-vacuity `constPullPushData`.  Geometric instance: **prove (M, AX)** = C.6 + GL26 **Lemma 2.13** (`lem:spacey_Lipman_Hashimoto`).  0D6D/0D6E are Stacks (`smallEtaleDerivedModulePullbackCompIso`, `DerivedPushforwardCompositionOnTopoi.*`); the conjugacy `conj_comp` is Lemma 2.13 itself |
| 6.2 | `DerivedPseudofunctorInput S` (`DualityMates.lean`) | `PullPushData` whose 1-cells are `DerivedMorphismData` (6.4) | **[A]** `DerivedPseudofunctorInput.lemma_7_12`, `coherence`, `lemma_7_15`, `lemma_7_17_*` | **prove (M, AX)**: as 6.1, plus 6.4 for every morphism (`ASSUMPTIONS.md` §1b row 1).  Non-vacuity `trivialInput` |
| 6.3 | `DerivedTensorHomData D` (`Duality.lean`) | symmetric monoidal `D`, `rhom`, `tensorLeft E ⊣ rhom E`, internal currying iso | 13 constructions; every row below | **Stacks** 08J8/08J9 (and 06YU), but AxiomMath's adjunction is on the model site and is **not transported** to `DerivedModules` (C.5): **prove (M–L, AX)**.  Affine: row 1.12 |
| 6.4 | `DerivedMorphismData TX TY` (`Duality.lean`) | `Lf^* ⊣ Rf_*`, `Rf_* ⊣ f^×`, `f^!`, `pullUnit`, `pullTensor`, projection formula, `χ`, `σ` (iso on perfect `E`), free `IsProper`/`IsFlat`/`HasFiniteTorDimension`, `σ` iso when flat, `f^× ≅ f^!` when proper, `pullRHom` iso on perfect `E` | **[P]** `DerivedDiagonalInput.identityIso`, **[P]** `lemma_2_26_of_correction` (through `CorrectedConvolutionData`), **[P]** `externalTensor_compactlyGenerates`; `Duality.lean` | mixed.  **Stacks**: 07A6, 0E55, 07A4, 08IN (rows 1.1, 1.2).  **prove (L, AX)**: `upperShriek`, `σ`, `χ`, `sigma_isIso_of_flat`, `properCrossShriek` are Neeman's `f^!` and GL26 **Lemmas 2.21–2.24** (`lem:neeman186`–`189`), absent from AxiomMath (C.3, 2–5k lines); `pullRHom_isIso_of_perfect` is GL26 **Lemma 2.16** (S–M).  **Refactor recommended**: split `f^!`, `χ`, `σ` off into a separate structure.  Their statements mention only the `pull`/`push`/adjunction/tensor/projection-formula side (the proofs were not audited field by field here), yet constructing any `DerivedMorphismData` forces C.3 |
| 6.5 | `PerfectDualityData T` (`Duality.lean`) | `Perf`, double-dual iso on `Perf` (08JJ), GL26 Lemma 2.10's `rhomTensor` iso, `dualTensor` (08J9) | `toPerfectDualityData` | **Stacks** 08JJ (1.3) + **prove** Lemma 2.10 (S, AX) |
| 6.6 | `CompositeDualityData` (`Duality.lean`) | pull/push/`f^×` composition isos; `ρ : (gf)^! ⟶ f^! g^!`, iso in four cases | none | pull/push: **Stacks** 0D6D/0D6E; `crossComp`: prove (S, from 0D6E by adjunction); `ρ` cases: **prove (L, AX)** (C.3) |
| 6.7 | `BaseChangeCoherenceData sq` (`Duality.lean`) | `pushComp` iso and its conjugacy with `θ` | **[A]** `pushComp_hom_eq`, `subsingleton`, `coherence`, `coherence_eq` | **proved** from `DerivedPseudofunctorInput` (`DualityMates.coherence`); reduces to 6.2 |
| 6.8 | `BaseChangeIsomorphismData sq`, `UpperShriekBaseChangeData sq` (`Duality.lean`) | `θ` iso if Tor-independent (08IR); `β` iso (proper flat base change for `f^×`); `^*`–`^!` base change (0E5D) iso in the cases of GL26 Lemmas 2.23 and 9.1 | none | `θ`: **Stacks** 08IR.  `β`: Stacks 0E5I only for affine bases; globalizing is **prove (M, AX)** (C.8).  `f^!` base change: **prove (L, AX)** (C.3; GL26 Lemma 9.1 `lem:base_change_relative_formula`) |
| 6.9 | `DiagonalIdentityData D DP unit` (`DiagonalIdentity.lean`) | free `tensorRight`, `tensorSource`, `pull`, `push`, `diagonal`, `diagonalPull`; projection-formula iso (08IN at `RΔ_*𝒪`), tensor unit, `pull ⋙ diagonalPull ≅ 1`, `diagonal ⋙ push ≅ 1` | **[P]** `lemma_2_25`, **[P]** `lemma_2_25Statement_proved` (via `Lemma25DiagonalData`), **[P]** `affine_lemma_2_25` (via `AffineDiagonalContext`) → GL26 **Lemma 2.25** (`lem:funct_on_kernel`) | spaces: **prove (M, AX)** from 08IN (Stacks), the tensor unit (C.5) and 0D6D/0D6E with `Δ ≫ prᵢ = 1` (C.6).  Affine (`AffineDiagonalContext`): **prove (M–L, now)**: `⊗^L` on `D(A)` and `D(A ⊗_R A)` (row 1.12), derived restriction/extension along `A ⊗_R A → A` and `A → A ⊗_R A`, the projection formula for rings |
| 6.10 | `DerivedDiagonalInput TD TP`, `DerivedFunctorialityData D`, `DiagonalFunctorialityInput F Δ p₁ p₂ unit` (`DiagonalDuality.lean`, `DiagonalFunctoriality.lean`) | other packagings of 6.9 (via `DerivedMorphismData`, or a pull/push family with id/comp isos) | **[P]** `DerivedDiagonalInput.identityIso`, **[P]** `DiagonalFunctorialityInput.identityTransformIso` | same as 6.9; `DerivedDiagonalInput` also inherits 6.4's `f^!` burden |
| 6.11 | `Lemma25DiagonalData C Δ` (`Scheme/Statements.lean`) | a `DiagonalIdentityData` whose functors equal the `FMContext`'s | **[P]** `lemma_2_25Statement_proved`, `…_no_properFlat` | same as 6.9 (an identification of fields) |
| 6.12 | `CorrectedConvolutionData B`, `ConvolutionCube …`, `AffineConvolutionInput R A B C` (`AffineConvolution.lean`) | seven `DerivedTensorHomData`, nine `DerivedMorphismData`, the 08IR square with `IsIso θ`, the 0D6D and 0D6E isos; identification with `ConvolutionData` | **[P]** `lemma_2_26_of_correction` → GL26 **Lemma 2.26** (`lem:convolution`) | **Stacks** for 08IR, 0D6D, 0D6E (as 1.2, 6.1); the cube itself: **prove (M, AX)** = C.1; plus 6.3, 6.4 (and C.3 unless 6.4 is split).  Affine (`AffineConvolutionInput`): **prove (L, now)**, the same constructions as 6.9 for triple tensor products |
| 6.13 | `TriangulatedFunctorData`, `TriangulatedTensorHomData`, `TriangulatedMorphismData` (`Duality.lean`) | `CommShift` + `IsTriangulated` for `⊗^L`, `RHom`, `Lf^*`, `Rf_*`, `f^×`, `f^!` | **[P]** `externalTensor_compactlyGenerates` | **prove (S–M, AX)**: derived functors are triangulated; `f^×` by GL26 **Lemma B.10** (proved) from `Rf_* ⊣ f^×`; `f^!` needs C.3 |
| 6.14 | `CoverComparisonInput` (`Lemma54.lean`) | flat base change iso; `Lt^* Lg₂^* ≅ Lh₂^*`; `Rh₂_*` reflects zero; `Lt^*` reflects zero | **[P]** `externalTensor_compactlyGenerates` → GL26 **Lemma 5.4** (`lem:neeman2023cor5_10`) | **Stacks** 08IR, 0D6D for the first two; **prove (S–M, AX)**: GL26 **Lemma 3.2** (`lem:quasi-affine_is_conservative`) and **Lemma 2.14** (`lem:faithfully_flat_is_conservative`, C.11) |
| 6.15 | `ProductPerfectCompactInput` (`Lemma54.lean`) | compact ⇒ perfect on `Y₁`, `Y₂`; `Lgᵢ^*` preserves perfect; `⊗^L` preserves perfect; perfect ⇒ compact on the product | **[P]** `externalTensor_compactlyGenerates` | **Stacks**: 09M8 `Space.isCompactObject_iff_isPerfect` (both directions), 08H6 (1.6), and the Stacks fact that perfect ⊗ perfect is perfect (AxiomMath declaration not located in this triage), after instantiation and the C.10 bridge |
| 6.16 | `HasBousfieldTriangles G` (`Prelim/Lemma24.lean`) | Bousfield triangles for `⟨G⟩‾` | **[A]** `isLocalizingGenerator_of_isPaperGenerator`, `isPaperGenerator_iff_isLocalizingGenerator` (secondary route) | **delete** (Lemma 2.4 uses 09SN; `ASSUMPTIONS.md` §1b row 2) **→ deleted (wave 6, `wave6/prune-dead-inputs`).** |
| 6.17 | `BNP310Input C` (`WeakApprox/PaperLemma43M2.lean`) | for WA `C`, compact zero-detecting `G` and the `t`-structure generated by `G`: `Hom(G[-n], Y) = 0` for `n ≫ 0` ⇒ `Y ∈ T^{≤m}` | `lemma_4_3_1_paper` (LP26 **Lemma 4.3(1)**, `lem:normalize`) | **prove (M, now)**: Burke–Neeman–Pauwels Cor 3.10(1), categorical.  Needed only if Setup 4.4's normalization `m` is to be derived instead of being a field (rows 7.2, 5.7) |
| 6.18 | `TransformPreservationForcesRelativePerfect C K`, `RelativePerfectLocusOpenInput X K` (`GL26Theorem12Reduction.lean`) | GL26 Remark 2.7 (`rem:rel_perfect_is_free`): a pseudo-coherent kernel preserving `D^b_coh` and `Perf` is relatively perfect over both factors; openness of the relatively perfect locus (Prop 12.8) | `relativelyPerfect_of_neeman_coherent_CHNS`, `theorem_1_2_open_of_relative_perfect_localization` → GL26 **Thm 1.2** (residues) | **prove (L, AX)**: GL26 **Remark 2.7** (Neeman coherence + CHNS) and **Prop 12.8** (`prop:relatively_perfect_locus`) |
| 6.19 | (no Lean name yet) LP26 **Lemma 5.6** (`lem:perf_vanishing`) | `Hom(P, Q[n]) = 0` for `n ≫ 0`, perfect `P, Q` on qcqs `X` with support | `CompactHomZeroAtTop` hypotheses (5.8), `SupportedCategoryInput.compactHomZeroAtTop` | **prove (S–M, AX)** from 09M8/0AED and bounded cohomological dimension (Stacks).  Proved in the affine model |
| 6.20 | (no Lean name yet) coherence clause of LP26 **Cor 1.2** | Noetherian `X`: `D_qc,S(X)` is coherent | `Neeman_coherent_example_5_4` (2.8, to delete) | **prove (M, AX)**: LP26 **Lemma 5.9** (`lem:characterize_T-_c`, from Stacks 08IK, 09M8, 08FV) and the CHNS criterion |

## 7. Setup data and specification structures (not assumptions)

| # | name (file) | role | verdict |
|---|---|---|---|
| 7.1 | `PaperWeakApproximationData C` (`WeakApprox/PaperGeneratorM2.lean`) | LP26 **Def 2.1** (`def:weak_approx`) with zero detection | **setup** (the definition).  Inhabited: `RegularCompact.affine_satisfiesPaperWA`, `satisfiesPaperWA_of_fg` |
| 7.2 | `PaperSetupMainMinimal`, `PaperSetup44Minimal` (`WeakApprox/PaperMainMinimalM2.lean`) | LP26 **Setup 4.4** (`setup:standing`) data | **setup** for **[P]** `PaperSetupMainMinimal.theorem_1_1` (LP26 **Thm 1.1**).  **Gap to name in the docstring:** the paper's Theorem 1.1 assumes only that `D_Z`, `D_U` are weakly approximable and that `G'` is a compact generator.  This structure additionally takes as fields the compactly generated `t`-structures `tD`, `tZ`, `tU` (Alonso–Jeremías–Souto existence), WA data with the **specific** generators `i^*G`, `G_U` (BNP Lemma 3.7; the tree proves the generator change: `OpenClosedCompletionW3.exists_changeGenerator` **[A]**, `exists_paperData` **[A]**), and the normalizing `m` (LP26 Lemma 4.3(1), row 6.17).  To close it: an AJS existence theorem (prove M, now) and 6.17 |
| 7.3 | `WeakApproximationData`, `SetupMainMinimal`, `Setup44*`, `SatisfiesWA` (`WeakApprox/Basic.lean`, `MainMinimal.lean`, …) | the `IsGenerator` (morphism-separation) versions | **delete** (F2).  They are pinned (`SetupMainMinimal.theorem_1_1`, the affine endpoints): unpinning is the orchestrator's call **→ kept (wave 6)**: pinned (`SetupMainMinimal.theorem_1_1`, `affine_theorem_1_1_small`) and in `WeakApprox/`, outside this task. |
| 7.4 | `OpenClosedFrame` (`OpenClosedCompletion.lean`) | Setup 4.4 data in one open/closed square | **setup**; its existence is 5.7 |
| 7.5 | `FMSetup`, `FMContext`, `MorphismContext`, `Subcats`, `BaseChange` (`Paper/DerivedSetup.lean`, `Scheme/Statements.lean`) | GL26 **Setup 2.20** (`setup:fm_cube_pullback`), Def 12.1, the interface for the nine targets; free `IsProperFlat : Prop`, `RepIndependent`, subcategories | **setup** (interface).  To be replaced by `FourierMukai/Spaces/` definitions (`wave5/spaces-foundations`); theorems over the free fields say nothing geometric (`InterfaceAudit.lean`) |
| 7.6 | `DiagonalFMData`, `DiagonalIdealData`, `ConvolutionData`, `EllipticFibrationPredicates`, `PerfectnessSquare`, `TensorPullPushData`, `AffineDiagonalContext` (non-`core` fields) | geometric objects (`RΔ_*`, `𝒪`, `I_Δ`, convolution, elliptic fibration) as free fields | **setup** (interface), same as 7.5 |
| 7.7 | `PerfectToDQCohInterface`, `PerfectThicknessInterface`, `PerfectCompactInterface` (`Perfect.lean`) | repo scheme-model interfaces | **setup** (interface); off path; superseded by AxiomMath's `IsPerfect` |
| 7.8 | `IdealSupportedCoproductInput`, `IdealSupportedCompactnessInput`, `KoszulPowerCoprodInput`, `KoszulDetectionInput` (`IdealNeemanM1.lean`) | finite-support Koszul inputs | **proved** (`KoszulInputs.idealSupportedCoproductInput` **[A]**, `idealSupportedCompactnessInput` **[A]**, `FiniteKoszulM1.koszulPowerCoprodInput` **[A]**, `StacksInterface.koszulDetectionInput` **[A]**).  The 0A9A label on `KoszulDetectionInput` is wrong (`AXIOMMATH_TAGS.md` open point 4) and should be dropped |
| 7.9 | `AffineExtensionSurjectivityInput`, `QuasicoherentExtensionInput` (`QCohSerreExtension*.lean`, `QCohSerre.lean`) | 01IE patching; extension closure of `QCoh` | **proved** (`affineExtensionSurjectivityInput`, `quasicoherentExtensionInput`).  Stacks 01IE is also in AxiomMath (`isQuasicoherent_X₂_of_shortExact_spec`) |
| 7.10 | `QuasicoherentSerreInput`, `QuasicoherentStrongClosureInput` (`Derived.lean`, `QCohSerre.lean`) | `QCoh` is a Serre class of `𝒪_X`-modules | **delete**: false (F3) **→ wave 6: consumers deleted (`isDQCohTriangulatedOfInput`, `quasicoherentSerreInputOfStrongClosure`); the two structures are kept only as the objects of the refutations** in `RefuteQCohSerre.lean`. |
| 7.11 | `*Statement` definitions (`Scheme/Statements.lean`: `theorem_1_2_*`, `theorem_1_3`, `theorem_1_6`, `theorem_1_7`, `theorem_12_3`, `lemma_12_2`, `corollary_6_18`, `corollary_12_4`, `lemma_2_25*`, `lemma_2_26`, `DescentAscentStatement`) and the nine `sorry`s of `Paper/Statements.lean` | targets, not inputs | out of scope (T in `COVERAGE.md`).  The bare 2.25/2.26 renderings are refuted (`lemma_2_25BareStatement_has_countermodel`, `bare_lemma_2_26_has_countermodel`) |

Not inputs, listed only because the name search matched them: `ConeData`,
`ScalarConeData`, `KoszulListData` (constructed objects), `ExtensionData`,
`StepData`, `TwoCellData` (proof-internal data), `homData`, `pData` (a counterexample),
`homPostcomp/PrecompLeftHomologyMapData`, `rebasePaperWeakApproximationData`,
`constPullPushData`, `constTensorPullPushData`, `trivialInput`, `toPullPushData`,
`toDiagonalIdentityData`, `boundedAboveFreeResolutionInput` (constructions),
`NeemanSetProperty`, `NeemanWeakApproximability`, `NeemanSupportedWeakApproximability`,
`Dqc(Supported)StandardPaperWeakApproximationData`, `DqcNeemanOpenClosedInput`,
`DqcSupportedNeemanOpenClosedInput` (conclusions or type abbreviations, not hypotheses).

## 8. Summary

### Counts (rows of §§1–7; a row that names several structures counts once)

| verdict | rows |
|---|---:|
| Stacks (alone) | 1.1, 1.2, 1.4, 1.5, 1.6, 1.7, 1.13, 1.14, 1.17, 1.18, 6.15 = **11** |
| Stacks + prove (partly Stacks, partly paper lemmas or a bridge) | 1.3, 1.16, 3.12, 5.6, 6.1, 6.3, 6.4, 6.5, 6.6, 6.8, 6.12, 6.14 = **12** |
| Mathlib | **0** (Mathlib lacks a derived tensor, `D_qc` of schemes, and compact generation) |
| prove | 1.11, 1.12, 2.10, 5.1, 5.7, 5.8, 6.2, 6.9, 6.10, 6.11, 6.13, 6.17, 6.18, 6.19, 6.20 = **15** |
| proved (closed; nothing to prove) | 2.2, 2.3, 3.1, 3.2, 3.3, 3.4, 3.9, 3.10, 3.11, 6.7, 7.8, 7.9 = **12** |
| delete | 1.8, 1.9, 1.10, 1.15, 1.19, 1.20, 2.8, 2.11, 3.5, 3.6, 3.7, 3.8, 3.13, 4.2, 4.3, 4.5, 4.6, 5.4, 5.5, 5.9, 6.16, 7.3, 7.10 = **23** |
| setup | 4.1, 4.4, 5.2, 5.3, 7.1, 7.2, 7.4, 7.5, 7.6, 7.7 = **10** |
| being removed (`neeman-prune`) | 2.1, 2.4, 2.5, 2.6, 2.7, 2.9 = **6** |

3.14 is a data carrier for 1.5 and 3.12 and is not counted separately; 7.11 is out
of scope.

### Shortest list making the pinned declarations unconditional

The 18 pinned declarations of `results/statement-baseline.txt` (plus the
`neeman-prune` change to `affine_theorem_1_1_neeman_only`), by what still stands
between each and "Stacks only":

| pinned declaration | open non-Stacks input | shortest fix |
|---|---|---|
| `NeemanAffineSupport.satisfiesPaperWA_of_fg` | none | — |
| `PrincipalNeemanM1.satisfiesPaperWA`, `IdealNeemanM1.satisfiesPaperWA_idealSupported` | none: the hypothesis `IsCompactAb (ringObject A)` is proved (`RegularCompact.ringObject_isCompactAb`) | none (the orchestrator may restate without the hypothesis) |
| `AffineSupportedSchemeBaseM1.neemanSupported_of_qc_closedComplement`, `…neemanSupportedWeakApproximability_of_isAffine` | **5.1** `AffineSupportedSchemeComparisonInput` | **P1**: prove 5.1 (L, repo model), or restate in AxiomMath's model (`neeman-affine-transport`) and unpin these |
| `PaperSetupMainMinimal.theorem_1_1` (LP26 Thm 1.1) | none beyond Stacks 09SR and Setup 4.4 data | **P2** (to *use* AxiomMath's 09SR): the C.10 bridges `IsCompactAb ↔ IsCompactObject`, `IsPaperGenerator ↔ IsWeakTriangulatedGenerator {·}` (S–M, AX).  To match the paper's hypotheses exactly: **P3** = AJS existence + 6.17 (7.2) |
| `SetupMainMinimal.theorem_1_1`, `affine_theorem_1_1_small` | Stacks09SR (`IsGenerator` form), which is Stacks | nothing to prove; **vacuous at ℤ** (F2): recommend unpinning in favour of the `Paper*` forms |
| `affine_theorem_1_1_neeman_only`, `StacksGluing.affine_theorem_1_1_stacks07LT` | `CompactPerfectInput` (proved, F6); `Stacks07LTCompactModelInput` (Stacks 07LT) | nothing to prove; **vacuous for every nonzero ring** (F1): recommend unpinning |
| `lemma_2_25`, `Noetherian.lemma_2_25Statement_proved`, `…_no_properFlat`, `DiagonalFunctorialityInput.identityTransformIso` | 6.9 / 6.10 / 6.11 (abstract diagonal data) | **P4**: instantiate for spaces: C.6 + GL26 Lemma 2.13, C.5 tensor unit, 08IN (M, AX) |
| `AffineDiagonalContext.affine_lemma_2_25` | 6.9 (affine) | **P5**: `⊗^L` on `D(A-Mod)` (1.12) + diagonal data for rings (M–L, now) |
| `DerivedDiagonalInput.identityIso`, `Convolution.NoetherianBridge.lemma_2_26_of_correction`, `Lemma54.externalTensor_compactlyGenerates` | 6.4 `DerivedMorphismData` (forces `f^!`) + 6.12 / 6.13 / 6.14 / 6.15 | **P6**: split `DerivedMorphismData` (refactor of the shared `Duality.lean`, S; the orchestrator's decision); then P4 + C.1 (the FM cube, M) + GL26 Lemmas 2.14 and 3.2 (S–M) + C.10.  Without the split, add C.3 (`f^!`, L, 2–5k lines) |

So the **shortest prove list** is: **P1** (or the AxiomMath restatement), **P2**,
**P4**, **P5**, **P6**, with C.1/C.5/C.6 as the shared algebraic-space prerequisites
for P4/P6.  The orchestrator should first decide whether to **unpin** the four
`IsGenerator`/large-coproduct endpoints (F1, F2), which cannot be made non-vacuous
and need no proof.

### Proposed worker tasks, in dependency order

**Wave 6: no AxiomMath needed (affine and abstract model)**

1. `wave6/vacuity-refutations` (S–M): prove F1 (`¬ HasCoproducts.{u+1} (AffineD A)`
   for `A ≠ 0`), F2 (no compact `IsGenerator` in `D(ℤ)`) and F3 (`¬ QuasicoherentSerreInput (Spec ℤ)`),
   in new files.  This makes the delete verdicts on 4.3, 4.5, 4.6, 7.3, 7.10 citeable.
2. `wave6/prune-dead-inputs` (S, after 1 and `neeman-prune`): delete the rows marked
   **delete** (1.8–1.10, 1.15, 1.19, 1.20, 2.8, 2.11, 3.5–3.8, 3.13, 4.2, 4.3, 4.5,
   4.6, 5.4, 5.5, 5.9, 6.16, 7.3, 7.10), after the orchestrator unpins the affected
   declarations.  Keep `M4Unconditional`/`M6Unconditional` (F6).
3. `wave6/affine-coextension` (M): prove 1.11 (derived coextension `RHom_A(A_f, -)`
   is right adjoint to `Rj_*`).  This makes GL26 Lemma A.4 (affine) unconditional.
4. `wave6/affine-derived-tensor` (M–L): `⊗^L`/`RHom` on `D(A-Mod)` (1.12), then the
   affine diagonal data of `AffineDiagonalContext` (P5).  Second task, if large: the
   affine convolution cube (6.12, affine).
5. `wave6/lp26-setup-gaps` (M): BNP Cor 3.10(1) (6.17) and AJS existence of compactly
   generated `t`-structures, so that a form of LP26 Thm 1.1 with exactly the paper's
   hypotheses follows from `PaperSetupMainMinimal.theorem_1_1` (7.2).
6. Orchestrator (not a worker; shared file): split `DerivedMorphismData` (P6).

**Wave 7: after AxiomMath is imported (`spaces-foundations` merged)**

7. `wave7/compactness-bridges` (S–M): C.10, i.e. `IsCompactAb ↔ IsCompactObject.{u}`
   and `IsPaperGenerator ↔ IsWeakTriangulatedGenerator {·}` on AxiomMath's `D_QCoh`.
   This discharges 1.13 and 1.14 by AxiomMath, and all of P2.
8. `neeman-affine-transport` (already planned): the affine supported base in
   AxiomMath's model; it supersedes 5.1 (P1) and 3.12.
9. `wave7/pseudofunctor-spaces` (M): C.6 + GL26 Lemma 2.13: instantiate `PullPushData`
   / `DerivedPseudofunctorInput` (6.1, 6.2) with `Lf^*`, `Rf_*` on spaces.
10. `wave7/closed-monoidal-spaces` (M–L): C.4 and C.5: `DerivedTensorHomData` (6.3) on
    `D_QCoh` of a space, the tensor unit, `Lf^*` monoidal.
11. `wave7/fm-cube-spaces` (M, after 9 and 10): C.1, the Fourier–Mukai cube.  Discharge
    `FMCube` (1.17, 1.18) by 08IR/08IN, and the diagonal data 6.9–6.11 (P4) for GL26
    Lemmas 2.25, 6.11, 10.1.

**Wave 8**

12. `wave8/convolution-and-5-4` (M): 6.12 (Lemma 2.26 cube), 6.13, 6.14 (GL26 Lemmas
    2.14 and 3.2), 6.15 → Lemmas 2.26 and 5.4 for spaces (P6).
13. `wave8/neeman-3-2-spaces` (L, splittable): 2.10 (Neeman (iii), GL26 Lemma A.9),
    6.19 (LP26 Lemma 5.6), 5.6, 5.7 (recollement for spaces = GL26 Lemma A.4 / LP26
    Prop 5.8, compactly generated `t`-structures), 1.16 (08DF excision), with induction
    by 09IT → LP26 **Cor 1.2** without Neeman.  Then 6.20 (the coherence clause).
14. Later, only if the headline results need it: C.3 (`f^!`, L) for 6.4's split-off
    part, 6.6, 6.8 (GL26 §§2.4, 9, Lemmas 2.21–2.24, 9.1), and 6.18 (GL26 Remark 2.7,
    Prop 12.8 → Thm 1.2).

### Open points for the orchestrator

* F1 and F2 make four pinned declarations vacuous (F1: two; F2: those two plus two
  more).  Unpinning or replacing them is a baseline change only the orchestrator
  makes (`CLAUDE.md` rule 4).
* F6: tell `wave5/neeman-prune` not to delete `compactToPerfectInput_unconditional`.
  With `perfectToCompactInput` it gives `CompactPerfectInput A` with no hypothesis.
* `Tag09SRPaper` is still a field of `SupportedCategoryInput`, not of `StacksInterface`
  (`ASSUMPTIONS.md` §4 row 09SR).
* `KoszulDetectionInput`'s 0A9A label is wrong (7.8).
* The two scheme models (the repo's Mathlib-based `Dqc`/`DqcSupported`/`SchemeD` and
  AxiomMath's) should not both be maintained.  Every scheme-level row in §§3 and 5 is
  cheaper to restate in AxiomMath's model than to prove in the repo's.
