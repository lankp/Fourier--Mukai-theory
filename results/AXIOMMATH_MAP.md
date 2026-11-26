# GL26 / LP26 notions → AxiomMath/Stacks: API map, fidelity audit, gaps, build cost

Wave 4, task `wave4/axiommath-api-map`.  Parts A, C, D of the brief
(`results/swarm/archive/wave4/axiommath-api-map.md`); part B (per-tag table) is
`results/AXIOMMATH_TAGS.md`, another worker's.

* **AxiomMath commit read:** `f56a316ddf7a930906d88b78d6f9a2668cffd0cf` (the pinned one; it was
  reachable from a depth-1 clone). Lean/Mathlib `v4.35.0`.
* **Method:** I read the definitions and the theorem signatures in the source files named
  below, not only the docstrings. Nothing was compiled. A signature quoted below is copied
  from the source; I did not elaborate it. Where an exact universe or instance argument matters
  and I could only infer it from the source, I say so ("to confirm with `#check`").
* **Paper side:** GL26 §2.2 (`sec:preliminaries_stacks`, with `sec:prelim_stacks_notions`,
  `sec:prelim_stacks_categories`, `sec:preliminaries_stacks_support`,
  `sec:prelim_stacks_perfects`, `sec:prelim_stacks_internal_homs`,
  `sec:prelim_stacks_functors`, `sec:preliminaries_stacks_lipman_hashimoto`), §2.3
  (`sec:prelim_fm_setup`), §2.4 (`sec:duality`), `def:relative_perf_stacks`,
  `def:quasi_perf`, `rem:comparison_stacks_project`.
* **Library:** every AxiomMath declaration named in this file is in **StacksFrontier**. None of
  them is in StacksCore. Paths are relative to `StacksFrontier/AlgebraicGeometry/Spaces/`
  unless they start with `StacksFrontier/`.
* **Namespaces:** `AlgebraicGeometry` (base, `IsAlgebraicSpace`, `AlgebraicSpaces`) and
  `AlgebraicGeometry.Space` (everything on spaces). The implicit or explicit triple
  `(B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)` is written `B S hS`.
  `X : AlgebraicSpaces B S hS` is a pair `⟨X.1, X.2⟩` of a presheaf and its
  `IsAlgebraicSpace` proof. A morphism `f : X ⟶ Y` is a morphism of the full subcategory, and
  `f.hom` is the underlying natural transformation. All morphism properties take `f.hom`.

## Summary for the next wave

1. **The base, the morphism properties, and `D(𝒪_X)`, `D_QCoh(𝒪_X)`, `Lf^*`, `Rf_*`, `⊗^L`,
   `Perf`, pseudo-coherence, `D^b_Coh`, support and `D_{QCoh,Z}` are all present for algebraic
   spaces.** They are defined on the small étale site, following the Stacks conventions that
   GL26 §2.2 adopts. I found them faithful, apart from the caveats listed in A.
2. **One model is canonical.** `D(𝒪_X)` is `DerivedCategory (Modules.{u, u} B S hS X.1 X.2)`
   at `HasDerivedCategory.standard`. Every headline theorem listed below is stated over this
   model. `DerivedModules` is the same category by `abbrev`. `ModelDerivedModules` and
   `SchemeStdDerived` are auxiliary models, connected to it by the explicit equivalence
   `modelDerivedEquivalence`. They are used internally for `R𝓗om` and duality (see A.0).
3. **Present on spaces:** compact = perfect (09M8), a single perfect generator (09IY), the
   same two for `D_{QCoh,T}` (0AED, 0AEC), `f^×` as the right adjoint of `Rf_*` on `D_QCoh`
   (0E55), Tor-independent base change (08IR), flat base change, the projection formula
   (08IN), the composition isomorphism for `Lf^*` (0D6D, with its cocycle identity) and for
   `Rf_*`, Nagata compactification (0F4D), dualizing complexes and their duality (0E4Z, 0E51),
   and `f^×` base change (0E5B–0E5L, 0E5I, the last only over **affine** bases).
4. **Gaps** (Part C). The main ones:
   * no Fourier–Mukai functor;
   * no weak approximability;
   * no Neeman `f^!`;
   * `Lf^*` is monoidal on `D_QCoh` only under an **undischarged hypothesis**
     `PullbackTensorAssociativity f`;
   * no symmetric or closed monoidal structure on `D_QCoh(𝒪_X)` for spaces;
   * no `Q` or bold `𝐑𝓗om` on `D_QCoh`;
   * GL26's `f`-perfect and `f`-quasi-perfect are not in AxiomMath. Its 0DKN notion is a
     different definition; it agrees with GL26's only via `rem:comparison_stacks_project`,
     which AxiomMath does not prove;
   * `f^×` base change (`lem:neeman188`) is available only over affine bases;
   * the universe of compactness differs from this repo's `IsCompactAb` (A.5).
5. **Build cost** (Part D). Everything in A: **16 622 AxiomMath modules, 5.0 M lines**. The
   statement layer (A.1–A.4, A.6, without the large theorems): **8 886 modules, 2.68 M
   lines**. The base and morphism properties alone: **67 modules, 19 k lines**.

---

## A. Notions and functors

Each entry gives the declaration(s), the file, the `@[stacks]` tag, the signature, and a
**verdict**:

* **faithful**: means what GL26 means;
* **faithful (variant)**: equivalent to GL26's notion, but the equivalence is a theorem, and
  the entry says whether AxiomMath proves it;
* **special case**: weaker or narrower than GL26's notion;
* **different**: not GL26's notion;
* **absent**: no such declaration.

### A.0 Models of the derived category, and universes

| model | declaration | file | what it is |
|---|---|---|---|
| **canonical** | `DerivedCategory (Modules.{u, u} B S hS X.1 X.2)` with `attribute [local instance] HasDerivedCategory.standard` | `RingedSite.lean` (`Modules`), used everywhere | `Modules.{u, m} B S hS F hF := SheafOfModules.{m} (ringSheaf (smallEtaleRingedSite B S hS F hF).O)`. Every theorem on spaces cited below uses `m = u` and the standard model. |
| same, second spelling | `DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))` | `SmallEtaleDerivedModulePullback.lean` | The same category up to `rfl`; `SmallEtaleDerivedTensor.lean` says so in its implementation notes. `Lf^*` and `⊗^L` are stated in this spelling. |
| `DerivedModules B S hS F hF` | `abbrev := @DerivedCategory (Modules.{u, u} …) _ _ (HasDerivedCategory.standard _)` | `DerivedDuality/Basic.lean` | Definitionally the canonical model, with the standard instance written explicitly. |
| `ModelDerivedModules B S hS F hF` | derived category of `ModelModules` (sheaves on the equi-universe model `smallEtaleModelRingedSite`, a `RingedSite.{u, u, u}`) | `DerivedDuality/Basic.lean` | Auxiliary. Comparison: `modelDerivedEquivalence : DerivedModules ≌ ModelDerivedModules`. It exists because `R𝓗om` (Stacks 0A97) is built only on equi-universe ringed sites. |
| `StdDerived`, `SchemeStdDerived T` | `Type (u + 1)` abbrevs | `DerivedDuality/ClosedBiduality.lean`, `DerivedDuality/LocalCharts.lean` | Auxiliary, inside the duality proofs (charts by schemes). Not a target for statements. |
| `D(QCoh(𝒪_X))` | `DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)` | `RingedSite.lean`, `Coherator.lean` | Different object. The comparison functor `quasicoherentDerivedComparison : D(QCoh) ⥤ D_QCoh` is proved an equivalence for affine `X` (`AffineSpaceDerivedComparison.lean`) and for Noetherian `X` (`Perfect/NoetherianDerivedCoheratorEquivalence.lean`), and only under a criterion in general (`Perfect/QuasicoherentDerivedEquivalenceCriterion.lean`). GL26 never uses `D(QCoh)`. |
| `D(𝒪_X)` on a ringed space, `PerfectDerivedCategory` for schemes | `StacksFrontier/AlgebraicGeometry/Perfect/BoundedLocallyFreeComplexes/Defs.lean`, `…/Perfect/ProperFlatPullbackHomProducts.lean` (`StdDerived X` for a scheme) | — | Scheme-side models, Zariski site. Not for spaces. The Zariski-to-étale comparison for schemes is 08HG (`Perfect/SmallEtalePerfectForward.lean`, `IsPerfectZariski` / `IsPerfectSmallEtale`). |

**Universes.**

* Schemes, the base and all algebraic spaces live in universe `u`. `points B S hS X.1` is
  `Type (u + 1)`.
* The small étale site is `RingedSite.{u + 1, u, u}`: its objects are in `Type (u + 1)`.
* Hence, by Mathlib's `SheafOfModules` (morphisms are natural transformations over the site)
  and `HasDerivedCategory.standard : HasDerivedCategory.{max u v} C`, **morphisms of `D(𝒪_X)`
  live in `Type (u + 1)`** (to confirm with `#check`).
* Coproducts exist for `Type u`-indexed families
  (`hasCoproducts_quasicoherentDerivedCategory_ringUniverse`).
* Compactness is quantified over `Type u` indices (A.5). This matters for the comparison with
  `IsCompactAb`.

### A.1 Base: sites, spaces, morphisms, fibre products, points

| GL26 notion | AxiomMath | file, tag | signature | verdict |
|---|---|---|---|---|
| big fppf site `(Sch/S)_fppf` (§2.4, `sec:duality_2cats`) | `AlgebraicGeometry.BigFppfSite` (structure: initial schemes, cutoff `κ`, bounded fppf coverings) | `StacksFrontier/AlgebraicGeometry/Topologies/Fppf.lean`, `@[stacks 021R]` | `structure BigFppfSite : Type (u+1)` (fields listed in the source) | **faithful**. It records all the choices of Stacks 021R explicitly. GL26 fixes "a base scheme" without naming the choices; any `B` is a legitimate reading. |
| `S ∈ (Sch/S)_fppf` | `B.Contains S` (`abbrev := X.size < B.cutoff`) | same | `abbrev BigFppfSite.Contains (B) (X : Scheme.{u}) : Prop` | **faithful** |
| `(Sch/S)_fppf` | `BigFppfOver B S hS := Over (B.obj hS)` | same, `@[stacks 021S "part (1), category"]` | `abbrev BigFppfOver (B) (S) (hS) : Type (u+1)` | **faithful** |
| algebraic space over `S` | `AlgebraicGeometry.IsAlgebraicSpace B S hS F`: fppf sheaf, diagonal representable (`yoneda.relativelyRepresentable (diag F)`), and a scheme atlas that is surjective and étale after every representable base change | `Basic.lean`, `@[stacks 025Y]` | `structure IsAlgebraicSpace (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop` | **faithful** (Stacks 025Y, as GL26 adopts) |
| category `Sp/S` | `AlgebraicGeometry.AlgebraicSpaces B S hS := ObjectProperty.FullSubcategory (IsAlgebraicSpace B S hS)`. Morphisms are natural transformations (`add_to_stacks 0260 CategoryTheory.NatTrans`). | `Category.lean`, `@[stacks 02X2]` | `abbrev AlgebraicSpaces (B) (S) (hS)` | **faithful** as a 1-category. GL26 §2.4 uses the (2,1)-category `Sp/S`; its 2-morphisms are identities for spaces (03YP, 003S), so the 1-category suffices. |
| scheme ↪ space | `isAlgebraicSpace_yoneda` (`@[stacks 025Z]`); `yonedaSpace B S hS T : AlgebraicSpaces B S hS := ⟨yoneda.obj T, _⟩` | `Category.lean` | `noncomputable abbrev yonedaSpace (B) (S) (hS) (T : BigFppfOver B S hS)` | **faithful**. Fullness is Yoneda. I found no packaged functor `BigFppfOver ⥤ AlgebraicSpaces`; one is `ObjectProperty.lift _ yoneda isAlgebraicSpace_yoneda`, a one-line definition. |
| fibre products `Y₁ ×_S Y₂`, `×_X` | `instance AlgebraicSpaces.hasPullbacks : HasPullbacks (AlgebraicSpaces B S hS)`; `isAlgebraicSpace_pullback`; `hasBinaryProducts_over_algebraicSpace (Z) : HasBinaryProducts (Over Z)` (`@[stacks 043C]`); products `isAlgebraicSpace_prod`, `AlgebraicSpaces.product`, `isLimitBinaryFanProduct` (`@[stacks 02X0]`) | `Category.lean:432`, `Limits.lean` | as named | **faithful**. Setup `setup:fm_cube_pullback` can use Mathlib `pullback` in `AlgebraicSpaces B S hS`. |
| `\|X\|`, points (03BT) | `points B S hS F := Quot (FieldValuedPoint.HasCommonExtension B S hS F)`. Topology `pointTopology B S hS F` (`PointsTopology.lean`); map `pointsMap`. | `Points.lean`, `@[stacks 03BU "set of points"]` | `abbrev points : Type (u + 1)` | **faithful**. 03BT has no attribute; 03BU carries the definition. |
| representative `t : Spec k → X` of `p ∈ \|X\|` | `structure FieldValuedPoint` (fields `carrier`, `field`, `contained`, `toBase`, `value : F.obj (op (Over.mk …))`). The morphism is `yoneda` of `value` out of `yonedaSpace B S hS p.siteObject`. | `Points.lean` | — | **faithful**. Note that `k` must satisfy `B.Contains (Spec k)` (field `contained`). Every residue field qualifies (`BigFppfSite.residueField_spec_contains`), but an arbitrary field extension need not. GL26 quantifies over all representatives in `lem:support_is_cohomological_for_finite_type_cohomology`; a faithful statement quantifies over the representatives in `B`. Large fields: `LargeValuedPoints.lean`. |
| decent (`lem:factor_residual_gerbes`) | `IsDecentSpace` (`@[stacks 03I8]`), `IsDecent` (`@[stacks 03KZ]`) | `Decent.lean` | `abbrev IsDecentSpace : Prop` | **faithful** |
| étale presentation (`sec:prelim_stacks_notions`) | no packaged notion. `IsAlgebraicSpace.exists_atlas` gives a surjective étale `yoneda.obj U ⟶ F`. | `Basic.lean` | — | **absent as a name**. Trivial to define. GL26's "finitely presented" is redundant (étale implies locally of finite presentation). |

### A.2 Properties of spaces and morphisms

All take `(f : F ⟶ G)` between presheaves on `BigFppfOver B S hS`, so they are applied to
`f.hom`.

| GL26 | AxiomMath | file, tag | definition (read) | verdict |
|---|---|---|---|---|
| quasi-compact space | `IsQuasiCompactSpace B S hS F` | `Morphisms.lean`, `@[stacks 03E3]` | exists a surjective étale chart from a scheme with compact underlying space | **faithful** |
| quasi-compact morphism | `IsQuasiCompact B S hS f` | `Morphisms.lean`, `@[stacks 03HE]` | every base change along a quasi-compact algebraic space has quasi-compact source | **faithful** |
| quasi-separated **space** | `IsAbsolutelyQuasiSeparated B S hS hZ F` with `hZ : B.Contains (⊤_ Scheme)` | `Separated.lean`, `@[stacks 03BS "part (3)"]` | quasi-separated over `Spec ℤ` | **faithful**: GL26 follows Stacks, where "quasi-separated space" is the absolute notion. `hZ` is always `B.contains_terminal` (`FiniteEtaleAtlasQuasiSeparated.lean:30`, a theorem). |
| quasi-separated / separated / locally separated morphism | `IsQuasiSeparated`, `IsSeparated`, `IsLocallySeparated` | `Morphisms.lean`, `@[stacks 03HL]` | the relative diagonal is quasi-compact / a closed immersion / an immersion | **faithful** |
| separated space | `IsAbsolutelySeparated` | `Separated.lean`, `@[stacks 03BS]` | — | **faithful** |
| Noetherian space | `IsNoetherian B S hS hZ F := IsQuasiCompactSpace ∧ IsAbsolutelyQuasiSeparated ∧ HasEtaleLocalProperty (IsLocallyNoetherian)` | `NoetherianSpaces.lean`, `@[stacks 03EA]` | — | **faithful** |
| locally Noetherian | `HasEtaleLocalProperty B S hS F (fun X => IsLocallyNoetherian X)` | (used in `NoetherianSpaces.lean`) | — | **faithful**. No standalone name. |
| proper | `IsProper B S hS f := IsSeparated ∧ IsFiniteType ∧ UniversallyClosed` | `UniversallyClosed.lean`, `@[stacks 03ZM]` | `UniversallyClosed` is closedness of `pointsMap` for every base change (`@[stacks 03HI]`) | **faithful** |
| flat | `IsFlat B S hS f := HoldsOnEveryEtaleChart … Flat f` | `Flat.lean`, `@[stacks 03ML, 03MK]` | flat on every étale chart square; `isFlat_iff_presheaf` compares it with the representable notion | **faithful** |
| surjective | `IsSurjective B S hS f` (surjective on `points`) | `Flat.lean`, `@[stacks 03ME]` | — | **faithful** |
| locally of finite type / finite type | `IsLocallyOfFiniteType`, `IsFiniteType := IsLocallyOfFiniteType ∧ IsQuasiCompact` | `FiniteType.lean`, `@[stacks 03XF]` | — | **faithful** |
| locally of finite presentation / finite presentation | `IsLocallyOfFinitePresentation` (`@[stacks 03XP]`); `IsFinitePresentation := IsLocallyOfFinitePresentation ∧ IsQuasiCompact ∧ IsQuasiSeparated` (`FinitePresentation.lean:115`) | `FinitePresentation.lean` | — | **faithful** |
| étale | `IsEtale B S hS f`: the composite with every étale scheme chart is étale | `Morphisms.lean`, `@[stacks 03FR]` | — | **faithful** (Stacks 03FR) |
| smooth | `IsSmooth` | `Smooth.lean`, `@[stacks 03ZC]` | — | **faithful** |
| affine morphism | `IsAffineHom B S hS f` (base change to an affine scheme is an affine scheme) | `Morphisms/Affine.lean`, `@[stacks 03WF]` | — | **faithful** |
| quasi-affine morphism (`lem:quasi-affine_via_diagonal`) | `IsQuasiAffineHom` | `Morphisms/QuasiAffine.lean`, `@[stacks 03WL]` | — | **faithful** |
| open / closed immersion, immersion | `IsOpenImmersion`, `IsClosedImmersion`, `IsImmersion`; subspaces `IsOpenSubspace`, `IsClosedSubspace` | `Morphisms.lean`, `@[stacks 02YU]` | representable, and every represented base change has the property | **faithful** |
| perfect morphism | `IsPerfect B S hS f` (`HoldsOnEveryEtaleChart … Perfect`) | `Morphisms/PseudoCoherent/Perfect.lean`, `@[stacks 06BZ]` | — | **faithful**. This is a **morphism** property, not to be confused with `RingedSite.IsPerfect` for objects. |
| finite Tor dimension (`rmk:relative_perfects4`) | `HasFiniteTorDimension (g : Y' ⟶ Y)` (structure: ring maps of affine étale chart squares have finite Tor dimension) | `HasFiniteTorDimension.lean`, untagged | takes morphisms of `AlgebraicSpaces` | **faithful (variant)**. GL26 defines it by bounded cohomology of `E ⊗^L Lf^*M` for `M ∈ Qcoh(X)`. The equivalence is a chart computation that AxiomMath does not state. |
| Tor independence (08IP) | `TorIndependent (hF) (hG) (hH) f g` | `TorIndependence.lean`, `@[stacks 08IP]` | Tor independence of étale local rings at geometric points | **faithful**. Flat implies Tor independent: `torIndependent_of_isFlat_left` (`Perfect/ProperFlatSingleDegreeRankLocus.lean:52`). |

### A.3 Categories: `Mod`, `Qcoh`, `D`, `D_qc`, `Perf`, pseudo-coherent, `D^b_coh`, support

| GL26 | AxiomMath | file, tag | signature / definition | verdict |
|---|---|---|---|---|
| `X_étale` | `Space.SmallEtale B S hS F := (IsEtaleChart B S hS F).FullSubcategory` (étale charts `yoneda.obj U ⟶ F`), `SmallEtale.topology` | `SmallEtaleSite.lean`, `@[stacks 03ED]` | `abbrev SmallEtale : Type (u+1)` | **faithful** |
| `Mod(X)` | `Space.Modules.{u, m} B S hS F hF := SheafOfModules.{m} (ringSheaf (smallEtaleRingedSite B S hS F hF).O)`; `smallEtaleRingedSite : RingedSite.{u+1, u, u}` | `RingedSite.lean` (refs 03G9, 04KH) | `noncomputable abbrev Modules (hF : IsAlgebraicSpace B S hS F)` | **faithful** (03LT / 04KH) |
| `Qcoh(X)` | `QuasicoherentSheaves (hF) := (SheafOfModules.isQuasicoherentOnSite …).FullSubcategory`. `IsQuasicoherentOnSite M`: every object has a covering on whose members `M` has a global presentation | `RingedSite.lean` (`@[stacks 03G9]`); predicate in `StacksFrontier/AlgebraicGeometry/Topologies/QuasicoherentOnSite.lean` (`@[stacks 03DL "quasi_coherent"]`) | `class IsQuasicoherentOnSite (M : SheafOfModules.{m} R) : Prop` | **faithful** (Stacks 03DL(6)). Weak Serre at `m = u`: `QuasicoherentWeakSerre.lean` (closed under extensions, kernels and cokernels; Stacks 03M1, 0754). |
| `D(X)` | `DerivedCategory (Modules.{u,u} B S hS X.1 X.2)` (standard model) | Mathlib | — | **faithful** (unbounded) |
| `D_qc(X)` | property `Space.QcohDerived B S hS Y := DerivedCategoryB.derivedCategoryB (isQuasicoherentOnSite …)`, i.e. `fun E => ∀ n, IsQuasicoherentOnSite (H^n E)`; category `Space.QuasicoherentDerivedCategory B S hS F hF` | `QuasicoherentDerivedPushforward.lean:101`; `QuasicoherentDerivedCategory.lean` (`@[stacks 071X]`); `derivedCategoryB` in `StacksFrontier/Algebra/Homology/DerivedCategory/SerreSubcategory.lean:1255` | `abbrev QcohDerived (Y : AlgebraicSpaces B S hS) : ObjectProperty (DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))` | **faithful** |
| `D_qc` triangulated | `instance isTriangulated_quasicoherentDerivedCategory : (derivedCategoryB (isQuasicoherentOnSite.{u+1,u,u,u} …)).IsTriangulated` | `QuasicoherentWeakSerre.lean:79` (Stacks 06UQ) | — | **faithful**. Import `QuasicoherentWeakSerre` explicitly: the docstring of `QuasicoherentDerivedCategory.lean` still says that `D_QCoh` is not yet known to be triangulated, which is stale. Also `IsClosedUnderIsomorphisms` (`QuasicoherentDerivedPushforward.lean`). |
| `Perf(X)` | `RingedSite.IsPerfect (smallEtaleRingedSite …) E`: `E ≅ Q(K)` with `K` **locally strictly perfect on a covering of every object**. `perfectProperty B S hS X`, `PerfectDerivedCategory := (perfectProperty …).FullSubcategory` | `StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/PerfectObjects.lean:113` (`@[stacks 08G5]`); `Perfect/LimitPerfectObjects.lean:173` | `noncomputable def IsPerfect [HasDerivedCategory.{d} …] (K : DerivedCategory (SheafOfModules.{m} …)) : Prop` | **faithful** (08G5; GL26 cites 08G4, the section). AxiomMath's `Perf` is a subcategory of `D(𝒪_X)`, and GL26's of `D_qc`. They agree because perfect objects lie in `D_QCoh`: `qcohDerived_of_isPerfect_derivedCategoryB` (`Perfect/PerfectRetract.lean:82`). |
| pseudo-coherent | `RingedSite.IsPseudoCoherent`, `IsPseudoCoherentFrom E m` | `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/PseudoCoherentObjects.lean`, `@[stacks 08FT]` | `noncomputable def IsPseudoCoherent [HasDerivedCategory.{d} …] (E) : Prop` | **faithful** |
| `coh(X)`, coherent | `IsCoherent B S hS F hF M` (07UA); `isWeakSerre_isCoherent` | `CoherentModules.lean` (imported by `DerivedDuality/Basic.lean`) | — | **faithful**. On locally Noetherian spaces, coherent = quasi-coherent of finite type is 07UB (15 attributions in Spaces). |
| `D^b_coh(X)` | `derivedCategoryBBounded (isCoherent.{u,u} B S hS X.1 X.2)` = bounded and all `H^n` coherent. Also `coherentDerived` (`DerivedDuality/Basic.lean`), `IsBoundedBelow`/`IsBoundedAbove` there, and `derivedCategoryBPlus`. | `SerreSubcategory.lean:1357` | — | **faithful (variant)**. GL26 defines `D^b_coh` as *bounded pseudo-coherent* (Noetherian `X`). The equivalence is 08IK, **present**: `PseudoCoherent/PseudoCoherentIffCoherentHomology.lean:264` and `:284` ("pseudo-coherent objects of `D_QCoh` are those of `D⁻_Coh`"). |
| `D^b_qc`, `D^-_coh`, `D^+_qc` | `derivedCategoryBBounded (isQuasicoherentOnSite …)`; `derivedCategoryBPlus`; `DerivedCategoryB.IsBoundedBelow` | `SerreSubcategory.lean` | — | **faithful**. Generic Serre-subcategory constructions, instantiated at the qc / coherent predicates. |
| `Supp(M)`, `M ∈ Qcoh` (`sec:preliminaries_stacks_support`) | `supportOfSheaf B S hS X F : Set (points B S hS X)` = points over which some geometric point has a nonzero stalk | `SheafSupport.lean:626` | `def supportOfSheaf (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})` | **faithful (variant)**. This is the 04K7-style support of abelian sheaves, which GL26 says coincides with its definition `p(Supp p^*M)` (07TY). AxiomMath has one 07TY attribution in Spaces; whether it is exactly this equality is part B's to confirm. |
| `Supp(E)`, `E ∈ D_qc` | `CohomologySupportedOn B S hS F hF T E := ∀ i, supportOfSheaf (H^i E) ⊆ T` | `DerivedSupport.lean:77` | `noncomputable abbrev CohomologySupportedOn … (T : Set (points B S hS F)) (E : DerivedCategory (Modules.{u, m} …)) : Prop` | **faithful** (GL26 defines `Supp E = ⋃ Supp H^j`, and "supported on `Z`" is exactly this) |
| `D_{qc,Z}(X)` | `quasicoherentDerivedSupportedOn X T : ObjectProperty (QuasicoherentDerivedCategory.{u,u} …)`; inclusion `quasicoherentDerivedSupportedOnι` | `Perfect/SupportedQuasicoherentDerived.lean:132` | — | **faithful**. Closed under `Type u` sums for closed `T`. |

### A.4 Functors

| GL26 | AxiomMath | file, tag | signature / note | verdict |
|---|---|---|---|---|
| `Lf^*: D(X) → D(Y)` | `smallEtaleDerivedModulePullback B S hS f`: the left derived functor (06YY) for the morphism of small étale ringed topoi `smallEtaleRingedToposHom` (03G8) | `SmallEtaleDerivedModulePullback.lean:122` | `abbrev smallEtaleDerivedModulePullback (f : X ⟶ Y) [(smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor (smallEtaleModuleQuasiIso B S hS Y)] : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ⥤ DerivedCategory (… X)` | **faithful**. The `HasLeftDerivedFunctor` argument is found by instance (`hasLeftDerivedFunctor_pullbackOnHomotopy`), so no user hypothesis. |
| `Rf_*: D(Y) → D(X)` | `derivedModulePushforward B S hS f := derivedPushforward (smallEtaleRingedToposHom B S hS f)`; triangulated (`derivedModulePushforward_isTriangulated`); a right derived functor of `modulePushforward` | `QuasicoherentDerivedDirectImage.lean` | `abbrev derivedModulePushforward (f : X ⟶ Y) : DerivedCategory (Modules.{u,u} … X.1 X.2) ⥤ DerivedCategory (Modules.{u,u} … Y.1 Y.2)` | **faithful**. A third spelling, `Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)`, appears in the 0E4U and 08GK statements. It is identified with this one by `totalRightDerived_modulePushforward_eq`. |
| `Lf^* ⊣ Rf_*` on `D` | `smallEtaleDerivedModuleAdjunction B S hS f` (07A6), compatible with shifts (`…_commShift`) | `SmallEtaleDerivedModuleAdjunction.lean:103` | `def … : smallEtaleDerivedModulePullback B S hS f ⊣ derivedPushforward (…) (smallEtaleRingedToposHom B S hS f)` | **faithful** |
| `Rf_*` preserves `D_qc` | `qcohDerived_derivedModulePushforward_obj` (08FA (1)), for `f` quasi-compact and quasi-separated; restricted functor `quasicoherentDerivedPushforward B S hS f hfqc hfqs` (`IsTriangulated`, `CommShift ℤ`) | `QuasicoherentDerivedDirectImage.lean` | `def quasicoherentDerivedPushforward (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) : QuasicoherentDerivedCategory.{u,u} … X.1 X.2 ⥤ … Y.1 Y.2` | **faithful**. GL26 assumes `X, Y` qcqs; `isQuasiCompact_of_isQuasiCompactSpace` and `isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source` produce the morphism hypotheses. |
| `Lf^*` preserves `D_qc` | `derivedQuasicoherent_smallEtaleDerivedModulePullback`; restricted functor `quasicoherentDerivedPullback` (`@[stacks 08F4]`, `QuasicoherentDerivedPullback.lean:227`) and `quasicoherentDerivedModulePullback` (`QuasicoherentDerivedModulePullback.lean`, the one used by the adjunction) | as named | for **arbitrary** `f` | **faithful**. Two spellings of the same functor between `rfl`-equal categories. Pick `quasicoherentDerivedModulePullback`. |
| `Lf^* ⊣ Rf_*` on `D_qc` | `quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs`, with unit and counit equal to those on `D` | `QuasicoherentDerivedAdjunction.lean` | `def … : quasicoherentDerivedModulePullback f ⊣ quasicoherentDerivedPushforward B S hS f hfqc hfqs` | **faithful** |
| `L(gf)^* ≅ Lf^* Lg^*` | `smallEtaleDerivedModulePullbackCompIso B S hS f g : Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` (0D6D for spaces), with cocycle `smallEtaleDerivedModulePullbackCompIso_assoc`; `…Congr` | `SmallEtaleDerivedModuleAdjunction.lean:153`, `SmallEtaleDerivedPullbackCompAssoc.lean` | natural isomorphism of functors | **faithful**, as a natural isomorphism with associativity. Not packaged as a Mathlib `Pseudofunctor`. The unit isomorphism exists as `smallEtaleDerivedModulePullbackIdIso X` (`Morphisms/PseudoCoherent/DerivedPullbackCompositionCanonical.lean:182`; also `…IdentityIso`, `…IdObjIso`). I did not check its unit coherence with `…CompIso`. |
| `R(gf)_* ≅ Rg_* Rf_*` | `smallEtaleDerivedPushforwardCompIso`, `derivedModulePushforwardCompIso` (`DerivedPushforwardHigherDirectImages.lean:129,139`); `smallEtaleDerivedPushforwardCompIsoToposHom`, adjoint to 0D6D (`conjugateEquiv_smallEtaleDerivedModulePullbackCompIso_inv`) | as named | natural isomorphism | **faithful**. On `D_QCoh` it is obtained by restriction, which is not packaged. |
| `⊗^L` | `smallEtaleDerivedTensorProduct B S hS X := canonicalDerivedTensorProduct _` (06YU); bifunctor `smallEtaleDerivedTensor B S hS X : D ⥤ D ⥤ D` | `SmallEtaleDerivedTensor.lean:87,92` | — | **faithful** |
| `Lf^*(E ⊗ G) ≅ Lf^*E ⊗ Lf^*G` | `smallEtaleDerivedPullbackTensorIso f` (07A4) | `SmallEtaleDerivedTensor.lean:103` | isomorphism of uncurried bifunctors | **faithful** |
| `D_qc ⊗ D_qc ⊆ D_qc` | `qcohDerived_smallEtaleDerivedTensor` (08F5) | `QuasicoherentDerivedTensorClosed.lean` | — | **faithful** |
| `D(X)`, `D_qc(X)` monoidal | `smallEtaleDerivedMonoidal X`, `quasicoherentDerivedMonoidal : MonoidalCategory (QuasicoherentDerivedCategory.{u,u} …)` (0FPT), `@[instance_reducible] def`, not a global instance | `QuasicoherentDerivedMonoidal.lean:92` | — | **special case**. Monoidal only. I found no `SymmetricCategory` or `MonoidalClosed` on `D(𝒪_X)` or `D_QCoh(𝒪_X)` for spaces; for equi-universe ringed sites there are `derivedTensorSymmetric` and `derivedTensorMonoidalClosed` (`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedTensorMonoidalClosed.lean`, 0FPT/08J8). GL26 `sec:prelim_stacks_internal_homs` needs closed symmetric monoidal `D_qc`. |
| `Lf^*` monoidal (`sec:prelim_stacks_functors`, used in `lem:spacey_Lipman_Hashimoto`) | `quasicoherentDerivedPullbackMonoidal (f) (hassoc : PullbackTensorAssociativity f)` | `QuasicoherentDerivedPullbackMonoidal.lean:184` | **takes the hypothesis** `PullbackTensorAssociativity f` (07A4 compatible with the associators), which is **not discharged** anywhere in AxiomMath | **conditional**. Gap C.4. |
| `ℝ𝓗om` on `D(X)` | `derivedSheafHomBifunctor B S hS F hF : (DerivedModules …)ᵒᵖ ⥤ DerivedModules … ⥤ DerivedModules …` (0A97 on the equi-universe model, conjugated by `modelDerivedEquivalence`); `derivedSheafHom A C` | `DerivedDuality/Basic.lean` | — | **faithful as a functor**. The adjunction `- ⊗^L E ⊣ ℝ𝓗om(E, -)` (08J8) is proved on the model site (`derivedTensorMonoidalClosed`) but **not transported** to `DerivedModules`, because `⊗^L` on spaces is built on the non-model site. Gap C.5. |
| bold `𝐑𝓗om` on `D_qc`; coherator `Q: D(X) → D_qc(X)` (`lem:internal_hom`) | absent on `D_QCoh`. Related: `coherator`, `derivedCoherator`, and `comparisonDerivedCoheratorAdjunctionOfCoherator : quasicoherentDerivedComparison ⊣ ι ⋙ derivedCoherator` (into `D(QCoh)`, not `D_QCoh`) | `Coherator.lean` | — | **absent** (GL26's `Q` is right adjoint to `D_qc ↪ D`). Constructible (Gap C.5). |
| `f^×` | `quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs : D_QCoh(Y) ⥤ D_QCoh(X)` and `quasicoherentDerivedRightAdjointAdjunction … : quasicoherentDerivedPushforward … ⊣ …`. Exactness: `exists_isTriangulated_rightAdjoint_quasicoherentDerivedPushforward` (the adjoint with `CommShift` and a triangulated adjunction). Preserves coproducts: `preservesCoproducts_rightAdjoint_quasicoherentDerivedPushforward`. | `DualityRightAdjointBaseChange.lean`, `CompactGeneration/QcqsCompactGeneration.lean` (`add_to_stacks 0E55`) | `def quasicoherentDerivedRightAdjoint (hZ) (f : X ⟶ Y) (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) : …` | **faithful**. It is defined by `.rightAdjoint`, so its shift structure is not the one from the `∃`; the next wave should take the `∃` version, or prove that the two agree, when it needs `IsTriangulated`. |
| projection formula | `smallEtaleProjectionFormulaMap`; isomorphism `isIso_smallEtaleProjectionFormulaMapSnd hfqc hfqs K hK E hE` (08IN, the `K ⊗ Rf_*E` order) and the `Rf_*E ⊗ K` order, `isIso_smallEtaleProjectionFormulaMap hfqc hfqs E hE K hK` (`SmallEtaleProjectionFormulaIso.lean:126`) | `SmallEtaleDerivedProjectionFormula.lean`, `SmallEtaleProjectionFormulaSnd.lean:249` | `f` quasi-compact and quasi-separated, `E, K ∈ D_QCoh` | **faithful** |
| base change map (07A7) | `smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w`; on `D_QCoh`: `quasicoherentDerivedBaseChange` | `SmallEtaleDerivedModuleAdjunction.lean`, `DualityRightAdjointBaseChange.lean` | — | **faithful** |
| Tor-independent base change | `isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent (sq : IsPullback g' f' f g) hfqc hfqs (hTor : TorIndependent …) E hE` | `SmallEtaleDerivedTorIndependentBaseChange.lean:248`, `@[stacks 08IR]` | — | **faithful** |
| flat base change | `isIso_smallEtaleDerivedBaseChangeMap_of_isFlat` (also via 08IR and `torIndependent_of_isFlat_left`) | used in `Perfect/CohomologyBaseChangeProper.lean` | — | **faithful** |
| `Rf_*` preserves `Perf` | `isPerfect_derivedModulePushforward_of_isProper hZ f (hY : IsNoetherian …) (hfPerfect : IsPerfect B S hS f.hom) (hfProper : IsProper …) E hE` (0E4U: proper **perfect** morphism, Noetherian target); `isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hfp hfl hf E hE` (0CTM (1): proper, flat, finite presentation, no Noetherian hypothesis, together with base change for arbitrary squares) | `Perfect/PerfectProperPushforward.lean:255`, `Perfect/CohomologyBaseChangeProper.lean:61` | — | **faithful** for these hypotheses. GL26 uses proper flat (`setup:fm_cube_pullback`), which 0CTM covers. |
| `Rf_*` preserves `D^b_coh` | `derivedCategoryBBounded_derivedModulePushforward_of_hasProperSupport hTop f (hf : IsLocallyOfFiniteType …) (hY : IsNoetherian …) E hE (hsupp : ∀ i, HasProperSupport …)` | `Perfect/DerivedPushforwardCoherentProperSupport.lean:153`, `@[stacks 08GK]` | — | **faithful**. For `f` proper, `HasProperSupport` should be automatic; that lemma has to be found or proved. The module-level `isCoherent_rightDerived_modulePushforward_of_isNoetherian_source` is conditional (hypotheses `h0720`, `hwitness`); avoid it. |
| `Lf^*` preserves `Perf` and pseudo-coherence (08H4, 08H6) | `isPerfect_smallEtaleDerivedModulePullback f E hE` (`Perfect/DerivedPullbackPerfect.lean:63`); `isPseudoCoherent_smallEtaleDerivedModulePullback` (`PseudoCoherent/DerivedPullback.lean:228`) | — | — | **faithful** |
| `Lt^*` for a point `t: Spec k → X` | no special API. `t` is a morphism `yonedaSpace B S hS p.siteObject ⟶ X` (from `p.value`), and `Lt^*` is `smallEtaleDerivedModulePullback` of it. | — | — | **faithful**, with the caveat on `B.Contains (Spec k)` (A.1) |

### A.5 Compactness and generation

| GL26 | AxiomMath | file, tag | statement | verdict |
|---|---|---|---|---|
| compact object | `CategoryTheory.IsCompactObject.{w} (K : C)`: for every `I : Type w` and every `E : I → C` with a coproduct, `⨁ i, (K ⟶ E i) → (K ⟶ ∐ E)` is bijective | `StacksFrontier/CategoryTheory/Triangulated/CompactObjects/ThickSubcategory.lean:106`, `@[stacks 07LS]` | `public class IsCompactObject (K : C) : Prop` (universe `w` of the index) | **AxiomMath's own notion**, not Mathlib's. Used at `w = u`. |
| compact = perfect in `D_qc` | `isCompactObject_iff_isPerfect X hqc hqs E : IsCompactObject.{u} E ↔ (smallEtaleRingedSite …).IsPerfect E.obj` | `Perfect/PerfectCompactQcqs.lean:155`, `@[stacks 09M8]` | `X` qcqs (`hqs` with `B.contains_terminal`) | **faithful** |
| single perfect generator | `exists_isPerfect_generator X hqc hqs : ∃ P, IsPerfect P ∧ ∀ E : D_QCoh, IsZero E.obj ↔ ∀ n, Subsingleton (P⟦n⟧ ⟶ E.obj)` (09IY); `exists_isCompactObject_isWeakTriangulatedGenerator_of_qcqs`; classical generator `exists_isPerfect_isWeakTriangulatedGenerator_triangEnvelope_eq` (`Perfect/PerfectClassicalGenerator.lean`, 0GFC); `approximationByPerfectComplexes_of_qcqs` (08HP, `Perfect/ApproximationQcqs.lean:61`) | `Perfect/PerfectCompactQcqs.lean:170` | — | **faithful** |
| `D_{qc,Z}` compactly generated; compacts = perfect | `isCompactObject_iff_isPerfect_of_supported X hXqc hXqs T (hT : IsClosed T) (hTc : IsCompact Tᶜ) E` (0AED); `exists_isPerfect_generator_of_supported` (0AEC) | `Perfect/SupportedCompactPerfect.lean:76`, `Perfect/SupportedPerfectGenerator.lean:392` | — | **faithful** to `sec:prelim_stacks_perfects` (`|X| \ Z` quasi-compact is `IsCompact Tᶜ`) |
| Brown representability | `exists_isTriangulated_rightAdjoint_of_compact_generator` | `StacksFrontier/CategoryTheory/Triangulated/LocallySmallTransport.lean:258` | — | generic tool for C.5 |

**Relation to this repo's `RelativeWeakApprox.IsCompactAb`** (`WeakApprox/Basic.lean:147`).
`IsCompactAb H` says that `preadditiveCoyoneda.obj (op H)` preserves colimits of shape
`Discrete J` for every `J : Type v`, where `v` is **the morphism universe of `C`**.
`IsCompactObject.{w}` says that the canonical map `⨁ Hom(K, E i) → Hom(K, ∐ E)` is bijective for
every `I : Type w`. For a fixed index universe the two say the same thing, because colimits in
`AddCommGrpCat` of a discrete diagram are direct sums. Writing that comparison lemma is a few
dozen lines; it is not in either library.

**The universes do not match.** On `D_QCoh(𝒪_X)` the morphism universe is (per A.0) `u + 1`,
while AxiomMath's 09M8 / 09IY / 0AED are at `IsCompactObject.{u}` (indices in `Type u`, the
coproducts that exist). So `IsCompactAb` on `D_QCoh(𝒪_X)` would quantify over `Type (u+1)`
index types, and 09M8 does not provide it.

What would settle it:
1. confirm the morphism universe with `#check (inferInstance : Category.{?} (QuasicoherentDerivedCategory.{u,u} …))`;
2. then either make `IsCompactAb` universe-polymorphic in the index universe (statement change
   in `WeakApprox/`: orchestrator decision), or prove that `IsCompactObject.{u}` implies
   `Type (u+1)`-compactness in `D_QCoh`. The latter is plausible, since a `Type (u+1)`-indexed
   coproduct that exists has only `u`-many non-zero summands up to isomorphism, but it is not
   obvious and I have not checked it.

### A.6 Relative perfectness

| | definition | where |
|---|---|---|
| **GL26 `def:relative_perf_stacks`** | `f: Y → X` a morphism of qcqs spaces. `E ∈ D_qc(Y)` is `f`-perfect if `E ⊗^L Lf^*A ∈ D^b_qc(Y)` for all `A ∈ D^b_qc(X)`. **No flatness, no finite presentation, no pseudo-coherence.** | `manuscripts/GL26/main.tex`, `def:relative_perf_stacks` |
| **GL26 `def:quasi_perf`** | `E ∈ D_qc(Y)` is `f`-quasi-perfect if `Rf_*(E ⊗^L P) ∈ Perf(X)` for all `P ∈ Perf(Y)` | `def:quasi_perf` |
| **AxiomMath 0DKN** | `IsPerfectRelativeTo B S hS f (_hflat : IsFlat B S hS f.hom) (_hlfp : IsLocallyOfFinitePresentation B S hS f.hom) (T : ∀ U, DerivedTensorProduct.{u+1,u,u,e} ((inverseImageRingedSite B S hS f).over U)) (E : DerivedCategory (Modules.{u,u} B S hS X.1 X.2)) : Prop := IsPseudoCoherent E ∧ LocallyHasFiniteTorDimension T ((derivedScalarRestriction B S hS f).obj E)`. `IsPerfectRelativeToCanonical` (`T` = the canonical 06YU family) and `isPerfectRelativeToCanonical` (a triangulated, saturated `ObjectProperty`, 0DKR). | `Perfect/Relative.lean:179`, `Perfect/RelativeSubcategory.lean:434–442`, `@[stacks 0DKN]` |

**Verdict: different notion.** The relation is GL26's own `rem:comparison_stacks_project`:
for `f` flat and locally of finite presentation between qcqs spaces, a pseudo-coherent `E` is
0DKN-perfect if and only if it is `f`-perfect. The remark proves this from étale locality
(`thm:relative_perf_iff_smooth_locally` and 0DKQ) and [GVLMP25, Prop. 3.1]. **AxiomMath does
not prove this comparison.**

So:
1. GL26's `f`-perfect must be **defined in this repo**, from `smallEtaleDerivedTensor`,
   `quasicoherentDerivedModulePullback` and `derivedCategoryBBounded (isQuasicoherentOnSite …)`.
   That is a short definition, faithful by construction.
2. 0DKN, with `IsPseudoCoherent` added, is the **special case** "flat, locally of finite
   presentation, pseudo-coherent". The comparison is a theorem to prove (Gap C.7). It is
   needed only where GL26 invokes 0DKT, 0DKX, 0GFK, 0GFL (alternative proofs), so it is optional
   for the main line.

Further notes on 0DKN:
* `_hflat` and `_hlfp` are unused arguments (the docstring says so), so they do no harm.
* `T` is a free parameter. Use `IsPerfectRelativeToCanonical` to avoid a vacuous or arbitrary
  choice.
* `f`-quasi-perfect is **absent**. It is a one-line definition from
  `quasicoherentDerivedPushforward`, `⊗^L` and `perfectProperty`.

### A.7 Nagata, duality, Grothendieck existence

| GL26 | AxiomMath | file, tag | verdict |
|---|---|---|---|
| Nagata compactification (`sec:duality_2cats`) | `hasCompactification_of_isSeparated_of_isFiniteType hZ hX hY (hYqc : IsQuasiCompactSpace …) (hYqs : IsAbsolutelyQuasiSeparated …) f (hsep : IsSeparated …) (hft : IsFiniteType …) : HasCompactification B S hS f`. Here `HasCompactification f := ∃ X' j p, IsAlgebraicSpace X' ∧ IsOpenImmersion j ∧ IsQuasiCompact j ∧ IsProper p ∧ j ≫ p = f`. | `NagataCompactification/Nagata.lean:63` (`@[stacks 0F4D]`), `…/HasCompactification.lean:64` | **faithful**, and slightly stronger than GL26 needs: qcqs target instead of Noetherian, finite type instead of finite presentation, and `j` quasi-compact. |
| dualizing complex; `D = R𝓗om(-, K)` | `IsDualizingComplexOnSpace` (0E4Z, `DualizingComplexEtaleCharts.lean:462`); `dualFunctor`, `derivedBiduality`, `dualizingComplex_duality` (0E51) | `DerivedDuality/SpaceDuality.lean` | **faithful**. GL26 §2.4 does not use dualizing complexes directly; relevant to `f^×`-based results. |
| `f^×` trace and evaluation; `Rf_* 𝐑𝓗om(L, f^×K) ≅ 𝐑𝓗om(Rf_*L, K)` (0E58) | `DualityPushforwardTrace.lean` (`@[stacks 0E57]`, `@[stacks 0E58]`); `DualityPushforwardTraceCriterion.lean` (0GG4 (1), (2)) | — | **present**. Stated with `R𝓗om` on `D(𝒪_X)` plus coherator readings. Check the exact form against `rem` after `lem:internal_hom` before use. |
| `f^×` base change map | `TorIndependentBaseChangeSquare` (0E5B), `quasicoherentDerivedRightAdjointBaseChange` (mate, 0E5B), `quasicoherentDerivedRightAdjointBaseChangeMap` (0E5D), trace compatibility (0E5L), vertical / horizontal pasting (0E5E, 0E5F) | `DualityBaseChange.lean`, `DualityRightAdjointBaseChange.lean`, `DualityBaseChangeMap.lean` | **faithful**, for Tor-independent squares of qcqs spaces |
| `f^×` base change **isomorphism** (`lem:neeman188`, second half) | 0E5I (1): `isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isFlat` (proper, flat, finite presentation, `Y`, `Y'` **affine**). 0E5I (2): `…_of_isPerfect` (proper, perfect, `Y`, `Y'` affine, `Y` Noetherian). 0E5I (3): `…_of_hasFiniteTorDimension` (`U' → U` affine of finite Tor dimension, `U` Noetherian, `K ∈ D^+`). | `DualityRightAdjointBaseChangeAffineIso.lean:265`, `DualityRightAdjointBaseChangeAffinePerfect.lean:53`, `DualityRightAdjointBaseChangeAffineTorDimension.lean:68` | **special case** (affine bases). GL26 needs it for Noetherian spaces with `v` flat and `g` proper. Globalizing over étale charts is Gap C.8. |
| `f^!` (Neeman 2023 Construction 9.4), `ρ`, `σ`, `χ` (`lem:neeman186`–`lem:neeman189`) | absent for spaces. Only closed-immersion and ring-level upper-shriek files: `StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionUpperShriekDualizing`, `StacksFrontier/RingTheory/Dualizing/UpperShriek/*`. | — | **absent** (Gap C.3) |
| Grothendieck existence | `Spaces/GrothendieckExistence/` exists | — | GL26 does not cite it (no 088x / 08BE tags, no textual use), so it is not mapped. |

### A.8 What GL26 §3, §6, §8–§12 cite

The per-tag answers are `results/AXIOMMATH_TAGS.md` (part B). Notions those sections need,
beyond A.1–A.7:

* **Tor amplitude / finite Tor dimension of objects.**
  `StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/LocallyFiniteTorDimension.lean`
  (`LocallyHasFiniteTorDimension`); spaces: `TorAmplitudeQuasiCoherentTests.lean`
  (`HasTorAmplitudeOnQuasicoherent`). **faithful (variant)**: GL26 measures boundedness
  against `Qcoh`; see `rmk:relative_perfects3`.
* **Derived fibres `Lt^*K` and fibrewise criteria.** There is no packaged "derived fibre". The
  geometric-stalk relative Tor amplitude results are in
  `Perfect/RelativeTorAmplitudeGeometricStalks.lean` and
  `Perfect/StalkRelativeTorAmplitudeBaseChange.lean`; the fibrewise bounded-below/above
  criteria are 0GFH, 0GFI, 0GFK, 0GFL (`Perfect/BoundedAboveCriterion.lean`,
  `BoundedBelowCriterion.lean`, `RelativeFibrewiseBoundedBelow.lean`,
  `DerivedChow/RelativePerfect.lean:303`). These are exactly what
  `rem:comparison_stacks_project` calls alternative proofs.
* **Openness of loci (§11) and semicontinuity.** I found no "perfect locus is open" or
  "quasi-perfect locus is open" for spaces among the declarations I searched. The
  `Morphisms/*Locus*` files are about flat, isomorphism and closed-immersion loci. Part B
  settles the individual tags.
* **Neeman's "compact ⇒ perfect"** (the repo's second permitted assumption) is AxiomMath's
  09M8, proved, for spaces. Once AxiomMath is imported, that assumption can be dropped.
* **Weak approximability** (`sec:loci__weak_approx`, `rem:rel_perfect_is_free`,
  `rmk:equivalences_induced`): absent (Gap C.2).

---

## C. Gaps: what GL26 / LP26 need that AxiomMath does not provide

Sizes are rough estimates of new Lean, assuming the AxiomMath API in A.

| # | gap | needed by (GL26 unless stated) | size | notes |
|---|---|---|---|---|
| C.1 | **Fourier–Mukai functor** `Φ_K = Rp_{2*}(Lp_1^*(-) ⊗^L K)` on `D_QCoh`, for `p_i` the projections of `Y₁ ×_S Y₂`; its base-change cube (`setup:fm_cube_pullback`); functoriality in `K` (`sec:funct_on_kernel`) | everything from `sec:prelim_fm_setup` on: `introthm:base_change`, §6–§10, §12 | M (300–800 lines) | All ingredients exist: pullbacks in `AlgebraicSpaces`, `quasicoherentDerivedModulePullback`, `quasicoherentDerivedPushforward` (projections are qcqs when `Y₂ → S` is), `⊗^L` on `D_QCoh`. The cost is in the natural-isomorphism bookkeeping of the cube: 0D6D/0D6E isomorphisms, 07A4, flat base change (08IR). |
| C.2 | **Weak approximability** (Neeman) of `D_qc(X)` and of `D_{qc,Z}(X)` | `sec:loci__weak_approx`, `rem:rel_perfect_is_free`, `rmk:equivalences_induced`, `prop:preservation_of_dbcoh` paths; LP26 throughout | L. Categorical part: the repo's `WeakApprox/` library. Geometric input (Neeman 2024, Thm 3.2 type, for spaces): large. | Not in Stacks, so not in AxiomMath. LP26 is mostly categorical; its geometric applications need C.2. |
| C.3 | **Neeman's `f^!`** for separated finite-type morphisms of Noetherian spaces (via 0F4D), the oplax `ρ(f,g)`, `σ`, `χ`, and `lem:neeman186`–`lem:neeman189` | §2.4 (`sec:duality_functors`, `sec:duality_relations`), §7 (`sec:base_change_for_adjoints`), §11 | L (2–5k lines) | Independence of the compactification is the hard part. The relevant Stacks chapter (Duality for Spaces, 0E4V) has no `@[stacks]` attribute in AxiomMath. Per GL26 §2.4, `f^×` alone suffices for the proper morphisms of `setup:fm_cube_pullback`; check whether the headline results need `f^!` at all before investing. |
| C.4 | **`Lf^*` strong monoidal on `D_QCoh`**: discharge `PullbackTensorAssociativity f`, i.e. compatibility of 07A4 with the associators of `⊗^L` | `lem:spacey_Lipman_Hashimoto`, every use of "`Lf^*` is monoidal" (`sec:prelim_stacks_functors`) | M (K-flat model computation; 200–600 lines) | Without it, `quasicoherentDerivedPullbackMonoidal` cannot be used unconditionally. The underlying object-level isomorphism `smallEtaleDerivedPullbackTensorIso` is unconditional. |
| C.5 | **Closed symmetric monoidal `D_QCoh(𝒪_X)`**: braiding on `D(𝒪_X)` for spaces; `- ⊗ E ⊣ ℝ𝓗om(E, -)` on `DerivedModules` (transport 08J8 from the model through `modelDerivedEquivalence`, compatibly with `smallEtaleDerivedTensor`); coherator `Q` right adjoint to `D_QCoh ↪ D(𝒪_X)` (Brown: `exists_isTriangulated_rightAdjoint_of_compact_generator`, since the inclusion preserves `Type u` sums); bold `𝐑𝓗om = Q ∘ ℝ𝓗om` and `lem:internal_hom` | `sec:prelim_stacks_internal_homs`, `lem:rhom_tensor_morphism`, `lem:internal_hom`, `lem:gortz_wedhorn_internal_hom`, derived reflexivity (§6) | M–L (500–1500 lines). The transport of 08J8 is the delicate part: two different tensor constructions (canonical 06YU on the `u+1` site vs on the model) must be identified. | AxiomMath already proves `qcohDerived_smallEtaleDerivedSheafHom_of_isPerfect` (`Perfect/DerivedSheafHomQuasicoherent.lean:98`), which gives the perfect case. |
| C.6 | **Pseudofunctor packaging** (Lipman §3.6): `Lf^*` and `Rf_*` on `D_QCoh` as Mathlib `Pseudofunctor`s on `AlgebraicSpaces`, the unit coherence `L(𝟙)^* ≅ 𝟭`, and the adjoint-pair compatibility | `lem:spacey_Lipman_Hashimoto`, Part 2 (§5 mates) | M (300–700 lines) | All 1- and 2-cell data exist (0D6D and its cocycle, the `Rf_*` composition isomorphism adjoint to it). |
| C.7 | **GL26 `f`-perfect and `f`-quasi-perfect** (definitions), and the comparison with 0DKN (`rem:comparison_stacks_project`) | §4–§5 (definitions: all headline results); the comparison is optional | definitions: S (< 50 lines); comparison: M–L (needs `thm:relative_perf_iff_smooth_locally`, 0DKQ, and [GVLMP25, Prop. 3.1]) | Definitions must also pass non-vacuity (CLAUDE.md step 5): `0` is `f`-perfect, and `𝒪_Y` is `f`-perfect for flat `f`. |
| C.8 | **`f^×` base change over non-affine bases** (`lem:neeman188`, second half): globalize 0E5I from affine charts | §7 (`sec:base_change_for_adjoints`), `introthm:base_change` | M (300–800 lines) | Étale-local on `Y` and `Y'`: needs compatibility of 0E5D with étale restriction (0E5E/0E5F give pasting). |
| C.9 | **`lem:support_is_cohomological_for_finite_type_cohomology`** (support = points where `Lt^*E ≠ 0`), with representatives restricted to `B` (A.1) | §3 (`sec:perfectness`), §11 | M | Needs the Iyengar–Lipman–Neeman Lemma A.1 on étale charts; not in AxiomMath (not a Stacks result). |
| C.10 | **Compactness universe bridge** `IsCompactObject.{u} ↔ IsCompactAb` on `D_QCoh` (A.5) | every use of `IsCompactAb` with a geometric category; LP26 applications | S–M, or an orchestrator decision on `IsCompactAb`'s universe | See A.5. |
| C.11 | **Faithfully flat `Lf^*` is conservative on `D_QCoh`** (`lem:faithfully_flat_is_conservative`, `lem:zero_object_via_covers`) | §2.2 onwards | S–M | AxiomMath has the étale-chart version (`isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace`) and the flat-pullback homology isomorphism; fpqc descent of vanishing for spaces has to be assembled. |
| C.12 | **Functors known only objectwise** | — | — | I found none among the core functors: `Lf^*`, `Rf_*`, `⊗^L`, `ℝ𝓗om`, `f^×` and the base change, projection formula and 0D6D maps are natural transformations. Statements that are objectwise only (`IsIso (… .app K)` under hypotheses on `K`): 08IN, 08IR, 0E5I. That is the paper's form too. |

---

## D. Build cost

Script: `scripts/axiommath/closure.py` (already committed by the orchestrator; used unchanged):
`python3 -I scripts/axiommath/closure.py <AxiomMath checkout> <Module>...`. It counts AxiomMath
modules (`Stacks*`) in the import closure, not Mathlib. All figures are at `f56a316`. For
scale, the whole of `StacksFrontier` is 64 215 modules and 18.5 M lines.

### D.1 Per module (prefix `StacksFrontier.AlgebraicGeometry.`)

| module | what it gives | modules | lines |
|---|---|---:|---:|
| `Spaces.Category` | `AlgebraicSpaces`, 025Z, `yonedaSpace`, pullbacks | 28 | 7 114 |
| `Spaces.Limits` | products, 043C | 31 | 7 609 |
| `Spaces.Morphisms` | qc, separated, étale, immersions | 24 | 6 381 |
| `Spaces.Separated` | absolute (quasi-)separatedness | 29 | 7 842 |
| `Spaces.UniversallyClosed` | proper | 33 | 8 330 |
| `Spaces.Flat` | flat, surjective | 26 | 6 803 |
| `Spaces.FinitePresentation` / `Spaces.FiniteType` | finiteness | 26 / 26 | 6 872 / 6 914 |
| `Spaces.Points` / `Spaces.PointsTopology` | `\|X\|` | 24 / 25 | 6 435 / 6 574 |
| `Spaces.Morphisms.Affine` | affine morphisms | 24 | 6 132 |
| `Spaces.Morphisms.PseudoCoherent.Perfect` | perfect morphism | 48 | 14 951 |
| `Spaces.NoetherianSpaces` | Noetherian | 1 023 | 261 986 |
| `Spaces.TorIndependence` | 08IP | 905 | 238 603 |
| `Spaces.HasFiniteTorDimension` | finite Tor dimension | 7 704 | 2 294 885 |
| `Spaces.RingedSite` | `Mod`, `Qcoh` | 862 | 215 542 |
| `Spaces.QuasicoherentDerivedCategory` | `D_QCoh` (definition only) | 865 | 218 148 |
| `Spaces.QuasicoherentWeakSerre` | `D_QCoh` triangulated | 2 308 | 712 075 |
| `Spaces.DerivedSupport` | support of objects of `D` | 1 007 | 256 434 |
| `Spaces.SmallEtaleDerivedModulePullback` | `Lf^*` | 1 153 | 324 602 |
| `Spaces.SmallEtaleDerivedModuleAdjunction` | 07A6, 0D6D, 07A7 | 1 880 | 547 878 |
| `Spaces.DerivedPushforwardHigherDirectImages` | `R(gf)_*` | 1 641 | 491 369 |
| `Spaces.SmallEtaleDerivedPullbackCompAssoc` | 0D6D cocycle | 2 320 | 683 130 |
| `Spaces.SmallEtaleDerivedTensor` | `⊗^L`, 07A4 | 1 744 | 505 447 |
| `Spaces.Perfect.LimitPerfectObjects` | `PerfectDerivedCategory` | 1 211 | 322 945 |
| `Spaces.Perfect.Relative` / `…RelativeSubcategory` | 0DKN | 1 100 / 1 357 | 286 307 / 381 871 |
| `Spaces.DerivedDuality.Basic` | `ℝ𝓗om`, `D_Coh`, models | 2 883 | 917 631 |
| `Spaces.Coherator` | coherator | 4 612 | 1 427 926 |
| `Spaces.QuasicoherentDerivedPullback` | 08F4 | 5 021 | 1 607 374 |
| `Spaces.QuasicoherentDerivedModulePullback` | 08F4 (spelling used by the adjunction) | 5 165 | 1 645 667 |
| `Spaces.Perfect.DerivedPullbackPerfect` / `Spaces.PseudoCoherent.DerivedPullback` | 08H4, 08H6 | 3 226 / 3 231 | 1.03 M / 1.03 M |
| `Spaces.QuasicoherentDerivedPushforward` | `QcohDerived`, 08FA input | 7 361 | 2 194 811 |
| `Spaces.QuasicoherentDerivedDirectImage` | `Rf_*` on `D_QCoh` | 7 475 | 2 228 635 |
| `Spaces.QuasicoherentDerivedAdjunction` | `Lf^* ⊣ Rf_*` on `D_QCoh` | 8 437 | 2 548 281 |
| `Spaces.CompactGeneration.QcqsCompactGeneration` | 0E55, compact generator | 8 516 | 2 571 896 |
| `Spaces.DualityRightAdjointBaseChange` | `f^×`, 0E5B | 8 518 | 2 572 478 |
| `Spaces.QuasicoherentDerivedTensorClosed` | 08F5 | 8 523 | 2 575 156 |
| `Spaces.PseudoCoherent.PseudoCoherentIffCoherentHomology` | 08IK | 8 564 | 2 587 091 |
| `Spaces.DerivedDuality.SpaceDuality` | 0E51 | 8 662 | 2 653 556 |
| `Spaces.SmallEtaleProjectionFormulaSnd` | 08IN | 8 672 | 2 618 485 |
| `Spaces.Perfect.PerfectCompactQcqs` | 09M8, 09IY | 8 698 | 2 625 354 |
| `Spaces.QuasicoherentDerivedMonoidal` / `…PullbackMonoidal` | monoidal `D_QCoh`, conditional monoidal `Lf^*` | 8 740 / 8 742 | 2.64 M / 2.64 M |
| `Spaces.SmallEtaleDerivedTorIndependentBaseChange` | 08IR | 8 893 | 2 686 114 |
| `Spaces.DualityBaseChangeMap` | 0E5D–0E5L | 8 919 | 2 693 454 |
| `Spaces.Perfect.DerivedPushforwardCoherentProperSupport` | 08GK | 9 677 | 2 911 792 |
| `Spaces.Perfect.PerfectProperPushforward` | 0E4U | 9 989 | 3 003 263 |
| `Spaces.Perfect.SupportedPerfectGenerator` / `…SupportedQuasicoherentDerived` | 0AEC, `D_{QCoh,T}` | 11 119 / 11 121 | 3.40 M / 3.40 M |
| `Spaces.Perfect.SupportedCompactPerfect` | 0AED | 11 763 | 3 578 379 |
| `Spaces.Perfect.CohomologyBaseChangeProper` | 0CTM | 13 776 | 4 206 783 |
| `Spaces.DualityRightAdjointBaseChangeAffineIso` | 0E5I (1) | 13 871 | 4 229 927 |
| `Spaces.NagataCompactification.Nagata` | 0F4D | 14 035 | 4 220 948 |

### D.2 Unions, and the recommended import sets

The closures overlap heavily: once `QuasicoherentDerivedAdjunction` (8.4 k) is in, most of the
rest adds little. The jumps come from the `D_{QCoh,T}` files (about +2.5 k), from 0CTM, 0E5I
and Nagata (about +4.5 k together), and from `HasFiniteTorDimension` (7.7 k on its own; it
pulls the duality and tensor stack).

| set | modules | lines | content |
|---|---:|---:|---|
| **T0**: base and morphism properties | 67 | 18 736 | `Spaces.{Category, Limits, Morphisms, Separated, UniversallyClosed, Flat, FinitePresentation, FiniteType, Points, PointsTopology, Morphisms.Affine, Morphisms.PseudoCoherent.Perfect}` |
| **T1**: statement layer (recommended first slice) | **8 886** | **2 678 435** | T0, `NoetherianSpaces`, `QuasicoherentDerivedAdjunction`, `QuasicoherentWeakSerre`, `SmallEtaleDerivedTensor`, `QuasicoherentDerivedMonoidal`, `DerivedPushforwardHigherDirectImages`, `SmallEtaleDerivedPullbackCompAssoc`, `Perfect.LimitPerfectObjects`, `DerivedSupport`, `HasFiniteTorDimension`, `DerivedDuality.Basic`, `Perfect.RelativeSubcategory` |
| T1 + generation, `f^×`, 08IN, 08IR | 9 200 | 2 772 155 | T1, `Perfect.PerfectCompactQcqs`, `CompactGeneration.QcqsCompactGeneration`, `DualityRightAdjointBaseChange`, `SmallEtaleProjectionFormulaSnd`, `SmallEtaleDerivedTorIndependentBaseChange` |
| T1 with `Perfect.SupportedQuasicoherentDerived` instead of `DerivedSupport` | 11 852 | 3 600 653 | the packaged `D_{QCoh,T}` |
| T2 = T1 + `D_{QCoh,T}`, generation, `f^×`, base change, monoidal `Lf^*`, 08H4/08H6, 08IK, coherator | 12 043 | 3 657 108 | |
| **T3 = everything named in A** | **16 622** | **5 005 743** | T2 + `Perfect.PerfectProperPushforward`, `Perfect.CohomologyBaseChangeProper`, `Perfect.DerivedPushforwardCoherentProperSupport`, `DualityRightAdjointBaseChangeAffineIso`, `DerivedDuality.SpaceDuality`, `NagataCompactification.Nagata` |

**Recommendation.** Build and distribute in two steps.

1. **T1** (8.9 k modules). It is enough to *state* GL26's headline results over spaces:
   * all notions of A.1–A.3;
   * `Lf^*`, `Rf_*`, the adjunction on `D_QCoh`, `⊗^L`, the composition isomorphisms, and
     `ℝ𝓗om` on `D`;
   * the support predicate;
   * the definitions GL26 needs that AxiomMath lacks (`f`-perfect, `f`-quasi-perfect,
     `Φ_K`), which are built on these.

   Replace `DerivedSupport` by `Perfect.SupportedQuasicoherentDerived` only when a statement
   needs `D_{qc,Z}` as a category (+3 k modules).
   `HasFiniteTorDimension` alone accounts for most of T1. If GL26's own definition of finite
   Tor dimension (`rmk:relative_perfects4`, via `⊗^L` and `Qcoh`) is used in the statements
   instead, T1 without it should be close to the 8.4 k of `QuasicoherentDerivedAdjunction`.
   I did not measure that set separately.
2. **T3** (16.6 k modules, 5.0 M lines), for the proofs: Nagata, 0CTM, 0E4U, 0E5I, 08GK,
   duality. A smaller T2 (12.0 k) covers the proofs that need only generation, `f^×`, base
   change and 08IK.

Nothing in A requires importing `StacksFrontier.lean` as a whole (64 k modules).
