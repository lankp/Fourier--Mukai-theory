# Formalizing *Gluing weak approximability along recollements*

P. Lank, B. Pauwels — 22 pages, November 2026.  It treats quasi-compact
quasi-separated **algebraic spaces**, and Corollary 1.2 is proved from the
induction principle for algebraic spaces (Stacks Tag 09IT).  This note is the
blueprint for the Lean development of the paper, in `WeakApprox/`.

## 0. What the paper does

* **Theorem 1.1.** For a recollement of singly compactly generated triangulated
  categories with `D_Z`, `D_U` weakly approximable, `D` is weakly approximable iff
  `Hom(G', G'[n]) = 0` for `n ≫ 0`.
* **Corollary 1.2.** For a quasi-compact quasi-separated algebraic space with
  quasi-finite separated diagonal, `D_qc,S(X)` is weakly approximable, and
  coherent when `X` is Noetherian.
* The engine is §3 (properties of `⟨H⟩^[a,b]`, the aisle lemma, the iterative
  approximation) and §4 (lifts to aisles, the key Lemma 4.6 and Proposition 4.8).

## 0b. Status of the formalization

Everything below compiles against Mathlib on Lean 4.33.1, `sorry`-free.  The
axiom audit for the §4 results is printed at the end of
`WeakApprox/TwoStage.lean` and `WeakApprox/Main.lean` (it is kept in the defining
modules because `#print axioms` over an imported proof term of this size
overflows Lean's stack); every audited declaration depends only on `propext`,
`Classical.choice` and `Quot.sound`.

* **Theorem 1.1** is proved, in both directions, at the level of Setup 4.4
  (`WeakApprox/Main.lean`, statement `SetupMain.theorem_1_1`).  Its forward
  direction needs neither weak approximability of `D` nor Stacks 09SR: in
  Setup 4.4 the normalized generator satisfies `G ∈ D^{≤0}` and
  `Hom(G, D^{≤-A}) = 0`, which gives `Hom(G, G⟦n⟧) = 0` for `n ≥ A`, and `G'`
  lies in the thick envelope of `G` because `G'⟦m⟧` is a summand of
  `G = G'⟦m⟧ ⊞ j_!G_U`.  Its reverse direction is the two-stage approximation
  of §4 (`WeakApprox/TwoStage.lean`): Proposition 4.8 lifts an approximation of
  `i^*F`, Lemma 4.6 approximates the `j^*`-component of the cone, Remark 3.2(2)
  glues the two, and Lemma 4.2 detects the aisle bound `D^{≤-1}`.
* **Compactness is rendered over `AddCommGrpCat`** (`IsCompactAb`), which is the
  paper's notion: `Hom(H,-)` into abelian groups preserves small coproducts.
  The previously used `IsCoproductCompact` asks this of the `Type`-valued
  `coyoneda`; it is strictly stronger, because a `Type`-valued coproduct is a
  disjoint union (every map into it factors through a single summand).  In
  particular `IsCoproductCompact` is *not* closed under binary biproducts while
  `IsCompactAb` is, which is exactly why Lemma 4.3(2) used to carry a
  compactness hypothesis on `G'⟦m⟧ ⊞ j_!G_U` and no longer does.
* **Setup 4.4 is reduced to its irreducible data.**  `Setup44Reduced`
  (`WeakApprox/Setup44Reduced.lean`) drops `G_compact`, `G_generates` and
  `tD_glued`, which are conclusions of Lemma 4.3, and `Setup44Minimal`
  (`WeakApprox/Setup44Minimal.lean`) also drops the common bound and condition
  (3): the bound is chosen after the fact (`WeakApproximationData.monoBound`)
  and `Hom(G, D^{≤-A}) = 0` is derived from Lemma 4.3(4) plus Lemma 3.5
  (`WeakApprox/Setup44Vanishing.lean`).  Proposition 4.8 is stated with its
  Lemma 4.6 premise discharged in `WeakApprox/Proposition48Paper.lean`, and
  Lemma 4.3(3) is upgraded to a `t`-structure identity in
  `WeakApprox/Lemma433TStructure.lean` (`TStructure.ext_le_zero`).
* **The single external input is Stacks Tag 09SR** (Ravenel–Neeman:
  `Loc(S)^c = thick(S)` for a set `S` of compact objects, hence for a compact
  generator every compact lies in the thick envelope).  It is *not* used in
  Theorem 1.1; it is needed only to derive Setup 4.4 from the paper's
  hypotheses, i.e. in Lemma 4.3(1)/(4).  `WeakApprox/NineSR.lean` formalizes
  the parts that are provable here — zero detection from separation, the
  finite-stage-retract rendering of the 09SR conclusion, its equivalence with
  `IsClassicalGeneratorOnCompacts`, and stability under isomorphisms and shifts
  — and leaves the Ravenel–Neeman theorem itself external.  Its proof needs
  Bousfield localization at a set of compact objects and that this localization
  is smashing; neither Mathlib nor this repository has that.

## 1. Module plan

| module | contents | state |
|---|---|---|
| `WeakApprox/Basic.lean` | `H[a,b]`, `Coprod` with universal property `Coprod.le`, `envelope H a b = ⟨H⟩^[a,b]`, `IsCompactAb` (the paper's compactness, with values in `AddCommGrpCat`), `IsCoproductCompact` (the strictly stronger `Type`-valued variant, kept for the 09SR statement), `IsGenerator`, `WeakApproximationData` (Definition 2.1) | done |
| `WeakApprox/CompactAb.lean` | `IsCompactAb`: the `DFinsupp` model of the coproduct in `AddCommGrpCat` and its colimit criterion; iso invariance; `IsCoproductCompact → IsCompactAb`; **closure under binary biproducts**; shift invariance; Neeman's adjoint criterion; preservation of coproducts by binary products of `Ab`-valued functors | done |
| `WeakApprox/Closure.lean` | Lemma 3.1(1): `⟨H⟩^[a,b]` closed under small coproducts, extensions and retracts, strictly full, containing `H[a,b]`, and minimal with these properties; plus the two reusable Mathlib-level facts about `retractClosure` | done |
| `WeakApprox/Shift.lean` | Lemma 3.1(2): `shiftImage`, `H[a,b]⟦s⟧ = H[a-s,b-s]`, `⟨H⟩^[a,b]⟦s⟧ = ⟨H⟩^[a-s,b-s]`, monotonicity in the interval | done |
| `WeakApprox/Functoriality.lean` | Lemma 3.1(3): `F(⟨H⟩^[a,b]) ⊆ ⟨H'⟩^[a+c,b+d]` for an exact coproduct-preserving `F` with `F(H) ∈ ⟨H'⟩^[c,d]` (source and target share the hom universe) | done |
| `WeakApprox/HomVanishing.lean` | Lemma 3.1(4): `Hom(X,Y) = 0` on `⟨H⟩^[a,b]`, and closure of `{Y : Hom(H,Y) = 0}` under coproducts, extensions and retracts; with `IsCompactAb` the coproduct step needs no joint-surjectivity argument | done |
| `WeakApprox/Proposition48.lean` | Lemma 3.1(5) (`⟨H⟩^[a,b] ≤ Coprod(H[a,b+1])`, via the `ULift ℕ` Eilenberg swindle) and Proposition 4.8: the liftable class is strictly full, closed under coproducts and extensions, contains the shifts `(i^*G)⟦-A-1..A⟧`, and `⟨i^*G⟩^[-A,A] ≤ Coprod((i^*G)[-A,A+1]) ≤ C` | done |
| `WeakApprox/Aisle.lean` | Lemma 3.3 (aisles closed under extensions) | done |
| `WeakApprox/Lemma34.lean` | Lemma 3.4: iterated weak approximation, by induction on `m` with the octahedron axiom (adds `[IsTriangulated C]`, the octahedron) | done |
| `WeakApprox/Lemma35.lean` | Lemma 3.5: `Hom(H, H⟦n⟧) = 0` for `n ≥ n₀` implies `Hom(H, Y) = 0` on the aisle `T^{≤-n₀}`, for `H` compact and `T^{≤0}` compactly generated by `H`, now with `[IsCompactAb H]` | done |
| `WeakApprox/Octahedron.lean` | Remark 3.2(2): from cocone triangles for `f`, `g`, `f ≫ g`, the octahedron axiom gives a distinguished triangle `F_f → F_gf → F_g → F_f⟦1⟧` | done |
| `WeakApprox/Recollement.lean` | Recollements: six exact functors, the four adjunctions, full faithfulness, the kernel condition, the zero composites, and the two gluing triangles of Setup 4.1, functorial in `E` | done |
| `WeakApprox/Lemma42.lean` | Lemma 4.2: the glued aisle in every degree and the four containments, given the glued `t`-structure and its degree-zero identity | done |
| `WeakApprox/Lemma43.lean` | Lemma 4.3(1) and (4): `j^*G' ∈ D_U^{≤m}` for some `m ≥ 0`, and eventual self-Hom vanishing for `G = G'⟦m⟧ ⊞ j_!G_U`. `IsClassicalGeneratorOnCompacts` (Stacks 09SR for the paper's compacts) is an explicit hypothesis | done modulo 09SR |
| `WeakApprox/Lemma4323.lean` | Lemma 4.3(2) in the paper's form: `G` and `i^*G` are compact generators, with **no compactness hypothesis on the biproduct** (it follows from `isCompactAb_biprod`); and Lemma 4.3(3): the aisle compactly generated by `G` is the glued aisle | done |
| `WeakApprox/Lemma46.lean` | Lemma 4.6: existence of a `P`-lift for `(i^*G)⟦n⟧ → i^*Y` with `Y ∈ D^{≤A+1}` and `-A-1 ≤ n ≤ A` | done |
| `WeakApprox/PLift.lean` | Definition 4.5: the `P`-lift structure and its transport API (along the morphism, the target, the domain, and the source) | done |
| `WeakApprox/Setup44.lean` | Setup 4.4: the recollement, the three `t`-structures, the weak approximation data on both ends, the normalized generator `G = G'⟦m⟧ ⊞ j_!G_U`, the aisle descriptions, `A`, `K`, `B`, and `P = ⟨G⟩^[-B,B] ∩ D^{≤K}` with its closure properties | done |
| `WeakApprox/EventualVanishing.lean` | weak approximation data force `Hom(G, G⟦n⟧) = 0` for `n ≥ 2A`; transport along the finite thick envelope; retract and shift invariance | done |
| `WeakApprox/TwoStage.lean` | the closing argument of §4: `Setup44` produces weak approximation data with generator `G'⟦m⟧ ⊞ j_!G_U`, the glued `t`-structure and the bound `3A` | done |
| `WeakApprox/Main.lean` | **Theorem 1.1**, both directions, over Setup 4.4 minus the conclusion of the forward direction; the forward direction needs neither `SatisfiesWA D` nor 09SR | done |
| `WeakApprox/NineSR.lean` | Stacks 09SR: zero detection from separation, the finite-stage retract rendering of its conclusion, its equivalence with `IsClassicalGeneratorOnCompacts`, and stability under isomorphisms and shifts. The Ravenel–Neeman theorem itself stays external | partial (documented) |
| `WeakApprox/WeakApproximable.lean` | Definition 5.3 and Remark 5.4 in categorical form: `SatisfiesWA`, `SatisfiesStandardWA`, and `standard ⟹ weak` | done (categorical layer) |
| Corollary 1.2 (`D_qc,S` on algebraic spaces) | needs the Stacks library for algebraic spaces and Hall–Rydh's induction principle | out of reach here |

The style follows the Stacks formalization the user is building: one module per
section of the paper, every declaration carries a docstring citing the numbered
item of the paper it formalizes, and the paper's hypotheses are hypotheses of the
Lean theorem (no interface structure unless the paper's own data is genuinely
unavailable, as for `D_qc,Z` of stacks).

## 2. What Mathlib already has (verified in this VM, Lean 4.33.1)

* Triangulated categories: `Pretriangulated`, `Triangle`, `distTriang`,
  `isIso₃_of_isIso₁₂`, rotations, shifts; `ObjectProperty.IsTriangulated`.
* Closure operators on object properties: `retractClosure` (with
  `IsStableUnderRetracts`), `colimitClosure`, `IsClosedUnderColimitsOfShape`,
  `extensionProduct` and friends in `ObjectProperty.Extensions`, `Orthogonal`,
  `Shift`, `triangEnvelope`/`triangEnvelopeIter`, `IsClassicalTriangulatedGenerator`.
* `TStructure` in `CategoryTheory.Triangulated.TStructure.Basic`, with `le`, `ge`,
  shift compatibility, orthogonality and truncation triangles.
* Homological functors, long exact sequences, coproducts in preadditive/triangulated
  categories.

So §2.1.2 and §3 are within reach, and §2.1.3 is partly there.

## 3. What is missing

1. **Recollements.** There is no `Recollement` anywhere in Mathlib (grep: zero hits).
   §2.1.4 and the whole of §4 need: two adjoint triples, full faithfulness of
   `i_*`, `j_!`, `j_*`, the kernel condition, the two gluing triangles, the glued
   t-structure, and the t-exactness statements. This is the largest single gap;
   it is a self-contained 2-categorical/triangulated project (analogous in size to
   the mate calculus).
2. **Compact objects.** Mathlib has no `IsCompact` class for triangulated
   categories, so the paper's `T^c` needs a definition.  `WeakApprox/CompactAb.lean`
   supplies it as `IsCompactAb` (coproduct preservation of the `Ab`-valued
   `Hom(G, -)`) together with the standard facts: iso invariance, the
   comparison with the `Type`-valued notion, closure under binary biproducts,
   shift invariance, and Neeman's adjoint criterion (`F` preserves compacts when
   its right adjoint preserves coproducts).  What is still missing is only the
   *global* statement that compacts are thick, i.e. Stacks 09SR.
3. **The `Coprod` closure.**  Done: `WeakApprox/Basic.lean` has `Coprod` as an
   inductive closure under small coproducts (colimits over `Discrete J`) and
   extensions, with the universal property `Coprod.le` that Lemma 3.1(1)'s
   minimality needs.
4. **The octahedron bookkeeping** of Remark 3.2 and §4: given composable
   morphisms, the two cocone triangles and their compatibility.  Mathlib has the
   octahedron axiom but little of the customary packaging; this has to be built.
5. **Homological algebra of algebraic stacks**: lisse-étale site, `D_qc`, `Perf`,
   support, `D_qc,Z`, the Thomason condition, the induction principle of Hall–Rydh
   [HR18, Theorem E], the étale-neighbourhood recollement of [Lan26, Prop. 3.1].
   The Stacks library (`StacksFrontier/AlgebraicGeometry/...`) has much of the
   *scheme/space* version (`Stacks.DerivedQCoh.IsDQCoh`, `IsPerfect`, support,
   coherator), but the stack-level statements of this paper are a further layer
   and are not formalized.

## 4. Order of work

1. §2–§3 (`Basic.lean`, `Closure.lean`, `Shift.lean`, `Functoriality.lean`,
   `HomVanishing.lean`, `Aisle.lean`, `Lemma34.lean`, `Lemma35.lean`,
   `Octahedron.lean`): done.
2. §4 (`Recollement.lean`, `Lemma42.lean`, `PLift.lean`, `Lemma46.lean`,
   `Proposition48.lean`, `Lemma43.lean`, `Lemma4323.lean`, `Setup44.lean`,
   `TwoStage.lean`): done modulo Stacks 09SR, which is the explicit
   `IsClassicalGeneratorOnCompacts` hypothesis of Lemma 4.3(1)/(4).
3. The compactness rendering: the paper's notion is `IsCompactAb`
   (`CompactAb.lean`), not the `Type`-valued `IsCoproductCompact`.  This is what
   makes Lemma 4.3(2) hold without an extra compactness hypothesis; using the
   `Type`-valued notion there was a genuine error of rendering, not a missing
   input.
4. Theorem 1.1 (`Main.lean`): done over Setup 4.4, in both directions, with no
   unproved input.  The forward direction is stronger than the paper's: it does
   not need weak approximability of `D`.
5. Remaining: derive Setup 4.4 (Lemma 4.3) from the paper's own hypotheses,
   which is where Stacks 09SR is used; and the geometric layer.
6. Corollary 1.2 — only after the Stacks library (or an equivalent) is available
   for algebraic spaces, and after Hall–Rydh's induction principle.

## 5. Notes on the paper for the formalizer

* §2.1.5 uses `⟨G⟩^{[-A,A]}` for `smd(Coprod(G[-A,A]))`; in the formalization this
  must be the *same* operator as in Lemma 3.1, including the `retractClosure`.
* Lemma 3.1(1)'s minimality is used constantly (every later "by Lemma 3.1(1)" is
  really minimality plus the closure properties), so it should be exposed as an
  induction principle (`⟨H⟩^[a,b] ≤ Q` from the three closure properties), not
  just as three separate lemmas.
* Lemma 3.1(5) is only used to pass from `smd(Coprod)` to `Coprod` with one extra
  index; a weakening to `b' > b` would be harmless and should be recorded if used.
* Definition 2.1 has `A > 0`; in the formalization `A : ℤ` with `0 < A` is the
  practical choice, and the definition should be a structure so that later lemmas
  can destructure it (`G`, `t`, `A`, the two properties).
