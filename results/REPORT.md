# Lean code for *Relative Fourier–Mukai theory for algebraic spaces*

Elías Guisado Villalgordo, Pat Lank — 102 pages, 12 sections, 3 appendices.

This report accompanies the Lean development in `FourierMukai/`. It says what is
proved, what is only stated, what is missing, and where the paper itself needs
attention before (or while) being formalized.

---

## 0. Bottom line

*Status.*  §2.1 and Appendix B are formalized: `Trinatural` (Definition B.9),
identity and vertical composition of trinatural transformations, Lemma 2.3(1)
(both halves), Lemma 2.3(2) (triangulated, thick and localizing parts),
Lemma 2.3(3) (essential density), Lemma 2.5 (compact objects), and the "check on
a classical generator" corollary.  The mate bijection of §7 (Lemma 7.1(2)) is formalized on
top of Mathlib's `CategoryTheory.mateEquiv`; what remains there is the paper's
Lemma 7.1(1) (naturality of the correspondence) and Lemma 7.8 (iso criteria).

* The paper's **algebraic core** — the 2-categorical and triangulated-category
  machinery of §2.1 and Appendix B, on which the whole paper's methodology
  rests — is formalized and **proved in Lean 4 against Mathlib**
  (`FourierMukai/Prelim/`). All declarations there depend only on
  `propext`, `Classical.choice` and `Quot.sound`; see §6.
* The paper's **geometric content** — derived categories of quasi-coherent
  sheaves on Noetherian algebraic spaces, relative perfectness, Grothendieck
  duality, mates for integral transforms, openness of Fourier–Mukai loci — is
  **not in Mathlib**: Mathlib has no algebraic spaces, no quasi-coherent sheaves
  on a scheme, no derived category of sheaves.  Most of it *is* in the AxiomMath
  Stacks library (`Stacks.DerivedQCoh.IsDQCoh`, `Stacks.Cohomology.PerfectComplexes.IsPerfect`,
  `Stacks.Duality.upperShriek`, `Space.IsAlgebraicSpace`; see §5.2 and
  `results/INTEGRATION.md`), which is why the porting target is that library.
  Until the port, the development fixes a precise *interface* for the geometric layer
  (`FourierMukai/Paper/DerivedSetup.lean`), defines the paper's notions on top of
  it (`Φ_K`, `f`-perfect, `f`-quasi-perfect, `FM(K)`, `fm(K)`), and **states**
  the main theorems (`FourierMukai/Paper/Statements.lean`), marking each with
  `sorry` and citing the exact part of the paper and the Stacks tags its proof
  uses.
* §5 is the inventory of missing content: what Mathlib lacks, what the
  AxiomMath Stacks formalization does and does not give you, and the
  mathematical points in the paper that require attention.  Four of the points
  raised in the first version of this report have been **resolved by the
  authors** (conventions for pseudocoherence, `D^-_coh`, the filtration `⟨S⟩_n`,
  and proper Gorenstein morphisms); they are recorded with their resolutions in
  §5.3, and the conventions are now part of the Lean interface.

---

## 1. Files

| File | Contents |
|---|---|
| `FourierMukai/Prelim/Triangulated.lean` | `Trinatural` (paper Def. B.9), the iso-locus, and **Lemma 2.3(2)**: the iso-locus of a trinatural transformation is a triangulated subcategory. |
| `FourierMukai/Prelim/Thickness.lean` | Retract closure of the iso-locus (the thickness half of Lemma 2.3(2)), and the corollary that a trinatural transformation which is an isomorphism on a classical generator is an isomorphism everywhere. |
| `FourierMukai/Prelim/Coproduct.lean` | The coproduct half of Lemma 2.3(1) (arbitrary index type, only the one coproduct assumed), `isIso_sigmaMap`, and the localizing corollary `Trinatural.isIso_app_coprod`. |
| `FourierMukai/Prelim/EssentiallyDense.lean` | Lemma 2.3(3): essential density and reflection of isomorphisms, in the paper's `⟨L(C)⟩₁` form and in a stronger finite-stage form. |
| `FourierMukai/Prelim/Lemma25.lean` | Lemma 2.5: an exact functor between singly compactly generated categories with coproduct-preserving right adjoint is an equivalence iff its restriction to compact objects is; plus `Trinatural.ofNatTrans`, `NatTrans.isIso_app_of_isColimit`, Neeman's compactness of a left adjoint, and the localizing-generator criterion. |
| `FourierMukai/Prelim/Mates.lean` | The mate bijection of §7 (Lemma 7.1(2)): the paper's explicit unit/counit formula, its definitional agreement with Mathlib's `CategoryTheory.mateEquiv`, componentwise formulas, the packaged bijection, and Lemma 7.8(2) (mates of isomorphisms for adjoint equivalences). |
| `FourierMukai/Prelim/Generation.lean` | §2.1 vocabulary mapped onto Mathlib: `⟨S⟩` = `ObjectProperty.triangEnvelope`, `FinitelyBuiltBy`, `IsClassicalGenerator`. |
| `FourierMukai/Paper/DerivedSetup.lean` | The interface: `Subcats` (`D^b_qc`, `D^b_coh`, `Perf`), `MorphismContext`, `IsRelativelyPerfect` (Def. 4.1), `IsQuasiPerfect` (Def. 5.1), `FMContext` and `transform` (`Φ_K`), `FMSetup`, `FM`/`fm` (Def. 12.1), `BaseChange`. |
| `FourierMukai/Paper/Statements.lean` | The numbered theorems, stated (10 `sorry`s). |
| `FourierMukai/Examples/Identity.lean` | A non-vacuous instantiation: the identity trinatural transformation of `𝟭 (DerivedCategory A)`, where `A` is any abelian category.  Shows the definitions are consistent and that Lemma 2.3(2) applies to a genuine triangulated category. |
| `FourierMukai/Audit.lean` | `#print axioms` for every declaration of interest. |
| `scripts/build.sh` | Build order and commands. |

Build (takes a few seconds per file once Mathlib's oleans are in the page cache):

```bash
cd <repo>
export LEAN_PATH="$LEAN_PATH:."
./scripts/build.sh          # compiles every module in dependency order
lean FourierMukai/Audit.lean  # prints the axiom audit
```

There is no Lake package, deliberately: `/opt/mathlib` is read-only in this VM and
`lake` wants to write into it.  `scripts/build.sh` calls `lean` directly and
writes `.olean` files next to the sources.  If you have a writable Mathlib
checkout, a two-line `lakefile` with `require mathlib from "..."` will do the same
job and is preferable for a long-term project.

---

## 2. What is proved

Everything in this section is `sorry`-free (`#print axioms` in §6).

### 2.1 `Trinatural` — Definition B.9

```lean
structure Trinatural (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] extends F ⟶ G where
  comm_shift (X : C) (n : ℤ) :
    (F.commShiftIso n).hom.app X ≫ (toNatTrans.app X)⟦n⟧' =
      toNatTrans.app (X⟦n⟧) ≫ (G.commShiftIso n).hom.app X
  triangle_lift (T : Triangle C) (hT : T ∈ distTriang C) :
    ∃ θ : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T,
      θ.hom₁ = toNatTrans.app T.obj₁ ∧ θ.hom₂ = toNatTrans.app T.obj₂ ∧
        θ.hom₃ = toNatTrans.app T.obj₃
```

`comm_shift` is equation (B.1) of the paper; `triangle_lift` is the commutativity
of (B.3) — the components on a distinguished triangle come from a morphism of
triangles.  By Lemma B.10 of the paper, `comm_shift` is implied by `triangle_lift`
(applied to `A → 0 → TA → TA`); we keep it as a field so that the shift-stability
proof does not need that triangle to be constructed.  See §4 for the design notes.

### 2.2 Lemma 2.3(2): the iso-locus is triangulated

For a trinatural transformation `η : F ⟶ G` between triangulated functors,

```lean
def isoLocus (η : Trinatural F G) : ObjectProperty C := fun X => IsIso (η.toNatTrans.app X)

lemma isIso_app_shift        -- stable under shifts (uses comm_shift)
lemma isIso_app_zero         -- contains a zero object
lemma isIso_app_of_distinguished
    (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsIso (η.app T.obj₁)) (h₂ : IsIso (η.app T.obj₂)) : IsIso (η.app T.obj₃)
instance isoLocus_isClosedUnderIsomorphisms
instance isoLocus_isTriangulated : η.isoLocus.IsTriangulated
```

The closure under cones is `Pretriangulated.isIso₃_of_isIso₁₂` applied to the
morphism of triangles supplied by `triangle_lift`; this is exactly the paper's
argument ("closedness under cones follows from the trinaturality condition (B.3)").

**Thickness.**  `FourierMukai/Prelim/Thickness.lean` completes Lemma 2.3(2):
`Trinatural.isoLocus_isStableUnderRetracts` (retract closure) and
`isIso_app_of_isIso_app_biprod_left`.  The proof is short: naturality makes the
component at a retract a retract of the arrow `η.app Y`, and isomorphisms are
stable under retracts of arrows (`MorphismProperty.of_retract`); no additive or
triangulated structure is needed for this half.  Combined with
`ObjectProperty.triangEnvelope_le_iff` this yields
`Trinatural.isIso_of_isClassicalGenerator`: an isomorphism only has to be checked
on a classical generator.  Mathlib's `ObjectProperty.IsTriangulated` does not
require retract closure, so the two halves are stated separately.

**Lemma 2.3(1).**  `FourierMukai/Prelim/Coproduct.lean` proves the coproduct half
for an arbitrary index type, assuming only that the one coproduct involved exists
and is preserved by `F` and `G` (the paper assumes all `I`-indexed coproducts).
Together with the triangulated and thick parts this gives the localizing statement
of Lemma 2.3(2) in the form `Trinatural.isIso_app_coprod`.  The *cofactor* half
(if `η` is an isomorphism at `∐ A` then it is at each `A i`) is being formalized in
the same Ultramath run.

**Not formalized:** the cofactor half of Lemma 2.3(1),
Lemma 2.3(3) (prewhiskering by an essentially dense functor), Lemmas 2.4 and 2.5
(they need the localizing closure of a set of objects, Verdier localization with a
right adjoint, and Brown representability — none of which is in Mathlib).

### 2.3 §2.1 vocabulary

```lean
noncomputable abbrev thickClosure := ObjectProperty.triangEnvelope
def FinitelyBuiltBy (P : ObjectProperty C) (E : C) : Prop := P.triangEnvelope E
def IsClassicalGenerator (P : ObjectProperty C) : Prop := P.IsClassicalTriangulatedGenerator
theorem isClassicalGenerator_iff : IsClassicalGenerator P ↔ P.triangEnvelope = ⊤
theorem FinitelyBuiltBy.mono
```

Mathlib's `triangEnvelopeIter` is the paper's `⟨S⟩_n`
(`⟨S⟩_0 = 0`, `⟨S⟩_1 = add(S)`, extensions) and `triangEnvelope = ⋃_n ⟨S⟩_n`; the
identification is exact up to the difference recorded in §5.3(d).

---

## 3. What is stated only

`FourierMukai/Paper/Statements.lean` states the numbered results over the
interface.  Each declaration's docstring gives the paper's number, the exact
statement in Lean, and the tags on which the paper's proof rests.

| Paper | Lean name | Hypotheses as stated |
|---|---|---|
| Thm 1.3 (= 6.2 + 6.8) | `theorem_1_3` | `f` proper, `E` bounded pseudocoherent: `f`-perfect ↔ (bounded cohomology after tensoring with any bounded pseudocoherent pullback) ∧ `f`-quasi-perfect |
| Thm 12.3 | `theorem_12_3` | `K` pseudocoherent and relatively perfect over both `Yᵢ`: `FM(K)` and `fm(K)` open |
| Thm 1.2(1) = 12.9 | `theorem_1_2_open` | arbitrary bounded pseudocoherent `K`: `FM(K)` open |
| Thm 1.2(2) = Cor 12.10 | `theorem_1_2_baseChange` | `t⁻¹(FM K) = FM(L(t')^*K)` |
| Cor 6.18 (easy half of Thm 1.5) | `corollary_6_18` | relative perfectness is preserved by arbitrary derived pullback |
| Lemma 12.2 | `lemma_12_2` | representative-independence of `fm`/`FM` under relative perfectness |
| Thm 1.6 = 10.13 | `theorem_1_6` | full faithfulness on `D^b_coh` ↔ full faithfulness of every closed-point fibre |
| Lemma 2.25 | `lemma_2_25` | `Φ_{RΔ_*O_Y} ≅ 𝟙` |
| Lemma 2.26 | `lemma_2_26` | `Φ_{K₂} ∘ Φ_{K₁} ≅ Φ_{K₂ ⋆ K₁}` |
| Thm 1.7 = 11.4 | `theorem_1_7` | elliptic fibration ⟹ `Φ_{I_Δ}` is an autoequivalence |

All of them carry `sorryAx` (see §6) — they are specifications, not proofs.
Two statements are weaker than the paper on purpose:

* `theorem_1_3` merges the three equivalent conditions into a single `↔`
  conjunction instead of an `TFAE`-style statement; a proper `TFAE` would be
  nicer but needs a list-of-propositions encoding, which I did not want to
  impose on the statement layer.
* `lemma_2_26` is stated for three spaces `Y₁, Y₂, Y₃` (two composable contexts),
  which is the only way the composition type-checks; the paper's `Y₁ = Y₃`
  special case is the one used in Remark 2.27.

---

## 4. The interface: design and deviations

The interface (`DerivedSetup.lean`) is *not* a set of axioms of mathematics.
It is a structure of data-and-hypotheses that a concrete instantiation must
provide.  Three fields deserve comment.

1. **`FMSetup.IsProperFlat`, `IsBoundedPseudoCoherent`, `RepIndependent`** are
   `Prop`-valued fields.  They stand for "these spaces and morphisms are a proper
   flat family of Noetherian algebraic spaces", "this kernel is bounded
   pseudocoherent", and the assertion of Lemma 12.2.  They cannot be *defined*
   before algebraic spaces and `D_qc` exist; putting them in the structure keeps
   every theorem's hypotheses visible instead of hiding them in a comment.
2. **`FMSetup.fibreTransform`** is data: a function assigning to each kernel and
   each point of `|S|` the fibre transform.  In real life this is
   `K ↦ Φ_{L(t')^*K}`; it cannot be *defined* without the fibre-product cube.
   Consequently the loci are defined correctly (`FM`, `fm` are real `Set`s), but
   nothing forces `fibreTransform` to come from geometry.  Statements involving
   it therefore also carry `IsProperFlat` etc. as hypotheses, exactly as the
   paper's theorems do.
3. **`FMContext.tensorRight : DP → DP ⥤ DP`** is the endofunctor
   `(-) ⊗^L K`, supplied as a function rather than derived from a monoidal
   structure.  This keeps the interface free of Mathlib's monoidal API, which
   would add noise without adding content: the paper only ever uses
   `(-) ⊗^L K` as an endofunctor, and its monoidality only through the
   projection formula, which is not formalized anyway.

The interface deliberately does *not* try to model Pseudofunctors, `f^×`, `f^!`,
or the base-change cube of Setup 2.20: doing so faithfully is the content of the
paper's §2.4 and would require a 2-categorical formalization of the six-functor
formalism that does not exist in Mathlib.  It is the first item of the roadmap in
§7.

---

## 5. Missing content that requires attention

### 5.1 Missing in Mathlib (verified in this VM, Mathlib at Lean 4.33.1)

Local checks (all run in `/opt/mathlib/Mathlib`):

| Search | Occurrences |
|---|---|
| `AlgebraicSpace` | **0** (no algebraic spaces at all) |
| `Qcoh`, `Dqc`, `PerfectComplex`, `GrothendieckDuality`, `FourierMukai` | **0** each |
| `QuasiCoherent` | 1, and it is a `QuasiCoherentData` for locally free module sheaves, unrelated |

What does exist and is used or usable:

* `CategoryTheory.Triangulated.*`: pretriangulated/triangulated categories,
  triangulated subcategories (`ObjectProperty.IsTriangulated`), exact functors,
  triangles, rotation, `TStructure`, generators (`triangEnvelope`,
  `IsClassicalTriangulatedGenerator`), and `CategoryTheory.Triangulated.LocalizingSubcategory`
  (Verdier localization, calculus of fractions).
* `Algebra.Homology.DerivedCategory.Basic`: the derived category of an **abelian
  category**, as a localization of the homotopy category, with a triangulated
  structure; plus `TStructure`, `Plus`, `Ext`, injective/projective
  derivability structures.
* `CategoryTheory.Sites.*`: Grothendieck topologies, sheaves, sheafification,
  hypercovers, and `Sites.SheafCohomology` (cohomology of abelian sheaves on a
  site as `Ext` groups).  `AlgebraicGeometry.Sites.{Etale,BigZariski,Fpqc,
  Proetale,AffineEtale}` give the étale/fpqc/pro-étale topologies on schemes.
* `CategoryTheory.Monoidal.*`, `CategoryTheory.Bicategory.*`,
  `CategoryTheory.Adjunction.*`: monoidal categories, bicategories, adjunctions,
  whiskering — everything needed for the mate calculus of §7.

What is missing, item by item, with the paper's dependence:

1. **Algebraic spaces.** Definitions (as étale sheaves on `(Sch/S)_{fppf}`),
   properties (quasi-compact, quasi-separated, separated, Noetherian, decent),
   fibre products, the small étale site, points `|X|` and representatives,
   residual gerbes.  Needed by *every* theorem; currently only the abstract
   interface exists.
2. **Quasi-coherent sheaves on a ringed site and on an algebraic space**; the
   category `Qcoh(X)`, its Grothendieck abelian property, `D(Qcoh X)`, and
   `D_qc(X)` as a full subcategory of `D(Mod(X))`.  Needed by §2.2 and
   everywhere after.
3. **Subcategories `D^b_qc`, `D^b_coh`, `Perf`, `D_qc,Z`** and their
   compact-generation properties (`D_qc(X)` singly compactly generated for
   Noetherian `X`, Stacks 09IY; `Perf = D_qc^c`, Stacks 09M8; support
   subcategories, Stacks 0AED/0AEC).
4. **The closed symmetric monoidal structure on `D_qc(X)`** and the two internal
   homs `RHom` (on `D(X)`) and `RHom` (on `D_qc(X)`), with the coherator `Q`
   (Lemma 2.11).  Needed by §2.2.5 and the whole duality section.
5. **Grothendieck duality**: `f^×`, `f^!`, their pseudofunctoriality, the base
   change morphisms, and Neeman's construction (Lemma 2.21–2.24, §2.4).
   This is the single largest missing piece; Neeman's paper is ~60 pages of
   category theory built on Brown representability.
6. **Nagata compactification for algebraic spaces** (Conrad–Lieblich–Olsson,
   Raoult), needed to define `f^!`.
7. **Weak approximability of `D_qc(X)`** for Noetherian algebraic spaces
   (Lank, *Gluing weak approximability along recollements*, Cor. 1.2) and the
   Canonaco–Haesemeyer–Neeman–Stellari theorem used in Remark 2.6.  Currently a
   preprint; a formalization would also need the theory of approximable
   triangulated categories, which is not in Mathlib.
8. **Concentrated/proper/flat morphisms and the cohomological dimension bound**
   (Stacks 08FA(2), which the paper cites as Tag 08FA in Lemma 4.3 — the citation
   is correct: I checked the tag, it gives exactly the uniform vanishing bound).
9. **Support of complexes on algebraic spaces** (§2.2.3), upper semicontinuity
   of the perfect locus (`lem:perfect_locus_open`), and the recollement of
   Appendix A (`lem:spacey_recollement`).
10. **Derived reflexivity** (§8), i.e. the duality involution
    `E → RHom(RHom(E, f^×O_X), f^×O_X)`, and its base-change compatibility.
11. **The mate calculus** (§7).  This one was missing only as *packaging*, and
    less of it was missing than I first thought: Mathlib already has
    `CategoryTheory.mateEquiv` and `conjugateEquiv` in
    `Mathlib.CategoryTheory.Adjunction.Mates`, with the counit formulas and the
    vertical/horizontal composition lemmas (`mateEquiv_vcomp`, `mateEquiv_hcomp`).
    `FourierMukai/Prelim/Mates.lean` now spells out the paper's formula, proves it is
    definitionally Mathlib's `mateEquiv`, and proves Lemma 7.8(2) (for adjoint
    equivalences the mate correspondence preserves and reflects isomorphisms).
    What remains is the paper's Lemma 7.1(1) (commutativity of the Hom-set
    square, which is `mateEquiv_vcomp`/`hcomp` transported to `NatTrans`) and
    parts (1) and (3) of Lemma 7.8 (conjugacy, and `H, K` equivalences).

### 5.2 The AxiomMath Stacks formalization

Repository: <https://github.com/AxiomMath/Stacks> (Apache 2.0, created Nov 2026,
pushed Nov 2026).  Facts verified from the repository and its site:

* It is a Lean 4 formalization of the Stacks Project on top of Mathlib, at
  **Lean 4.35.0**; this VM has **Lean 4.33.1**.
* ~63,000 Lean files / ~663,000 declarations / ~15.8M lines; every tag carries a
  `@[stacks TAG]` attribute; the README states there is no `sorry` and no
  `native_decide`, and only the three standard axioms.
* Building requires `lake exe cache get` followed by `lake build`; the README
  warns that the library has ~64,000 modules and that a cache service for the
  compiled modules is only planned.

Consequences for this project:

* The library **cannot be imported in this VM as it stands** (toolchain mismatch
  by two minor versions, and a full build is out of reach here).  I did not clone
  or build it, so everything I say about its *content* is from its README and
  metadata, not from compiling it.
* The tags the paper leans on — 08FA, 08IN, 08IR, 08G4, 08H4, 08H6, 08JJ, 08J9,
  08JF, 08GH, 09IY, 09M8, 09SN, 09SR, 0AED, 0AEC, 0E55, 0E58, 0E5D, 0E5F, 0GEU,
  0GG4, 0H1T, 0H1U, 03BT, 03I7, 03K3, 03TF, 06QZ, 06R0, 07A4, 07A6, 07TY,
  07TZ, 0DKN — are exactly the kind of statement that library is meant to contain.
  **Recommendation:** upgrade the toolchain to 4.35.0, pin the Stacks revision,
  run `lake exe cache get`, and then *test* the specific tags with
  `#stacks_tags 08IN` before relying on them.
* Even if all of those tags are available, the *derived-category-of-sheaves* API
  that this paper needs (`D_qc`, `Perf`, `D^b_coh`, `f^×`, `f^!`, the coherator)
  is a different matter.  The Stacks library formalizes the statements of the
  Stacks Project, and the relevant chapter (75, "Derived Categories of Spaces")
  is enormous.  A first task after upgrading is: find the names of the
  declarations tagged 08FA, 09IY, 09M8, 0AED, 0AEC and see how they are phrased.

### 5.3 The paper itself: points requiring attention

These are things a formalizer (or a referee) must resolve.  I have separated
verified corrections from questions.

**(a) [RESOLVED] `pseudocoherent` and `D^-_coh`.**  §2.2.2 defines
`D^b_coh(X)` as "the full subcategory of `D(X)` consisting of bounded
pseudocoherent complexes", but "pseudocoherent" itself is not defined anywhere in
the preliminaries.  `D^-_coh` appears in Corollary 1.4 and Remark 2.7 without
definition.  **Resolution (authors):** pseudocoherence is the notion for ringed topoi (locally
quasi-isomorphic to a bounded above complex of finite free modules), `D^-_coh` is
`D_qc^-` with coherent cohomology, and on a Noetherian space `E ∈ D_qc`
pseudocoherent is equivalent to `E ∈ D^-_coh`.  This is now recorded in
`FourierMukai/Paper/DerivedSetup.lean` (the field `Subcats.IsPseudocoherent` and
the conditions `DcohEq`, `DcohLeDbQc`), so the paper's statements can be phrased
without ambiguity.  Recommendation for the paper: add the definition to §2.2.2
for readers who do not know Illusie's convention.

**(b) Lemma 3.1, proof.**  "any `E ∈ D^b_qc(Spec k)` is a small coproduct of
shifts of `O_{Spec k}`. In particular `E ≅ ⊕_{α∈I} O_{Spec k}^{⊕α}[n_α]` where `I`
is some finite set of cardinals."  The intended statement is that `E` is a
**finite** direct sum of shifts of `k` (a bounded complex of `k`-vector spaces has
finite-dimensional total cohomology).  "Small coproduct" and "finite set of
cardinals" should be replaced by "finite direct sum, with multiplicities
`n_j ∈ ℕ` and all but finitely many `n_j = 0`".  As written, boundedness of
`R i_* E` does not follow.

**(c) Two typos.**  Lemma 2.11's second display reads
`RHom(i(E), i(L)) ≅ RHom(i(E), i(L))`; the left-hand side should be
`Q(RHom(i(E), i(L)))`.  Remark 2.12 quantifies `L ∈ D_qc(X)`, `K ∈ D_qc(Y)` and
then writes `f^× K` and `RHom(Rf_* L, K)`; for `f^× : D_qc(X) → D_qc(Y)` the
correct variances are `L ∈ D_qc(Y)` and `K ∈ D_qc(X)`.

**(d) [RESOLVED] The filtration `⟨S⟩_n`.**  §2.1 sets
`⟨S⟩_n := add{cone(φ) : φ ∈ Hom_T(⟨S⟩_{n-1}, ⟨S⟩_1)}`.  The standard
Bondal–Van den Bergh filtration (and Mathlib's `triangEnvelopeIter`) uses
morphisms between objects of `⟨S⟩_{n-1}` (or a recursive `⟨S⟩_n = add(⟨S⟩_{n-1} ∪
cones of maps in ⟨S⟩_{n-1})`).  With `Hom(⟨S⟩_{n-1}, ⟨S⟩_1)` the filtration is
coarser and it is not immediate that `⋃_n ⟨S⟩_n` is thick or that it is closed
under extensions of arbitrary objects of the union.  **Resolution (authors):** the filtration as written is correct.  Accordingly,
`FourierMukai/Prelim/Generation.lean` records only the identification of `⟨S⟩`
(as `ObjectProperty.triangEnvelope`) and leaves the `⟨S⟩_n` filtration to the
paper; if the two filtrations are later needed to agree, that is a lemma to
state, not an erratum.

**(e) [RESOLVED] Theorem 1.3: `D_qc` pseudocoherent vs `D^-_coh`.**  The introduction states
Theorem 1.3 for `E ∈ D_qc(Y)` pseudocoherent; Proposition 6.10
(`prop:stacky_all_coincide`) states it for `E ∈ D^-_coh(Y)`; Example 6.17 and
Theorem 6.16 use bounded kernels.  **Resolution (authors):** on a Noetherian space the two hypotheses agree, so no
change is needed; the Lean interface records the equivalence as the condition
`Subcats.DcohEq` rather than choosing one phrasing.

**(f) [RESOLVED] Theorem 1.7 / Reminder 11.2: Gorenstein without flatness.**  Lemma 11.1
(`lem:ideal_sheaf_relatively_perfect`) asserts that the cone of
`O_{Y×_X Y} → RΔ_*O_Y` is relatively perfect over both projections.  Relative
perfectness of `O_Y` over `X` is finite tor-dimension of `f`, which follows from
flatness but not from "proper Gorenstein" if Gorenstein only means "Cohen–Macaulay
fibres with an invertible dualizing sheaf".  In [HLS09] the corresponding
statement is for flat Gorenstein morphisms.  **Resolution (authors):** "proper Gorenstein" means proper *and* Gorenstein, and
"Gorenstein morphism" is the standard Stacks notion, which — as for normal and
Cohen–Macaulay morphisms (cf. Stacks Definition 37.20.1) — includes flatness and
local finite presentation.  With that reading finite tor-dimension is automatic
and Lemma 11.1 is fine.  Recommendation: add the word "flat" (or a pointer to
the Stacks definition) to Reminder 11.2, since readers may use the other
convention.

**(g) Lemma 3.9, proof: a missing sentence.**  The proof passes from
`L(s∘s_u∘i_u)^*E ∈ D^b_coh(κ(u))` to `L(s∘s_u)^*E ∈ Perf(O_{U,u})`, citing Tags
068W and 08HG.  The implication is correct — for a Noetherian local ring `A` with
residue field `k`, a bounded complex of finite `A`-modules has finite projective
dimension iff `E ⊗^L_A k` has bounded cohomology — but that theorem should be
stated, since the naive version ("bounded at the closed fibre implies perfect")
is false without the finite-generation/boundedness hypotheses (compare Example
2.17).

**(h) Dependence on preprints.**  Theorem 1.2(1) uses weak approximability of
`D_qc` for algebraic spaces [Lank, arXiv 2610.22161, Cor. 1.2], and Remark 2.6
uses [Canonaco–Haesemeyer–Neeman–Stellari, arXiv 2402.04605, Thm. B]; Theorem 1.6
rests on the companion [GLMP25, arXiv 2512.16503] and on [Neeman 2023]; §11 uses
[HLS09] and the notion of Gorenstein morphism.  A formalization should record
these as explicit dependencies; a referee should check that the main theorem does
not depend on an unpublished statement that is itself unproved.

**(i) Appendix C, Example-Claim C.4.**  This is labelled a *claim*, not a theorem,
and the accompanying Remark C.5 discusses rather than proves the comparison with
enhanced (dg/∞-categorical) integral transforms.  Fine as an example, but it
should not be cited as a proof of non-liftability without further argument.

**(j) Notation.**  The paper distinguishes `RHom` on `D(X)` from `RHom` on
`D_qc(X)` by fonts (`\operatorname{\mathbb{R}\mathcal{H}\!\mathit{om}}` vs
`\operatorname{\mathbf{R}\mathcal{H}\!\mathit{om}}`), and `D^b_{\operatorname{coh}}`
from `D_{\operatorname{coh}}^b`.  Both distinctions are easy to lose (they already
produced typo (c)), and a formalization cannot rely on fonts at all.  A notation
table in the preliminaries would help.

**(k) Bookkeeping checks I could not settle from the text alone** (worth a
look before formalizing):

* Proposition 12.8 (openness of the relative-perfectness locus) is proved using
  §6's base change results; check it does not use Theorem 6.16 in the direction
  that Theorem 6.16 itself obtains from §12.
* Lemma 2.15(4) chooses a flat surjective `f : Y → X` with `Y` an algebraic space
  and then an étale presentation `t : V → Y ×_X U`; the composite `f' ∘ t` is
  flat and surjective, and Lemma 2.14 is applied to it — this is correct but the
  text says "smooth surjective" in item (3) and "flat surjective" in (4); the
  equivalence is fine, the wording should be uniform.
* The proof of Lemma 2.25 writes `L(f'_1)^*(-) ⊗ RΔ_*O_Y` and then applies the
  projection formula for `Δ`; since `f'_1 ∘ Δ = f'_2 ∘ Δ = 𝟙`, both readings work,
  but the indices in the display (`f'_1` for the tensor, `f'_2` for the
  pushforward) are worth checking once.

### 5.4 Request to the authors: weak approximability

To formalize Remark 2.6 (the passage between equivalences on `D_qc`, `D^-_coh`,
`D^b_coh` and `Perf`) and the part of §12 that uses it, the formalization needs
the notion of a weakly approximable triangulated category and the gluing theorem.
Please attach the LaTeX of

* P. Lank, *Gluing weak approximability along recollements* (arXiv:2610.22161),
  in particular Corollary 1.2, and
* the definition of weak approximability from Neeman, *Triangulated categories
  with a single compact generator, and two Brown representability theorems*
  (arXiv/Invent. Math. 2026) and from Canonaco–Haesemeyer–Neeman–Stellari,
  *The passage among the subcategories of weakly approximable triangulated
  categories* (arXiv:2402.04605, Definition 10.1.1).

For the current sprint (mate calculus, generation, thickness) none of this is
needed: those results are independent of weak approximability.  It becomes
necessary only when formalizing §10–§12.

---

## 6. Axiom audit

`lean FourierMukai/Audit.lean`, verbatim:

```
'RelativeFM.Trinatural.isIso_app_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RelativeFM.Trinatural.isIso_app_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RelativeFM.Trinatural.isIso_app_of_distinguished' depends on axioms: [propext, Classical.choice, Quot.sound]
'RelativeFM.Trinatural.isoLocus_isTriangulated' depends on axioms: [propext, Classical.choice, Quot.sound]
'RelativeFM.Trinatural.isoLocus_isClosedUnderIsomorphisms' depends on axioms: [propext, Classical.choice, Quot.sound]
'RelativeFM.FinitelyBuiltBy.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RelativeFM.isClassicalGenerator_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RelativeFM.Trinatural.id' depends on axioms: [propext, Classical.choice, Quot.sound]
'RelativeFM.theorem_1_3' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'RelativeFM.theorem_12_3' depends on axioms: [sorryAx]
'RelativeFM.theorem_1_2_open' depends on axioms: [sorryAx]
'RelativeFM.theorem_1_2_baseChange' depends on axioms: [sorryAx]
'RelativeFM.corollary_6_18' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'RelativeFM.lemma_12_2' depends on axioms: [sorryAx]
'RelativeFM.theorem_1_6' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'RelativeFM.lemma_2_25' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'RelativeFM.lemma_2_26' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'RelativeFM.theorem_1_7' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

So: the `Prelim` and `Examples` modules are complete; the `Paper.Statements`
module is a specification.  There are ten `sorry`s in the whole development and
they are all in that one file, by design.

---

## 7. Roadmap

Ordered by cost/benefit, with what each step unblocks.

**Phase 0 (done here).** Appendix B and Lemma 2.3(2); the interface; the
statements.

**Phase 1 — mate calculus (§7).  No algebraic geometry needed.**
`mate` of a 2-cell under two adjunctions, the bijection of Lemma 7.1, the
characterizations of Lemma 7.4, the unit/counit remark 7.5, and the
"mates preserve isos" criteria of Lemma 7.8, all in `CategoryTheory`
(`Adjunction`, `NatTrans`, whiskering).  ~600–1000 lines, no new mathematics.
This is the piece of the paper that a Lean user can get the most from.

**Phase 2 — generation and the 2-category of triangulated categories.**
Lemma 2.3(1) and (3), thickness, Lemma 2.5 (needs compact objects and Brown
representability), and the bicategory `Triang` of Appendix B (Mathlib's
`Bicategory` API is there; `Triang` is not).  ~1500 lines.

**Phase 3 — algebraic spaces and `D_qc`.** Either (a) port the relevant part of
the Stacks library (toolchain 4.35.0), or (b) restrict the paper to *schemes*,
where `AlgebraicGeometry.Scheme` plus `Sites.Etale` at least give the site, and
build `Qcoh`/`D_qc` by hand.  Option (b) loses the paper's stated generality but
makes Parts 1–2 formalizable in a realistic horizon.  The scheme-theoretic
predecessor [GLMP25] is the natural target.

**Phase 4 — relative perfectness (Part 1).**  This is the most *formal* part of
the paper: Definitions 4.1/5.1, the étale-local criteria (Theorem 4.8), the
properness/coherence theorem (6.2, 6.8), base change (6.16, Cor. 6.18).  Once
`D_qc` and the six functors exist, this is mechanical but long (~5–10k lines).

**Phase 5 — duality.** `f^×`, `f^!`, Neeman's construction, base-change squares
(§2.4, §7.2–7.3, §9).  This is the hard part, and it is where a formalization
would produce genuinely new infrastructure: Mathlib has nothing comparable.

**Phase 6 — loci and openness (§12), elliptic fibrations (§11).**  Needs
support theory, t-structures (`TStructure` exists), and the Gorenstein
material.  Last.

A realistic estimate: Phases 1–2 are a few months of one person's work; Phases
3–4 are a year or more; Phases 5–6 are a multi-year project.  What is here is
the part that could be done correctly now, plus a machine-checked statement
inventory to grow into.

---

## 8. Reproduction

```bash
export LEAN_PATH="$LEAN_PATH:."
./scripts/build.sh
lean FourierMukai/Audit.lean
```

The build was run in this VM (about 6 s from a clean tree): all eight modules
compile.  The only warnings are the ten `sorry` warnings in
`Paper/Statements.lean` and linter style warnings (unused section variables,
`letI` versus `let`, one universe annotation).  The linter warnings are
cosmetic; the `letI`s are deliberate, since the hypothesis has to be found by
instance search.
