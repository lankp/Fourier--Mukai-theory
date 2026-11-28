/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.InternalHom.Inputs

/-!
# The two internal Homs of GL26 §2.2, and Lemma 2.11 (`lem:internal_hom`)

Guisado Villalgordo–Lank, *Relative Fourier–Mukai theory for algebraic spaces* (GL26), §2.2,
subsection `sec:prelim_stacks_internal_homs`, over an algebraic space `X`:

* the derived sheaf Hom `R𝓗om(E, G) ∈ D(X)` (blackboard `ℝ𝓗om` in GL26), right adjoint of
  `- ⊗^L E` on `D(X)`.  This is AxiomMath's `smallEtaleDerivedSheafHom` with its adjunction
  `smallEtaleDerivedTensorSheafHomAdjunction` (Stacks 08J8), renamed, not redefined: `sheafHom`,
  `sheafHomObj`, `tensorSheafHomAdj`;
* the coherator `Q : D(X) ⥤ D_qc(X)`, a right adjoint of the inclusion `i : D_qc(X) ⥤ D(X)`.
  GL26 obtains it from Brown representability for the compactly generated `D_qc(X)`
  (Stacks 09IY, Neeman), i.e. for `X` quasi-compact and quasi-separated; AxiomMath proves its
  existence there (Stacks 0CR4, `Tag0CR4Input`).  Everything below is stated for an arbitrary
  algebraic space `X` together with *any* adjunction `adj : i ⊣ Q`; `coheratorAdj` supplies one
  for qcqs `X` from `Tag0CR4Input`;
* the internal Hom of `D_qc(X)` (bold `𝐑𝓗om` in GL26): `qcHom adj E = Q ∘ R𝓗om(i E, i -)`,
  right adjoint of `- ⊗^L E` on `D_qc(X)` (`tensorQcRightQcHomAdj`).  `- ⊗^L E` preserves
  `D_qc(X)` by Stacks 08F5 (`Tag08F5Input`).

## Lemma 2.11 (`lem:internal_hom`)

GL26 defines `𝐑𝓗om(E, -)` as *the* right adjoint of `- ⊗^L E` on `D_qc(X)` and proves
`𝐑𝓗om(E, L) ≅ Q(R𝓗om(i E, i L))` by uniqueness of adjoints.  Here: `lemma_2_11` gives, for
every right adjoint `R` of `- ⊗^L E` on `D_qc(X)`, the canonical natural isomorphism
`R ≅ Q ∘ R𝓗om(i E, i -)`; `lemma_2_11_of_mem` gives `i(R L) ≅ R𝓗om(i E, i L)` when
`R𝓗om(i E, i L)` has quasi-coherent cohomology (the counit of `i ⊣ Q` is invertible there);
`sheafHomObj_mem_Dqc_of_isPseudoCoherent` is the last sentence of the lemma (Stacks 0A8A,
`Tag0A8AInput`), and `sheafHomObj_mem_Dqc_of_perfect` its perfect variant.

## Differences from GL26

* GL26 states Lemma 2.11 for an algebraic space `X` without further hypothesis, but the right
  adjoint `Q` it uses is constructed (Brown representability) only for qcqs `X`.  The Lean
  statement takes `Q` as data (any right adjoint of `i`), so it covers every `X` for which `Q`
  exists, in particular every qcqs `X` (`coheratorAdj`).
* The last sentence of the lemma says "`E` pseudo-coherent and `L` locally bounded below".  The
  Lean statement asks `L ∈ D^+_qc(X)` (bounded below), which is the hypothesis of Stacks 0A8A as
  stated in the Stacks Project and in AxiomMath; for quasi-compact `X` the two agree.  This is
  the only gap.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space Opposite

namespace RelativeFM.Spaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The derived sheaf Hom on `D(X)` -/

/-- **`R𝓗om(-, -)` on `D(X)`** (GL26 `sec:prelim_stacks_internal_homs`, blackboard `ℝ𝓗om`):
AxiomMath's `smallEtaleDerivedSheafHom`, contravariant in the first variable. -/
abbrev sheafHom (X : AlgebraicSpaces B S hS) : (D B S hS X)ᵒᵖ ⥤ D B S hS X ⥤ D B S hS X :=
  smallEtaleDerivedSheafHom B S hS X

/-- `R𝓗om(E, G)`. -/
abbrev sheafHomObj {X : AlgebraicSpaces B S hS} (E G : D B S hS X) : D B S hS X :=
  ((sheafHom X).obj (op E)).obj G

/-- **`- ⊗^L P ⊣ R𝓗om(P, -)` on `D(X)`** (Stacks 08J8): AxiomMath's
`smallEtaleDerivedTensorSheafHomAdjunction`. -/
def tensorSheafHomAdj {X : AlgebraicSpaces B S hS} (P : D B S hS X) :
    (tensor X).flip.obj P ⊣ (sheafHom X).obj (op P) :=
  smallEtaleDerivedTensorSheafHomAdjunction B S hS X P

/-- **`D^+_qc(X)`**: cohomologically bounded-below objects of `D_qc(X)`. -/
abbrev DplusQc (X : AlgebraicSpaces B S hS) : ObjectProperty (D B S hS X) :=
  DerivedCategoryB.derivedCategoryBPlus (qcoh X)

/-! ### The coherator -/

/-- **The coherator of a qcqs algebraic space** (GL26 `sec:prelim_stacks_internal_homs`, Stacks
0CR4): for `X` quasi-compact and quasi-separated, a right adjoint `Q` of the inclusion
`i : D_qc(X) ⥤ D(X)`, from `Tag0CR4Input`. -/
def coherator (h : Tag0CR4Input B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) : D B S hS X ⥤ (Dqc X).FullSubcategory :=
  haveI := h hZ X hqc hqs
  (Dqc X).ι.rightAdjoint

/-- The adjunction `i ⊣ Q` of the coherator of a qcqs algebraic space (`coherator`). -/
def coheratorAdj (h : Tag0CR4Input B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    (Dqc X).ι ⊣ coherator h hZ X hqc hqs :=
  haveI := h hZ X hqc hqs
  Adjunction.ofIsLeftAdjoint (Dqc X).ι

/-- The counit `i Q M ⟶ M` of any adjunction `i ⊣ Q` is invertible at an object `M` of `D(X)`
with quasi-coherent cohomology. -/
theorem isIso_counit_app_of_mem {X : AlgebraicSpaces B S hS}
    {Q : D B S hS X ⥤ (Dqc X).FullSubcategory} (adj : (Dqc X).ι ⊣ Q) {M : D B S hS X}
    (hM : Dqc X M) : IsIso (adj.counit.app M) :=
  adj.isIso_counit_app_of_iso (Y := ⟨M, hM⟩) (Iso.refl _)

/-! ### The internal Hom of `D_qc(X)` -/

/-- **`- ⊗^L E` on `D_qc(X)`**, for `E ∈ D_qc(X)` (Stacks 08F5, `Tag08F5Input`).  The functor of
GL26's adjunction `(- ⊗^L E) ⊣ 𝐑𝓗om(E, -)`; `tensorQc` of `Spaces/AxiomMathInputs.lean` is the
other side `E ⊗^L -`. -/
def tensorQcRight (h : Tag08F5Input B S hS) {X : AlgebraicSpaces B S hS}
    (E : (Dqc X).FullSubcategory) : (Dqc X).FullSubcategory ⥤ (Dqc X).FullSubcategory :=
  (Dqc X).lift ((Dqc X).ι ⋙ (tensor X).flip.obj E.obj) fun F =>
    h X F.obj E.obj F.property E.property

/-- **The internal Hom of `D_qc(X)`** (GL26 `sec:prelim_stacks_internal_homs`, bold `𝐑𝓗om`), in
the form of GL26 Lemma 2.11: `𝐑𝓗om(E, -) = Q ∘ R𝓗om(i E, i -)`, for a coherator `adj : i ⊣ Q`. -/
def qcHom {X : AlgebraicSpaces B S hS} {Q : D B S hS X ⥤ (Dqc X).FullSubcategory}
    (_adj : (Dqc X).ι ⊣ Q) (E : (Dqc X).FullSubcategory) :
    (Dqc X).FullSubcategory ⥤ (Dqc X).FullSubcategory :=
  (Dqc X).ι ⋙ (sheafHom X).obj (op E.obj) ⋙ Q

/-- **`(- ⊗^L E) ⊣ Q ∘ R𝓗om(i E, i -)` on `D_qc(X)`**: the composite adjunction
`(i ⊣ Q) ∘ (- ⊗^L i E ⊣ R𝓗om(i E, -))` of GL26's proof of Lemma 2.11, restricted along the fully
faithful `i` (GL26: "restriction gives an adjunction"). -/
def tensorQcRightQcHomAdj (h : Tag08F5Input B S hS) {X : AlgebraicSpaces B S hS}
    {Q : D B S hS X ⥤ (Dqc X).FullSubcategory} (adj : (Dqc X).ι ⊣ Q)
    (E : (Dqc X).FullSubcategory) : tensorQcRight h E ⊣ qcHom adj E :=
  Adjunction.restrictFullyFaithful (iC := 𝟭 _) (iD := (Dqc X).ι)
    (adj.comp (tensorSheafHomAdj E.obj)) (Functor.FullyFaithful.id _) (ObjectProperty.fullyFaithfulι _)
    (Functor.leftUnitor _ ≪≫ ((Dqc X).liftCompιIso _ _).symm) (Functor.rightUnitor _).symm

/-- **Lemma 2.11** (`lem:internal_hom`), main statement.  Let `X` be an algebraic space with a
coherator `adj : i ⊣ Q` and `E ∈ D_qc(X)`.  For any right adjoint `R` of `- ⊗^L E` on `D_qc(X)`
(GL26's `𝐑𝓗om(E, -)`, defined as such a right adjoint), the canonical isomorphism
`𝐑𝓗om(E, -) ≅ Q(R𝓗om(i E, i -))` (uniqueness of adjoints).  GL26 states it for every algebraic
space, with `Q` constructed for qcqs `X`; see the module docstring. -/
def lemma_2_11 (h : Tag08F5Input B S hS) {X : AlgebraicSpaces B S hS}
    {Q : D B S hS X ⥤ (Dqc X).FullSubcategory} (adj : (Dqc X).ι ⊣ Q)
    (E : (Dqc X).FullSubcategory) {R : (Dqc X).FullSubcategory ⥤ (Dqc X).FullSubcategory}
    (adjR : tensorQcRight h E ⊣ R) : R ≅ qcHom adj E :=
  adjR.rightAdjointUniq (tensorQcRightQcHomAdj h adj E)

/-- **Lemma 2.11** (`lem:internal_hom`), "in particular": if `R𝓗om(i E, i L)` has quasi-coherent
cohomology, then `i 𝐑𝓗om(E, L) ≅ R𝓗om(i E, i L)`, the isomorphism of `lemma_2_11` followed by the
counit of `i ⊣ Q`. -/
def lemma_2_11_of_mem (h : Tag08F5Input B S hS) {X : AlgebraicSpaces B S hS}
    {Q : D B S hS X ⥤ (Dqc X).FullSubcategory} (adj : (Dqc X).ι ⊣ Q)
    (E : (Dqc X).FullSubcategory) {R : (Dqc X).FullSubcategory ⥤ (Dqc X).FullSubcategory}
    (adjR : tensorQcRight h E ⊣ R) (L : (Dqc X).FullSubcategory)
    (hEL : Dqc X (sheafHomObj E.obj L.obj)) :
    (Dqc X).ι.obj (R.obj L) ≅ sheafHomObj E.obj L.obj :=
  (Dqc X).ι.mapIso ((lemma_2_11 h adj E adjR).app L) ≪≫
    @asIso _ _ _ _ (adj.counit.app (sheafHomObj E.obj L.obj)) (isIso_counit_app_of_mem adj hEL)

/-- The isomorphism of `lemma_2_11_of_mem` is the image of the isomorphism of `lemma_2_11` followed
by the counit. -/
theorem lemma_2_11_of_mem_hom (h : Tag08F5Input B S hS) {X : AlgebraicSpaces B S hS}
    {Q : D B S hS X ⥤ (Dqc X).FullSubcategory} (adj : (Dqc X).ι ⊣ Q)
    (E : (Dqc X).FullSubcategory) {R : (Dqc X).FullSubcategory ⥤ (Dqc X).FullSubcategory}
    (adjR : tensorQcRight h E ⊣ R) (L : (Dqc X).FullSubcategory)
    (hEL : Dqc X (sheafHomObj E.obj L.obj)) :
    (lemma_2_11_of_mem h adj E adjR L hEL).hom =
      (Dqc X).ι.map ((lemma_2_11 h adj E adjR).hom.app L) ≫
        adj.counit.app (sheafHomObj E.obj L.obj) :=
  rfl

/-- **Lemma 2.11** (`lem:internal_hom`), last sentence (Stacks 0A8A, `Tag0A8AInput`): for `E`
pseudo-coherent and `L ∈ D^+_qc(X)`, `R𝓗om(E, L)` has quasi-coherent cohomology.  GL26 says
"`L` locally bounded below"; see the module docstring. -/
theorem sheafHomObj_mem_Dqc_of_isPseudoCoherent (h : Tag0A8AInput B S hS)
    {X : AlgebraicSpaces B S hS} {E L : D B S hS X} (hE : IsPseudoCoherent X E)
    (hL : DplusQc X L) : Dqc X (sheafHomObj E L) :=
  h X E L (Or.inl ⟨hE, hL⟩)

/-- The perfect case of Stacks 0A8A (`Tag0A8AInput`): for `E` perfect and `L ∈ D_qc(X)`,
`R𝓗om(E, L)` has quasi-coherent cohomology. -/
theorem sheafHomObj_mem_Dqc_of_perfect (h : Tag0A8AInput B S hS) {X : AlgebraicSpaces B S hS}
    {E L : D B S hS X} (hE : Perf X E) (hL : Dqc X L) : Dqc X (sheafHomObj E L) :=
  h X E L (Or.inr ⟨hE, hL⟩)

/-- **Lemma 2.11** (`lem:internal_hom`) with its last sentence: for `E` pseudo-coherent and
`L ∈ D^+_qc(X)`, `i 𝐑𝓗om(E, L) ≅ R𝓗om(i E, i L)`. -/
def lemma_2_11_of_isPseudoCoherent (h : Tag08F5Input B S hS) (h0A8A : Tag0A8AInput B S hS)
    {X : AlgebraicSpaces B S hS} {Q : D B S hS X ⥤ (Dqc X).FullSubcategory}
    (adj : (Dqc X).ι ⊣ Q) (E : (Dqc X).FullSubcategory)
    {R : (Dqc X).FullSubcategory ⥤ (Dqc X).FullSubcategory} (adjR : tensorQcRight h E ⊣ R)
    (hE : IsPseudoCoherent X E.obj) (L : (Dqc X).FullSubcategory) (hL : DplusQc X L.obj) :
    (Dqc X).ι.obj (R.obj L) ≅ sheafHomObj E.obj L.obj :=
  lemma_2_11_of_mem h adj E adjR L (sheafHomObj_mem_Dqc_of_isPseudoCoherent h0A8A hE hL)

end RelativeFM.Spaces
