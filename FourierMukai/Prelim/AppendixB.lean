/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as
described in the file LICENSE. -/
import FourierMukai.Prelim.Triangulated
import FourierMukai.Prelim.Mates
import FourierMukai.Prelim.Lemma25
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Appendix B: transadjunctions and triadjunctions

This file formalizes the following results of Appendix B of

  E. Guisado Villalgordo, P. Lank, *Relative Fourier--Mukai theory for algebraic spaces*
  (GL26):

* **Lemma B.4** (`lem:equiv_transadj`): `Trans.lemma_B4` (a `List.TFAE` of the five
  conditions);
* **Lemma B.5** (`lem:adj_and_equiv_in_trans`): `Trans.lemma_B5_existsUnique`,
  `Trans.lemma_B5_iff`, `Trans.lemma_B5_equivalence`;
* **Lemma B.7** (`lem:transnat_is_trinat`): `lemma_B7`, and its comparison with
  Mathlib's `NatTrans.CommShift` and with `RelativeFM.Trinatural`: `lemma_B7_natTrans`;
* **Lemma B.10** (`lem:triadjoint_iff_adjoint`, `lem:triequiv_iff_equiv`):
  `lemma_B10_exists`, `lemma_B10_unique`, `lemma_B10_commShiftIso`,
  `lemma_B10_equivalence`.

Lemma B.2 (`lem:trans_is_2-cat`, the strict 2-category `Trans`) is not formalized.

Nothing is assumed: no Stacks field, no hypothesis beyond the paper's.

## Rendering

**Categories with translation (B.4, B.5).**  Part I works exactly with the paper's data: a
category `C` with one endofunctor `T : C ⥤ C`, and 1-morphisms `(F, ξ)` with
`ξ : T ⋙ F ≅ F ⋙ T'` (the paper's `ξ : FT ≅ T'F`, in Mathlib's diagrammatic order).  A
transnatural transformation (paper, diagram `diag:transnat`) is `Trans.IsTransnatural`.  The
composite of `(F, ξ)` and `(G, ζ)` is `(F ⋙ G, Trans.compIso ξ ζ)`, whose component at `c`
is `G ξ_c ≫ ζ_{F c}` (the paper's `ζ_F · Gξ`); the identity is `(𝟭, Trans.idIso T)`.

Since Lemma B.2 (that these data form a strict 2-category whose 2-cells compose as in
`Cat`) is out of scope, an adjunction in `Trans` with underlying 1-cells `(F, ξ)`, `(G, ζ)`
and underlying `Cat`-adjunction `adj` is *defined* (`Trans.IsTransAdjunction`) as: the unit
and counit are transnatural.  This is what an adjunction in `Trans` is, because the
triangle identities in `Trans` are the triangle identities in `Cat` (2-cells of `Trans` are
2-cells of `Cat` and are composed as such); with this definition B.4 (5) ⇔ (2)+(3) is by
definition, as in the paper ("is clear").  Similarly an equivalence in `Trans` is rendered
in `Trans.lemma_B5_equivalence` by transnatural isomorphisms `𝟭 ≅ F ⋙ G`, `G ⋙ F ≅ 𝟭`; the
inverse of a transnatural isomorphism is transnatural (`Trans.IsTransnatural.inv`), so
these are 2-isomorphisms of `Trans`.

The paper asks `T` to be an autoequivalence.  B.4 and B.5(2) hold for an arbitrary
endofunctor and are stated so; B.5(1) uses `[T.IsEquivalence] [T'.IsEquivalence]` (only to
show that the mate of `ξ` is invertible).

**Triangulated categories (B.7, B.10).**  Part II uses Mathlib's pretriangulated categories,
whose translation is `shiftFunctor C (1 : ℤ)` inside a shift by `ℤ`, and Mathlib's triangulated
functors, which carry a `Functor.CommShift F ℤ`, a compatible family of isomorphisms for every
`n : ℤ`; the paper's `ξ` is `F.commShiftIso 1`.  The paper's trinatural transformation
(Definition B.9, `def:trinat_trans`: a family of morphisms, not assumed natural, making the
ladder over each distinguished triangle commute) is `IsTrinatural`.  "Transnatural" for a
triangulated functor means transnatural for the degree-1 isomorphisms, i.e.
`Trans.IsTransnatural (F.commShiftIso 1) (G.commShiftIso 1)`.  `lemma_B7_natTrans` shows that
this is equivalent to Mathlib's `NatTrans.CommShift α ℤ` (compatibility in every degree; the
degree-1 condition propagates by `natTransCommShift_of_one`) and to being the underlying
transformation of a `RelativeFM.Trinatural` (the repository's rendering of Definition B.9,
which asks compatibility in every degree and a morphism of triangles on each distinguished
triangle).  `Trinatural.ofNatTrans` (`Prelim/Lemma25.lean`) is the direction
"`NatTrans.CommShift` ⇒ `Trinatural`" of this.

In B.10, "`(G, ζ)` is a triangulated functor" requires, in Mathlib, a whole `CommShift ℤ`
structure on `G`, not only `ζ = G.commShiftIso 1`.  We therefore prove:
* existence: Mathlib's `Adjunction.rightAdjointCommShift` makes `G` triangulated with unit
  and counit trinatural (`lemma_B10_exists`);
* uniqueness of the whole structure: any `CommShift ℤ` structure on `G` for which the unit is
  trinatural equals Mathlib's (`lemma_B10_unique`) — the paper also asks the counit to be
  trinatural and `G` triangulated; neither is needed;
* its degree-`n` iso is the inverse of the mate of `F.commShiftIso n` (`lemma_B10_commShiftIso`);
  for `n = 1` this says the paper's `ζ` is the one of Lemma B.5.

The displayed "`(G, ζ) ⊣ (F, ξ)`" in item (1) of the paper's lemma reads as a typo for
`(F, ξ) ⊣ (G, ζ)`; the latter is what is formalized (as Mathlib's `Adjunction.IsTriangulated`).
The "similar statements for left adjoints" are not formalized.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory Category Functor

/-! ## Part I: categories with translation -/

namespace Trans

variable {C C' C'' : Type*} [Category* C] [Category* C'] [Category* C'']

/-- The compatibility isomorphism of the identity 1-morphism `(𝟭, 1_T)` of a category with
translation `(C, T)` (GL26, Definition B.1(3)). -/
def idIso (T : C ⥤ C) : T ⋙ 𝟭 C ≅ 𝟭 C ⋙ T :=
  NatIso.ofComponents (fun c => Iso.refl (T.obj c)) (by intros; simp)

@[simp] lemma idIso_hom_app (T : C ⥤ C) (c : C) : (idIso T).hom.app c = 𝟙 (T.obj c) := rfl

@[simp] lemma idIso_inv_app (T : C ⥤ C) (c : C) : (idIso T).inv.app c = 𝟙 (T.obj c) := rfl

/-- The compatibility isomorphism of the composite `(G, ζ)(F, ξ) = (GF, ζ_F · Gξ)` of two
1-morphisms of categories with translation (GL26, Definition B.1(4)). -/
def compIso {T : C ⥤ C} {T' : C' ⥤ C'} {T'' : C'' ⥤ C''} {F : C ⥤ C'} {G : C' ⥤ C''}
    (ξ : T ⋙ F ≅ F ⋙ T') (ζ : T' ⋙ G ≅ G ⋙ T'') : T ⋙ (F ⋙ G) ≅ (F ⋙ G) ⋙ T'' :=
  NatIso.ofComponents (fun c => G.mapIso (ξ.app c) ≪≫ ζ.app (F.obj c)) (by
    intro X Y f
    have h₁ := ξ.hom.naturality f
    have h₂ := ζ.hom.naturality (F.map f)
    dsimp at h₁ h₂ ⊢
    rw [← G.map_comp_assoc, h₁, G.map_comp_assoc, h₂, assoc])

@[simp] lemma compIso_hom_app {T : C ⥤ C} {T' : C' ⥤ C'} {T'' : C'' ⥤ C''} {F : C ⥤ C'}
    {G : C' ⥤ C''} (ξ : T ⋙ F ≅ F ⋙ T') (ζ : T' ⋙ G ≅ G ⋙ T'') (c : C) :
    (compIso ξ ζ).hom.app c = G.map (ξ.hom.app c) ≫ ζ.hom.app (F.obj c) := rfl

/-- A **transnatural transformation** `(F, ξ) ⇒ (G, ζ)` (GL26, Definition B.1(5), diagram
`diag:transnat`): a natural transformation `α : F ⟶ G` with `ζ ∘ α_T = T'α ∘ ξ`. -/
def IsTransnatural {T : C ⥤ C} {T' : C' ⥤ C'} {F G : C ⥤ C'}
    (ξ : T ⋙ F ≅ F ⋙ T') (ζ : T ⋙ G ≅ G ⋙ T') (α : F ⟶ G) : Prop :=
  ∀ c : C, α.app (T.obj c) ≫ ζ.hom.app c = ξ.hom.app c ≫ T'.map (α.app c)

/-- The inverse of a transnatural isomorphism is transnatural; so transnatural isomorphisms
are the 2-isomorphisms of `Trans`. -/
lemma IsTransnatural.inv {T : C ⥤ C} {T' : C' ⥤ C'} {F G : C ⥤ C'}
    {ξ : T ⋙ F ≅ F ⋙ T'} {ζ : T ⋙ G ≅ G ⋙ T'} {e : F ≅ G}
    (h : IsTransnatural ξ ζ e.hom) : IsTransnatural ζ ξ e.inv := by
  intro c
  have hc := h c
  rw [← cancel_epi (e.hom.app (T.obj c)), e.hom_inv_id_app_assoc, reassoc_of% hc,
    ← T'.map_comp, e.hom_inv_id_app, T'.map_id, comp_id]

section B4

variable {T : C ⥤ C} {T' : C' ⥤ C'} {F : C ⥤ C'} {G : C' ⥤ C} (adj : F ⊣ G)
  (ξ : T ⋙ F ≅ F ⋙ T') (ζ : T' ⋙ G ≅ G ⋙ T)

/-- Condition (1) of Lemma B.4: `(ξ, ζ⁻¹)` are mates for the square with `T`, `T'` as
horizontal edges and `F ⊣ G` on both vertical sides.  `RelativeFM.mate` is Mathlib's
`mateEquiv` (`mate_eq_categoryTheory_mateEquiv`). -/
def AreMates : Prop := mate adj adj ξ.hom = ζ.inv

/-- Condition (2) of Lemma B.4: the counit `ε : (F, ξ)(G, ζ) ⇒ 1_{(C', T')}` is
transnatural. -/
def CounitTransnatural : Prop := IsTransnatural (compIso ζ ξ) (idIso T') adj.counit

/-- Condition (3) of Lemma B.4: the unit `η : 1_{(C, T)} ⇒ (G, ζ)(F, ξ)` is transnatural. -/
def UnitTransnatural : Prop := IsTransnatural (idIso T) (compIso ξ ζ) adj.unit

/-- Condition (4) of Lemma B.4: the square of Hom-sets
`C'(Fc, d) ≅ C(c, Gd)`, `C'(FTc, T'd) ≅ C(Tc, GT'd)` with vertical maps `ξ_c^* ∘ T'` and
`ζ⁻¹_{d,*} ∘ T` commutes. -/
def HomSquare : Prop :=
  ∀ (c : C) (d : C') (f : F.obj c ⟶ d),
    T.map (adj.homEquiv c d f) ≫ ζ.inv.app d =
      adj.homEquiv (T.obj c) (T'.obj d) (ξ.hom.app c ≫ T'.map f)

/-- Condition (5) of Lemma B.4: `(F, ξ) ⊣ (G, ζ)` in `Trans` with unit `η` and counit `ε`.
See the module docstring: since 2-cells of `Trans` are composed as in `Cat` (Lemma B.2, not
formalized), the triangle identities are those of `adj`, and the condition is that `η` and
`ε` be 2-cells of `Trans`. -/
def IsTransAdjunction : Prop := UnitTransnatural adj ξ ζ ∧ CounitTransnatural adj ξ ζ

/-- The unit identity of the mate (Mathlib's `unit_mateEquiv`). -/
lemma unit_mate (c : C) :
    T.map (adj.unit.app c) ≫ (mate adj adj ξ.hom).app (F.obj c) =
      adj.unit.app (T.obj c) ≫ G.map (ξ.hom.app c) :=
  unit_mateEquiv adj adj ξ.hom c

/-- The counit identity of the mate (Mathlib's `mateEquiv_counit`). -/
lemma mate_counit (d : C') :
    F.map ((mate adj adj ξ.hom).app d) ≫ adj.counit.app (T'.obj d) =
      ξ.hom.app (G.obj d) ≫ T'.map (adj.counit.app d) :=
  mateEquiv_counit adj adj ξ.hom d

variable {adj ξ} in
/-- A transformation `G ⋙ T ⟶ T' ⋙ G` satisfying the unit identity is the mate of `ξ`. -/
lemma eq_mate_of_unit (γ : G ⋙ T ⟶ T' ⋙ G)
    (h : ∀ c, T.map (adj.unit.app c) ≫ γ.app (F.obj c) =
      adj.unit.app (T.obj c) ≫ G.map (ξ.hom.app c)) :
    γ = mate adj adj ξ.hom := by
  -- Both are determined by their values after `T η_{G d}`, by naturality and a triangle law.
  have key : ∀ (δ : G ⋙ T ⟶ T' ⋙ G) (d : C'), δ.app d =
      T.map (adj.unit.app (G.obj d)) ≫ δ.app (F.obj (G.obj d)) ≫
        G.map (T'.map (adj.counit.app d)) := by
    intro δ d
    have hn := δ.naturality (adj.counit.app d)
    dsimp at hn
    rw [← hn, ← T.map_comp_assoc, Adjunction.right_triangle_components]
    simp
  ext d
  rw [key γ d, key (mate adj adj ξ.hom) d, reassoc_of% (h (G.obj d)),
    reassoc_of% (unit_mate adj ξ (G.obj d))]

variable {adj ξ} in
/-- A transformation `G ⋙ T ⟶ T' ⋙ G` satisfying the counit identity is the mate of `ξ`. -/
lemma eq_mate_of_counit (γ : G ⋙ T ⟶ T' ⋙ G)
    (h : ∀ d, F.map (γ.app d) ≫ adj.counit.app (T'.obj d) =
      ξ.hom.app (G.obj d) ≫ T'.map (adj.counit.app d)) :
    γ = mate adj adj ξ.hom := by
  ext d
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, h, mate_counit]

/-- The common reformulation of (1), (3), (4): `T η_c ≫ ζ⁻¹_{Fc} = η_{Tc} ≫ G ξ_c`. -/
def UnitSquare : Prop :=
  ∀ c : C, T.map (adj.unit.app c) ≫ ζ.inv.app (F.obj c) =
    adj.unit.app (T.obj c) ≫ G.map (ξ.hom.app c)

lemma areMates_iff_unitSquare : AreMates adj ξ ζ ↔ UnitSquare adj ξ ζ := by
  constructor
  · intro h c
    rw [← unit_mate, show mate adj adj ξ.hom = ζ.inv from h]
  · intro h
    exact (eq_mate_of_unit _ h).symm

lemma unitTransnatural_iff_unitSquare : UnitTransnatural adj ξ ζ ↔ UnitSquare adj ξ ζ := by
  refine forall_congr' fun c => ?_
  simp only [idIso_hom_app, compIso_hom_app, Functor.comp_obj, Functor.id_obj]
  constructor
  · intro h
    rw [← cancel_mono (ζ.hom.app (F.obj c))]
    simpa using h.symm
  · intro h
    have h' := congrArg (· ≫ ζ.hom.app (F.obj c)) h
    simpa using h'.symm

lemma counitTransnatural_iff_areMates :
    CounitTransnatural adj ξ ζ ↔ AreMates adj ξ ζ := by
  constructor
  · intro h
    refine (eq_mate_of_counit ζ.inv fun d => ?_).symm
    have hd := h d
    simp only [idIso_hom_app, compIso_hom_app, Functor.comp_obj, Functor.id_obj,
      comp_id] at hd
    dsimp
    rw [hd]
    simp only [← assoc, ← F.map_comp, Iso.inv_hom_id_app]
    simp
  · intro h d
    have hd := mate_counit adj ξ d
    rw [show mate adj adj ξ.hom = ζ.inv from h] at hd
    simp only [idIso_hom_app, compIso_hom_app, Functor.comp_obj, Functor.id_obj, comp_id]
    dsimp at hd ⊢
    rw [assoc, ← hd, ← F.map_comp_assoc, Iso.hom_inv_id_app]
    simp

lemma homSquare_iff_unitSquare : HomSquare adj ξ ζ ↔ UnitSquare adj ξ ζ := by
  -- Both sides of (4) are `T η_c ≫ ζ⁻¹_{Fc} ≫ G T' f` and `η_{Tc} ≫ G ξ_c ≫ G T' f`.
  have expand : ∀ (c : C) (d : C') (f : F.obj c ⟶ d),
      T.map (adj.homEquiv c d f) ≫ ζ.inv.app d =
        T.map (adj.unit.app c) ≫ ζ.inv.app (F.obj c) ≫ G.map (T'.map f) := by
    intro c d f
    have hn := ζ.inv.naturality f
    dsimp at hn
    rw [Adjunction.homEquiv_unit, T.map_comp, assoc, hn]
  constructor
  · intro h c
    have hc := h c (F.obj c) (𝟙 _)
    rw [expand, Adjunction.homEquiv_unit] at hc
    simpa using hc
  · intro h c d f
    rw [expand, reassoc_of% (h c), Adjunction.homEquiv_unit, G.map_comp]

/-- **Lemma B.4** (`lem:equiv_transadj`).  Let `(F, ξ) : (C, T) → (C', T')` and
`(G, ζ) : (C', T') → (C, T)` be 1-morphisms of categories with translation and `adj : F ⊣ G`
an adjunction in `Cat`.  The following are equivalent:
(1) `(ξ, ζ⁻¹)` are mates; (2) the counit is transnatural; (3) the unit is transnatural;
(4) the Hom-set square commutes; (5) `(F, ξ) ⊣ (G, ζ)` in `Trans` with the same unit and
counit (rendered as in `IsTransAdjunction`).  `T` and `T'` are arbitrary endofunctors.

The paper derives (1)–(4) from Lemma 7.4 (`lem:morph_adj`); here they are proved directly
from Mathlib's `unit_mateEquiv` and `mateEquiv_counit`. -/
theorem lemma_B4 :
    List.TFAE [AreMates adj ξ ζ, CounitTransnatural adj ξ ζ, UnitTransnatural adj ξ ζ,
      HomSquare adj ξ ζ, IsTransAdjunction adj ξ ζ] := by
  tfae_have 1 ↔ 2 := (counitTransnatural_iff_areMates adj ξ ζ).symm
  tfae_have 1 ↔ 3 :=
    (areMates_iff_unitSquare adj ξ ζ).trans (unitTransnatural_iff_unitSquare adj ξ ζ).symm
  tfae_have 1 ↔ 4 :=
    (areMates_iff_unitSquare adj ξ ζ).trans (homSquare_iff_unitSquare adj ξ ζ).symm
  tfae_have 5 ↔ 1 := by
    rw [IsTransAdjunction, counitTransnatural_iff_areMates, unitTransnatural_iff_unitSquare,
      ← areMates_iff_unitSquare, and_self]
  tfae_finish

/-- Under the conditions of Lemma B.4, `ζ` is determined by `ξ`: `ζ⁻¹` is the mate of `ξ`.
(Uniqueness half of Lemma B.5(1).) -/
lemma inv_eq_mate_of_isTransAdjunction (h : IsTransAdjunction adj ξ ζ) :
    ζ.inv = mate adj adj ξ.hom :=
  ((counitTransnatural_iff_areMates adj ξ ζ).1 h.2).symm

end B4

section B5

variable {T : C ⥤ C} {T' : C' ⥤ C'} {F : C ⥤ C'} {G : C' ⥤ C} (adj : F ⊣ G)
  (ξ : T ⋙ F ≅ F ⋙ T')

/-- The Hom-set square for the mate of `ξ` itself. -/
lemma mate_homSquare (c : C) (d : C') (f : F.obj c ⟶ d) :
    T.map (adj.homEquiv c d f) ≫ (mate adj adj ξ.hom).app d =
      adj.homEquiv (T.obj c) (T'.obj d) (ξ.hom.app c ≫ T'.map f) := by
  have hn := (mate adj adj ξ.hom).naturality f
  dsimp at hn
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, T.map_comp, assoc, hn,
    reassoc_of% (unit_mate adj ξ c), G.map_comp]

/-- If `T` and `T'` are equivalences and `ξ` is an isomorphism, then the mate
`T G ⟶ G T'` of `ξ` is an isomorphism (the instance of Lemma 7.11 used in the proof of
Lemma B.5).  Only `T` essentially surjective and fully faithful, and `T'` fully faithful,
are used. -/
lemma isIso_mate [T.IsEquivalence] [T'.IsEquivalence] : IsIso (mate adj adj ξ.hom) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  apply isIso_of_yoneda_map_bijective
  intro X
  -- First the case `X = T c`.
  have hT : ∀ c : C, Function.Bijective
      (fun x : T.obj c ⟶ T.obj (G.obj d) => x ≫ (mate adj adj ξ.hom).app d) := by
    intro c
    have hcomp : (fun x : T.obj c ⟶ T.obj (G.obj d) => x ≫ (mate adj adj ξ.hom).app d) ∘
        (fun f : F.obj c ⟶ d => T.map (adj.homEquiv c d f)) =
        (fun f : F.obj c ⟶ d => adj.homEquiv (T.obj c) (T'.obj d)
          (ξ.hom.app c ≫ T'.map f)) := by
      funext f
      exact mate_homSquare adj ξ c d f
    have hbij₁ : Function.Bijective (fun f : F.obj c ⟶ d => T.map (adj.homEquiv c d f)) :=
      ((Functor.FullyFaithful.ofFullyFaithful T).map_bijective _ _).comp
        (adj.homEquiv c d).bijective
    have hbij₂ : Function.Bijective (fun f : F.obj c ⟶ d =>
        adj.homEquiv (T.obj c) (T'.obj d) (ξ.hom.app c ≫ T'.map f)) := by
      refine (adj.homEquiv _ _).bijective.comp (Function.Bijective.comp ?_
        ((Functor.FullyFaithful.ofFullyFaithful T').map_bijective _ _))
      exact (Function.bijective_iff_has_inverse).2
        ⟨fun g => inv (ξ.hom.app c) ≫ g, fun g => by simp, fun g => by simp⟩
    rw [← hcomp] at hbij₂
    exact (Function.Bijective.of_comp_iff _ hbij₁).1 hbij₂
  -- General `X`, via `X ≅ T c`.
  let e : T.obj (T.objPreimage X) ≅ X := T.objObjPreimageIso X
  have hcomp : (fun x : X ⟶ (G ⋙ T).obj d => x ≫ (mate adj adj ξ.hom).app d) =
      (fun y => e.inv ≫ y) ∘
        (fun x : T.obj (T.objPreimage X) ⟶ T.obj (G.obj d) =>
          x ≫ (mate adj adj ξ.hom).app d) ∘ (fun x => e.hom ≫ x) := by
    funext x
    simp
  rw [hcomp]
  refine Function.Bijective.comp ?_ ((hT _).comp ?_)
  · exact (Function.bijective_iff_has_inverse).2
      ⟨fun g => e.hom ≫ g, fun g => by simp, fun g => by simp⟩
  · exact (Function.bijective_iff_has_inverse).2
      ⟨fun g => e.inv ≫ g, fun g => by simp, fun g => by simp⟩

/-- The translation isomorphism `ζ : G T' ≅ T G` of the right adjoint, defined as the inverse
of the mate of `ξ` (GL26, proof of Lemma B.5(1)). -/
noncomputable def rightAdjointIso [T.IsEquivalence] [T'.IsEquivalence] : T' ⋙ G ≅ G ⋙ T :=
  haveI := isIso_mate adj ξ
  (asIso (mate adj adj ξ.hom)).symm

/-- **Lemma B.5(1)** (`lem:adj_and_equiv_in_trans`).  Let `(F, ξ) : (C, T) → (C', T')` be a
1-morphism of categories with translation (`T`, `T'` autoequivalences) and `adj : F ⊣ G` an
adjunction in `Cat`.  There is a unique `ζ : G T' ≅ T G` such that `η` and `ε` are
transnatural, i.e. `(F, ξ) ⊣ (G, ζ)` in `Trans` with unit and counit those of `adj`.  It is
`rightAdjointIso adj ξ`, the inverse of the mate of `ξ`. -/
theorem lemma_B5_existsUnique [T.IsEquivalence] [T'.IsEquivalence] :
    ∃! ζ : T' ⋙ G ≅ G ⋙ T, IsTransAdjunction adj ξ ζ := by
  refine ⟨rightAdjointIso adj ξ, ?_, fun ζ hζ => ?_⟩
  · have h1 : AreMates adj ξ (rightAdjointIso adj ξ) := rfl
    have := lemma_B4 adj ξ (rightAdjointIso adj ξ)
    exact (this.out 0 4).1 h1
  · have h := inv_eq_mate_of_isTransAdjunction adj ξ ζ hζ
    ext1
    rw [← Iso.inv_eq_inv]
    exact h

/-- **Lemma B.5(1)** (`lem:adj_and_equiv_in_trans`), first sentence: `F` has a right adjoint
in `Cat` if and only if `(F, ξ)` has a right adjoint in `Trans`. -/
theorem lemma_B5_iff [T.IsEquivalence] [T'.IsEquivalence] :
    F.IsLeftAdjoint ↔
      ∃ (G : C' ⥤ C) (ζ : T' ⋙ G ≅ G ⋙ T) (adj : F ⊣ G), IsTransAdjunction adj ξ ζ := by
  constructor
  · intro _
    let adj := Adjunction.ofIsLeftAdjoint F
    obtain ⟨ζ, hζ, -⟩ := lemma_B5_existsUnique adj ξ
    exact ⟨_, ζ, adj, hζ⟩
  · rintro ⟨G, -, adj, -⟩
    exact adj.isLeftAdjoint

/-- **Lemma B.5(2)** (`lem:adj_and_equiv_in_trans`).  `F` is an equivalence in `Cat` if and
only if `(F, ξ)` is an equivalence in `Trans`: there are `(G, ζ)` and transnatural
isomorphisms `𝟭 ≅ (G, ζ)(F, ξ)` and `(F, ξ)(G, ζ) ≅ 𝟭`.  No hypothesis on `T`, `T'` is
needed (the mate of `ξ` is invertible because the unit and counit are). -/
theorem lemma_B5_equivalence :
    F.IsEquivalence ↔
      ∃ (G : C' ⥤ C) (ζ : T' ⋙ G ≅ G ⋙ T) (u : 𝟭 C ≅ F ⋙ G) (v : G ⋙ F ≅ 𝟭 C'),
        IsTransnatural (idIso T) (compIso ξ ζ) u.hom ∧
          IsTransnatural (compIso ζ ξ) (idIso T') v.hom := by
  constructor
  · intro _
    let adj : F ⊣ F.inv := F.asEquivalence.toAdjunction
    have : IsIso adj.unit := inferInstanceAs (IsIso F.asEquivalence.unitIso.hom)
    have : IsIso adj.counit := inferInstanceAs (IsIso F.asEquivalence.counitIso.hom)
    have := RelativeFM.isIso_mate adj adj ξ.hom
    let ζ : T' ⋙ F.inv ≅ F.inv ⋙ T := (asIso (mate adj adj ξ.hom)).symm
    have h1 : AreMates adj ξ ζ := rfl
    have h5 := ((lemma_B4 adj ξ ζ).out 0 4).1 h1
    exact ⟨F.inv, ζ, F.asEquivalence.unitIso, F.asEquivalence.counitIso, h5.1, h5.2⟩
  · rintro ⟨G, -, u, v, -, -⟩
    exact (CategoryTheory.Equivalence.mk F G u v).isEquivalence_functor

end B5

end Trans

/-! ## Part II: triangulated categories -/

section ShiftDegreeOne

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ] (τ : F₁ ⟶ F₂)

omit [HasShift C ℤ] [HasShift D ℤ] [F₁.CommShift ℤ] [F₂.CommShift ℤ] in
/-- Two natural transformations agreeing at an object agree at every isomorphic object. -/
lemma app_eq_app_of_iso {P Q : C ⥤ D} (α β : P ⟶ Q) {X Y : C} (e : X ≅ Y)
    (h : α.app X = β.app X) : α.app Y = β.app Y := by
  rw [← cancel_epi (P.map e.hom), α.naturality, β.naturality, h]

/-- Compatibility of `τ` with the shift by `a` implies compatibility with the shift by `-a`. -/
lemma commShiftCore_of_add_eq_zero {a b : ℤ} (h : a + b = 0)
    (ha : NatTrans.CommShiftCore τ a) : NatTrans.CommShiftCore τ b := by
  have hX : ∀ X : C, (F₁.commShiftIso b).hom.app (X⟦a⟧) ≫ (τ.app (X⟦a⟧))⟦b⟧' =
      τ.app (X⟦a⟧⟦b⟧) ≫ (F₂.commShiftIso b).hom.app (X⟦a⟧) := by
    intro X
    rw [← cancel_mono (((F₂.commShiftIso a).hom.app X)⟦b⟧' ≫
      (shiftFunctorCompIsoId D a b h).hom.app (F₂.obj X))]
    rw [assoc, assoc, ← F₂.map_shiftFunctorCompIsoId_hom_app X a b h,
      ← τ.naturality, ← (shiftFunctor D b).map_comp_assoc,
      ← NatTrans.CommShiftCore.shift_app_comm τ ha X, (shiftFunctor D b).map_comp_assoc]
    have hn := (shiftFunctorCompIsoId D a b h).hom.naturality (τ.app X)
    dsimp at hn
    rw [hn, F₁.map_shiftFunctorCompIsoId_hom_app X a b h, assoc, assoc]
    rfl
  refine ⟨?_⟩
  ext Y
  have hba : b + a = 0 := by omega
  refine app_eq_app_of_iso _ _ ((shiftFunctorCompIsoId C b a hba).app Y) ?_
  exact hX (Y⟦b⟧)

/-- A natural transformation between functors commuting with the shift by `ℤ` is compatible
with all shifts as soon as it is compatible with the shift by `1`. -/
lemma natTransCommShift_of_one (h1 : NatTrans.CommShiftCore τ (1 : ℤ)) :
    NatTrans.CommShift τ ℤ := by
  have hm1 := commShiftCore_of_add_eq_zero τ (by norm_num : (1 : ℤ) + -1 = 0) h1
  refine NatTrans.CommShift.of_core (fun n => ?_)
  induction n using Int.induction_on with
  | zero => exact NatTrans.CommShiftCore.zero ℤ
  | succ i hi => exact hi.add h1
  | pred i hi => rw [sub_eq_add_neg]; exact hi.add hm1

end ShiftDegreeOne

section Triangulated

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroObject C] [HasShift C ℤ] [HasShift D ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A **trinatural transformation** `(F, ξ) ⇒ (G, ζ)` (GL26, Definition B.9,
`def:trinat_trans`, diagram `diag:trinat`): a family of morphisms `η A : F A ⟶ G A`, not
assumed natural, such that for every distinguished triangle `A → B → C → A⟦1⟧` the ladder
between its images under `F` and `G` commutes; the last maps of the rungs are
`F h ≫ ξ_A` and `G h ≫ ζ_A`, with `ξ = F.commShiftIso 1`, `ζ = G.commShiftIso 1`.
(The paper states this for triangulated functors; only the translation isomorphisms are
used in the definition.) -/
def IsTrinatural (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
    (η : ∀ A : C, F.obj A ⟶ G.obj A) : Prop :=
  ∀ T ∈ distTriang C,
    F.map T.mor₁ ≫ η T.obj₂ = η T.obj₁ ≫ G.map T.mor₁ ∧
    F.map T.mor₂ ≫ η T.obj₃ = η T.obj₂ ≫ G.map T.mor₂ ∧
    (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫ (η T.obj₁)⟦(1 : ℤ)⟧' =
      η T.obj₃ ≫ G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁

section B7

variable {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]

/-- **Lemma B.7** (`lem:transnat_is_trinat`).  A family `η A : F A ⟶ G A` is a trinatural
transformation `(F, ξ) ⇒ (G, ζ)` if and only if it is a transnatural transformation, i.e.
natural and compatible with `ξ = F.commShiftIso 1` and `ζ = G.commShiftIso 1`
(`ζ ∘ η_T = T η ∘ ξ`).  The paper assumes `F`, `G` triangulated; this is not needed. -/
theorem lemma_B7 (η : ∀ A : C, F.obj A ⟶ G.obj A) :
    IsTrinatural F G η ↔
      (∀ ⦃A B : C⦄ (f : A ⟶ B), F.map f ≫ η B = η A ≫ G.map f) ∧
        ∀ A : C, η (A⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app A =
          (F.commShiftIso (1 : ℤ)).hom.app A ≫ (η A)⟦(1 : ℤ)⟧' := by
  constructor
  · intro h
    refine ⟨fun A B f => ?_, fun A => ?_⟩
    · obtain ⟨Z, g, k, hT⟩ := distinguished_cocone_triangle f
      exact (h _ hT).1
    · have h3 : (F.map (𝟙 (A⟦(1 : ℤ)⟧)) ≫ (F.commShiftIso (1 : ℤ)).hom.app A) ≫
          (η A)⟦(1 : ℤ)⟧' =
          η (A⟦(1 : ℤ)⟧) ≫ G.map (𝟙 (A⟦(1 : ℤ)⟧)) ≫ (G.commShiftIso (1 : ℤ)).hom.app A :=
        (h _ (contractible_distinguished₂ A)).2.2
      rw [F.map_id, G.map_id, id_comp, id_comp] at h3
      exact h3.symm
  · rintro ⟨hnat, hsh⟩ T _
    refine ⟨hnat _, hnat _, ?_⟩
    rw [assoc, ← hsh, reassoc_of% (hnat T.mor₃)]

/-- A natural transformation compatible with the shifts (Mathlib's `NatTrans.CommShift`) is
trinatural. -/
lemma isTrinatural_of_commShift (α : F ⟶ G) [NatTrans.CommShift α ℤ] :
    IsTrinatural F G α.app :=
  (lemma_B7 α.app).2 ⟨fun _ _ f => α.naturality f,
    fun X => (NatTrans.shift_app_comm α (1 : ℤ) X).symm⟩

/-- A trinatural natural transformation is compatible with all shifts. -/
lemma commShift_of_isTrinatural (α : F ⟶ G) (h : IsTrinatural F G α.app) :
    NatTrans.CommShift α ℤ := by
  have h1 := ((lemma_B7 α.app).1 h).2
  refine natTransCommShift_of_one α ⟨?_⟩
  ext X
  exact (h1 X).symm

/-- The inverse of a trinatural isomorphism is trinatural: trinatural isomorphisms are the
2-isomorphisms of `Triang`. -/
lemma IsTrinatural.inv (e : F ≅ G) (h : IsTrinatural F G e.hom.app) :
    IsTrinatural G F e.inv.app := by
  have := commShift_of_isTrinatural e.hom h
  exact isTrinatural_of_commShift e.inv

variable [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- **Lemma B.7** (`lem:transnat_is_trinat`) for a natural transformation `α : F ⟶ G` of
triangulated functors, compared with the other renderings in the repository and Mathlib:
(1) `α` is trinatural (Definition B.9); (2) `α` is transnatural for the degree-1
translation isomorphisms (Definition B.1(5)); (3) Mathlib's `NatTrans.CommShift α ℤ`
(compatibility with the shift in every degree); (4) `α` underlies a
`RelativeFM.Trinatural F G`.  (3) ⇒ (4) is `Trinatural.ofNatTrans`. -/
theorem lemma_B7_natTrans [F.IsTriangulated] [G.IsTriangulated] (α : F ⟶ G) :
    List.TFAE [IsTrinatural F G α.app,
      Trans.IsTransnatural (F.commShiftIso (1 : ℤ)) (G.commShiftIso (1 : ℤ)) α,
      NatTrans.CommShift α ℤ, ∃ t : Trinatural F G, t.toNatTrans = α] := by
  tfae_have 1 ↔ 2 := by
    rw [lemma_B7]
    exact ⟨fun h => h.2, fun h => ⟨fun _ _ f => α.naturality f, h⟩⟩
  tfae_have 1 → 3 := commShift_of_isTrinatural α
  tfae_have 3 → 1 := fun _ => isTrinatural_of_commShift α
  tfae_have 3 → 4 := fun _ => ⟨Trinatural.ofNatTrans α, rfl⟩
  tfae_have 4 → 2 := by
    rintro ⟨t, rfl⟩ X
    exact (t.comm_shift X 1).symm
  tfae_finish

end B7

section B10

variable [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D]

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.CommShift ℤ] [F.IsTriangulated]

/-- **Lemma B.10(1)** (`lem:triadjoint_iff_adjoint`), existence.  Let `F` be a triangulated
functor and `adj : F ⊣ G` an adjunction in `Cat`.  With the `CommShift` structure
`adj.rightAdjointCommShift ℤ` of Mathlib, `G` is triangulated, `adj` is an adjunction of
triangulated functors (`Adjunction.IsTriangulated`), and the unit and counit are
trinatural; so `(F, ξ) ⊣ (G, ζ)` in `Triang`. -/
theorem lemma_B10_exists :
    letI := adj.rightAdjointCommShift ℤ
    G.IsTriangulated ∧ adj.IsTriangulated ∧
      IsTrinatural (𝟭 C) (F ⋙ G) adj.unit.app ∧ IsTrinatural (G ⋙ F) (𝟭 D) adj.counit.app := by
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have := adj.isTriangulated_rightAdjoint
  exact ⟨inferInstance, Adjunction.IsTriangulated.mk' adj, isTrinatural_of_commShift _,
    isTrinatural_of_commShift _⟩

omit [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] [F.IsTriangulated] in
/-- **Lemma B.10(1)** (`lem:triadjoint_iff_adjoint`), uniqueness.  Any `CommShift ℤ`
structure on the right adjoint `G` for which the unit is trinatural is Mathlib's
`adj.rightAdjointCommShift ℤ`.  (The paper's uniqueness is among `ζ` for which `(G, ζ)` is
triangulated and both `η` and `ε` are trinatural; neither of the extra conditions is
needed.) -/
theorem lemma_B10_unique [inst : G.CommShift ℤ]
    (hη : IsTrinatural (𝟭 C) (F ⋙ G) adj.unit.app) :
    inst = adj.rightAdjointCommShift ℤ := by
  have := commShift_of_isTrinatural _ hη
  have : adj.CommShift ℤ := Adjunction.CommShift.mk' adj ℤ inferInstance
  have key : ∀ n : ℤ, G.commShiftIso n = Adjunction.RightAdjointCommShift.iso adj n := by
    intro n
    refine Adjunction.CommShift.compatibilityUnit_unique_right adj (F.commShiftIso n) _ _
      (fun X => ?_) (Adjunction.RightAdjointCommShift.compatibilityUnit_iso adj n)
    rw [← adj.unit_app_commShiftIso_hom_app ℤ n X, Functor.commShiftIso_comp_hom_app]
  revert key
  cases inst with
  | mk f h0 hadd =>
    intro key
    unfold Adjunction.rightAdjointCommShift
    congr 1
    funext n
    exact key n

omit [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] [F.IsTriangulated] in
/-- **Lemma B.10(1)** (`lem:triadjoint_iff_adjoint`): the translation isomorphism of the
right adjoint is the one of Lemma B.5, in every degree: if the unit is trinatural then
`(G.commShiftIso n)⁻¹` is the mate of `F.commShiftIso n`. -/
theorem lemma_B10_commShiftIso [G.CommShift ℤ]
    (hη : IsTrinatural (𝟭 C) (F ⋙ G) adj.unit.app) (n : ℤ) :
    (G.commShiftIso n).inv = mate adj adj (F.commShiftIso n).hom := by
  have := commShift_of_isTrinatural _ hη
  have hu : Trans.UnitTransnatural adj (F.commShiftIso n) (G.commShiftIso n) := by
    intro X
    have := NatTrans.shift_app_comm adj.unit n X
    simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app,
      Functor.id_obj, Functor.comp_obj, id_comp] at this
    simpa using this.symm
  have := ((Trans.lemma_B4 adj (F.commShiftIso n) (G.commShiftIso n)).out 2 0).1 hu
  exact this.symm

/-- **Lemma B.10(2)** (`lem:triequiv_iff_equiv`).  A triangulated functor `F` is an
equivalence in `Cat` if and only if it is an equivalence in `Triang`: there are a
triangulated functor `G` and trinatural isomorphisms `𝟭 ≅ F ⋙ G`, `G ⋙ F ≅ 𝟭`. -/
theorem lemma_B10_equivalence :
    F.IsEquivalence ↔
      ∃ (G : D ⥤ C) (_ : G.CommShift ℤ), G.IsTriangulated ∧
        ∃ (u : 𝟭 C ≅ F ⋙ G) (v : G ⋙ F ≅ 𝟭 D),
          IsTrinatural (𝟭 C) (F ⋙ G) u.hom.app ∧ IsTrinatural (G ⋙ F) (𝟭 D) v.hom.app := by
  constructor
  · intro _
    let adj : F ⊣ F.inv := F.asEquivalence.toAdjunction
    obtain ⟨h1, -, h3, h4⟩ := lemma_B10_exists adj
    exact ⟨F.inv, adj.rightAdjointCommShift ℤ, h1, F.asEquivalence.unitIso,
      F.asEquivalence.counitIso, h3, h4⟩
  · rintro ⟨G, _, _, u, v, -, -⟩
    exact (CategoryTheory.Equivalence.mk F G u v).isEquivalence_functor

end B10

end Triangulated

end RelativeFM
