/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as
described in the file LICENSE. -/
import FourierMukai.Prelim.Mates
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Tactic.TFAE

/-!
# The calculus of mates in `Cat`

This file continues `FourierMukai.Prelim.Mates` with the remaining categorical
results on mates and conjugates from Section 7 of E. Guisado Villalgordo and
P. Lank, *Relative Fourier--Mukai theory for algebraic spaces* (GL26).

* **Lemma 7.2(1)** (`lem:mates_bijection`, item 1): the square of Hom-bijections
  `Hom(F'H, KF) ≅ Hom(H, G'KF)`, `Hom(F'H, KF) ≅ Hom(F'HG, K)`,
  `Hom(H, G'KF) ≅ Hom(HG, G'K)`, `Hom(F'HG, K) ≅ Hom(HG, G'K)` commutes, and the
  common diagonal is the mate map `mate` of `Prelim/Mates.lean`
  (`mates_hom_square`, `mates_hom_square_eq_mate`).  The four bijections are the
  Hom-equivalences of the whiskered adjunctions on functor categories
  (`Adjunction.whiskerLeft`, `Adjunction.whiskerRight`), i.e. postcomposition
  with `F' ⊣ G'` and precomposition with `F ⊣ G`.
* **Lemma 7.4** (`lem:morph_adj`): `lemma_7_4`, the equivalence of (1) mates,
  (2) the counit square, (3) the unit square and (4) the ladder of Hom-sets.
  The equivalences (1) ⇔ (2) and (1) ⇔ (3) are deduced from Lemma 7.2(1): (2) says
  that `α` and `β` agree in the corner `Hom(F'HG, K)` of the square and (3) that
  they agree in the corner `Hom(H, G'KF)`.
* **Remark 7.5(1)** (`rem:unit_counit_is_mate`): `unit_isMate`, `counit_isMate`.
* **Lemma 7.6** (`lem:taking_conjugates_is_taking_mates_twice`):
  `lemma_7_6`.  This is Mathlib's `iterated_mateEquiv_conjugateEquiv`, restated as
  an equality of the two bijections.
* **Lemma 7.9** (`lem:conjugates_are_functorial`): `lemma_7_9_id`,
  `lemma_7_9_comp`, reduced to Mathlib's `conjugateEquiv_id` and
  `conjugateEquiv_comp` (proved there via `mateEquiv_vcomp`, not via the double
  categories of Lemma 7.8, which is not formalized).

Nothing is assumed: everything is proved from Mathlib.

## Deviations from the paper

* The paper states these results in an arbitrary 2-category `𝒯`; here they are
  stated and proved for the 2-category of categories (Mathlib categories,
  functors and natural transformations).  Part (4) of Lemma 7.4 is in the paper
  only for `Cat` anyway.
* Mathlib composes functors diagrammatically: the paper's `F'H` is `H ⋙ F'`,
  `KF` is `F ⋙ K`, `HG` is `G ⋙ H` and `G'K` is `K ⋙ G'`.  Whiskerings and the
  associators/unitors of `Cat`, which are identities in the paper, are written
  out (`Functor.associator`, `Functor.leftUnitor`, `Functor.rightUnitor`).
* "Mates" (Definition 7.3(1)) is `mate adj adj' α = β` with `mate` from
  `Prelim/Mates.lean` (definitionally Mathlib's `mateEquiv`).  "Conjugates"
  (Definition 7.3(2)) is Mathlib's `conjugateEquiv`, which is `mateEquiv` with
  identity vertical functors, composed with the unitors.
-/

@[expose] public section

namespace RelativeFM

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section MatesSquare

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {B : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} B]
  {F : C ⥤ D} {G : D ⥤ C} {F' : E ⥤ B} {G' : B ⥤ E}
  {H : C ⥤ E} {K : D ⥤ B}

/-! ### Lemma 7.2(1): the square of Hom-bijections -/

/-- The top bijection `Hom(F'H, KF) ≅ Hom(H, G'KF)` of **Lemma 7.2(1)**
(`lem:mates_bijection`): the Hom-equivalence of the adjunction
`(- ⋙ F') ⊣ (- ⋙ G')` induced by `adj' : F' ⊣ G'` on functor categories. -/
def matesHomTop (adj' : F' ⊣ G') : (H ⋙ F' ⟶ F ⋙ K) ≃ (H ⟶ F ⋙ K ⋙ G') :=
  (adj'.whiskerRight C).homEquiv H (F ⋙ K)

/-- The left bijection of **Lemma 7.2(1)** (`lem:mates_bijection`), in the
direction `Hom(F'HG, K) ≅ Hom(F'H, KF)`: the Hom-equivalence of the adjunction
`(G ⋙ -) ⊣ (F ⋙ -)` induced by `adj : F ⊣ G`.  The paper's arrow is its inverse. -/
def matesHomLeft (adj : F ⊣ G) : (G ⋙ H ⋙ F' ⟶ K) ≃ (H ⋙ F' ⟶ F ⋙ K) :=
  (adj.whiskerLeft B).homEquiv (H ⋙ F') K

/-- The right bijection of **Lemma 7.2(1)** (`lem:mates_bijection`), in the
direction `Hom(HG, G'K) ≅ Hom(H, G'KF)`: the Hom-equivalence of the adjunction
`(G ⋙ -) ⊣ (F ⋙ -)` induced by `adj : F ⊣ G`.  The paper's arrow is its inverse. -/
def matesHomRight (adj : F ⊣ G) : (G ⋙ H ⟶ K ⋙ G') ≃ (H ⟶ F ⋙ K ⋙ G') :=
  (adj.whiskerLeft E).homEquiv H (K ⋙ G')

/-- The bottom bijection `Hom(F'HG, K) ≅ Hom(HG, G'K)` of **Lemma 7.2(1)**
(`lem:mates_bijection`): the Hom-equivalence of `(- ⋙ F') ⊣ (- ⋙ G')`. -/
def matesHomBottom (adj' : F' ⊣ G') : (G ⋙ H ⋙ F' ⟶ K) ≃ (G ⋙ H ⟶ K ⋙ G') :=
  (adj'.whiskerRight D).homEquiv (G ⋙ H) K

/-- The clockwise composite of the square of **Lemma 7.2(1)** (top, then right)
is the mate map. -/
theorem matesHomRight_symm_matesHomTop (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) :
    (matesHomRight adj).symm (matesHomTop adj' α) = mate adj adj' α := by
  ext d
  rw [matesHomRight, matesHomTop, Adjunction.homEquiv_counit, Adjunction.homEquiv_unit]
  simp

/-- The counterclockwise composite of the square of **Lemma 7.2(1)** (left, then
bottom) is the mate map. -/
theorem matesHomBottom_matesHomLeft_symm (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) :
    matesHomBottom adj' ((matesHomLeft adj).symm α) = mate adj adj' α := by
  ext d
  rw [matesHomBottom, matesHomLeft, Adjunction.homEquiv_counit, Adjunction.homEquiv_unit]
  simp

/-- **Lemma 7.2(1)** (`lem:mates_bijection`, item 1).  The square of Hom-bijections
```
Hom(F'H, KF)  ──≅──>  Hom(H, G'KF)
     │≅                    │≅
Hom(F'HG, K)  ──≅──>  Hom(HG, G'K)
```
commutes.  Paper notation: `F'H = H ⋙ F'`, `KF = F ⋙ K`, `HG = G ⋙ H`,
`G'K = K ⋙ G'`.  Stated for the 2-category of categories. -/
theorem mates_hom_square (adj : F ⊣ G) (adj' : F' ⊣ G') (α : H ⋙ F' ⟶ F ⋙ K) :
    matesHomBottom adj' ((matesHomLeft adj).symm α) =
      (matesHomRight adj).symm (matesHomTop adj' α) := by
  rw [matesHomBottom_matesHomLeft_symm, matesHomRight_symm_matesHomTop]

/-- **Lemma 7.2(1)–(2)** (`lem:mates_bijection`): the diagonal of the square of
Hom-bijections is the right-mate map `α ↦ (G'Kε) ∘ (G'αG) ∘ (η'HG)`. -/
theorem mates_hom_square_eq_mate (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) :
    (matesHomRight adj).symm (matesHomTop adj' α) = mate adj adj' α :=
  matesHomRight_symm_matesHomTop adj adj' α

/-! ### Lemma 7.4 -/

/-- Condition (2) of **Lemma 7.4** (`lem:morph_adj`): the counit square
`K ε ∘ α G = ε' K ∘ F' β : F'HG ⟶ K`. -/
def CounitSquare (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) (β : G ⋙ H ⟶ K ⋙ G') : Prop :=
  whiskerLeft G α ≫ (associator G F K).inv ≫ whiskerRight adj.counit K ≫
      K.leftUnitor.hom =
    (associator G H F').inv ≫ whiskerRight β F' ≫ (associator K G' F').hom ≫
      whiskerLeft K adj'.counit ≫ K.rightUnitor.hom

/-- Condition (3) of **Lemma 7.4** (`lem:morph_adj`): the unit square
`G' α ∘ η' H = β F ∘ H η : H ⟶ G'KF`. -/
def UnitSquare (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) (β : G ⋙ H ⟶ K ⋙ G') : Prop :=
  H.rightUnitor.inv ≫ whiskerLeft H adj'.unit ≫ (associator H F' G').inv ≫
      whiskerRight α G' ≫ (associator F K G').hom =
    H.leftUnitor.inv ≫ whiskerRight adj.unit H ≫ (associator F G H).hom ≫
      whiskerLeft F β

/-- Condition (4) of **Lemma 7.4** (`lem:morph_adj`), for the 2-category of
categories: for all `c : C`, `d : D`, the ladder
`𝒟(Fc, d) ≅ 𝒞(c, Gd)`, `K`, `α_c^*`, `H`, `β_{d,*}`, `𝒟'(F'Hc, Kd) ≅ 𝒞'(Hc, G'Kd)`
commutes; the horizontal bijections are `Adjunction.homEquiv` (induced by the
units). -/
def HomLadder (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) (β : G ⋙ H ⟶ K ⋙ G') : Prop :=
  ∀ (c : C) (d : D) (f : F.obj c ⟶ d),
    adj'.homEquiv (H.obj c) (K.obj d) (α.app c ≫ K.map f) =
      H.map (adj.homEquiv c d f) ≫ β.app d

/-- Condition (2) of Lemma 7.4 says that `α` and `β` have the same image in the
corner `Hom(F'HG, K)` of the square of Lemma 7.2(1). -/
theorem counitSquare_iff (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) (β : G ⋙ H ⟶ K ⋙ G') :
    CounitSquare adj adj' α β ↔ (matesHomLeft adj).symm α = (matesHomBottom adj').symm β := by
  rw [CounitSquare, matesHomLeft, matesHomBottom, Adjunction.homEquiv_counit,
    Adjunction.homEquiv_counit]
  constructor <;> intro h <;> ext d <;> have := congr_app h d <;> simpa using this

/-- Condition (3) of Lemma 7.4 says that `α` and `β` have the same image in the
corner `Hom(H, G'KF)` of the square of Lemma 7.2(1). -/
theorem unitSquare_iff (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) (β : G ⋙ H ⟶ K ⋙ G') :
    UnitSquare adj adj' α β ↔ matesHomTop adj' α = matesHomRight adj β := by
  rw [UnitSquare, matesHomTop, matesHomRight, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit]
  constructor <;> intro h <;> ext c <;> have := congr_app h c <;> simpa using this

/-- (1) ⇔ (2) of **Lemma 7.4** (`lem:morph_adj`). -/
theorem mate_eq_iff_counitSquare (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) (β : G ⋙ H ⟶ K ⋙ G') :
    mate adj adj' α = β ↔ CounitSquare adj adj' α β := by
  rw [counitSquare_iff, ← matesHomBottom_matesHomLeft_symm, Equiv.eq_symm_apply]

/-- (1) ⇔ (3) of **Lemma 7.4** (`lem:morph_adj`). -/
theorem mate_eq_iff_unitSquare (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) (β : G ⋙ H ⟶ K ⋙ G') :
    mate adj adj' α = β ↔ UnitSquare adj adj' α β := by
  rw [unitSquare_iff, ← matesHomRight_symm_matesHomTop, Equiv.symm_apply_eq]

/-- (3) ⇔ (4) of **Lemma 7.4** (`lem:morph_adj`). -/
theorem unitSquare_iff_homLadder (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) (β : G ⋙ H ⟶ K ⋙ G') :
    UnitSquare adj adj' α β ↔ HomLadder adj adj' α β := by
  unfold UnitSquare HomLadder
  constructor
  · intro h c d f
    have hc : adj'.unit.app (H.obj c) ≫ G'.map (α.app c) =
        H.map (adj.unit.app c) ≫ β.app (F.obj c) := by
      simpa using NatTrans.congr_app h c
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, G'.map_comp,
      ← Category.assoc, hc, H.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact (β.naturality f).symm
  · intro h
    ext c
    have hc := h c (F.obj c) (𝟙 _)
    simp only [Adjunction.homEquiv_unit, Functor.map_id] at hc
    simpa using hc

/-- **Lemma 7.4** (`lem:morph_adj`).  For `α : F'H ⟶ KF` and `β : HG ⟶ G'K`
(Mathlib: `H ⋙ F' ⟶ F ⋙ K` and `G ⋙ H ⟶ K ⋙ G'`) the following are equivalent:
(1) `α` and `β` are mates; (2) the counit square commutes; (3) the unit square
commutes; (4) the ladder of Hom-sets commutes for all `c`, `d`.

Stated for the 2-category of categories (in which the paper also has (4)). -/
theorem lemma_7_4 (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : H ⋙ F' ⟶ F ⋙ K) (β : G ⋙ H ⟶ K ⋙ G') :
    List.TFAE [mate adj adj' α = β, CounitSquare adj adj' α β,
      UnitSquare adj adj' α β, HomLadder adj adj' α β] := by
  tfae_have 1 ↔ 2 := mate_eq_iff_counitSquare adj adj' α β
  tfae_have 1 ↔ 3 := mate_eq_iff_unitSquare adj adj' α β
  tfae_have 3 ↔ 4 := unitSquare_iff_homLadder adj adj' α β
  tfae_finish

end MatesSquare

/-! ### Remark 7.5(1) -/

section UnitCounit

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- **Remark 7.5(1)** (`rem:unit_counit_is_mate`), first half: `(id_F, η)` are mates
under the square with top `1_C`, bottom `F`, left `1_C ⊣ 1_C` and right `F ⊣ G`.
(`𝟭 C ⋙ 𝟭 C` and `𝟭 C` are identified by the unitor.) -/
theorem unit_isMate (adj : F ⊣ G) :
    mate Adjunction.id adj (𝟙 (𝟭 C ⋙ F)) = (𝟭 C).leftUnitor.hom ≫ adj.unit := by
  ext c
  simp

/-- **Remark 7.5(1)** (`rem:unit_counit_is_mate`), second half: `(ε, id_G)` are mates
under the square with top `G`, bottom `1_D`, left `1_D ⊣ 1_D` and right `F ⊣ G`.
(`𝟭 D ⋙ 𝟭 D` and `𝟭 D` are identified by the unitor.) -/
theorem counit_isMate (adj : F ⊣ G) :
    mate Adjunction.id adj (adj.counit ≫ (𝟭 D).leftUnitor.inv) = 𝟙 (𝟭 D ⋙ G) := by
  ext d
  simp

end UnitCounit

/-! ### Lemma 7.6 -/

section ConjugatesTwice

variable {X' : Type u₁} {X : Type u₂} {Z' : Type u₃} {Z : Type u₄}
  [Category.{v₁} X'] [Category.{v₂} X] [Category.{v₃} Z'] [Category.{v₄} Z]
  {q'Lower : X' ⥤ X} {p'Lower : X' ⥤ Z'} {pLower : X ⥤ Z} {qLower : Z' ⥤ Z}
  {q'Upper : X ⥤ X'} {p'Upper : Z' ⥤ X'} {pUpper : Z ⥤ X} {qUpper : Z ⥤ Z'}

/-- **Lemma 7.6** (`lem:taking_conjugates_is_taking_mates_twice`).  For a square of
functors `q'_* : X' ⥤ X`, `p'_* : X' ⥤ Z'`, `p_* : X ⥤ Z`, `q_* : Z' ⥤ Z` with left
adjoints `u^* ⊣ u_*`, taking the right conjugate of a 2-cell `p'^* q^* ⟶ q'^* p^*`
(Mathlib: `q^* ⋙ p'^* ⟶ p^* ⋙ q'^*`) with respect to the composite adjunctions
`p'^* q^* ⊣ q_* p'_*` and `q'^* p^* ⊣ p_* q'_*` equals taking first the right mate
with respect to `p'^* ⊣ p'_*`, `p^* ⊣ p_*`, and then the right mate with respect to
`q^* ⊣ q_*`, `q'^* ⊣ q'_*`.

Here the three bijections are given as `Equiv`s and their equality is the
commutativity of the paper's triangle.  Stated for the 2-category of categories;
the proof is Mathlib's `iterated_mateEquiv_conjugateEquiv`. -/
theorem lemma_7_6 (adjp : pUpper ⊣ pLower) (adjp' : p'Upper ⊣ p'Lower)
    (adjq : qUpper ⊣ qLower) (adjq' : q'Upper ⊣ q'Lower) :
    (matesEquiv (H := qUpper) (K := q'Upper) adjp adjp').trans
        (matesEquiv (H := pLower) (K := p'Lower) adjq' adjq) =
      conjugateEquiv (adjp.comp adjq') (adjq.comp adjp') := by
  ext α : 1
  exact iterated_mateEquiv_conjugateEquiv adjp adjp' adjq adjq' α

end ConjugatesTwice

/-! ### Lemma 7.9 -/

section ConjugatesFunctorial

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {F F' F'' : C ⥤ D} {G G' G'' : D ⥤ C}

/-- **Lemma 7.9** (`lem:conjugates_are_functorial`), first formula: the identity
is self-conjugate.  This is Mathlib's `conjugateEquiv_id`. -/
theorem lemma_7_9_id (adj : F ⊣ G) : conjugateEquiv adj adj (𝟙 F) = 𝟙 G :=
  conjugateEquiv_id adj

/-- **Lemma 7.9** (`lem:conjugates_are_functorial`), second formula: if
`(α : F' ⟶ F, β : G ⟶ G')` and `(α' : F'' ⟶ F', β' : G' ⟶ G'')` are pairs of
conjugates, then so is `(α ∘ α', β' ∘ β)` (Mathlib: `(α' ≫ α, β ≫ β')`).
This is Mathlib's `conjugateEquiv_comp`; the paper's proof via Lemma 7.8 (double
categories) is not used. -/
theorem lemma_7_9_comp (adj : F ⊣ G) (adj' : F' ⊣ G') (adj'' : F'' ⊣ G'')
    {α : F' ⟶ F} {β : G ⟶ G'} {α' : F'' ⟶ F'} {β' : G' ⟶ G''}
    (h : conjugateEquiv adj adj' α = β) (h' : conjugateEquiv adj' adj'' α' = β') :
    conjugateEquiv adj adj'' (α' ≫ α) = β ≫ β' := by
  rw [← h, ← h', conjugateEquiv_comp]

end ConjugatesFunctorial

end RelativeFM
