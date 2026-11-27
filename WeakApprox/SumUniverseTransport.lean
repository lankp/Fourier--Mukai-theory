/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.SumUniverse
import WeakApprox.Recollement
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Transport of the sum-universe notions along triangulated equivalences

Source: Lank--Pauwels, *Gluing weak approximability along recollements* (LP26), Definition 2.1
(`def:weak_approx`), §2.1.2 and Setup 4.1 (`setup:recollement`).

For a triangulated equivalence `e : C ≌ D` whose two categories may have **different Hom
universes**, the notions of `WeakApprox/SumUniverse.lean` for a fixed coproduct universe `w`
correspond: compactness (`isCompactAb_functor_obj_iff`, in `SumUniverse.lean`), zero detection
by the shifts (`isPaperGenerator_functor_obj_iff`), `Coprod.{w}` and `envelope.{w}`
(`Coprod.map_obj`, `envelope_map_obj`), weak approximability (`satisfiesPaperWA_iff_of_equivalence`),
and recollements (`Recollement.transport`).  With the small model of
`WeakApprox/SmallModel.lean` this reduces statements about a locally `w`-small category to
statements about a category with Hom universe `w`.

## Assumptions

None.  Mathlib only.
-/

@[expose] public section

namespace RelativeWeakApprox.SumUniverse

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

universe w v v' u u' vA vB vD vA' vB' vD' uA uB uD uA' uB' uD' vZ vU vZ' vU' uZ uU uZ' uU'

section Transport

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- Coproducts indexed by `Type w` transport along an equivalence. -/
theorem hasCoproducts_of_equivalence (e : C ≌ D) [HasCoproducts.{w} C] :
    HasCoproducts.{w} D := fun _ =>
  Adjunction.hasColimitsOfShape_of_equivalence e.inverse

/-! ### `Coprod` and envelopes along a triangulated functor -/

/-- A triangulated functor preserving `Type w`-indexed coproducts maps `Coprod.{w} P` into
`Coprod.{w} Q` as soon as it maps `P` into it. -/
theorem Coprod.map_obj (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F]
    {P : ObjectProperty C} {Q : ObjectProperty D} (h : ∀ X, P X → Coprod.{w} Q (F.obj X))
    {X : C} (hX : Coprod.{w} P X) : Coprod.{w} Q (F.obj X) := by
  induction hX with
  | of_mem X hX => exact h X hX
  | of_isoClosure e _ ih => exact .of_isoClosure (F.mapIso e) ih
  | of_colimitPresentation pres _ ih => exact .of_colimitPresentation (pres.map F) ih
  | of_extension T hT _ _ ih₁ ih₃ =>
    exact .of_extension (F.mapTriangle.obj T) (F.map_distinguished T hT) ih₁ ih₃

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- A functor commuting with the shift maps `H[a,b]` into `F(H)[a,b]`. -/
theorem shiftInterval_map_obj (F : C ⥤ D) [F.CommShift ℤ] {H X : C} {a b : ℤ}
    (hX : shiftInterval H a b X) : shiftInterval (F.obj H) a b (F.obj X) := by
  obtain ⟨k, hk₁, hk₂, ⟨e⟩⟩ := hX
  exact ⟨k, hk₁, hk₂, ⟨F.mapIso e ≪≫ (F.commShiftIso (-k)).app H⟩⟩

/-- A triangulated functor preserving `Type w`-indexed coproducts maps `⟨H⟩^[a,b]` into
`⟨F H⟩^[a,b]`. -/
theorem envelope_map_obj (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F] {H X : C} {a b : ℤ}
    (hX : envelope.{w} H a b X) : envelope.{w} (F.obj H) a b (F.obj X) := by
  obtain ⟨Y, hY, ⟨r⟩⟩ := hX
  exact ⟨F.obj Y, Coprod.map_obj F (fun Z hZ => .of_mem _ (shiftInterval_map_obj F hZ)) hY,
    ⟨r.map F⟩⟩

/-! ### Zero detection -/

omit [Pretriangulated C] in
/-- Zero detection by the shifts is invariant under isomorphism. -/
theorem isPaperGenerator_of_iso {G G' : C} (e : G ≅ G') (hG : IsPaperGenerator G) :
    IsPaperGenerator G' := by
  intro E hE
  refine hG fun n f => ?_
  have h := hE n ((shiftFunctor C n).map e.inv ≫ f)
  rw [← cancel_epi ((shiftFunctor C n).map e.inv)]
  simpa using h

variable (e : C ≌ D) [e.functor.Additive] [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [e.inverse.CommShift ℤ] in
/-- An equivalence commuting with the shift carries a zero-detecting object to a
zero-detecting object. -/
theorem isPaperGenerator_functor_obj {G : C} (hG : IsPaperGenerator G) :
    IsPaperGenerator (e.functor.obj G) := by
  intro E hE
  have hz : IsZero (e.inverse.obj E) := by
    refine hG fun n f => ?_
    apply e.functor.map_injective
    rw [Functor.map_zero]
    have h := hE n ((e.functor.commShiftIso n).inv.app G ≫ e.functor.map f ≫
      e.counitIso.hom.app E)
    rw [← cancel_epi ((e.functor.commShiftIso n).inv.app G),
      ← cancel_mono (e.counitIso.hom.app E)]
    simpa [Category.assoc] using h
  exact IsZero.of_iso (Functor.map_isZero e.functor hz) (e.counitIso.app E).symm

omit [Pretriangulated C] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- **Zero detection is invariant under equivalences commuting with the shift**, across Hom
universes. -/
theorem isPaperGenerator_functor_obj_iff (G : C) :
    IsPaperGenerator (e.functor.obj G) ↔ IsPaperGenerator G := by
  have : e.inverse.Additive := e.toAdjunction.right_adjoint_additive
  refine ⟨fun h => ?_, isPaperGenerator_functor_obj e⟩
  let : e.symm.functor.CommShift ℤ := inferInstanceAs (e.inverse.CommShift ℤ)
  let : e.symm.inverse.CommShift ℤ := inferInstanceAs (e.functor.CommShift ℤ)
  have : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
  have h' : IsPaperGenerator (e.symm.functor.obj (e.functor.obj G)) :=
    isPaperGenerator_functor_obj e.symm h
  intro E hE
  exact isPaperGenerator_of_iso (e.unitIso.app G).symm h' hE

/-! ### `t`-structures -/

variable [e.functor.IsTriangulated]

/-- **Transport of a `t`-structure along a triangulated equivalence** `e : C ≌ D`, across Hom
universes: `Y ∈ D^{≤ n}` iff `e⁻¹ Y ∈ C^{≤ n}`, and likewise for `D^{≥ n}`.  (The
repository's `transportTStructure` is the same construction for a functor with a chosen
inverse and equal Hom universes.) -/
noncomputable def transportTStructure (t : TStructure C) : TStructure D :=
  { le := fun n Y => t.le n (e.inverse.obj Y)
    ge := fun n Y => t.ge n (e.inverse.obj Y)
    le_isClosedUnderIsomorphisms := fun n =>
      ⟨fun e' h => (t.le n).prop_of_iso (e.inverse.mapIso e') h⟩
    ge_isClosedUnderIsomorphisms := fun n =>
      ⟨fun e' h => (t.ge n).prop_of_iso (e.inverse.mapIso e') h⟩
    le_shift := fun n a n' h X hX =>
      (t.le n').prop_of_iso ((e.inverse.commShiftIso a).app X).symm
        (t.le_shift n a n' h _ hX)
    ge_shift := fun n a n' h X hX =>
      (t.ge n').prop_of_iso ((e.inverse.commShiftIso a).app X).symm
        (t.ge_shift n a n' h _ hX)
    zero' := by
      intro X Y f hX hY
      have : e.inverse.Additive := e.toAdjunction.right_adjoint_additive
      apply e.inverse.map_injective
      rw [e.inverse.map_zero]
      exact t.zero' (e.inverse.map f) hX hY
    le_zero_le := fun _ hX => t.le_zero_le _ hX
    ge_one_le := fun _ hX => t.ge_one_le _ hX
    exists_triangle_zero_one := fun A => by
      obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ := t.exists_triangle_zero_one (e.inverse.obj A)
      refine ⟨e.functor.obj X, e.functor.obj Y,
        (t.le 0).prop_of_iso (e.unitIso.app X) hX,
        (t.ge 1).prop_of_iso (e.unitIso.app Y) hY,
        e.functor.map f ≫ e.counitIso.hom.app A, e.counitIso.inv.app A ≫ e.functor.map g,
        e.functor.map h ≫ (e.functor.commShiftIso (1 : ℤ)).hom.app X, ?_⟩
      exact isomorphic_distinguished _ (e.functor.map_distinguished _ hT) _
        (Triangle.isoMk _ _ (Iso.refl _) (e.counitIso.app A).symm (Iso.refl _)
          (by simp) (by simp) (by simp)) }

@[simp]
theorem transportTStructure_le (t : TStructure C) (n : ℤ) (Y : D) :
    (transportTStructure e t).le n Y ↔ t.le n (e.inverse.obj Y) := Iff.rfl

/-! ### Weak approximation data -/

/-- **Transport of weak approximation data** (Definition 2.1, `def:weak_approx`) along a
triangulated equivalence, across Hom universes, for a fixed coproduct universe `w`. -/
noncomputable def PaperWeakApproximationData.transport
    (W : PaperWeakApproximationData.{w} C) : PaperWeakApproximationData.{w} D where
  G := e.functor.obj W.G
  t := transportTStructure e W.t
  A := W.A
  A_pos := W.A_pos
  G_compact := (isCompactAb_functor_obj_iff e W.G).2 W.G_compact
  G_paperGenerates := isPaperGenerator_functor_obj e W.G_paperGenerates
  G_mem_le := (W.t.le W.A).prop_of_iso (e.unitIso.app W.G) W.G_mem_le
  hom_vanishing := by
    intro Y hY f
    have : e.inverse.Additive := e.toAdjunction.right_adjoint_additive
    have h := W.hom_vanishing hY (e.unitIso.hom.app W.G ≫ e.inverse.map f)
    apply e.inverse.map_injective
    rw [e.inverse.map_zero, ← cancel_epi (e.unitIso.hom.app W.G), h, Limits.comp_zero]
  exists_triangle := by
    intro F hF
    have : ∀ J : Type w, PreservesColimitsOfShape (Discrete J) e.functor := fun _ =>
      e.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
    obtain ⟨E, D', f, g, h, hT, hE, hD'⟩ := W.exists_triangle (e.inverse.obj F) hF
    refine ⟨e.functor.obj E, e.functor.obj D', e.functor.map f ≫ e.counitIso.hom.app F,
      e.counitIso.inv.app F ≫ e.functor.map g,
      e.functor.map h ≫ (e.functor.commShiftIso (1 : ℤ)).hom.app E, ?_,
      envelope_map_obj e.functor hE, (W.t.le (-1)).prop_of_iso (e.unitIso.app D') hD'⟩
    exact isomorphic_distinguished _ (e.functor.map_distinguished _ hT) _
      (Triangle.isoMk _ _ (Iso.refl _) (e.counitIso.app F).symm (Iso.refl _)
        (by simp) (by simp) (by simp))

/-- **Weak approximability is invariant under triangulated equivalences**, across Hom
universes, for a fixed coproduct universe `w`. -/
theorem satisfiesPaperWA_iff_of_equivalence [e.inverse.IsTriangulated] :
    SatisfiesPaperWA.{w} C ↔ SatisfiesPaperWA.{w} D := by
  have : e.inverse.Additive := e.toAdjunction.right_adjoint_additive
  let : e.symm.functor.CommShift ℤ := inferInstanceAs (e.inverse.CommShift ℤ)
  let : e.symm.inverse.CommShift ℤ := inferInstanceAs (e.functor.CommShift ℤ)
  have : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
  have : e.symm.functor.IsTriangulated := inferInstanceAs e.inverse.IsTriangulated
  exact ⟨fun ⟨W⟩ => ⟨W.transport e⟩, fun ⟨W⟩ => ⟨W.transport e.symm⟩⟩


omit [e.functor.Additive] [e.inverse.CommShift ℤ] in
variable {e} in
/-- Eventual vanishing of `Hom(G, G[n])` is invariant under equivalences commuting with the
shift. -/
theorem homShift_vanishing_iff (G : C) (n : ℤ) :
    (∀ f : e.functor.obj G ⟶ (e.functor.obj G)⟦n⟧, f = 0) ↔ ∀ f : G ⟶ G⟦n⟧, f = 0 := by
  constructor
  · intro h f
    apply e.functor.map_injective
    rw [Functor.map_zero, ← cancel_mono ((e.functor.commShiftIso n).hom.app G), Limits.zero_comp]
    exact h (e.functor.map f ≫ (e.functor.commShiftIso n).hom.app G)
  · intro h f
    obtain ⟨g, hg⟩ := e.functor.map_surjective (f ≫ (e.functor.commShiftIso n).inv.app G)
    have : f = e.functor.map g ≫ (e.functor.commShiftIso n).hom.app G := by
      rw [hg]; simp
    rw [this, h g, Functor.map_zero, Limits.zero_comp]

end Transport

/-! ### Recollements -/

/-- A composite with a factor isomorphic to zero, conjugated by equivalences, is isomorphic to
zero. -/
noncomputable def transportIsoZero {X : Type uA} {Y : Type uB} [Category.{vA} X]
    [Category.{vB} Y] [HasZeroMorphisms Y] [HasZeroObject Y]
    {X' : Type uA'} {Y' : Type uB'} [Category.{vA'} X'] [Category.{vB'} Y']
    [HasZeroMorphisms Y'] [HasZeroObject Y']
    (eA : X ≌ X') (eB : Y ≌ Y') {M : Type uD} [Category.{vD} M] {M' : Type uD'}
    [Category.{vD'} M'] (eM : M ≌ M') [eB.functor.PreservesZeroMorphisms]
    (F : X ⥤ M) (G : M ⥤ Y) (hFG : F ⋙ G ≅ 0) :
    (eA.inverse ⋙ F ⋙ eM.functor) ⋙ (eM.inverse ⋙ G ⋙ eB.functor) ≅ 0 :=
  (Functor.isZero _ fun Z => by
    have h0 : IsZero (G.obj (F.obj (eA.inverse.obj Z))) :=
      IsZero.of_iso ((Functor.isZero_iff _).1 (isZero_zero _) _) (hFG.app _)
    exact Functor.map_isZero eB.functor
      (IsZero.of_iso h0 (G.mapIso (eM.unitIso.app (F.obj (eA.inverse.obj Z))).symm))).isoZero

section RecollementTransport

variable {A : Type uA} {B : Type uB} {D : Type uD} {A' : Type uA'} {B' : Type uB'}
  {D' : Type uD'} [Category.{vA} A] [Category.{vB} B] [Category.{vD} D] [Category.{vA'} A']
  [Category.{vB'} B'] [Category.{vD'} D']
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D']
  (eA : A ≌ A') (eB : B ≌ B') (eD : D ≌ D') [eD.functor.CommShift ℤ]

/-- The connecting transformation of a gluing triangle, transported along equivalences: from
`γ : K ⋙ M ⟶ Q ⋙ P ⋙ [1]` (for `K : D ⥤ A`, `M : A ⥤ D`, `Q : D ⥤ B`, `P : B ⥤ D`) to the
conjugated functors `e_D⁻¹ ⋙ K ⋙ e_A`, `e_A⁻¹ ⋙ M ⋙ e_D`, `e_D⁻¹ ⋙ Q ⋙ e_B`,
`e_B⁻¹ ⋙ P ⋙ e_D`. -/
noncomputable def transportConnecting (K : D ⥤ A) (M : A ⥤ D) (Q : D ⥤ B) (P : B ⥤ D)
    (γ : K ⋙ M ⟶ Q ⋙ P ⋙ shiftFunctor D (1 : ℤ)) :
    (eD.inverse ⋙ K ⋙ eA.functor) ⋙ (eA.inverse ⋙ M ⋙ eD.functor) ⟶
      (eD.inverse ⋙ Q ⋙ eB.functor) ⋙ (eB.inverse ⋙ P ⋙ eD.functor) ⋙
        shiftFunctor D' (1 : ℤ) where
  app X := eD.functor.map (M.map (eA.unitIso.inv.app (K.obj (eD.inverse.obj X)))) ≫
    eD.functor.map (γ.app (eD.inverse.obj X)) ≫
    eD.functor.map ((shiftFunctor D (1 : ℤ)).map
      (P.map (eB.unitIso.hom.app (Q.obj (eD.inverse.obj X))))) ≫
    (eD.functor.commShiftIso (1 : ℤ)).hom.app
      (P.obj (eB.inverse.obj (eB.functor.obj (Q.obj (eD.inverse.obj X)))))
  naturality X Y f := by
    have hγ := γ.naturality (eD.inverse.map f)
    simp only [Functor.comp_obj, Functor.comp_map] at hγ ⊢
    have h₁ := eA.unitIso.inv.naturality (K.map (eD.inverse.map f))
    have h₂ := eB.unitIso.hom.naturality (Q.map (eD.inverse.map f))
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    rw [← Functor.commShiftIso_hom_naturality]
    rw [h₁, ← Functor.map_comp_assoc]
    refine congrArg (fun φ => eD.functor.map φ ≫ (eD.functor.commShiftIso (1 : ℤ)).hom.app
      (P.obj (eB.inverse.obj (eB.functor.obj (Q.obj (eD.inverse.obj Y)))))) ?_
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hγ]
    refine congrArg (M.map _ ≫ ·) (congrArg (γ.app _ ≫ ·) ?_)
    simpa only [Functor.map_comp] using
      congrArg (fun φ => (shiftFunctor D (1 : ℤ)).map (P.map φ)) h₂

variable [eD.functor.IsTriangulated]

/-- **The gluing triangles transport along equivalences.**  If `P ⊣ Q`, `K ⊣ M` and, for every
`Y`, `P Q Y → Y → M K Y → (P Q Y)[1]` (counit, unit, `γ`) is distinguished, then the same holds
for the conjugated adjunctions (composites with the equivalences) and the transported `γ`. -/
theorem transport_distinguished {K : D ⥤ A} {M : A ⥤ D} {Q : D ⥤ B} {P : B ⥤ D}
    (adjP : P ⊣ Q) (adjK : K ⊣ M) (γ : K ⋙ M ⟶ Q ⋙ P ⋙ shiftFunctor D (1 : ℤ))
    (h : ∀ Y, Triangle.mk (adjP.counit.app Y) (adjK.unit.app Y) (γ.app Y) ∈ distTriang D)
    (X : D') :
    Triangle.mk (((eB.symm.toAdjunction.comp adjP).comp eD.toAdjunction).counit.app X)
      (((eD.symm.toAdjunction.comp adjK).comp eA.toAdjunction).unit.app X)
      ((transportConnecting eA eB eD K M Q P γ).app X) ∈ distTriang D' := by
  let Y := eD.inverse.obj X
  refine isomorphic_distinguished _ (eD.functor.map_distinguished _ (h Y)) _ ?_
  refine Triangle.isoMk _ _
    (eD.functor.mapIso (P.mapIso (eB.unitIso.app (Q.obj Y)).symm))
    (eD.counitIso.app X).symm
    (eD.functor.mapIso (M.mapIso (eA.unitIso.app (K.obj Y)).symm)) ?_ ?_ ?_
  · simp [Y, ← Functor.map_comp]
  · simp [Y, ← Functor.map_comp]
  · simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Functor.mapTriangle_obj,
      Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, transportConnecting, Category.assoc]
    rw [← Functor.commShiftIso_hom_naturality]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Functor.comp_obj, Functor.id_obj]
    simp [Y]

end RecollementTransport

section Recollement

variable {DZ : Type uZ} {D : Type uD} {DU : Type uU} [Category.{vZ} DZ] [Category.{vD} D]
  [Category.{vU} DU]
  [Preadditive DZ] [Preadditive D] [Preadditive DU]
  [HasZeroObject DZ] [HasZeroObject D] [HasZeroObject DU]
  [HasShift DZ ℤ] [HasShift D ℤ] [HasShift DU ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU n).Additive]
  [Pretriangulated DZ] [Pretriangulated D] [Pretriangulated DU]
  [CategoryTheory.IsTriangulated DZ] [CategoryTheory.IsTriangulated D]
  [CategoryTheory.IsTriangulated DU]
  {DZ' : Type uZ'} {D' : Type uD'} {DU' : Type uU'} [Category.{vZ'} DZ'] [Category.{vD'} D']
  [Category.{vU'} DU']
  [Preadditive DZ'] [Preadditive D'] [Preadditive DU']
  [HasZeroObject DZ'] [HasZeroObject D'] [HasZeroObject DU']
  [HasShift DZ' ℤ] [HasShift D' ℤ] [HasShift DU' ℤ]
  [∀ (n : ℤ), (shiftFunctor DZ' n).Additive] [∀ (n : ℤ), (shiftFunctor D' n).Additive]
  [∀ (n : ℤ), (shiftFunctor DU' n).Additive]
  [Pretriangulated DZ'] [Pretriangulated D'] [Pretriangulated DU']
  [CategoryTheory.IsTriangulated DZ'] [CategoryTheory.IsTriangulated D']
  [CategoryTheory.IsTriangulated DU']
  (eZ : DZ ≌ DZ') (eD : D ≌ D') (eU : DU ≌ DU')
  [eZ.functor.Additive] [eD.functor.Additive] [eU.functor.Additive]
  [eZ.functor.CommShift ℤ] [eD.functor.CommShift ℤ] [eU.functor.CommShift ℤ]
  [eZ.inverse.CommShift ℤ] [eD.inverse.CommShift ℤ] [eU.inverse.CommShift ℤ]
  [eZ.functor.IsTriangulated] [eD.functor.IsTriangulated] [eU.functor.IsTriangulated]
  [eZ.inverse.IsTriangulated] [eD.inverse.IsTriangulated] [eU.inverse.IsTriangulated]

/-- **Transport of a recollement** (Setup 4.1, `setup:recollement`) along triangulated
equivalences `e_Z`, `e_D`, `e_U`, which may change the Hom universes: each of the six functors
is conjugated by the equivalences, each adjunction is composed with them, and the gluing
triangles are carried by `e_D` (`transport_distinguished`). -/
noncomputable def Recollement.transport (R : Recollement DZ D DU) : Recollement DZ' D' DU' where
  iStar := eD.inverse ⋙ R.iStar ⋙ eZ.functor
  iLower := eZ.inverse ⋙ R.iLower ⋙ eD.functor
  iShriek := eD.inverse ⋙ R.iShriek ⋙ eZ.functor
  jShriek := eU.inverse ⋙ R.jShriek ⋙ eD.functor
  jStar := eD.inverse ⋙ R.jStar ⋙ eU.functor
  jUpper := eU.inverse ⋙ R.jUpper ⋙ eD.functor
  iStarAdj := (eD.symm.toAdjunction.comp R.iStarAdj).comp eZ.toAdjunction
  iLowerAdj := (eZ.symm.toAdjunction.comp R.iLowerAdj).comp eD.toAdjunction
  jShriekAdj := (eU.symm.toAdjunction.comp R.jShriekAdj).comp eD.toAdjunction
  jStarAdj := (eD.symm.toAdjunction.comp R.jStarAdj).comp eU.toAdjunction
  kernel X := by
    constructor
    · rintro ⟨e⟩
      have h0 : IsZero (R.jStar.obj (eD.inverse.obj X)) :=
        IsZero.of_iso (Functor.map_isZero eU.inverse (IsZero.of_iso (isZero_zero _) e))
          (eU.unitIso.app _)
      obtain ⟨Y, ⟨eY⟩⟩ := (R.kernel (eD.inverse.obj X)).1 ⟨h0.isoZero⟩
      exact ⟨eZ.functor.obj Y, ⟨(eD.counitIso.app X).symm ≪≫ eD.functor.mapIso
        (eY ≪≫ R.iLower.mapIso (eZ.unitIso.app Y))⟩⟩
    · rintro ⟨Y, ⟨eY⟩⟩
      have h0 : IsZero (R.jStar.obj (eD.inverse.obj X)) := by
        have := (R.kernel (R.iLower.obj (eZ.inverse.obj Y))).2 ⟨_, ⟨Iso.refl _⟩⟩
        obtain ⟨e₀⟩ := this
        exact IsZero.of_iso (IsZero.of_iso (isZero_zero _) e₀)
          (R.jStar.mapIso (eD.inverse.mapIso eY ≪≫ (eD.unitIso.app _).symm))
      exact ⟨(Functor.map_isZero eU.functor h0).isoZero⟩
  jStar_iLower := transportIsoZero eZ eU eD R.iLower R.jStar R.jStar_iLower
  iShriek_jUpper := transportIsoZero eU eZ eD R.jUpper R.iShriek R.iShriek_jUpper
  iStar_jShriek := transportIsoZero eU eZ eD R.jShriek R.iStar R.iStar_jShriek
  firstConnecting := transportConnecting eZ eU eD R.iStar R.iLower R.jStar R.jShriek
    R.firstConnecting
  secondConnecting := transportConnecting eU eZ eD R.jStar R.jUpper R.iShriek R.iLower
    R.secondConnecting
  first_distinguished X :=
    transport_distinguished eZ eU eD R.jShriekAdj R.iStarAdj R.firstConnecting
      R.first_distinguished X
  second_distinguished X :=
    transport_distinguished eU eZ eD R.iLowerAdj R.jStarAdj R.secondConnecting
      R.second_distinguished X

end Recollement

end RelativeWeakApprox.SumUniverse


#print axioms RelativeWeakApprox.SumUniverse.satisfiesPaperWA_iff_of_equivalence
#print axioms RelativeWeakApprox.SumUniverse.isPaperGenerator_functor_obj_iff
#print axioms RelativeWeakApprox.SumUniverse.Recollement.transport
