import FourierMukai.Scheme.KProjectiveResolution
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Spaltenstein's countable cone step

This file develops Lemma 3.3 of Spaltenstein, *Resolutions of unbounded
complexes*, Compositio Math. 65 (1988), 121--154.
-/

@[expose] public section

namespace RelativeFM.Spaltenstein

open CategoryTheory CategoryTheory.Limits
open CochainComplex HomComplex

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {P B Q : CochainComplex C ℤ} (f : P ⟶ B)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma δ_mappingCocone_snd :
    δ (-1) 0 (mappingCocone.snd f) =
      -Cochain.ofHom (mappingCocone.fst f ≫ f) := by
  rw [mappingCocone.snd, Cochain.δ_leftShift, mappingCone.δ_snd,
    Cochain.leftShift_neg, Cochain.leftShift_comp_zero_cochain] <;> try norm_num
  simp [mappingCocone.fst, Cochain.ofHom_comp]

/-- The first component of a map to the mapping cocone. -/
def sourceMap (g : Q ⟶ mappingCocone f) : Q ⟶ P :=
  g ≫ mappingCocone.fst f

/-- The second component of a map to the mapping cocone, as a `(-1)`-cochain. -/
def targetCochain (g : Q ⟶ mappingCocone f) : Cochain Q B (-1) :=
  (Cochain.ofHom g).comp (mappingCocone.snd f) (zero_add _)

lemma δ_targetCochain (g : Q ⟶ mappingCocone f) :
    δ (-1) 0 (targetCochain f g) + Cochain.ofHom (sourceMap f g ≫ f) = 0 := by
  rw [targetCochain, δ_ofHom_comp, δ_mappingCocone_snd, sourceMap]
  simp [Cochain.ofHom_comp]

/-- Spaltenstein's map out of the cone of `-sourceMap`. -/
noncomputable def stageMap (g : Q ⟶ mappingCocone f) :
    mappingCone (-sourceMap f g) ⟶ B :=
  mappingCone.desc _ (targetCochain f g) f (by
    have h := δ_targetCochain f g
    rw [Preadditive.neg_comp, Cochain.ofHom_neg]
    exact eq_neg_of_add_eq_zero_left h)

@[simp, reassoc]
lemma inr_stageMap (g : Q ⟶ mappingCocone f) :
    mappingCone.inr (-sourceMap f g) ≫ stageMap f g = f := by
  simp [stageMap]

/-- The same map, with the harmless sign change in the cone removed from the
construction. -/
noncomputable def stageMap' (g : Q ⟶ mappingCocone f) :
    mappingCone (sourceMap f g) ⟶ B :=
  mappingCone.desc _ (-targetCochain f g) f (by
    rw [δ_neg]
    exact neg_eq_of_add_eq_zero_left (by
      simpa only [add_comm] using δ_targetCochain f g))

@[simp, reassoc]
lemma inr_stageMap' (g : Q ⟶ mappingCocone f) :
    mappingCone.inr (sourceMap f g) ≫ stageMap' f g = f := by
  simp [stageMap']

lemma isKProjective_mappingCone_sourceMap (g : Q ⟶ mappingCocone f)
    [P.IsKProjective] [Q.IsKProjective] :
    (mappingCone (sourceMap f g)).IsKProjective :=
  KProjectiveResolution.isKProjective_mappingCone _

lemma isKProjective_mappingCone_negSourceMap (g : Q ⟶ mappingCocone f)
    [P.IsKProjective] [Q.IsKProjective] :
    (mappingCone (-sourceMap f g)).IsKProjective :=
  KProjectiveResolution.isKProjective_mappingCone _

attribute [local instance] HasDerivedCategory.standard

noncomputable def mappingCoconeShiftIso : (mappingCocone f)⟦(1 : ℤ)⟧ ≅ mappingCone f :=
  eqToIso (by rfl) ≪≫ (shiftFunctorCompIsoId (CochainComplex C ℤ) (-1) 1 (by omega)).app (mappingCone f)

/-- A map from the mapping cocone, transported to the ordinary mapping cone
after one shift. -/
noncomputable def shiftToCone (g : Q ⟶ mappingCocone f) :
    Q⟦(1 : ℤ)⟧ ⟶ mappingCone f :=
  g⟦(1 : ℤ)⟧' ≫ (mappingCoconeShiftIso f).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The third triangle identity holds up to the explicit cone homotopy. -/
noncomputable def stageCommHomotopy (g : Q ⟶ mappingCocone f) :
    Homotopy
      ((mappingCone.triangle (sourceMap f g)).mor₃ ≫ shiftToCone f g)
      (stageMap' f g ≫ mappingCone.inr f) := by
  apply mappingCone.descHomotopy (sourceMap f g) _ _ 0 (-mappingCone.inl f)
  · ext p q hpq
    obtain rfl : q = p - 1 := by omega
    apply mappingCone.ext_to f (p - 1) p (by omega)
    · simp [mappingCone.triangle, mappingCoconeShiftIso, shiftToCone, stageMap',
        targetCochain, sourceMap, Cochain.comp_v, Cochain.rightShift_v,
        mappingCocone.fst, shiftFunctorCompIsoId,
        shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]
      rw [Cochain.leftShift_v (n := 1) (mappingCone.fst f).1
        (-1) 0 (by omega) p p (add_zero p) (p - 1) (by omega)]
      rw [← HomologicalComplex.XIsoOfEq_inv_naturality_assoc g
        (show p - 1 + 1 = p by omega)]
      simp [HomologicalComplex.XIsoOfEq, eqToIso, eqToHom_map]
    · simp [mappingCone.triangle, mappingCoconeShiftIso, shiftToCone, stageMap',
        targetCochain, sourceMap, Cochain.comp_v, Cochain.rightShift_v,
        Cochain.leftShift_v, mappingCocone.snd, shiftFunctorCompIsoId,
        shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]
      rw [← HomologicalComplex.XIsoOfEq_inv_naturality_assoc g
        (show p - 1 + 1 = p by omega)]
      simp [HomologicalComplex.XIsoOfEq, eqToIso, eqToHom_map,
        Int.negOnePow_even 2 ⟨1, rfl⟩]
  · have hz : mappingCone.inr (sourceMap f g) ≫
        (mappingCone.triangle (sourceMap f g)).mor₃ ≫ shiftToCone f g = 0 := by
      rw [← Category.assoc]
      have hz' : mappingCone.inr (sourceMap f g) ≫
          (mappingCone.triangle (sourceMap f g)).mor₃ = 0 := by
        ext p
        simp
      rw [hz', zero_comp]
    have hs : mappingCone.inr (sourceMap f g) ≫ stageMap' f g ≫
        mappingCone.inr f = f ≫ mappingCone.inr f := by
      rw [← Category.assoc, inr_stageMap']
    rw [hz, hs]
    simp [Cochain.ofHom_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma mappingCocone_mor₃_comp_shiftIso :
    (mappingCocone.triangle f).mor₃ ≫ (mappingCoconeShiftIso f).hom =
      mappingCone.inr f := by
  dsimp [mappingCocone.triangle, mappingCoconeShiftIso]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma derived_stageComm (g : Q ⟶ mappingCocone f) :
    DerivedCategory.Q.map (mappingCone.triangle (sourceMap f g)).mor₃ ≫
        DerivedCategory.Q.map (g⟦(1 : ℤ)⟧') =
      DerivedCategory.Q.map (stageMap' f g) ≫
        DerivedCategory.Q.map (mappingCocone.triangle f).mor₃ := by
  rw [← cancel_mono (DerivedCategory.Q.map (mappingCoconeShiftIso f).hom)]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [show (mappingCocone.triangle f).mor₃ ≫ (mappingCoconeShiftIso f).hom =
    mappingCone.inr f from mappingCocone_mor₃_comp_shiftIso f]
  exact DerivedCategory.Q_map_eq_of_homotopy C (stageCommHomotopy f g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma quasiIso_stageMap' (g : Q ⟶ mappingCocone f) [QuasiIso g] :
    QuasiIso (stageMap' f g) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  let T₁ := DerivedCategory.Q.mapTriangle.obj
    (mappingCone.triangle (sourceMap f g))
  let T₂ := DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle f)
  let φ : T₁ ⟶ T₂ :=
    { hom₁ := DerivedCategory.Q.map g
      hom₂ := 𝟙 _
      hom₃ := DerivedCategory.Q.map (stageMap' f g)
      comm₁ := by
        dsimp [T₁, T₂]
        simp [← Functor.map_comp, sourceMap]
      comm₂ := by
        dsimp [T₁, T₂]
        simp [← Functor.map_comp]
      comm₃ := by
        dsimp [T₁, T₂]
        simp only [Category.assoc, ← Functor.commShiftIso_hom_naturality]
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
            (mappingCocone f)) (derived_stageComm f g) }
  have h₁ : IsIso φ.hom₁ := by
    dsimp [φ]
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso C g).2 inferInstance
  have h₂ : IsIso φ.hom₂ := by dsimp [φ]; infer_instance
  exact Pretriangulated.isIso₃_of_isIso₁₂ φ
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (DerivedCategory.mappingCocone_triangle_distinguished _) h₁ h₂

#print axioms RelativeFM.Spaltenstein.stageCommHomotopy
#print axioms RelativeFM.Spaltenstein.quasiIso_stageMap'
#print axioms RelativeFM.Spaltenstein.isKProjective_mappingCone_sourceMap

end
end RelativeFM.Spaltenstein
