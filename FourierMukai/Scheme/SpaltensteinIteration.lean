import FourierMukai.Scheme.SpaltensteinStage
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Spaltenstein's countable system of bounded-above resolutions

This file implements the induction in Lemma 3.3 of Spaltenstein,
*Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121--154.
The targets are an arbitrary nested sequence of bounded-above complexes.
-/

@[expose] public section

namespace RelativeFM.Spaltenstein

open CategoryTheory CategoryTheory.Limits
open CochainComplex HomComplex

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

lemma isStrictlyLE_mappingCone_of_pred {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (d : ℤ) [K.IsStrictlyLE (d + 1)] [L.IsStrictlyLE d] :
    (mappingCone f).IsStrictlyLE d := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  simp only [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyLE (d + 1) (i + 1) (by omega),
    L.isZero_of_isStrictlyLE d i hi⟩

lemma isStrictlyLE_mappingCocone_succ {P B : CochainComplex C ℤ} (f : P ⟶ B)
    (d : ℤ) [P.IsStrictlyLE d] [B.IsStrictlyLE d] :
    (mappingCocone f).IsStrictlyLE (d + 1) := by
  letI : P.IsStrictlyLE (d + 1) := P.isStrictlyLE_of_le d (d + 1) (by omega)
  letI : (mappingCone f).IsStrictlyLE d := isStrictlyLE_mappingCone_of_pred f d
  exact (mappingCone f).isStrictlyLE_shift d (-1) (d + 1) (by omega)

/-- A bounded-above K-projective resolution of a complex, with its chain-map
resolution retained explicitly. -/
structure BoundedResolution (B : CochainComplex C ℤ) (d : ℤ) where
  complex : CochainComplex C ℤ
  map : complex ⟶ B
  quasiIso : QuasiIso map
  isKProjective : complex.IsKProjective
  isStrictlyLE : complex.IsStrictlyLE d

attribute [instance] BoundedResolution.quasiIso BoundedResolution.isKProjective
  BoundedResolution.isStrictlyLE

/-- The new resolution used at a successor in Spaltenstein's induction. -/
structure ExtensionData {B₀ B₁ : CochainComplex C ℤ} {d₀ d₁ : ℤ}
    (R : BoundedResolution B₀ d₀) (t : B₀ ⟶ B₁) (hd : d₀ ≤ d₁) where
  Q : CochainComplex C ℤ
  g : Q ⟶ mappingCocone (R.map ≫ t)
  quasiIso : QuasiIso g
  isKProjective : Q.IsKProjective
  isStrictlyLE : Q.IsStrictlyLE (d₁ + 1)

attribute [instance] ExtensionData.quasiIso ExtensionData.isKProjective
  ExtensionData.isStrictlyLE

/-- Obtain the successor's bounded projective resolution from the existing
bounded-above projective-resolution theorem. -/
noncomputable def extensionData [EnoughProjectives C]
    {B₀ B₁ : CochainComplex C ℤ} {d₀ d₁ : ℤ}
    (R : BoundedResolution B₀ d₀) (t : B₀ ⟶ B₁) (hd : d₀ ≤ d₁)
    (hB : B₁.IsStrictlyLE d₁) : ExtensionData R t hd := by
  letI : B₁.IsStrictlyLE d₁ := hB
  letI : R.complex.IsStrictlyLE d₁ := R.complex.isStrictlyLE_of_le d₀ d₁ hd
  letI : (mappingCocone (R.map ≫ t)).IsStrictlyLE (d₁ + 1) :=
    isStrictlyLE_mappingCocone_succ (R.map ≫ t) d₁
  let H := KProjectiveResolution.exists_projective_resolution_of_isStrictlyLE
    (mappingCocone (R.map ≫ t)) (d₁ + 1)
  let Q := H.choose
  let g : Q ⟶ mappingCocone (R.map ≫ t) := H.choose_spec.choose
  have hg : QuasiIso g := H.choose_spec.choose_spec.1
  have hQ : Q.IsStrictlyLE (d₁ + 1) := H.choose_spec.choose_spec.2.1
  have hproj : ∀ n, Projective (Q.X n) := H.choose_spec.choose_spec.2.2
  letI : Q.IsStrictlyLE (d₁ + 1) := hQ
  letI (n : ℤ) : Projective (Q.X n) := hproj n
  exact
    { Q := Q
      g := g
      quasiIso := hg
      isKProjective := CochainComplex.isKProjective_of_projective Q (d₁ + 1)
      isStrictlyLE := hQ }

/-- The bounded resolution at the next stage. -/
noncomputable def nextResolution {B₀ B₁ : CochainComplex C ℤ} {d₀ d₁ : ℤ}
    (R : BoundedResolution B₀ d₀) (t : B₀ ⟶ B₁) (hd : d₀ ≤ d₁)
    (E : ExtensionData R t hd) : BoundedResolution B₁ d₁ where
  complex := mappingCone (sourceMap (R.map ≫ t) E.g)
  map := stageMap' (R.map ≫ t) E.g
  quasiIso := quasiIso_stageMap' (R.map ≫ t) E.g
  isKProjective := by
    letI : R.complex.IsStrictlyLE d₁ := R.complex.isStrictlyLE_of_le d₀ d₁ hd
    exact isKProjective_mappingCone_sourceMap (R.map ≫ t) E.g
  isStrictlyLE := by
    letI : R.complex.IsStrictlyLE d₁ := R.complex.isStrictlyLE_of_le d₀ d₁ hd
    exact isStrictlyLE_mappingCone_of_pred (sourceMap (R.map ≫ t) E.g) d₁

/-- The initial stage, like every later stage, follows from the existing
bounded-above projective-resolution theorem. -/
noncomputable def initialResolution [EnoughProjectives C]
    (B : CochainComplex C ℤ) (d : ℤ) [B.IsStrictlyLE d] : BoundedResolution B d := by
  let H := KProjectiveResolution.exists_projective_resolution_of_isStrictlyLE B d
  let P := H.choose
  let π : P ⟶ B := H.choose_spec.choose
  have hπ : QuasiIso π := H.choose_spec.choose_spec.1
  have hP : P.IsStrictlyLE d := H.choose_spec.choose_spec.2.1
  have hproj : ∀ n, Projective (P.X n) := H.choose_spec.choose_spec.2.2
  letI : P.IsStrictlyLE d := hP
  letI (n : ℤ) : Projective (P.X n) := hproj n
  exact
    { complex := P
      map := π
      quasiIso := hπ
      isKProjective := CochainComplex.isKProjective_of_projective P d
      isStrictlyLE := hP }

/-- A nested system of bounded-above approximations of `A`. -/
structure BoundedAboveFiltration (A : CochainComplex C ℤ) where
  B : ℕ → CochainComplex C ℤ
  isStrictlyLE (n : ℕ) : (B n).IsStrictlyLE (n : ℤ)
  step (n : ℕ) : B n ⟶ B (n + 1)
  toA (n : ℕ) : B n ⟶ A
  step_toA (n : ℕ) : step n ≫ toA (n + 1) = toA n

attribute [instance] BoundedAboveFiltration.isStrictlyLE

lemma intBoundSucc (n : ℕ) : (n : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by
  exact_mod_cast Nat.le_succ n

/-- Spaltenstein's induction, packaged as a sequence of bounded K-projective
resolutions. -/
noncomputable def filteredResolution [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) :
    ∀ n : ℕ, BoundedResolution (F.B n) (n : ℤ)
  | 0 => letI := F.isStrictlyLE 0; initialResolution (F.B 0) 0
  | n + 1 => nextResolution (filteredResolution F n) (F.step n) (intBoundSucc n)
    (extensionData (filteredResolution F n) (F.step n) (intBoundSucc n)
      (F.isStrictlyLE (n + 1)))

/-- The extension data used at the successor stage. -/
noncomputable abbrev filteredExtension [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) (n : ℕ) :=
  extensionData (filteredResolution F n) (F.step n) (intBoundSucc n)
    (F.isStrictlyLE (n + 1))

/-- The degreewise split inclusion of the previous bounded resolution. -/
noncomputable def filteredStep [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) (n : ℕ) :
    (filteredResolution F n).complex ⟶ (filteredResolution F (n + 1)).complex :=
  mappingCone.inr (sourceMap ((filteredResolution F n).map ≫ F.step n)
    (filteredExtension F n).g)

lemma filteredStep_map [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) (n : ℕ) :
    filteredStep F n ≫ (filteredResolution F (n + 1)).map =
      (filteredResolution F n).map ≫ F.step n := by
  exact inr_stageMap' ((filteredResolution F n).map ≫ F.step n)
    (filteredExtension F n).g

/-- The K-projective cokernel complex of the successor inclusion. -/
noncomputable def filteredCokernel [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) (n : ℕ) :
    CochainComplex C ℤ := (filteredExtension F n).Q⟦(1 : ℤ)⟧

instance [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) (n : ℕ) :
    (filteredExtension F n).Q.IsKProjective := (filteredExtension F n).isKProjective

instance [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) (n : ℕ) :
    (filteredCokernel F n).IsKProjective := by
  dsimp [filteredCokernel]
  infer_instance

/-- A degreewise retraction of the successor inclusion. -/
noncomputable def filteredStepRetraction [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) (n : ℕ) (i : ℤ) :
    (filteredResolution F (n + 1)).complex.X i ⟶
      (filteredResolution F n).complex.X i :=
  (mappingCone.snd (sourceMap ((filteredResolution F n).map ≫ F.step n)
    (filteredExtension F n).g)).v i i (add_zero i)

lemma filteredStep_retraction [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) (n : ℕ) (i : ℤ) :
    (filteredStep F n).f i ≫ filteredStepRetraction F n i = 𝟙 _ := by
  exact mappingCone.inr_f_snd_v (sourceMap ((filteredResolution F n).map ≫ F.step n)
    (filteredExtension F n).g) i

/-- The induced diagram of bounded resolutions. -/
noncomputable def filteredResolutionDiagram [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) :
    ℕ ⥤ CochainComplex C ℤ :=
  Functor.ofSequence (filteredStep F)

/-- The induced diagram of approximants. -/
noncomputable def filtrationDiagram
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) :
    ℕ ⥤ CochainComplex C ℤ :=
  Functor.ofSequence F.step

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Compatibility of resolutions and approximants is a natural transformation. -/
noncomputable def filteredResolutionNatTrans [EnoughProjectives C]
    {A : CochainComplex C ℤ} (F : BoundedAboveFiltration A) :
    filteredResolutionDiagram F ⟶ filtrationDiagram F := by
  apply NatTrans.ofSequence (fun n => (filteredResolution F n).map)
  intro n
  simpa only [filteredResolutionDiagram, filtrationDiagram, Functor.ofSequence_obj,
    Functor.ofSequence_map_homOfLE_succ] using filteredStep_map F n

#print axioms RelativeFM.Spaltenstein.filteredResolution
#print axioms RelativeFM.Spaltenstein.filteredStep_map
#print axioms RelativeFM.Spaltenstein.filteredStep_retraction
#print axioms RelativeFM.Spaltenstein.filteredResolutionNatTrans

end
end RelativeFM.Spaltenstein
