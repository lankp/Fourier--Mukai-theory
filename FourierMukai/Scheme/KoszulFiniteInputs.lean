/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.FiniteKoszulM1
import FourierMukai.Scheme.KoszulConeSwap
import FourierMukai.Scheme.NeemanPreferred

/-!
# Finite Koszul objects: powers and zero detection

Source: LP26, Corollary 1.2 (`cor:weak_approx_spaces`), affine base case, which is
Neeman, *Acta Math.* 233 (2024), Theorem 3.2(iv) for `X = Spec A`, `Z = V(I)` with
`I = (f₁,…,fₙ)`; the two facts proved here are the inputs of Neeman's Lemma 7.6
argument (Construction 7.3 and the generation of `D_{V(I)}`).

Model: `AffineD A = D(A-Mod)`, and the finite Koszul objects
`FiniteKoszulM1.koszulListData A ps`, the iterated scalar cones
`K(a₁^{n₁},…,a_k^{n_k})` built from `A[0]`.

* `koszulList_power_coprod` (**Neeman, Construction 7.3**): for exponent lists of
  the same length, `K(f₁^{n₁},…,fₙ^{nₙ})` lies in `Coprod(K(f₁,…,fₙ)[0,0])`, the
  closure of `{K(f₁,…,fₙ)}` under isomorphisms, coproducts and extensions (in fact
  a finite extension; exponents `0` give the zero object).
* `koszulList_detects_zero`: the degree-one Koszul object `K(f₁,…,fₙ)` detects zero
  on complexes supported on `V(f₁,…,fₙ)`: if `Hom(K⟦k⟧, F) = 0` for all `k` and `F`
  is supported on `V(f₁,…,fₙ)`, then `F ≅ 0`.

Proof ingredients, all proved:
1. scalar cones are unique up to isomorphism (`IsScalarCone.iso`);
2. the octahedral axiom gives `cone(b^{n+1}) ∈ ext(cone(b), cone(b^n))`
   (`coprod_of_isScalarCone_pow`);
3. iterated scalar cones commute, `cone(c, cone(b, X)) ≅ cone(b, cone(c, X))`
   (`IsScalarCone.swap`), from the chain-level isomorphism
   `KoszulConeSwap.coneSwapIso` and `DerivedCategory.mappingCone_triangle_distinguished`;
   so any exponent can be moved to the outermost cone, where 2 applies;
4. for zero detection: a map from a perfect object to an `f`-supported object is
   killed by a power of `f` (`PerfectPowerTorsionM1.perf_sourcePowerTorsion`), while
   `Hom(cone(f, Y)⟦k⟧, F) = 0` makes `f` injective on `Hom(Y⟦k⟧, F)`; induction on
   the list, ending with `A[0]` (`NeemanPreferredM6.ringObject_isPaperGenerator`).

Nothing is assumed: no Stacks field and no named hypothesis.
-/

@[expose] public section

namespace RelativeFM.KoszulFiniteInputs

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject
open RelativeFM.SupportedAisleM6.Koszul
open RelativeFM.NeemanFiniteSupportM4
open RelativeFM.PerfectPowerTorsionM1
open RelativeFM.FiniteKoszulM1

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- `Y` is a cone of `b • 𝟙 X`. -/
def IsScalarCone (b : A) (X Y : AffineD A) : Prop :=
  ∃ (g : X ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk (b • 𝟙 X) g h ∈ distTriang (AffineD A)

variable {A}

lemma isScalarCone_scalarConeData (b : A) {X : AffineD A} (hX : Perf A X) :
    IsScalarCone A b X (scalarConeData A b hX).obj :=
  ⟨_, _, (scalarConeData A b hX).distinguished⟩

lemma exists_isScalarCone (b : A) (X : AffineD A) : ∃ Y, IsScalarCone A b X Y := by
  obtain ⟨Y, g, h, hT⟩ := distinguished_cocone_triangle (b • 𝟙 X)
  exact ⟨Y, g, h, hT⟩

/-- Scalar cones of isomorphic objects are isomorphic. -/
lemma IsScalarCone.iso {b : A} {X X' Y Y' : AffineD A} (e : X ≅ X')
    (h : IsScalarCone A b X Y) (h' : IsScalarCone A b X' Y') : Nonempty (Y ≅ Y') := by
  obtain ⟨g, k, hT⟩ := h
  obtain ⟨g', k', hT'⟩ := h'
  obtain ⟨φ, -, -⟩ := exists_iso_of_arrow_iso _ _ hT hT'
    (Arrow.isoMk e e (by simp [Linear.smul_comp, Linear.comp_smul]))
  exact ⟨Triangle.π₃.mapIso φ⟩

/-- Being a scalar cone is invariant under isomorphism of the cone. -/
lemma IsScalarCone.of_iso {b : A} {X Y Y' : AffineD A} (h : IsScalarCone A b X Y)
    (e : Y ≅ Y') : IsScalarCone A b X Y' := by
  obtain ⟨g, k, hT⟩ := h
  refine ⟨g ≫ e.hom, e.inv ≫ k, isomorphic_distinguished _ hT _ ?_⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp) (by simp) (by simp)

/-- Being a scalar cone is invariant under isomorphism of the source. -/
lemma IsScalarCone.of_iso_left {b : A} {X X' Y : AffineD A} (h : IsScalarCone A b X Y)
    (e : X ≅ X') : IsScalarCone A b X' Y := by
  obtain ⟨Y', h'⟩ := exists_isScalarCone b X'
  obtain ⟨e'⟩ := h.iso e h'
  exact h'.of_iso e'.symm

/-- The image in `D(A)` of the chain-level mapping cone of `b • 𝟙 K` is a scalar cone. -/
lemma isScalarCone_Q (b : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsScalarCone A b (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj (KoszulConeSwap.cone b K)) := by
  have hT := DerivedCategory.mappingCone_triangle_distinguished (b • 𝟙 K)
  refine ⟨DerivedCategory.Q.map (CochainComplex.mappingCone.inr (b • 𝟙 K)),
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (b • 𝟙 K))).mor₃,
    isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · dsimp
    rw [Category.comp_id, Category.id_comp, Functor.map_smul, CategoryTheory.Functor.map_id]
  · dsimp
    rw [Category.comp_id, Category.id_comp]
  · dsimp
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- **Iterated scalar cones commute**: `cone(b, cone(c, X)) ≅ cone(c, cone(b, X))`. -/
lemma IsScalarCone.swap {b c : A} {X Y Z Y' Z' : AffineD A}
    (h₁ : IsScalarCone A c X Y) (h₂ : IsScalarCone A b Y Z)
    (h₃ : IsScalarCone A b X Y') (h₄ : IsScalarCone A c Y' Z') : Nonempty (Z ≅ Z') := by
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  obtain ⟨eY⟩ := (isScalarCone_Q c K).iso e h₁
  obtain ⟨eZ⟩ := (isScalarCone_Q b (KoszulConeSwap.cone c K)).iso eY h₂
  obtain ⟨eY'⟩ := (isScalarCone_Q b K).iso e h₃
  obtain ⟨eZ'⟩ := (isScalarCone_Q c (KoszulConeSwap.cone b K)).iso eY' h₄
  exact ⟨eZ.symm ≪≫ DerivedCategory.Q.mapIso (KoszulConeSwap.coneSwapIso K b c).symm ≪≫ eZ'⟩

section Coprod

/-- The class `Coprod(Y[0,0])`. -/
abbrev E (Y : AffineD A) : ObjectProperty (AffineD A) := Coprod (shiftInterval Y 0 0)

lemma E_of_iso {Y X : AffineD A} (e : X ≅ Y) : E Y X :=
  Coprod.of_mem _ ⟨0, le_rfl, le_rfl, ⟨e ≪≫ (shiftFunctorZero (AffineD A) ℤ).symm.app Y ≪≫
    eqToIso (by simp)⟩⟩

lemma E_of_isZero (Y : AffineD A) {X : AffineD A} (hX : IsZero X) : E Y X := by
  let pres : ColimitPresentation (Discrete PEmpty.{u + 2}) X :=
    { diag := Functor.empty _
      ι := { app := fun j => j.as.elim
             naturality := fun j => j.as.elim }
      isColimit :=
        { desc := fun s => hX.to_ s.pt
          fac := fun _ j => j.as.elim
          uniq := fun _ _ _ => hX.eq_of_src _ _ } }
  exact Coprod.of_colimitPresentation pres (fun j => j.as.elim)

/-- Transitivity of `E`. -/
lemma E_trans {Y U V : AffineD A} (hU : E Y U) (hV : E U V) : E Y V := by
  induction hV with
  | of_mem X hX =>
      obtain ⟨k, hk₀, hk₁, ⟨e⟩⟩ := hX
      obtain rfl : k = 0 := le_antisymm hk₁ hk₀
      exact Coprod.of_isoClosure (e ≪≫ eqToIso (by simp) ≪≫
        (shiftFunctorZero (AffineD A) ℤ).app U).symm hU
  | of_isoClosure e _ ih => exact .of_isoClosure e ih
  | of_colimitPresentation pres _ ih => exact .of_colimitPresentation pres ih
  | of_extension T hT _ _ ih₁ ih₃ => exact .of_extension T hT ih₁ ih₃

lemma E_congr {Y Y' X : AffineD A} (e : Y ≅ Y') (h : E Y X) : E Y' X :=
  E_trans (E_of_iso e) h

/-- **Octahedral step.** A cone of `b ^ n` lies in the extension closure of a cone
of `b`. -/
lemma coprod_of_isScalarCone_pow (b : A) {X Y : AffineD A} (hY : IsScalarCone A b X Y) :
    ∀ (n : ℕ) {Yn : AffineD A}, IsScalarCone A (b ^ n) X Yn → E Y Yn
  | 0, Yn, ⟨g, h, hT⟩ => by
      apply E_of_isZero
      refine (Triangle.isZero₃_iff_isIso₁ _ hT).mpr ?_
      simp only [Triangle.mk_mor₁, pow_zero, one_smul]
      exact IsIso.id _
  | n + 1, Yn₁, ⟨g₃, h₃, hT₃⟩ => by
      obtain ⟨Yn, hn⟩ := exists_isScalarCone (b ^ n) X
      have ih := coprod_of_isScalarCone_pow b hY n hn
      obtain ⟨g₁, h₁, hT₁⟩ := hY
      obtain ⟨g₂, h₂, hT₂⟩ := hn
      have comm : (b • 𝟙 X) ≫ (b ^ n • 𝟙 X) = b ^ (n + 1) • 𝟙 X := by
        rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, pow_succ,
          mul_comm]
      let O := Triangulated.someOctahedron comm hT₁ hT₂ hT₃
      exact Coprod.of_extension _ O.mem (E_of_iso (Iso.refl _)) ih

end Coprod

section KoszulList

/-- `X` is (isomorphic to) the iterated scalar cone of the list `ps` on `A[0]`;
the head of the list is the outermost cone, as in `koszulListData`. -/
def IsKoszul : List (A × ℕ) → AffineD A → Prop
  | [], X => Nonempty (X ≅ ringObject A)
  | (a, n) :: ps, Y => ∃ X, IsKoszul ps X ∧ IsScalarCone A (a ^ n) X Y

lemma isKoszul_koszulListData : ∀ ps : List (A × ℕ), IsKoszul ps (koszulListData A ps).obj
  | [] => ⟨Iso.refl _⟩
  | (a, n) :: ps => ⟨_, isKoszul_koszulListData ps,
      isScalarCone_scalarConeData (a ^ n) (koszulListData A ps).perfect⟩

lemma exists_isKoszul : ∀ ps : List (A × ℕ), ∃ X : AffineD A, IsKoszul ps X
  | ps => ⟨_, isKoszul_koszulListData ps⟩

lemma IsKoszul.iso : ∀ {ps : List (A × ℕ)} {X X' : AffineD A},
    IsKoszul ps X → IsKoszul ps X' → Nonempty (X ≅ X')
  | [], _, _, ⟨e⟩, ⟨e'⟩ => ⟨e ≪≫ e'.symm⟩
  | (_, _) :: _, _, _, ⟨_, hX, hc⟩, ⟨_, hX', hc'⟩ => by
      obtain ⟨e⟩ := IsKoszul.iso hX hX'
      exact hc.iso e hc'

lemma IsKoszul.of_iso : ∀ {ps : List (A × ℕ)} {X X' : AffineD A},
    IsKoszul ps X → (X ≅ X') → IsKoszul ps X'
  | [], _, _, ⟨e⟩, e' => ⟨e'.symm ≪≫ e⟩
  | (_, _) :: _, _, _, ⟨W, hW, hc⟩, e => ⟨W, hW, hc.of_iso e⟩

/-- **Moving one cone outermost.** -/
lemma isKoszul_move (p : A × ℕ) (qs : List (A × ℕ)) :
    ∀ (ℓ : List (A × ℕ)) {X X' : AffineD A}, IsKoszul (ℓ ++ p :: qs) X →
      IsKoszul (p :: (ℓ ++ qs)) X' → Nonempty (X ≅ X')
  | [], _, _, h, h' => h.iso h'
  | (c, m) :: ℓ, X, X', ⟨X₁, hX₁, hc⟩, h' => by
      obtain ⟨X'₁, ⟨X'', hX'', hq⟩, hp⟩ := h'
      -- `X'₁ = cone(c^m, X'')` and `X' = cone(p, X'₁)`
      obtain ⟨W, hW⟩ := exists_isScalarCone (p.1 ^ p.2) X''
      have hpW : IsKoszul (p :: (ℓ ++ qs)) W := ⟨X'', hX'', hW⟩
      obtain ⟨e₁⟩ := isKoszul_move p qs ℓ hX₁ hpW
      obtain ⟨V, hV⟩ := exists_isScalarCone (c ^ m) W
      obtain ⟨e₂⟩ := hc.iso e₁ hV
      obtain ⟨e₃⟩ := IsScalarCone.swap hW hV hq hp
      exact ⟨e₂ ≪≫ e₃⟩

/-- Exponents replaced by one. -/
def ones (ps : List (A × ℕ)) : List (A × ℕ) := ps.map (fun p => (p.1, 1))

/-- **Power envelope**, general form: `K(ps ++ qs) ∈ Coprod(K(ones ps ++ qs)[0,0])`. -/
lemma isKoszul_power_E : ∀ (ps qs : List (A × ℕ)) {X Y : AffineD A},
    IsKoszul (ps ++ qs) X → IsKoszul (ones ps ++ qs) Y → E Y X
  | [], _, _, _, hX, hY => by
      obtain ⟨e⟩ := hX.iso hY
      exact E_of_iso e
  | (a, n) :: ps, qs, X, Y, ⟨X₁, hX₁, hX⟩, hY => by
      obtain ⟨W, hW⟩ := exists_isScalarCone a X₁
      have hW' : IsScalarCone A (a ^ 1) X₁ W := by simpa using hW
      have h1 : E W X := coprod_of_isScalarCone_pow a hW n hX
      have hWk : IsKoszul ((a, 1) :: (ps ++ qs)) W := ⟨X₁, hX₁, hW'⟩
      obtain ⟨W', hW'k⟩ := exists_isKoszul (ps ++ (a, 1) :: qs)
      obtain ⟨eW⟩ := isKoszul_move (a, 1) qs ps hW'k hWk
      obtain ⟨Y', hY'k⟩ := exists_isKoszul (ones ps ++ (a, 1) :: qs)
      have h2 : E Y' W' := isKoszul_power_E ps ((a, 1) :: qs)
        (by simpa using hW'k) hY'k
      obtain ⟨eY⟩ := isKoszul_move (a, 1) qs (ones ps) hY'k hY
      exact E_trans (E_congr eY (E_trans h2 (E_of_iso eW.symm))) h1

lemma ones_zip (fs : List A) (ns : List ℕ) (h : ns.length = fs.length) :
    ones (fs.zip ns) = unitExponents A fs := by
  induction fs generalizing ns with
  | nil => cases ns <;> rfl
  | cons a fs ih =>
      cases ns with
      | nil => simp at h
      | cons n ns =>
          simp only [List.zip_cons_cons, ones, List.map_cons, unitExponents] at ih ⊢
          rw [ih ns (by simpa using h)]

/-- **Neeman, Construction 7.3** (finite-power envelope), proved: for every
exponent list of the right length,
`K(f₁^{n₁},…,fₙ^{nₙ}) ∈ Coprod(K(f₁,…,fₙ)[0,0])`. -/
theorem koszulList_power_coprod (fs : List A) (ns : List ℕ) (h : ns.length = fs.length) :
    Coprod (shiftInterval (koszulListData A (unitExponents A fs)).obj 0 0)
      (koszulListData A (fs.zip ns)).obj := by
  have := isKoszul_power_E (fs.zip ns) [] (X := (koszulListData A (fs.zip ns)).obj)
    (Y := (koszulListData A (unitExponents A fs)).obj)
    (by simpa using isKoszul_koszulListData (fs.zip ns))
    (by simpa [ones_zip fs ns h] using isKoszul_koszulListData (unitExponents A fs))
  exact this

end KoszulList

section Detection

/-- Injectivity of `b` on maps out of the first object of a distinguished triangle
whose first map is `b • 𝟙`, when its third object has no maps to `F`. -/
lemma eq_zero_of_smul_comp {b : A} {X C F : AffineD A} {f : X ⟶ X} {g : X ⟶ C}
    {h : C ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang (AffineD A))
    (hf : f = b • 𝟙 X) (hC : ∀ β : C ⟶ F, β = 0) (γ : X ⟶ F) (hγ : (b • 𝟙 X) ≫ γ = 0) :
    γ = 0 := by
  have hγ' : (Triangle.mk f g h).mor₁ ≫ γ = 0 := by
    change f ≫ γ = 0
    rw [hf]
    exact hγ
  obtain ⟨β, hβ⟩ := exists_factor_through_triangle_obj₃ _ hT γ hγ'
  rw [← hβ, hC β, comp_zero]

lemma eq_zero_of_pow_smul_comp {b : A} {X C F : AffineD A} {f : X ⟶ X} {g : X ⟶ C}
    {h : C ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang (AffineD A))
    (hf : f = b • 𝟙 X) (hC : ∀ β : C ⟶ F, β = 0) :
    ∀ (m : ℕ) (γ : X ⟶ F), (b ^ m • 𝟙 X) ≫ γ = 0 → γ = 0
  | 0, γ, hγ => by simpa using hγ
  | m + 1, γ, hγ => by
      apply eq_zero_of_pow_smul_comp hT hf hC m
      apply eq_zero_of_smul_comp hT hf hC
      rw [← Category.assoc, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
        ← pow_succ']
      exact hγ

/-- **Koszul zero detection**: the degree-one finite Koszul object detects zero on
complexes supported on `V(f₁,…,fₙ)`. -/
theorem koszulList_detects_zero : ∀ (fs : List A) (F : AffineD A),
    AffineIsSupportedIdeal A (functionIdeal A fs) F →
    (∀ k : ℤ, ∀ g : (koszulListData A (unitExponents A fs)).obj⟦k⟧ ⟶ F, g = 0) → IsZero F
  | [], F, _, hF => NeemanPreferredM6.ringObject_isPaperGenerator A hF
  | a :: fs, F, hsupp, hF => by
      change AffineIsSupportedIdeal A (Ideal.span {a} ⊔ functionIdeal A fs) F at hsupp
      rw [affineIsSupportedIdeal_sup, affineIsSupportedIdeal_span_singleton] at hsupp
      obtain ⟨ha, hfs⟩ := hsupp
      apply koszulList_detects_zero fs F hfs
      intro k γ
      let Y := (koszulListData A (unitExponents A fs)).obj
      have hY : Perf A Y := (koszulListData A (unitExponents A fs)).perfect
      let D := scalarConeData A (a ^ 1) hY
      have hT := Triangle.shift_distinguished _ D.distinguished k
      let u : A := ((k.negOnePow : ℤ) : A)
      have hf : k.negOnePow • (a ^ 1 • 𝟙 Y)⟦k⟧' = (u * a) • 𝟙 (Y⟦k⟧) := by
        rw [Functor.map_smul, CategoryTheory.Functor.map_id, pow_one, mul_smul, Units.smul_def]
        exact (Int.cast_smul_eq_zsmul A _ _).symm
      obtain ⟨m, -, hm⟩ := perf_sourcePowerTorsion A a (perf_shift A hY k) F ha γ
      refine eq_zero_of_pow_smul_comp hT hf (fun β => hF k β) m γ ?_
      rw [mul_pow, mul_smul, Linear.smul_comp]
      erw [hm]
      rw [smul_zero]

end Detection

end

end RelativeFM.KoszulFiniteInputs

#print axioms RelativeFM.KoszulFiniteInputs.IsScalarCone.swap
#print axioms RelativeFM.KoszulFiniteInputs.coprod_of_isScalarCone_pow
#print axioms RelativeFM.KoszulFiniteInputs.koszulList_power_coprod
#print axioms RelativeFM.KoszulFiniteInputs.koszulList_detects_zero
