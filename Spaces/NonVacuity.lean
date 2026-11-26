/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import Spaces.RelativePerfect
import Spaces.IntegralTransform

/-!
# Non-vacuity of the algebraic-space vocabulary

CLAUDE.md, verification step 5: every hypothesis-carrying notion of `Spaces/` is
satisfiable.  Proved here, with no tagged input:

* an algebraic space exists for every base `(B, S, hS)`: the representable space of the base
  scheme (`yonedaSpace`, Stacks 025Z), `baseSpace`;
* a zero object of `D(X)` lies in `D_qc(X)`, `D^b_qc(X)`, `D^-_qc(X)`, `D^-_coh(X)`,
  `D^b_coh(X)`, `Perf(X)`, is pseudo-coherent, and lies in `D_{qc,T}(X)` for `T = |X|`;
* a zero object is `f`-perfect (GL26 Def 4.1, `def:relative_perf_stacks`) and
  `f`-quasi-perfect (GL26 Def 5.1, `def:quasi_perf`) for every `f`;
* `Φ_0` is a zero functor (`Spaces/IntegralTransform.lean`).

For `D_{qc,T}(X)` with an arbitrary `T`, a zero object is supported on `T` because its
cohomology sheaves have empty support; that needs the stalks of the zero sheaf to be
subsingletons, i.e. that the étale neighbourhoods of a geometric point form a connected
(indeed cofiltered) category, which AxiomMath proves only outside the import list.  The
witness is therefore given for `T = |X|`, which already shows the notion is satisfiable.

The proofs that a zero object is perfect and pseudo-coherent build the local models directly
from Stacks 08G5 / 08FT (the zero complex is strictly perfect and the zero map to the
restriction of a zero complex is an isomorphism).  The proof that a zero module is coherent
in the sense of Stacks 03DL(8) is AxiomMath's `SheafOfModules.IsCoherentOnSite.of_isZero`
(`StacksFrontier/AlgebraicGeometry/Spaces/CoherentModules.lean`, outside the import list),
reproduced here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space Opposite
open ZeroObject

namespace RelativeFM.Spaces

universe u

/-! ### Zero modules are coherent (Stacks 03DL(8)) -/

section Coherent

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Every object of a site covers the final object, as the family of all objects
(AxiomMath's `GrothendieckTopology.coversTop_self`, reproduced). -/
theorem coversTop_self (J : GrothendieckTopology C) : J.CoversTop (fun Y : C => Y) := fun Y =>
  Sieve.id_mem_iff_eq_top.1
    ((Sieve.mem_ofObjects_iff (fun Y : C => Y) (𝟙 Y)).2 ⟨Y, ⟨𝟙 Y⟩⟩) ▸ J.top_mem Y

/-- Every section of a zero sheaf of modules vanishes (AxiomMath's
`Stacks.SheafOfModules.eq_zero_of_isZero`, reproduced). -/
theorem eq_zero_of_isZero {Z : SheafOfModules.{u} R} (hZ : IsZero Z) (X : Cᵒᵖ)
    (x : Z.val.obj X) : x = 0 := by
  have h : (𝟙 Z : Z ⟶ Z).val.app X x = (0 : Z ⟶ Z).val.app X x := by
    rw [hZ.eq_of_src (𝟙 Z) 0]
  have h0 : (0 : Z ⟶ Z).val.app X x = 0 := by
    change (0 : Z.val ⟶ Z.val).app X x = 0
    simp
  simpa [h0] using h

/-- A zero sheaf of modules is of finite type (AxiomMath's
`PresheafOfModules.isFiniteType_of_isZero`, reproduced). -/
theorem isFiniteType_of_isZero {M : SheafOfModules.{u} R} (hM : IsZero M) :
    PresheafOfModules.IsFiniteType J M.val := by
  refine ⟨C, fun Y => Y, coversTop_self J, fun _ => ⟨0, fun j => j.elim0, ?_⟩⟩
  intro V f t
  refine ⟨⊤, J.top_mem V, fun W g _ => ⟨fun j => j.elim0, ?_⟩⟩
  rw [Fin.sum_univ_zero, eq_zero_of_isZero hM _ t, map_zero]

/-- **Stacks 03DL(8) for a zero module**: a zero sheaf of modules is coherent (AxiomMath's
`SheafOfModules.IsCoherentOnSite.of_isZero`, reproduced). -/
theorem isCoherentOnSite_of_isZero {M : SheafOfModules.{u} R} (hM : IsZero M) :
    SheafOfModules.IsCoherentOnSite M where
  isFiniteType := isFiniteType_of_isZero hM
  kernel_isFiniteType U n s := by
    have hsum : ∀ {A : Type u} [Ring A] {p : _root_.Submodule A (Fin n → A)} (c : Fin n → A)
        (y : Fin n → p) (j : Fin n), ((∑ i, c i • y i) : p).val j = ∑ i, c i * (y i).val j := by
      intro A _ p c y j
      simp
    have hres : ∀ {V' W' : Over U} (h : W' ⟶ V')
        (y : (PresheafOfModules.relations M.val s).obj (op V')) (k : Fin n),
        (((PresheafOfModules.relations M.val s).restrictₛₗ h.op) y).val k
          = R.obj.map h.left.op (y.val k) := fun _ _ _ => rfl
    refine ⟨Over U, fun Z => Z, coversTop_self (J.over U), fun Z => ⟨n, fun j =>
      ⟨Pi.single j 1, LinearMap.mem_ker.2 (eq_zero_of_isZero hM _ _)⟩, ?_⟩⟩
    intro V f t
    refine ⟨⊤, (J.over U).top_mem V, fun W g _ =>
      ⟨fun j => R.obj.map g.left.op (t.val j), ?_⟩⟩
    refine Subtype.ext (funext fun j => ?_)
    refine (hsum (p := LinearMap.ker (Fintype.linearCombination
      (R.obj.obj (op W.left)) (fun i => M.val.restrictₛₗ W.hom.op (s i))))
      (fun i => R.obj.map g.left.op (t.val i)) _ j).trans ?_
    rw [hres g t j]
    have hδ : ∀ i : Fin n,
        (((PresheafOfModules.relations M.val s).restrictₛₗ (g ≫ f).op)
          ⟨Pi.single i 1, LinearMap.mem_ker.2 (eq_zero_of_isZero hM _ _)⟩).val j
          = if i = j then (1 : R.obj.obj (op W.left)) else 0 := by
      intro i
      refine Eq.trans (hres (g ≫ f) _ j) ?_
      by_cases h : i = j
      · subst h; simp
      · simp [Ne.symm h, h]
    simp only [hδ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Coherent

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### An algebraic space exists -/

/-- The base scheme `S` as an algebraic space over itself: the representable presheaf of the
identity of `S` in `(Sch/S)_fppf` (AxiomMath's `yonedaSpace`, Stacks 025Z). -/
abbrev baseSpace (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    AlgebraicSpaces B S hS :=
  yonedaSpace B S hS (Over.mk (𝟙 (B.obj hS)))

instance (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Nonempty (AlgebraicSpaces B S hS) :=
  ⟨baseSpace B S hS⟩

/-! ### Zero objects lie in every subcategory -/

variable {X Y : AlgebraicSpaces B S hS}

/-- The cohomology sheaves of a zero object are zero. -/
theorem isZero_homology_of_isZero {E : D B S hS X} (hE : IsZero E) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj E) :=
  (DerivedCategory.homologyFunctor _ n).map_isZero hE

theorem Dqc_of_isZero {E : D B S hS X} (hE : IsZero E) : Dqc X E :=
  fun n => SheafOfModules.IsQuasicoherentOnSite.of_isZero (isZero_homology_of_isZero hE n)

theorem Dbqc_of_isZero {E : D B S hS X} (hE : IsZero E) : Dbqc X E :=
  ⟨DerivedCategoryB.isBounded_of_isZero hE, Dqc_of_isZero hE⟩

theorem DminusQc_of_isZero {E : D B S hS X} (hE : IsZero E) : DminusQc X E :=
  ⟨DerivedCategoryB.isBoundedAbove_of_isZero hE, Dqc_of_isZero hE⟩

theorem DminusCoh_of_isZero {E : D B S hS X} (hE : IsZero E) : DminusCoh X E :=
  ⟨DerivedCategoryB.isBoundedAbove_of_isZero hE, fun n =>
    ⟨SheafOfModules.IsQuasicoherentOnSite.of_isZero (isZero_homology_of_isZero hE n),
      isCoherentOnSite_of_isZero (isZero_homology_of_isZero hE n)⟩⟩

/-- A zero complex is strictly perfect (Stacks 08FL). -/
theorem isStrictlyPerfect_of_isZero {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    {P : CochainComplex (SheafOfModules.{u} R) ℤ} (hP : IsZero P) :
    IsStrictlyPerfect R P where
  bounded := by
    convert Set.finite_empty
    ext i
    simpa using (HomologicalComplex.eval _ _ i).map_isZero hP
  termDirectSummand i := by
    rw [isDirectSummandOfFiniteFree_iff_free]
    exact ⟨0, 0, 0, ((HomologicalComplex.eval _ _ i).map_isZero hP).eq_of_src _ _⟩

/-- The zero map from the zero complex to the restriction of the zero complex of
`𝒪_X`-modules to a slice is an isomorphism. -/
theorem isIso_zero_restrictComplex_zero (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    IsIso (0 : (0 : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over
          V)) ℤ) ⟶ (smallEtaleRingedSite B S hS X.1 X.2).restrictComplex
            (0 : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) V) :=
  isIso_of_source_target_iso_zero _ (isZero_zero _).isoZero
    (Functor.map_isZero _ (isZero_zero _)).isoZero

/-- The covering sieve used for the zero complex: the maximal one. -/
theorem generate_top_mem (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    Sieve.generate (⊤ : Presieve U) ∈ (smallEtaleRingedSite B S hS X.1 X.2).J U := by
  rw [Sieve.generate_top]
  exact GrothendieckTopology.top_mem _ _

/-- **A zero object of `D(X)` is perfect** (Stacks 08G5): it is the image of the zero
complex, which is locally (on the maximal covering of every object) isomorphic to the zero
complex, a strictly perfect one. -/
theorem Perf_of_isZero {E : D B S hS X} (hE : IsZero E) : Perf X E :=
  ⟨0, fun U => ⟨⊤, generate_top_mem U, fun V _ _ =>
    ⟨0, isStrictlyPerfect_of_isZero (isZero_zero _), 0,
      have := isIso_zero_restrictComplex_zero V; inferInstance⟩⟩,
    ⟨(DerivedCategory.Q.map_isZero (isZero_zero _)).iso hE⟩⟩

/-- **A zero object of `D(X)` is pseudo-coherent** (Stacks 08FT). -/
theorem IsPseudoCoherent_of_isZero {E : D B S hS X} (hE : IsZero E) : IsPseudoCoherent X E :=
  ⟨0, fun _ U => ⟨⊤, generate_top_mem U, fun V _ _ =>
    ⟨0, isStrictlyPerfect_of_isZero (isZero_zero _), 0,
      have := isIso_zero_restrictComplex_zero V
      ⟨fun _ _ => inferInstance, inferInstance⟩⟩⟩,
    ⟨(DerivedCategory.Q.map_isZero (isZero_zero _)).iso hE⟩⟩

theorem DbCoh_of_isZero {E : D B S hS X} (hE : IsZero E) : DbCoh X E :=
  ⟨Dbqc_of_isZero hE, IsPseudoCoherent_of_isZero hE⟩

/-- A zero object lies in `D_{qc,T}(X)` for `T = |X|` (see the module docstring for general
`T`). -/
theorem DqcSupported_univ_of_isZero {E : D B S hS X} (hE : IsZero E) :
    DqcSupported X Set.univ E :=
  ⟨Dqc_of_isZero hE, fun _ => Set.subset_univ _⟩

/-! ### Relative perfectness -/

/-- **A zero object is `f`-perfect** (GL26 Definition 4.1, `def:relative_perf_stacks`), for
every morphism `f`. -/
theorem isRelativelyPerfect_of_isZero (f : Y ⟶ X) {E : D B S hS Y} (hE : IsZero E) :
    IsRelativelyPerfect f E :=
  ⟨Dqc_of_isZero hE, fun _ _ => Dbqc_of_isZero (isZero_tensorObj_left hE _)⟩

/-- **A zero object is `f`-quasi-perfect** (GL26 Definition 5.1, `def:quasi_perf`), for every
morphism `f`. -/
theorem isQuasiPerfect_of_isZero (f : Y ⟶ X) {E : D B S hS Y} (hE : IsZero E) :
    IsQuasiPerfect f E :=
  ⟨Dqc_of_isZero hE, fun P _ => Perf_of_isZero (isZero_push_obj f (isZero_tensorObj_left hE P))⟩

/-- The notions are inhabited on an actual algebraic space and an actual morphism: the
identity of the base space, with the zero object. -/
example : IsRelativelyPerfect (𝟙 (baseSpace B S hS)) 0 ∧ IsQuasiPerfect (𝟙 (baseSpace B S hS)) 0 ∧
    DbCoh (baseSpace B S hS) 0 ∧ DminusCoh (baseSpace B S hS) 0 :=
  ⟨isRelativelyPerfect_of_isZero _ (isZero_zero _), isQuasiPerfect_of_isZero _ (isZero_zero _),
    DbCoh_of_isZero (isZero_zero _), DminusCoh_of_isZero (isZero_zero _)⟩

end RelativeFM.Spaces
