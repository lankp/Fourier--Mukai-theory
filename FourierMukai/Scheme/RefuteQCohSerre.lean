/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import FourierMukai.Scheme.QCohSerre
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Data.Nat.Prime.Int

/-!
# F3: quasi-coherent sheaves on `Spec ℤ` are not closed under subobjects

Refutation **F3** of `results/OPEN_INPUTS.md` §0 (task `wave6/vacuity-refutations`,
rule 3 of `CLAUDE.md`).

`QuasicoherentSerreInput X` (`Scheme/Derived.lean`) asserts that `Qcoh(X)` is a Serre
class of `X.Modules`, and `QuasicoherentStrongClosureInput X` (`Scheme/QCohSerre.lean`)
asserts, among other things, that it is closed under arbitrary `𝒪_X`-submodules.
Stacks Tag 01LA asserts closure under kernels, cokernels and extensions only, and the
stronger statements are **false** for `X = Spec ℤ`
(`not_quasicoherentSerreInput_spec_int`, `not_quasicoherentStrongClosureInput_spec_int`).

## The counterexample

For a point `x₀` of a scheme `X`, let `𝒪_X(x₀) ⊆ 𝒪_X` be the subsheaf of sections
whose germ at `x₀` vanishes (no condition on opens not containing `x₀`)
(`germVanishingSubmodule`, a `SheafOfModules.Submodule` of the unit sheaf; locality
of the condition is immediate).  On `X = Spec R`, `R` a domain, `x₀ ∋ f` with
`f ≠ 0`:

* its global sections vanish, since germs of an integral scheme are injective;
* its sections over `D(f) ∌ x₀` are all of `𝒪(D(f)) ≠ 0`.

A quasi-coherent sheaf on an affine scheme is `M̃` for its global sections
(Mathlib's `isQuasicoherent_iff_isIso_fromTildeΓ`), so it would be zero: a
contradiction (`not_isQuasicoherent_germVanishing`).  For `R = ℤ`, `x₀ = (2)`,
`f = 2`, this is the subsheaf `j_!𝒪_U ⊂ 𝒪_X` of the sketch in §0 (`U = D(2)`).

The negated propositions are the tree's own `QuasicoherentSerreInput` and
`QuasicoherentStrongClosureInput` (`quasiCoherent X` is Mathlib's
`SheafOfModules.isQuasicoherent X.ringCatSheaf`).  Nothing is assumed.

**Consumers made vacuous at `Spec ℤ`:** every declaration taking a
`QuasicoherentSerreInput X` or `QuasicoherentStrongClosureInput X` argument, e.g.
`isDQCohTriangulatedOfInput` and `quasicoherentSerreInputOfStrongClosure`.  None of
them is pinned in `results/statement-baseline.txt`; the extension-only route
(`QuasicoherentExtensionInput`) is unaffected.
-/

@[expose] public section

namespace RelativeFM.VacuityF3

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

section General

variable {X : Scheme.{u}} (x₀ : X)

/-- The sections of `𝒪_X` whose germ at `x₀` vanishes (all sections on opens not
containing `x₀`). -/
def germVanishingSubmodule : (SheafOfModules.unit X.ringCatSheaf).Submodule where
  obj U :=
    { carrier := {s | ∀ h : x₀ ∈ U.unop,
        X.presheaf.germ U.unop x₀ h (s : Γ(X, U.unop)) = 0}
      add_mem' := fun {a b} ha hb h => by
        have e := map_add (X.presheaf.germ U.unop x₀ h).hom (a : Γ(X, U.unop)) b
        have ha' : (X.presheaf.germ U.unop x₀ h).hom (a : Γ(X, U.unop)) = 0 := ha h
        have hb' : (X.presheaf.germ U.unop x₀ h).hom (b : Γ(X, U.unop)) = 0 := hb h
        exact e.trans ((congrArg₂ (· + ·) ha' hb').trans (add_zero 0))
      zero_mem' := fun h => map_zero (X.presheaf.germ U.unop x₀ h).hom
      smul_mem' := fun r s hs h => by
        have e := map_mul (X.presheaf.germ U.unop x₀ h).hom (r : Γ(X, U.unop)) s
        have hs' : (X.presheaf.germ U.unop x₀ h).hom (s : Γ(X, U.unop)) = 0 := hs h
        exact e.trans ((congrArg (_ * ·) hs').trans (mul_zero _)) }
  map {U V} f s hs h := by
    have e := TopCat.Presheaf.germ_res_apply X.presheaf f.unop x₀ h (s : Γ(X, U.unop))
    exact e.trans (hs _)
  isSheaf U s hs h := by
    obtain ⟨V, g, hg, hV⟩ := hs x₀ h
    have e := TopCat.Presheaf.germ_res_apply X.presheaf g x₀ hV (s : Γ(X, U.unop))
    exact e.symm.trans (hg hV)

/-- The subsheaf `𝒪_X(x₀) ⊆ 𝒪_X` of sections with vanishing germ at `x₀`. -/
def germVanishing : X.Modules := (germVanishingSubmodule x₀).toSheafOfModules

/-- The inclusion `𝒪_X(x₀) ⟶ 𝒪_X`, a monomorphism. -/
def germVanishingι : germVanishing x₀ ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (germVanishingSubmodule x₀).ι

instance : Mono (germVanishingι x₀) :=
  (inferInstance : @Mono (SheafOfModules X.ringCatSheaf) _ _ _ (germVanishingSubmodule x₀).ι)

end General

section Affine

variable {R : CommRingCat.{u}} [IsDomain R]

/-- On `Spec R` with `R` a domain, `𝒪(x₀)` is not quasi-coherent as soon as some
`f ≠ 0` lies in `x₀`: its global sections vanish but its sections over
`D(f) ∌ x₀` do not. -/
theorem not_isQuasicoherent_germVanishing (x₀ : Spec R) (f : R) (hf0 : f ≠ 0)
    (hfx : f ∈ x₀.asIdeal) : ¬ (germVanishing x₀).IsQuasicoherent := by
  intro hqc
  -- global sections vanish
  have hsub : Subsingleton ((germVanishingSubmodule x₀).obj (op ⊤)) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have hinj := germ_injective_of_isIntegral (Spec R) (U := ⊤) x₀ trivial
    have ha : (Spec R).presheaf.germ ⊤ x₀ trivial (a.1 : Γ(Spec R, ⊤)) = 0 := a.2 trivial
    have hb : (Spec R).presheaf.germ ⊤ x₀ trivial (b.1 : Γ(Spec R, ⊤)) = 0 := b.2 trivial
    exact hinj (ha.trans hb.symm)
  have hΓ : IsZero ((modulesSpecToSheaf.obj (germVanishing x₀)).presheaf.obj (op ⊤)) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact hsub
  have hiso : IsIso (germVanishing x₀).fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).1 hqc
  have hz : IsZero (germVanishing x₀) :=
    ((tilde.functor R).map_isZero hΓ).of_iso (asIso (germVanishing x₀).fromTildeΓ).symm
  -- sections over `D(f)` do not vanish
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  have hx₀U : x₀ ∉ U := fun h => (PrimeSpectrum.mem_basicOpen f x₀).1 h hfx
  have h1 : (𝟙 (germVanishing x₀) : germVanishing x₀ ⟶ germVanishing x₀) = 0 :=
    hz.eq_of_src _ _
  have h2 := congrArg (fun φ => Scheme.Modules.Hom.app φ U) h1
  simp only [Scheme.Modules.Hom.id_app, Scheme.Modules.Hom.zero_app] at h2
  let η : Spec R := ⟨⊥, Ideal.isPrime_bot⟩
  have hηU : η ∈ U := (PrimeSpectrum.mem_basicOpen f η).2 hf0
  let one : (germVanishingSubmodule x₀).obj (op U) := ⟨(1 : Γ(Spec R, U)), fun h => absurd h hx₀U⟩
  have h3 := ConcreteCategory.congr_hom h2 (one : Γ(germVanishing x₀, U))
  simp only [AddCommGrpCat.hom_id, AddCommGrpCat.hom_zero] at h3
  have h10 : ((1 : Γ(Spec R, U)) : Γ(Spec R, U)) = 0 := congrArg Subtype.val h3
  have := congrArg ((Spec R).presheaf.germ U η hηU) h10
  rw [map_one, map_zero] at this
  exact one_ne_zero this

end Affine

section Int

/-- The point `(2)` of `Spec ℤ`. -/
def pointTwo : Spec (CommRingCat.of ℤ) :=
  (⟨Ideal.span {(2 : ℤ)}, (Ideal.span_singleton_prime two_ne_zero).2 Int.prime_two⟩ :
    PrimeSpectrum ℤ)

/-- The structure sheaf of `Spec ℤ` is quasi-coherent. -/
lemma unit_isQuasicoherent_spec_int :
    quasiCoherent (Spec (CommRingCat.of ℤ))
      (SheafOfModules.unit (Spec (CommRingCat.of ℤ)).ringCatSheaf) :=
  inferInstanceAs ((tilde (ModuleCat.of (CommRingCat.of ℤ) (CommRingCat.of ℤ))).IsQuasicoherent)

/-- **F3.**  Quasi-coherent sheaves on `Spec ℤ` are not closed under subobjects:
`𝒪(2) ⊂ 𝒪_{Spec ℤ}` (sections vanishing at `(2)`; this is `j_!𝒪_{D(2)}`) is not
quasi-coherent. -/
theorem not_quasiCoherent_isClosedUnderSubobjects_spec_int :
    ¬ (quasiCoherent (Spec (CommRingCat.of ℤ))).IsClosedUnderSubobjects := by
  intro h
  have hq := h.prop_of_mono (germVanishingι pointTwo) unit_isQuasicoherent_spec_int
  refine not_isQuasicoherent_germVanishing pointTwo (2 : ℤ) two_ne_zero ?_ hq
  exact Ideal.subset_span rfl

/-- **F3.**  `QuasicoherentSerreInput (Spec ℤ)` is false: its field `serreClass`
contains closure under subobjects.  Every declaration taking a
`QuasicoherentSerreInput X` (e.g. `isDQCohTriangulatedOfInput`) is vacuous at
`X = Spec ℤ`. -/
theorem not_quasicoherentSerreInput_spec_int :
    ¬ QuasicoherentSerreInput (Spec (CommRingCat.of ℤ)) := fun h =>
  not_quasiCoherent_isClosedUnderSubobjects_spec_int h.serreClass.toIsClosedUnderSubobjects

/-- **F3.**  `QuasicoherentStrongClosureInput (Spec ℤ)` is false: its field
`subobjects` fails.  So `quasicoherentSerreInputOfStrongClosure` is vacuous at
`Spec ℤ`. -/
theorem not_quasicoherentStrongClosureInput_spec_int :
    ¬ QuasicoherentStrongClosureInput (Spec (CommRingCat.of ℤ)) := fun h =>
  not_quasiCoherent_isClosedUnderSubobjects_spec_int h.subobjects

end Int

end

end RelativeFM.VacuityF3

#print axioms RelativeFM.VacuityF3.germVanishingSubmodule
#print axioms RelativeFM.VacuityF3.not_isQuasicoherent_germVanishing
#print axioms RelativeFM.VacuityF3.not_quasiCoherent_isClosedUnderSubobjects_spec_int
#print axioms RelativeFM.VacuityF3.not_quasicoherentSerreInput_spec_int
#print axioms RelativeFM.VacuityF3.not_quasicoherentStrongClosureInput_spec_int
