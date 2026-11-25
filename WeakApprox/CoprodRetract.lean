/-
Retract closure of a nonnegative `Coprod` class.  The proof reuses the
`ULift ℕ` Eilenberg swindle already constructed in `WeakApprox.Proposition48`,
but transports the split triangle in the opposite order so that only a
positive shift is needed.
-/
import WeakApprox.Proposition48
import WeakApprox.Lemma35

@[expose] public section

namespace RelativeWeakApprox.CoprodRetractM3

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A nonnegative `Coprod` class is closed under positive shifts. -/
lemma shift_one {G : C} {X : C} (hX : Coprod (shiftTail G 0) X) :
    Coprod (shiftTail G 0) (X⟦(1 : ℤ)⟧) := by
  have h := map_shift_Coprod (shiftTail G 0) (1 : ℤ) hX
  rw [shiftImage_shiftTail] at h
  apply Coprod_mono _ _ h
  rintro Y ⟨n, hn, e⟩
  exact ⟨n, by omega, e⟩

/-- A retract of an object of `Coprod (shiftTail G 0)` lies in the same
class, assuming small coproducts in the ambient category. -/
theorem mem_coprod_shiftTail_of_retract {G X Y : C}
    (hcop : ∀ Z : C, HasCoproduct (fun _ : ULift.{v} ℕ => Z))
    (h : Retract X Y) (hY : Coprod (shiftTail G 0) Y) :
    Coprod (shiftTail G 0) X := by
  obtain ⟨X', ⟨e⟩⟩ := retract_exists_biprod_complement h
  let _ := hcop (X ⊞ X')
  have hY' : Coprod (shiftTail G 0) (X ⊞ X') := .of_isoClosure e hY
  let Z : C := ∐ fun _ : ULift.{v} ℕ => X ⊞ X'
  have hZ : Coprod (shiftTail G 0) Z :=
    Coprod.of_sigma (fun _ : ULift.{v} ℕ => X ⊞ X') (fun _ => hY')
  let eZ : Z ⊞ X ≅ Z := (biprod.braiding Z X) ≪≫ swindleIso X X'
  let T := Triangle.mk (biprod.inl ≫ eZ.hom) (eZ.inv ≫ biprod.snd) 0
  let eT : binaryBiproductTriangle Z X ≅ T :=
    Triangle.isoMk _ _ (Iso.refl Z) eZ (Iso.refl X)
      (by
        show biprod.inl ≫ eZ.hom = 𝟙 Z ≫ (biprod.inl ≫ eZ.hom)
        simp)
      (by
        show (biprod.snd : Z ⊞ X ⟶ X) ≫ 𝟙 X = eZ.hom ≫ (eZ.inv ≫ biprod.snd)
        simp)
      (by
        show (0 : X ⟶ Z⟦(1 : ℤ)⟧) ≫ (shiftFunctor C 1).map (𝟙 Z) =
          𝟙 X ≫ (0 : X ⟶ Z⟦(1 : ℤ)⟧)
        simp)
  have hT : T ∈ distTriang C := isomorphic_distinguished (binaryBiproductTriangle Z X)
    (binaryBiproductTriangle_distinguished Z X) T eT.symm
  exact Coprod.of_extension T.rotate (rot_of_distTriang T hT) hZ (shift_one hZ)


/-- Nonnegative shifts preserve membership in a nonnegative `Coprod` class. -/
lemma shift_nonneg {G : C} {n : ℤ} (hn : 0 ≤ n) {X : C}
    (hX : Coprod (shiftTail G 0) X) : Coprod (shiftTail G 0) (X⟦n⟧) := by
  have h := map_shift_Coprod (shiftTail G 0) n hX
  rw [shiftImage_shiftTail] at h
  apply Coprod_mono _ _ h
  rintro Y ⟨m, hm, e⟩
  exact ⟨m, by omega, e⟩

/-- A shift of a generator belongs to its own nonnegative `Coprod` class. -/
lemma self {G : C} : Coprod (shiftTail G 0) G :=
  Coprod.of_mem _ ⟨0, le_rfl, ⟨(shiftFunctorZero C ℤ).symm.app G⟩⟩

/-- Adjoining a biproduct summand already lying in the class does not change
the class. -/
theorem coprod_shiftTail_biprod_eq_of_mem {G H : C}
    (hcop : ∀ Z : C, HasCoproduct (fun _ : ULift.{v} ℕ => Z))
    (hH : Coprod (shiftTail G 0) H) :
    Coprod (shiftTail (G ⊞ H) 0) = Coprod (shiftTail G 0) := by
  have hGself : Coprod (shiftTail G 0) G := self
  have hGHself : Coprod (shiftTail (G ⊞ H) 0) (G ⊞ H) := self
  have hG : Coprod (shiftTail (G ⊞ H) 0) G :=
    mem_coprod_shiftTail_of_retract hcop (BinaryBiproduct.bicone G H).retract_left hGHself
  have hGH : Coprod (shiftTail G 0) (G ⊞ H) :=
    Coprod.of_extension (binaryBiproductTriangle G H)
      (binaryBiproductTriangle_distinguished G H) hGself hH
  apply le_antisymm
  · apply Coprod.le
    rintro X ⟨n, hn, ⟨e⟩⟩
    exact (Coprod (shiftTail G 0)).prop_of_iso e.symm (shift_nonneg (G := G) hn hGH)
  · apply Coprod.le
    rintro X ⟨n, hn, ⟨e⟩⟩
    exact (Coprod (shiftTail (G ⊞ H) 0)).prop_of_iso e.symm
      (shift_nonneg (G := G ⊞ H) hn hG)

end RelativeWeakApprox.CoprodRetractM3

#print axioms RelativeWeakApprox.CoprodRetractM3.shift_one
#print axioms RelativeWeakApprox.CoprodRetractM3.mem_coprod_shiftTail_of_retract
#print axioms RelativeWeakApprox.CoprodRetractM3.coprod_shiftTail_biprod_eq_of_mem
