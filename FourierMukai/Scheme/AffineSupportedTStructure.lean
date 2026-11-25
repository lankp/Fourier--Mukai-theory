import FourierMukai.Scheme.AffineSupportedAssembly
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

@[expose] public section

namespace RelativeFM.Recollement.AssemblyM6

open RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open ZeroObject

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

open RelativeFM

/-- On cohomology in degrees at most `n`, the map from the `≤ n` truncation
is an isomorphism. -/
lemma isIso_homology_truncLEι {A : Type u} [CommRing A]
    (X : AffineD A) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app X)) := by
  let t : TStructure (AffineD A) := DerivedCategory.TStructure.t
  let T := (t.triangleLEGE n (n + 1) (by omega)).obj X
  have hT : T ∈ distTriang (AffineD A) := t.triangleLEGE_distinguished n (n + 1) (by omega) X
  have hz (k : ℤ) (hk : k < n + 1) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj
        ((t.truncGE (n + 1)).obj X)) :=
    DerivedCategory.isZero_of_isGE _ (n + 1) k hk
  have hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app X)) := by
    apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mpr
    exact (hz i (by omega)).eq_of_tgt _ _
  have hmono : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app X)) := by
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hT (i - 1) i (by omega)).mpr
    exact (hz (i - 1) (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- On cohomology in degrees at least `n + 1`, the map to the `≥ n + 1`
truncation is an isomorphism. -/
lemma isIso_homology_truncGEπ {A : Type u} [CommRing A]
    (X : AffineD A) (n i : ℤ) (hi : n < i) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((DerivedCategory.TStructure.t.truncGEπ (n + 1)).app X)) := by
  let t : TStructure (AffineD A) := DerivedCategory.TStructure.t
  let T := (t.triangleLEGE n (n + 1) (by omega)).obj X
  have hT : T ∈ distTriang (AffineD A) := t.triangleLEGE_distinguished n (n + 1) (by omega) X
  have hz (k : ℤ) (hk : n < k) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj
        ((t.truncLE n).obj X)) :=
    DerivedCategory.isZero_of_isLE _ n k hk
  have hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((DerivedCategory.TStructure.t.truncGEπ (n + 1)).app X)) := by
    apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
      T hT i (i + 1) (by omega)).mpr
    exact (hz (i + 1) (by omega)).eq_of_tgt _ _
  have hmono : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((DerivedCategory.TStructure.t.truncGEπ (n + 1)).app X)) := by
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i).mpr
    exact (hz i hi).eq_of_src _ _
  exact isIso_of_mono_of_epi _


/-- The standard `≤ n` truncation preserves cohomology with `f`-power-torsion
support. -/
lemma affineIsSupported_truncLE {A : Type u} [CommRing A] (f : A)
    (X : AffineD A) (hX : AffineIsSupported A f X) (n : ℤ) :
    AffineIsSupported A f ((DerivedCategory.TStructure.t.truncLE n).obj X) := by
  intro i
  by_cases hi : n < i
  · exact (PowerTorsion A f).prop_of_isZero
      (DerivedCategory.isZero_of_isLE _ n i hi)
  · have hi' : i ≤ n := by omega
    let _ := isIso_homology_truncLEι X n i hi'
    exact (PowerTorsion A f).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((DerivedCategory.TStructure.t.truncLEι n).app X))).symm (hX i)

/-- The standard `≥ n + 1` truncation preserves cohomology with
`f`-power-torsion support. -/
lemma affineIsSupported_truncGE {A : Type u} [CommRing A] (f : A)
    (X : AffineD A) (hX : AffineIsSupported A f X) (n : ℤ) :
    AffineIsSupported A f ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj X) := by
  intro i
  by_cases hi : n < i
  · let _ := isIso_homology_truncGEπ X n i hi
    exact (PowerTorsion A f).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((DerivedCategory.TStructure.t.truncGEπ (n + 1)).app X))) (hX i)
  · exact (PowerTorsion A f).prop_of_isZero
      (DerivedCategory.isZero_of_isGE _ (n + 1) i (by omega))

/-- The supported category inherits the standard `t`-structure.  Stability
under both truncations is proved from the long exact homology sequence and the
Serre property of power-torsion modules. -/
noncomputable instance affineIsSupported_hasInducedTStructure
    (A : Type u) [CommRing A] (f : A) :
    (AffineIsSupported A f).HasInducedTStructure (AffineD.standardTStructure A) := by
  apply ObjectProperty.HasInducedTStructure.mk'
  intro X hX n
  constructor
  · exact affineIsSupported_truncLE f X hX n
  · change AffineIsSupported A f ((DerivedCategory.TStructure.t.truncGE n).obj X)
    simpa using affineIsSupported_truncGE f X hX (n - 1)

/-- The standard `t`-structure on `AffineDZ A f`, induced by the standard
`t`-structure on `AffineD A`. -/
noncomputable def affineDZStandardTStructure (A : Type u) [CommRing A] (f : A) :
    TStructure (AffineDZ A f) :=
  (AffineIsSupported A f).tStructure (AffineD.standardTStructure A)

@[simp] lemma affineDZStandardTStructure_le (A : Type u) [CommRing A] (f : A)
    (X : AffineDZ A f) (n : ℤ) :
    (affineDZStandardTStructure A f).le n X = (AffineD.standardTStructure A).le n X.obj := rfl

@[simp] lemma affineDZStandardTStructure_ge (A : Type u) [CommRing A] (f : A)
    (X : AffineDZ A f) (n : ℤ) :
    (affineDZStandardTStructure A f).ge n X = (AffineD.standardTStructure A).ge n X.obj := rfl

end
end RelativeFM.Recollement.AssemblyM6

#print axioms RelativeFM.Recollement.AssemblyM6.isIso_homology_truncLEι
#print axioms RelativeFM.Recollement.AssemblyM6.isIso_homology_truncGEπ
#print axioms RelativeFM.Recollement.AssemblyM6.affineIsSupported_truncLE
#print axioms RelativeFM.Recollement.AssemblyM6.affineIsSupported_truncGE
#print axioms RelativeFM.Recollement.AssemblyM6.affineIsSupported_hasInducedTStructure
#print axioms RelativeFM.Recollement.AssemblyM6.affineDZStandardTStructure
