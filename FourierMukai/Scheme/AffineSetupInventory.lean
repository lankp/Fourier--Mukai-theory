/-
The post-recollement input to the affine Lank--Pauwels setup.

The standard t-structures on the two module-derived categories are fixed.
Everything left in this file is an explicit field of the existing
`SetupMainMinimal`; no weak-approximability, compact-generation or aisle claim
is proved merely by packaging it here.
-/
import FourierMukai.Scheme.AffineSupportedAssembly

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

/-- The exact `SetupMainMinimal` type in the affine orientation: the abstract
`DZ` slot is the open localization and the abstract `DU` slot is supported. -/
abbrev AffineSetup (A : Type u) [CommRing A] (f : A) :=
  SetupMainMinimal (AffineD (Away A f)) (AffineD A) (AffineDZ A f)

/-- Data beyond a recollement needed by `SetupMainMinimal`, with `tD` and `tZ`
already fixed to the standard module-derived t-structures. -/
structure StandardSetupInput {A : Type u} [CommRing A] {f : A}
    (R : AffineRecollement A f) where
  tU : TStructure (AffineDZ A f)
  approxZ : WeakApproximationData (AffineD (Away A f))
  approxU : WeakApproximationData (AffineDZ A f)
  GU : AffineDZ A f
  G' : AffineD A
  G'_compact : IsCompactAb G'
  G'_generates : IsGenerator G'
  m : ℤ
  jStar_G'_mem : tU.le m (R.jStar.obj G')
  [normalized_biproduct : HasBinaryBiproduct (G'⟦m⟧) (R.jShriek.obj GU)]
  tD_compactlyGenerated :
    (AffineD.standardTStructure A).le 0 =
      Coprod (shiftTail (G'⟦m⟧ ⊞ R.jShriek.obj GU) 0)
  tZ_compactlyGenerated :
    (AffineD.standardTStructure (Away A f)).le 0 =
      Coprod (shiftTail (R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)) 0)
  tU_compactlyGenerated : tU.le 0 = Coprod (shiftTail GU 0)
  approxZ_t : approxZ.t = AffineD.standardTStructure (Away A f)
  approxU_t : approxU.t = tU
  approxZ_G : approxZ.G = R.iStar.obj (G'⟦m⟧ ⊞ R.jShriek.obj GU)
  approxU_G : approxU.G = GU

attribute [instance] StandardSetupInput.normalized_biproduct

namespace StandardSetupInput

variable {A : Type u} [CommRing A] {f : A} {R : AffineRecollement A f}
  (I : StandardSetupInput R)

include I

/-- Assemble the exact affine `SetupMainMinimal`.  The recollement and the two
standard t-structures are parameters/definitions, not residual fields. -/
noncomputable def toSetupMainMinimal : AffineSetup A f where
  R := R
  tD := AffineD.standardTStructure A
  tZ := AffineD.standardTStructure (Away A f)
  tU := I.tU
  approxZ := I.approxZ
  approxU := I.approxU
  GU := I.GU
  G' := I.G'
  G'_compact := I.G'_compact
  G'_generates := I.G'_generates
  m := I.m
  jStar_G'_mem := I.jStar_G'_mem
  normalized_biproduct := I.normalized_biproduct
  tD_compactlyGenerated := I.tD_compactlyGenerated
  tZ_compactlyGenerated := I.tZ_compactlyGenerated
  tU_compactlyGenerated := I.tU_compactlyGenerated
  approxZ_t := I.approxZ_t
  approxU_t := I.approxU_t
  approxZ_G := I.approxZ_G
  approxU_G := I.approxU_G

@[simp] theorem toSetupMainMinimal_R : I.toSetupMainMinimal.R = R := rfl
@[simp] theorem toSetupMainMinimal_tD :
    I.toSetupMainMinimal.tD = AffineD.standardTStructure A := rfl
@[simp] theorem toSetupMainMinimal_tZ :
    I.toSetupMainMinimal.tZ = AffineD.standardTStructure (Away A f) := rfl
@[simp] theorem toSetupMainMinimal_tU : I.toSetupMainMinimal.tU = I.tU := rfl

end StandardSetupInput


end
end RelativeFM.Recollement.AssemblyM6

#print axioms RelativeFM.Recollement.AssemblyM6.StandardSetupInput.toSetupMainMinimal
