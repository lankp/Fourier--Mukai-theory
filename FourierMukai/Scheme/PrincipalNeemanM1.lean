import FourierMukai.Scheme.PrincipalH0CoverM1

/-!
# Principal affine supported Neeman weak approximability

No Stacks input is used.  The only remaining argument is compactness of the
ambient regular module in the large-Hom model.  Supported compactness, zero
detection, the unshifted interval bound and the supported `H⁰` cover are all
constructed.
-/

@[expose] public section

namespace RelativeFM.PrincipalNeemanM1

open RelativeFM RelativeWeakApprox
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open RelativeFM.SupportedAisleM6.Koszul

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Principal supported paper weak approximation data. -/
noncomputable def paperData (A : Type u) [CommRing A] (f : A)
    (hAc : IsCompactAb (ringObject A)) :
    PaperM2.PaperWeakApproximationData (AffineDZ A f) :=
  AffineSupportedBaseM1.koszulSupportedPaperDataOfH0Cover' A f hAc
    (PrincipalH0CoverM1.principalSupportedH0Cover A f)

@[simp] theorem paperData_G (A : Type u) [CommRing A] (f : A)
    (hAc : IsCompactAb (ringObject A)) :
    (paperData A f hAc).G = supportedGenerator A f := rfl

@[simp] theorem paperData_t (A : Type u) [CommRing A] (f : A)
    (hAc : IsCompactAb (ringObject A)) :
    (paperData A f hAc).t = Recollement.AssemblyM6.affineDZStandardTStructure A f := rfl

@[simp] theorem paperData_A (A : Type u) [CommRing A] (f : A)
    (hAc : IsCompactAb (ringObject A)) :
    (paperData A f hAc).A = 2 := rfl

/-- Principal supported Neeman weak approximability, with regular-module
compactness as its sole argument. -/
theorem satisfiesPaperWA (A : Type u) [CommRing A] (f : A)
    (hAc : IsCompactAb (ringObject A)) :
    PaperM2.SatisfiesPaperWA (AffineDZ A f) :=
  ⟨paperData A f hAc⟩

end

end RelativeFM.PrincipalNeemanM1

#print axioms RelativeFM.PrincipalNeemanM1.paperData
#print axioms RelativeFM.PrincipalNeemanM1.satisfiesPaperWA
