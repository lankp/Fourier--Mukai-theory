import FourierMukai.Scheme.KProjHomComplex
import FourierMukai.Scheme.KProjIndependence
import FourierMukai.Scheme.KProjHomContravariant
import FourierMukai.Scheme.FixedDerivedTensorHom
import FourierMukai.Scheme.AffineDerivedTensorHom

/-!
# Verification umbrella for the K-projective/tensor--Hom direction

This module has no new declarations.  It links every source file in the
submission and repeats the principal axiom audits in one place.
-/

#print axioms RelativeFM.KProjectiveTensorHom.homotopyEquivOfDerivedIso
#print axioms RelativeFM.KProjectiveTensorHom.qObjTensorIsoOfDerivedIso
#print axioms RelativeFM.KProjectiveTensorHom.postcomp_quasiIso_of_isKProjective
#print axioms RelativeFM.KProjectiveTensorHom.precomp_quasiIso_of_isKProjective
#print axioms RelativeFM.KProjectiveTensorHom.derivedHomComplexFunctor
#print axioms RelativeFM.KProjectiveTensorHom.FixedComplexTensorHomModel.derivedTensorHomAdj
#print axioms RelativeFM.KProjectiveTensorHom.affineDerivedTensorHomData
