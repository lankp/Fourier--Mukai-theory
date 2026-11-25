#!/usr/bin/env bash
# Build the Lean files of this repository against the Mathlib installation on
# LEAN_PATH (there is no Lake package: /opt/mathlib is read-only, so we call
# `lean` directly and write the .olean files next to the sources).
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_PATH="${LEAN_PATH}:."
for f in \
  FourierMukai/Prelim/Generation.lean \
  FourierMukai/Prelim/Triangulated.lean \
  FourierMukai/Prelim/Thickness.lean \
  FourierMukai/Prelim/Coproduct.lean \
  FourierMukai/Prelim/EssentiallyDense.lean \
  FourierMukai/Prelim/Mates.lean \
  FourierMukai/Prelim/Lemma25.lean \
  FourierMukai/Paper/DerivedSetup.lean \
  FourierMukai/Scheme/Inputs.lean \
  FourierMukai/Scheme/DerivedCoproducts.lean \
  FourierMukai/Scheme/KProjectiveResolution.lean \
  FourierMukai/Scheme/SpecialDirectLimits.lean \
  FourierMukai/Scheme/SpaltensteinStage.lean \
  FourierMukai/Scheme/SpaltensteinIteration.lean \
  FourierMukai/Scheme/SpaltensteinColimit.lean \
  FourierMukai/Scheme/SpaltensteinReplacement.lean \
  FourierMukai/Scheme/SpaltensteinCanonicalTruncation.lean \
  FourierMukai/Scheme/SpaltensteinSequentialComparisons.lean \
  FourierMukai/Scheme/SpaltensteinTheoremC.lean \
  FourierMukai/Scheme/AffineSpaltenstein.lean \
  FourierMukai/Scheme/ProjectiveModel.lean \
  FourierMukai/Scheme/SmallObjectPresentable.lean \
  FourierMukai/Scheme/GeneratingCofibrations.lean \
  FourierMukai/Scheme/WeakApprox.lean \
  FourierMukai/Scheme/OpenImmersion.lean \
  FourierMukai/Scheme/Derived.lean \
  FourierMukai/Scheme/QCohSerre.lean \
  FourierMukai/Scheme/QCohSerreExtension.lean \
  FourierMukai/Scheme/QCohSerreExtension01IE.lean \
  FourierMukai/Scheme/Statements.lean \
  FourierMukai/Scheme/Duality.lean \
  FourierMukai/Scheme/Lemma54.lean \
  FourierMukai/Scheme/PerfectRing.lean \
  FourierMukai/Scheme/PerfectModel.lean \
  FourierMukai/Scheme/PerfectModelConverse.lean \
  FourierMukai/Scheme/LeChen.lean \
  FourierMukai/Scheme/PerfectField.lean \
  FourierMukai/Scheme/Affine.lean \
  FourierMukai/Scheme/AffineCoproducts.lean \
  FourierMukai/Scheme/AffineBoundedAboveCoproducts.lean \
  FourierMukai/Scheme/AffineUniverse.lean \
  FourierMukai/Scheme/AisleCoproducts.lean \
  FourierMukai/Scheme/SmallAffineAssembly.lean \
  FourierMukai/Scheme/AffineRecollement.lean \
  FourierMukai/Scheme/AffineLocalCohomology.lean \
  FourierMukai/Scheme/AffineGluing.lean \
  FourierMukai/Scheme/AffineLocalCohomologySupport.lean \
  FourierMukai/Scheme/AffineSupportedAssembly.lean \
  FourierMukai/Scheme/AffineMain.lean \
  FourierMukai/Scheme/AffineDictionary.lean \
  FourierMukai/Scheme/AffineQCoh.lean \
  FourierMukai/Scheme/AffineDiagonal.lean \
  FourierMukai/Scheme/Perfect.lean \
  FourierMukai/Scheme/PerfectRingStacks.lean \
  FourierMukai/Scheme/PerfectCompactThick.lean \
  FourierMukai/Scheme/CompactToPerfect.lean \
  FourierMukai/Scheme/Affine066S.lean \
  FourierMukai/Paper/Statements.lean \
  FourierMukai/Paper/InterfaceAudit.lean \
  FourierMukai/Examples/Identity.lean \
  FourierMukai.lean \
  FourierMukai/Audit.lean \
  WeakApprox/Basic.lean \
  WeakApprox/CompactAb.lean \
  WeakApprox/Aisle.lean \
  WeakApprox/HomVanishing.lean \
  WeakApprox/Shift.lean \
  WeakApprox/Closure.lean \
  WeakApprox/Functoriality.lean \
  WeakApprox/PLift.lean \
  WeakApprox/Setup44.lean \
  WeakApprox/Lemma43.lean \
  WeakApprox/Lemma4323.lean \
  WeakApprox/Lemma46.lean \
  WeakApprox/Proposition48.lean \
  WeakApprox/Lemma42.lean \
  WeakApprox/Recollement.lean \
  WeakApprox/Lemma34.lean \
  WeakApprox/Lemma35.lean \
  WeakApprox/Octahedron.lean \
  WeakApprox/WeakApproximable.lean \
  WeakApprox/EventualVanishing.lean \
  WeakApprox/BoundedVanishing.lean \
  WeakApprox/ShiftAudit.lean \
  WeakApprox/TStructureConvention.lean \
  WeakApprox/StatementAudit.lean \
  WeakApprox/CompactVanishing.lean \
  WeakApprox/TwoStage.lean \
  WeakApprox/NineSR.lean \
  WeakApprox/GeneratorBridge.lean \
  WeakApprox/Lemma433TStructure.lean \
  WeakApprox/Setup44Vanishing.lean \
  WeakApprox/Proposition48Paper.lean \
  WeakApprox/Main.lean \
  WeakApprox/Setup44Reduced.lean \
  WeakApprox/MainMinimal.lean \
  WeakApprox/Setup44Minimal.lean \
  WeakApprox/CompactThick.lean \
  WeakApprox.lean ; do
  echo "== compiling $f"
  lean -o "${f%.lean}.olean" "$f"
done
echo "all modules compiled"
