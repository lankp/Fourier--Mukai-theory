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
  FourierMukai/Paper/Statements.lean \
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
  WeakApprox.lean ; do
  echo "== compiling $f"
  lean -o "${f%.lean}.olean" "$f"
done
echo "all modules compiled"
