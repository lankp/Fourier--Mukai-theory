#!/usr/bin/env bash
# Independent statement check.
#
# `StatementCheck.lean` prints the type and the axioms of every headline result
# the repository proves.  This script re-elaborates that file and compares the
# output with `results/statement-baseline.txt`, so a statement that is silently
# weakened, a strengthened hypothesis, or a new axiom fails even when all the
# proofs still compile.
#
#   scripts/check_statements.sh            check against the baseline
#   scripts/check_statements.sh --update   re-record the baseline
#
# It runs under Lake when the package has been resolved (the CI path, where
# `lake exe cache get` has populated Mathlib), and otherwise against the Lean on
# PATH with `LEAN_PATH` pointing at a prebuilt Mathlib (the VM path here).
set -euo pipefail
cd "$(dirname "$0")/.."

# `--spaces`: check the AxiomMath-based libraries instead (needs `lake build Spaces`).
file=StatementCheck.lean
baseline=results/statement-baseline.txt
if [ "${1:-}" = "--spaces" ]; then
  shift; file=StatementCheckSpaces.lean; baseline=results/statement-baseline-spaces.txt
fi
out="${TMPDIR:-.scratch}/statement-check-$(basename "$file" .lean).out"
mkdir -p "$(dirname "$out")"

run_lean() {
  if [ -f lake-manifest.json ] && [ -d .lake/packages ]; then
    lake env lean "$file"
  else
    LEAN_PATH="${LEAN_PATH}:." lean "$file"
  fi
}

if ! run_lean > "$out" 2>&1; then
  echo "statement check: $file failed to elaborate" >&2
  cat "$out" >&2
  exit 1
fi

if grep -q "error" "$out"; then
  echo "statement check: elaboration reported errors" >&2
  grep -n "error" "$out" >&2
  exit 1
fi

if [ "${1:-}" = "--update" ]; then
  cp "$out" "$baseline"
  echo "statement check: wrote $baseline ($(wc -l < "$baseline") lines)"
  exit 0
fi

if grep -q "sorryAx" "$out"; then
  echo "statement check: a checked declaration depends on sorryAx" >&2
  grep -n "sorryAx" "$out" >&2
  exit 1
fi

if ! diff -u "$baseline" "$out"; then
  echo "statement check: the statements drift from $baseline" >&2
  echo "If the drift is intended, run scripts/check_statements.sh --update and review the diff." >&2
  exit 1
fi

audits=$(grep -c "depends on axioms" "$out" || true)
echo "statement check: OK — $audits declarations match $baseline, none depends on sorryAx"
