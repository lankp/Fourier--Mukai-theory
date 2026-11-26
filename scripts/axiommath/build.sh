#!/usr/bin/env bash
# Build AxiomMath/Stacks modules in an AxiomMath checkout, keeping the disk small.
#
#   scripts/axiommath/build.sh <AxiomMath checkout> <log file> <Module.Name>...
#
# Runs `lake build <modules>` there, writing the log, and every two minutes deletes the
# `.setup.json` files of modules already built (they are large and not needed afterwards).
# The log ends with `exit=<status>`.  Memory: `StacksFrontier.RingTheory.MilnorPatching.Relative`
# peaks near 13.6 GB; on a 16 GB machine enable swap first and run no other heavy build.
# Run detached: `nohup setsid scripts/axiommath/build.sh ... > /dev/null 2>&1 < /dev/null &`.
set -u
dir="$1"; log="$2"; shift 2
export PATH="$HOME/.elan/bin:$PATH"
cd "$dir" || exit 2
prune() { (cd .lake/build 2>/dev/null && find ir -name '*.setup.json' -mmin +2 | while read -r f; do
  m=${f#ir/}; m=${m%.setup.json}; [ -f "lib/lean/$m.olean" ] && rm -f "$f"; done); }
( while true; do prune; sleep 120; done ) & pruner=$!
echo "== start $(date -u +%FT%H:%MZ)" > "$log"
lake build "$@" >> "$log" 2>&1
status=$?
kill "$pruner"; prune
echo "exit=$status $(date -u +%FT%H:%MZ)" >> "$log"
exit "$status"
