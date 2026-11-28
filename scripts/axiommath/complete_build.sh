#!/usr/bin/env bash
# Finish a partial AxiomMath build for SpacesVerified with low memory pressure.
#   scripts/axiommath/complete_build.sh [log]
# Single-threaded Lean (the Proj/Chart/Twist cluster needs ~10 GB per module), low priority.
# Restartable: Lake skips what is built, so after a container restart just run it again
# (restore swap and vm.max_map_count first).
set -u
cd "$(dirname "$0")/../.."
export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
log="${1:-.scratch/complete_build.log}"; mkdir -p "$(dirname "$log")"
nice -n 10 lake build SpacesVerified >"$log" 2>&1; echo "EXIT $?" >>"$log"
