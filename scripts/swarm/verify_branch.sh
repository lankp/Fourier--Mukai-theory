#!/bin/bash
# Usage: scripts/swarm/verify_branch.sh wave<N>/<slug>   (orchestrator only)
# Merges origin/<branch> into a local copy of origin/formalization (no push),
# then runs the CLAUDE.md verification steps on the merge result.
set -uo pipefail
B="$1"
cd "$(dirname "$0")/../.."
export PATH="$HOME/.elan/bin:$PATH"
S="${VERIFY_LOG_DIR:-${TMPDIR:-/tmp}/fm-verify}"
mkdir -p "$S"; slug=${B//\//_}; LOG="$S/$slug"
git fetch -q --depth=200 origin "+refs/heads/formalization:refs/remotes/origin/formalization" "+refs/heads/$B:refs/remotes/origin/$B" || { echo "FETCH FAILED"; exit 1; }
git checkout -q -B verify/"$slug" origin/formalization
echo "== files changed by $B relative to formalization:"
git diff --stat origin/formalization...origin/"$B" | tail -20
echo "== files outside the allowed set:"
git diff --name-only origin/formalization...origin/"$B" | grep -vE '^FourierMukai/(Prelim|Scheme)/[A-Za-z0-9]+\.lean$|^FourierMukai\.lean$|^FourierMukai/Audit\.lean$' || echo "(none)"
echo "== tex/pdf/bib committed?"
git diff --name-only origin/formalization...origin/"$B" | grep -E '\.(tex|pdf|bib)$' || echo "(none)"
if ! git -c user.name="Claude" -c user.email="noreply@anthropic.com" merge -q --no-ff --no-edit origin/"$B" > "$LOG.merge" 2>&1; then
  U=$(git diff --name-only --diff-filter=U)
  if [ -n "$U" ] && [ -z "$(echo "$U" | grep -vE '^(FourierMukai\.lean|FourierMukai/Audit\.lean)$')" ]; then
    for f in $U; do sed -i -E '/^(<<<<<<< .*|=======|>>>>>>> .*)$/d' "$f"; done
    git add $U && git -c user.name="Claude" -c user.email="noreply@anthropic.com" commit -q --no-edit
    echo "== merge conflict in [$U] resolved by keeping both sides"
  else
    echo "MERGE CONFLICT"; cat "$LOG.merge"; git merge --abort; exit 2
  fi
fi
NEW=$(git diff --name-only origin/formalization HEAD | grep -E "^(FourierMukai/(Prelim|Scheme|Spaces)|WeakApprox)/.*\.lean$")
echo "== new modules: $NEW"
echo "== sorry/axiom/True-hypothesis/autoImplicit scan:"
[ -n "$NEW" ] && { grep -nE '\bsorry\b|^\s*axiom\b|: True\)|autoImplicit' $NEW || echo "(none)"; } || echo "(no new modules)"

echo "== step 5: lake build"
( time lake build ) > "$LOG.build" 2>&1; echo "exit=$?"; grep -E '^real' "$LOG.build"
grep -E ': error' "$LOG.build" | grep -v '^warning' | head -5
for f in $NEW; do
  echo "== step 1-3: lake env lean $f"
  lake env lean "$f" > "$LOG.$(basename $f).out" 2>&1; echo "exit=$?"
  grep -n 'error' "$LOG.$(basename $f).out" | head -5 || true
done
echo "sorry warnings: $(grep -cE "declaration uses .sorry." "$LOG.build")  (expected 9, all in Paper/Statements.lean)"
grep -E "declaration uses .sorry." "$LOG.build" | grep -v 'Paper/Statements.lean' | head
echo "== axiom audit"
lake env lean FourierMukai/Audit.lean > "$LOG.audit" 2>&1; echo "exit=$?"
tr '\n' ' ' < "$LOG.audit" | grep -oE "'[^']+' depends on axioms: \[[^]]*\]" | awk '{print ($0 ~ /sorryAx/) ? "SORRY" : "clean"}' | sort | uniq -c
tr '\n' ' ' < "$LOG.audit" | grep -oE "'[^']+' depends on axioms: \[[^]]*\]" | grep -vE "sorryAx" | grep -vE "\[(propext|Classical\.choice|Quot\.sound)(, *(propext|Classical\.choice|Quot\.sound))*\]" | grep -v "does not depend" | head
echo "== step 6: statement check"
TMPDIR="$S" scripts/check_statements.sh 2>&1 | tail -2
echo "== merge commit ready on verify/$slug: $(git rev-parse --short HEAD) (not pushed)"
