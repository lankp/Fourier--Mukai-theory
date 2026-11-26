# Usage:
#   python3 -I scripts/axiommath/section_tags.py <stacks-project dir> <axiommath_tags.tsv> TAG...
#
# <stacks-project dir> holds the Stacks Project `tags/tags` file (as `tags`) and the
# chapter sources `<chapter>.tex` (https://github.com/stacks/stacks-project).
# <axiommath_tags.tsv> is the full list of AxiomMath `@[stacks]` rows: run
# tag_map.py with ALL=1 in the environment to write it for every tag, not only
# the paper's.
#
# For each TAG that is a *section* tag (label `<chapter>-section-...`), prints the
# tagged items (lemmas, definitions, ...) of that section, with the AxiomMath
# declarations carrying each item's tag.  This is how a section tag that has no
# `@[stacks]` attribute of its own is checked for coverage "under another tag".
import os, re, sys
from collections import defaultdict

D, TSV = sys.argv[1], sys.argv[2]
tag_of = {}; label_of = {}
for ln in open(os.path.join(D, 'tags')):
    if ln.startswith('#') or ',' not in ln: continue
    t, l = ln.strip().split(',', 1)
    tag_of[l] = t; label_of[t] = l
ax = defaultdict(list)
for ln in open(TSV):
    r = ln.rstrip('\n').split('\t')
    ax[r[0]].append('%s «%s»' % (r[4], r[1]))
for t in sys.argv[3:]:
    lab = label_of.get(t, '?')
    print('=====', t, lab)
    if '-section-' not in lab:
        print('  (not a section tag)'); continue
    chap, sec = lab.split('-section-', 1)
    p = os.path.join(D, chap + '.tex')
    if not os.path.exists(p):
        print('  chapter source missing:', p); continue
    tex = open(p, encoding='utf8').read()
    m = re.search(r'\\label\{section-' + re.escape(sec) + r'\}', tex)
    if not m:
        print('  section label not found'); continue
    nxt = re.search(r'\\(sub)?section\{', tex[m.end():])
    body = tex[m.end(): m.end() + nxt.start()] if nxt else tex[m.end():]
    for env, lbl in re.findall(r'\\begin\{(\w+)\}[^\n]*\n\\label\{([^}]*)\}', body):
        full = chap + '-' + lbl
        tg = tag_of.get(full, '????')
        print('  %-11s %s %s' % (env, tg, lbl))
        for a in ax.get(tg, []): print('       AX', a)
