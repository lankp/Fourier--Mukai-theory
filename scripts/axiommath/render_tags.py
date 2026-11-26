# Usage:
#   python3 -I scripts/axiommath/render_tags.py <dir with tag_map.py output> > results/AXIOMMATH_TAGS.md
#
# Merges the extracted data (tex_citations.tsv, axiommath_tags.tsv written by
# tag_map.py) with the human reading in scripts/axiommath/judgments.txt, and fills
# the placeholders of scripts/axiommath/AXIOMMATH_TAGS.template.md:
#   <!-- COUNTS -->  verdict counts
#   <!-- TABLE -->   one row per tag
#   <!-- GAPS -->    tags not usable for spaces, grouped by the result that cites them
import os, re, sys
from collections import defaultdict, OrderedDict

HERE = os.path.dirname(os.path.abspath(__file__))
D = sys.argv[1]


def cell(s):
    return s.replace('|', '\\|').replace('\n', ' ')


tex = defaultdict(list)
for ln in open(os.path.join(D, 'tex_citations.tsv'), encoding='utf8'):
    t, paper, line, where, ctx = ln.rstrip('\n').split('\t')
    tex[t].append((paper, int(line), where))
ax = defaultdict(list)
for ln in open(os.path.join(D, 'axiommath_tags.tsv'), encoding='utf8'):
    r = ln.rstrip('\n').split('\t')
    ax[r[0]].append(r)
J = OrderedDict()
for ln in open(os.path.join(HERE, 'judgments.txt'), encoding='utf8'):
    if not ln.strip() or ln.startswith('#'): continue
    ln = ln.rstrip()
    if ln.endswith(' |'): ln = ln[:-2]          # empty last field
    parts = [p.strip() for p in ln.split(' | ')]
    parts += [''] * (6 - len(parts))
    J[parts[0]] = parts[1:6]
    if parts[4] not in ('usable', 'usable†', 'partial', 'schemes only', 'absent'):
        sys.exit('bad verdict for %s: %r' % (parts[0], parts[4]))

tags = sorted(tex)
missing = [t for t in tags if t not in J]
extra = [t for t in J if t not in tex]
if missing or extra:
    sys.exit('judgments out of sync: missing %s, extra %s' % (missing, extra))


def where_cell(t):
    out = []
    for paper in ('GL26', 'LP26'):
        ws = list(OrderedDict.fromkeys(w for p, _, w in sorted(tex[t], key=lambda r: r[1]) if p == paper))
        if ws: out.append('%s: %s' % (paper, '; '.join(ws)))
    return ' — '.join(out)


def decl_cell(t, extra_txt):
    seen = OrderedDict()
    for r in ax[t]:
        name, com = r[4], r[1]
        com = (com[:77] + '…') if len(com) > 80 else com
        seen.setdefault(name, [])
        if com and com not in seen[name]: seen[name].append(com)
    items = ['`%s`%s' % (n, (' (%s)' % '; '.join(c)) if c else '') for n, c in seen.items()]
    s = '; '.join(items) if items else '— (no `@[stacks %s]` in AxiomMath)' % t
    if extra_txt: s += '. *Also:* ' + extra_txt
    return s


rows = []
for t in tags:
    use, scope, spaces, verdict, extra_txt = J[t]
    rows.append('| %s | %s | %s | %s | %s | %s | **%s** |' % (
        t, cell(where_cell(t)), cell(use), cell(decl_cell(t, extra_txt)), cell(scope),
        cell(spaces), verdict))
table = '\n'.join(['| tag | cited in | used for | AxiomMath declaration(s) | scope | spaces or schemes | verdict |',
                   '|---|---|---|---|---|---|---|'] + rows)

order = ['usable', 'usable†', 'partial', 'schemes only', 'absent']
cnt = {v: sum(1 for t in tags if J[t][3] == v) for v in order}
paper_cnt = {p: len({t for t in tags if any(r[0] == p for r in tex[t])}) for p in ('GL26', 'LP26')}
counts = '\n'.join([
    '| verdict | tags |', '|---|---|'] +
    ['| **%s** | %d |' % (v, cnt[v]) for v in order] +
    ['| total | %d (GL26 %d, LP26 %d, both %d) |' % (
        len(tags), paper_cnt['GL26'], paper_cnt['LP26'],
        paper_cnt['GL26'] + paper_cnt['LP26'] - len(tags))])

gaps = defaultdict(list)
for t in tags:
    v = J[t][3]
    if v in ('usable', 'usable†'): continue
    for p, _, w in tex[t]:
        key = '%s %s' % (p, re.sub(r'^proof of ', '', w))
        if (t, v) not in gaps[key]: gaps[key].append((t, v))


def sort_key(k):
    m = re.match(r'(GL26|LP26) (?:§)?(?:[A-Za-z-]+ )?([A-C]|\d+)\.?(\d+)?', k)
    if not m: return (k, 0, 0)
    a = m.group(2); sec = int(a) if a.isdigit() else 100 + ord(a)
    return (m.group(1), sec, int(m.group(3) or 0))


glines = []
for k in sorted(gaps, key=sort_key):
    glines.append('* %s: %s' % (k, ', '.join('%s (%s)' % (t, v) for t, v in gaps[k])))

tpl = open(os.path.join(HERE, 'AXIOMMATH_TAGS.template.md'), encoding='utf8').read()
out = tpl.replace('<!-- COUNTS -->', counts).replace('<!-- TABLE -->', table) \
         .replace('<!-- GAPS -->', '\n'.join(glines))
sys.stdout.write(out)
