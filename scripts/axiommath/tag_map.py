# Usage:
#   python3 -I scripts/axiommath/tag_map.py <AxiomMath checkout> [out_dir]
#
# Builds the raw data behind results/AXIOMMATH_TAGS.md:
#   * every Stacks Project tag cited in the GL26 and LP26 main.tex files
#     (not stored in the repository; pass their location) (links stacks.math.columbia.edu/tag/XXXX), with
#     the enclosing numbered result (as LaTeX would number it: shared counter
#     within sections, appendices lettered) and its \label, or the enclosing
#     section when the citation is in running text;
#   * every AxiomMath/Stacks declaration carrying `@[stacks TAG "comment"]` or
#     named in `add_to_stacks TAG "comment" Name`, with file, line, attribute
#     comment and the declaration header up to `:=` / `where` / `|`.
# Writes <out_dir>/tex_citations.tsv, <out_dir>/axiommath_tags.tsv and a
# per-tag text dump <out_dir>/per_tag.txt (default out_dir: current directory).
# The verdict columns of the table are a human reading of this dump; the
# script does not decide them.
import os, re, sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
AXS = sys.argv[1]
OUT = sys.argv[2] if len(sys.argv) > 2 else '.'

NUMBERED = ['theorem', 'lemma', 'corollary', 'proposition', 'definition', 'example',
            'remark', 'setup', 'conjecture', 'notation', 'reminder', 'question',
            'lemma-definition', 'example-claim']
TAGRE = re.compile(r'tag/([0-9A-Za-z]{4})')


def tex_citations(paper):
    # The manuscripts are not in the repository; MANUSCRIPTS_DIR points to a local copy
    # (GL26/main.tex, LP26/main.tex) provided by the maintainer.
    path = os.path.join(os.environ.get('MANUSCRIPTS_DIR', os.path.join(ROOT, 'manuscripts')), paper, 'main.tex')
    lines = open(path, encoding='utf8').read().split('\n')
    sec = 0; sub = 0; appendix = False; thm = 0
    secname = ''; seclabel = ''
    stack = []          # open numbered environments: (display, label)
    last = None         # last closed numbered result, for proofs
    inproof = False
    pending_label = None
    rows = []
    in_doc = False
    for i, ln in enumerate(lines, 1):
        s = ln.split('%')[0] if not ln.strip().startswith('\\href') else ln
        if '\\begin{document}' in s: in_doc = True
        if not in_doc: continue
        if '\\appendix' in s:
            appendix = True; sec = 0
        m = re.search(r'\\section\{(.*)\}', s)
        if m:
            sec += 1; thm = 0; secname = m.group(1); seclabel = ''; sub = 0
            pending_label = 'section'
        m = re.search(r'\\subsection\{(.*)\}', s)
        if m:
            sub += 1; secname = m.group(1); seclabel = ''
            pending_label = 'section'
        for m in re.finditer(r'\\begin\{(' + '|'.join(re.escape(e) for e in NUMBERED) + r')\}', s):
            thm += 1
            num = (chr(64 + sec) if appendix else str(sec)) + '.' + str(thm)
            stack.append([m.group(1).replace('-', ' ').title().replace(' ', '-') + ' ' + num, ''])
            pending_label = 'env'
        if '\\begin{proof}' in s: inproof = True
        for m in re.finditer(r'\\label\{([^}]*)\}', s):
            # an equation label or an item label is not the result's own label
            if pending_label == 'env' and (m.group(1).startswith('eq:') or '\\item' in s):
                continue
            if pending_label == 'env' and stack and not stack[-1][1]:
                stack[-1][1] = m.group(1); pending_label = None
            elif pending_label == 'section':
                seclabel = m.group(1); pending_label = None
        for m in TAGRE.finditer(s):
            tag = m.group(1).upper()
            if stack:
                where = ('', stack[-1])   # label resolved below: it may follow the citation
            elif inproof and last:
                where = ('proof of ', last)
            else:
                where = '§%s%s %s (`%s`)' % ((chr(64 + sec) if appendix else sec),
                                             ('.%d' % sub) if sub else '', secname, seclabel)
            ctx = re.sub(r'\\href\{[^}]*\}\{([^}]*)\}', r'\1', ln.strip())
            rows.append((tag, paper, i, where, ctx[:300]))
        for m in re.finditer(r'\\end\{(' + '|'.join(re.escape(e) for e in NUMBERED) + r')\}', s):
            if stack:
                closed = stack.pop()
                # a proof belongs to the last provable statement (a remark may sit
                # between a proposition and its proof)
                if closed[0].split()[0] not in ('Remark', 'Example', 'Notation', 'Setup',
                                                'Definition', 'Reminder', 'Question'):
                    last = closed
        if '\\end{proof}' in s: inproof = False
    def fmt(w):
        if isinstance(w, str): return w
        pre, env = w
        return '%s%s (%s)' % (pre, env[0], ('`%s`' % env[1]) if env[1] else 'no label')
    return [(t, p, i, fmt(w), c) for (t, p, i, w, c) in rows]


ATTR = re.compile(r'@\[[^\]]*?\bstacks\s+([0-9A-Z]{4})(?:\s+"((?:[^"\\]|\\.)*)")?', re.S)
ATTRCMD = re.compile(r'^\s*attribute\s*\[([^\]]*\bstacks\b[^\]]*)\]\s*([^\n]*)', re.M)
STK = re.compile(r'\bstacks\s+([0-9A-Z]{4})(?:\s+"((?:[^"\\]|\\.)*)")?')
ADD = re.compile(r'^\s*add_to_stacks\s+([0-9A-Z]{4})(?:\s+"((?:[^"\\]|\\.)*)")?\s*\n?\s*([^\s]+)?', re.M)
DECL = re.compile(r'\b(theorem|lemma|def|abbrev|instance|structure|class|inductive|irreducible_def)\s+([^\s:({\[]+?)(?:\.\{[^}]*\})?(?=[\s:({\[])')


TOK = re.compile(r'/-|-/|--|"|\n')


def blank_comments(txt):
    """Replace Lean comments (nested /- -/ and --) by spaces, keeping offsets and
    newlines, so that `@[stacks ...]` quoted in docstrings is not read as an
    attribute.  String literals outside comments are skipped over."""
    out = []; depth = 0; last = 0; i = 0; n = len(txt)
    mode = 'code'            # code | block | line | string
    for m in TOK.finditer(txt):
        if m.start() < i: continue
        t = m.group(); j = m.start()
        if mode == 'code':
            if t == '"':
                mode = 'string'
            elif t == '/-':
                out.append(txt[last:j]); last = j; depth = 1; mode = 'block'
            elif t == '--':
                out.append(txt[last:j]); last = j; mode = 'line'
        elif mode == 'string':
            if t == '"':
                k = j - 1; bs = 0
                while k >= 0 and txt[k] == '\\': bs += 1; k -= 1
                if bs % 2 == 0: mode = 'code'
        elif mode == 'line':
            if t == '\n':
                out.append(' ' * (j - last)); last = j; mode = 'code'
        elif mode == 'block':
            if t == '/-': depth += 1
            elif t == '-/':
                depth -= 1
                if depth == 0:
                    seg = txt[last:m.end()]
                    out.append(re.sub(r'[^\n]', ' ', seg)); last = m.end(); mode = 'code'
        i = m.end()
    seg = txt[last:]
    out.append(seg if mode in ('code', 'string') else re.sub(r'[^\n]', ' ', seg))
    return ''.join(out)


def header_at(txt, pos):
    body = txt[pos:pos + 3000]
    cut = re.search(r':=|\swhere\b|\n\s*\|', body)
    return ' '.join((body[:cut.start()] if cut else body[:600]).split())


def axiom_tags():
    out = []
    for base in ('StacksCore', 'StacksFrontier', 'Stacks'):
        for dp, _, fs in os.walk(os.path.join(AXS, base)):
            for f in fs:
                if not f.endswith('.lean'): continue
                p = os.path.join(dp, f)
                raw = open(p, encoding='utf8').read()
                if 'stacks' not in raw: continue
                txt = blank_comments(raw)
                rel = os.path.relpath(p, AXS)
                for m in ATTR.finditer(txt):
                    line = txt.count('\n', 0, m.start()) + 1
                    attr_end = txt.find(']', m.end() - 1)
                    attr_end = attr_end if attr_end >= 0 else m.end()
                    d = DECL.search(txt, attr_end)
                    name = d.group(2) if d else '?'
                    hdr = header_at(txt, d.start()) if d else ''
                    nsp = namespace_at(txt, m.start())
                    out.append((m.group(1), m.group(2) or '', rel, line, qualify(nsp, name), hdr[:1500], 'attr'))
                    for m2 in STK.finditer(txt, m.end(), attr_end + 1):
                        out.append((m2.group(1), m2.group(2) or '', rel, line, qualify(nsp, name), hdr[:1500], 'attr'))
                for m in ATTRCMD.finditer(txt):
                    line = txt.count('\n', 0, m.start()) + 1
                    nsp = namespace_at(txt, m.start())
                    for name in m.group(2).split():
                        for m2 in STK.finditer(m.group(1)):
                            out.append((m2.group(1), m2.group(2) or '', rel, line, qualify(nsp, name), '', 'attribute'))
                for m in ADD.finditer(txt):
                    line = txt.count('\n', 0, m.start()) + 1
                    out.append((m.group(1), m.group(2) or '', rel, line, m.group(3) or '?', '', 'add_to_stacks'))
    return out


def fill_headers(rows, wanted):
    """For `add_to_stacks` / `attribute [stacks]` rows, find the declaration's
    header by its last name component (all candidates are listed)."""
    need = defaultdict(list)
    for k, r in enumerate(rows):
        if r[0] in wanted and not r[5]:
            need[r[4].split('.')[-1]].append(k)
    if not need: return rows
    found = defaultdict(list)
    for base in ('StacksCore', 'StacksFrontier', 'Stacks'):
        for dp, _, fs in os.walk(os.path.join(AXS, base)):
            for f in fs:
                if not f.endswith('.lean'): continue
                p = os.path.join(dp, f)
                raw = open(p, encoding='utf8').read()
                if not any(n in raw for n in need): continue
                txt = blank_comments(raw)
                for d in DECL.finditer(txt):
                    short = d.group(2).split('.')[-1]
                    if short in need:
                        found[short].append((os.path.relpath(p, AXS), header_at(txt, d.start())))
    rows = list(rows)
    for short, ks in need.items():
        hs = found.get(short, [])
        h = ' || '.join('[%s] %s' % (a, b[:700]) for a, b in hs[:3]) if hs else '(declaration not found)'
        for k in ks:
            r = rows[k]; rows[k] = r[:5] + (h,) + r[6:]
    return rows


def namespace_at(txt, pos):
    ns = []
    for m in re.finditer(r'^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:public[ \t]+)?(?:noncomputable[ \t]+)?'
                         r'(namespace|end|section)\b[ \t]*([A-Za-z0-9_.]*)', txt[:pos], re.M):
        kind, n = m.group(1), m.group(2)
        if kind == 'namespace': ns.extend(('ns', c) for c in n.split('.'))
        elif kind == 'section': ns.append(('sec', n))
        elif ns:
            for _ in range(max(1, len(n.split('.')) if n else 1)):
                if ns: ns.pop()
    return '.'.join(n for k, n in ns if k == 'ns' and n)


def qualify(ns, name):
    if name.startswith('_root_.'): return name[7:]
    return (ns + '.' + name) if ns and name != '?' else name


tex = tex_citations('GL26') + tex_citations('LP26')
paper_tags = sorted({r[0] for r in tex})
if os.environ.get('TEXONLY'):        # TeX side only (fast): print the citations and stop
    for r in tex: print('\t'.join(map(str, r)))
    sys.exit(0)
ax = fill_headers(axiom_tags(), set(paper_tags))
by_tag_tex = defaultdict(list); by_tag_ax = defaultdict(list)
for r in tex: by_tag_tex[r[0]].append(r)
for r in ax: by_tag_ax[r[0]].append(r)
os.makedirs(OUT, exist_ok=True)
with open(os.path.join(OUT, 'tex_citations.tsv'), 'w') as f:
    for r in tex: f.write('\t'.join(map(str, r)) + '\n')
with open(os.path.join(OUT, 'axiommath_tags.tsv'), 'w') as f:
    for r in ax:
        if r[0] in by_tag_tex or os.environ.get('ALL'): f.write('\t'.join(' '.join(str(x).split()) for x in r) + '\n')
with open(os.path.join(OUT, 'per_tag.txt'), 'w') as f:
    for t in paper_tags:
        f.write('=' * 20 + ' ' + t + '\n')
        for r in by_tag_tex[t]: f.write('  TEX %s:%d %s\n      %s\n' % r[1:])
        for r in by_tag_ax[t]:
            f.write('  AX  [%s] "%s" %s:%d %s\n      %s\n' % (r[6], r[1], r[2], r[3], r[4], r[5]))
        if not by_tag_ax[t]: f.write('  AX  (none)\n')
print(len(paper_tags), 'tags;',
      sum(1 for t in paper_tags if not by_tag_ax[t]), 'without AxiomMath attribute:',
      ' '.join(t for t in paper_tags if not by_tag_ax[t]))
