#!/usr/bin/env python3
"""Set the status and note of one row of results/COVERAGE.md, found by its TeX label.

    python3 scripts/coverage_row.py <label> "<status>" "<note>"

Labels are unique across both papers (numbers are not: GL26 and LP26 both have a Lemma 5.7),
so always address a row by its label.  Fails unless exactly one row carries the label.
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
label, status, note = sys.argv[1:4]
p = os.path.join(ROOT, 'results', 'COVERAGE.md')
lines = open(p, encoding='utf8').read().split('\n')
hits = [i for i, l in enumerate(lines) if re.match(r'^\| [^|]+ \| `' + re.escape(label) + r'` \|', l)]
if len(hits) != 1:
    sys.exit(f'coverage_row: {len(hits)} rows carry `{label}` (need exactly one)')
i = hits[0]
num = lines[i].split(' | ')[0].lstrip('| ').strip()
lines[i] = f'| {num} | `{label}` | {status} | {note} |'
open(p, 'w', encoding='utf8').write('\n'.join(lines))
print(f'coverage_row: {num} `{label}` updated')
