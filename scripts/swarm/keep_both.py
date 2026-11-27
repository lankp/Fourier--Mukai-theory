#!/usr/bin/env python3
"""Resolve append-only merge conflicts by keeping both sides (ours first, then the lines of
theirs not already present).  For the files swarm branches only append to: `Spaces.lean`, the
`Audit.lean` files, root import files.  Do not use it on anything else.

    python3 scripts/swarm/keep_both.py <file>...
"""
import re, sys

for p in sys.argv[1:]:
    s = open(p, encoding='utf8').read()
    s = re.sub(r'<<<<<<< [^\n]*\n(.*?)=======\n(.*?)>>>>>>> [^\n]*\n',
               lambda m: m.group(1) + ''.join(l + '\n' for l in m.group(2).split('\n')[:-1]
                                              if l + '\n' not in m.group(1)),
               s, flags=re.S)
    assert '<<<<<<<' not in s, p
    open(p, 'w', encoding='utf8').write(s)
