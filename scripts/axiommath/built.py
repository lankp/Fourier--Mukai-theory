#!/usr/bin/env python3
"""Is every AxiomMath module a target needs already built?

    python3 -I scripts/axiommath/built.py <AxiomMath checkout> <Module.Name>...

Prints the AxiomMath modules of the import closure that have no `.olean` yet, and their
number; exit 1 if any is missing.  Run it before a build that would otherwise compile
AxiomMath modules alongside another heavy build (memory).  For the repository's own
checkout the AxiomMath checkout is `.lake/packages/Stacks`.
"""
import os, re, sys

root, targets = sys.argv[1], sys.argv[2:]
imp = re.compile(r'^\s*(?:public\s+|meta\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)
seen, stack = set(), list(targets)
while stack:
    m = stack.pop()
    if m in seen: continue
    p = os.path.join(root, m.replace('.', '/') + '.lean')
    if not os.path.exists(p): continue
    seen.add(m)
    stack += [x for x in imp.findall(open(p, encoding='utf8').read())
              if x.split('.')[0] in ('Stacks', 'StacksCore', 'StacksFrontier')]
missing = sorted(m for m in seen if not os.path.exists(
    os.path.join(root, '.lake', 'build', 'lib', 'lean', m.replace('.', '/') + '.olean')))
for m in missing: print('not built:', m)
print(f'{len(seen)} AxiomMath modules in the closure, {len(missing)} not built')
sys.exit(1 if missing else 0)
