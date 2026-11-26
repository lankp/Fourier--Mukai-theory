# Usage: python3 -I scripts/axiommath/closure.py <AxiomMath checkout> <Module.Name>...
# Prints the number of AxiomMath modules (and their lines) in the import closure.
import os,re,sys
root=sys.argv[1]; targets=sys.argv[2:]
imp=re.compile(r'^\s*(?:public\s+|meta\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)',re.M)
cache={}
def deps(m):
    if m in cache: return cache[m]
    p=os.path.join(root,m.replace('.','/')+'.lean')
    if not os.path.exists(p): cache[m]=None; return None
    txt=open(p,encoding='utf8').read()
    cache[m]=[x for x in imp.findall(txt) if x.split('.')[0] in ('Stacks','StacksCore','StacksFrontier')]
    return cache[m]
seen=set(); st=list(targets)
while st:
    m=st.pop()
    if m in seen: continue
    d=deps(m)
    if d is None: print('missing',m); continue
    seen.add(m); st+=d
lines=sum(sum(1 for _ in open(os.path.join(root,m.replace('.','/')+'.lean'),encoding='utf8')) for m in seen)
print(len(seen),'modules',lines,'lines')
