import sys,os,functools,subprocess
sys.setrecursionlimit(100000)
def imps(m):
    p=m.replace('.','/')+'.lean'
    if not os.path.exists(p): return []
    return [l.split()[1] for l in open(p) if l.startswith('import ')]
@functools.lru_cache(None)
def anc(m):
    s=set()
    for i in imps(m):
        s.add(i); s|=anc(i)
    return frozenset(s)
for f in sys.argv[1:]:
    orig=subprocess.check_output(['git','show','HEAD:proofs/'+f],text=True)
    old={l.split()[1] for l in orig.split('\n') if l.startswith('import ')}
    L=open(f).read().split('\n'); cur=[l.split()[1] for l in L if l.startswith('import ')]
    drop=set()
    for i in cur:
        if i in old: continue
        if any(i in anc(j) for j in cur if j!=i and j not in drop): drop.add(i)
    L=[l for l in L if not (l.startswith('import ') and l.split()[1] in drop)]
    open(f,'w').write('\n'.join(L)); print(f,'dropped',sorted(drop))
