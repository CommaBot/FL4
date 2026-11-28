"""collapse A / B3: delete the source blocks of srcmap.py's rows; emptied modules are left for git rm.
usage: apply.py SRC.json PROOFS_ROOT [--apply]. Only the block lines are removed, plus the blank lines that
follow a removed block when the line before it is blank (no other whitespace change)."""
import json,collections,sys,os
S,ROOT=sys.argv[1:3]; dry='--apply' not in sys.argv
s=json.load(open(S)); empty=set(s['empty'])
bym=collections.defaultdict(list)
for m,n,k,a,b in s['rows']: bym[m].append((a-1,b))
tot=0
for m,rs in sorted(bym.items()):
    if m in empty: continue
    path=os.path.join(ROOT,m.replace('.','/')+'.lean')
    lines=open(path).read().split('\n')
    drop=set()
    for a,b in sorted(rs):
        drop|=set(range(a,b))
    for a,b in sorted(rs):
        k=a-1
        while k>=0 and k in drop: k-=1
        if k<0 or not lines[k].strip():
            e=b
            while e<len(lines) and e not in drop and not lines[e].strip() and e<len(lines)-1: drop.add(e); e+=1
    tot+=len(drop)
    if not dry: open(path,'w').write('\n'.join(l for i,l in enumerate(lines) if i not in drop))
print('modules edited',len([m for m in bym if m not in empty]),'lines removed (incl. blank separators)',tot,'emptied (not edited)',len(empty))
