exec(open('/private/tmp/claude-502/col/ana.py').read())
import json
mod,kind,deps=load('depdump.tsv.gz')
g=json.load(open('/private/tmp/claude-502/col/g_head.json'))
anc={}
def ancestors(m):
    if m in anc: return anc[m]
    s=set();st=[m]
    while st:
        x=st.pop()
        if x in s: continue
        s.add(x); st+=g.get(x,[])
    anc[m]=s; return s
R='/Users/stillfail/.stillfail/sessions/claude-ember@d70ccd1321eaa3aa3390df77fb901ff2774a7cc3da926c3cf25ca287a3ba5f22/C0AQ0C0KVMH-1794890878-390829/workspace/FL4-collapse/proofs/Fl4Proofs/'
pr=re.compile(r"\(``?([A-Za-z0-9_.']+), ``?([A-Za-z0-9_.']+)\)")
res={}
for f in ['P3/StallNarrowGen','P3/ArchIrqNarrowGen','P3/IrqFixGenB','P3/IrqFixGen','P3/P3JGen','P3/P3KGen1','P3/P3KGen']:
    pairs=pr.findall(open(R+f+'.lean').read())
    print('==',f)
    for a,b in pairs:
        if a not in mod or b not in mod: continue
        tgt=mod[a]; A=ancestors(tgt)
        P=set(); st=[b]
        while st:
            x=st.pop()
            if x in P: continue
            if mod[x] in A: continue
            P.add(x); st+=deps.get(x,[])
        P.discard(b)
        ms=collections.Counter(mod[x] for x in P)
        print(f'   {a.split(".")[-1]:30} @{tgt.split(".")[-1]:20} move {len(P):6} consts from {len(ms):4} mods: {[m.split(".")[-1]+":"+str(k) for m,k in ms.most_common(6)]}')
