"""collapse A / B3 rule 2: match identifiers of given files against the dead set (dotted suffixes; a single
component only if no other declaration of the x86 or A64 env ends with it). usage: textchk.py DEAD.json DEPDUMP DEPDUMPA64 FILE..."""
import json,re,sys,gzip,collections
d=json.load(open(sys.argv[1])); D=set(d['D'])
# single-component false positives (namespace / field names that also occur as other identifiers; cls.py's FP list)
FP={'Fl4Proofs.P2.E2EV.ExitGhostV.maps','Fl4Proofs.P3.JEntryHyps.glob','Fl4Proofs.P1.obj.Tcb.fault_type.fa','Fl4Proofs.P3.SInv.P0'}
D-=FP
cnt=collections.Counter()
for f in sys.argv[2:4]:
    for l in gzip.open(f,'rt'):
        n=l.split('\t',1)[0]; cnt[n.split('.')[-1]]+=1
idx=collections.defaultdict(set)
for c in D:
    ps=c.split('.')
    for k in range(1,len(ps)): idx['.'.join(ps[-k:])].add(c)
TOK=re.compile(r"[A-Za-z_α-ω][A-Za-z0-9_'!?₀-₉α-ω]*(?:\.[A-Za-z_][A-Za-z0-9_'!?₀-₉]*)*")
hits=0
for f in sys.argv[4:]:
    for i,l in enumerate(open(f,errors='replace'),1):
        for t in set(TOK.findall(l)):
            ps=t.split('.')
            for k in range(len(ps),0,-1):
                s='.'.join(ps[:k])
                if s in idx and (k>1 or cnt[s]<=1):
                    hits+=1; print(f'{f}:{i}: {t} -> {sorted(idx[s])[:3]} | {l.strip()[:160]}'); break
                # also any suffix of the token prefix
print('HITS',hits)
