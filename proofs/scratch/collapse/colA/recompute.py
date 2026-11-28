"""collapse A / B3: recompute the B3 dead set over a depdump (decl level, #115 fixpoint).
usage: recompute.py DEPDUMP.tsv.gz B3_FINAL.txt OUT.json [--old-keeps] [--no-fprot]
Seeds = every SEED name of b3_final.txt; protected = its KEEP names (minus the three docstring-only keeps
JHole.mcsPPJI / JHole.mcsPPJU / kernel_entryJ33 unless --old-keeps) plus every declaration of
P3.SpecInvYieldScopeF1..F4 (Architect ruling 04:17Z; off with --no-fprot)."""
import gzip,collections,re,sys,json
dd,b3f,out=sys.argv[1:4]; opts=set(sys.argv[4:])
mod={};kind={};deps={}
for line in gzip.open(dd,'rt'):
    p=line.rstrip('\n').split('\t'); mod[p[0]]=p[1]; kind[p[0]]=p[2]; deps[p[0]]=p[3].split() if len(p)>3 and p[3] else []
AUXC=re.compile(r'^(match_\d+|proof_\d+|_proof_\d+|_simp_\d+|eq_\d+|eq_def|_unfold|_sunfold|_cstage\d*|_sparseCasesOn_\d+|splitter|congr_simp|inj|injEq|sizeOf_spec|noConfusion|noConfusionType|recOn|casesOn|below|brecOn|binductionOn|ibelow|_sizeOf_\d+|_sizeOf_inst|rec|_flat_ctor|refl|ctorIdx|_auxLemma\d*|_lambda_\d+|_override|elim|ctorElim|ctorElimType)$')
def dmap(n):
    m=re.match(r'^_private\.(.*?)\.0\.(.*)$',n)
    if m: n=m.group(2)
    parts=n.split('.')
    while len(parts)>2 and AUXC.match(parts[-1]): parts.pop()
    n2='.'.join(parts)
    if n2 in kind and kind[n2]=='ctor': n2=n2.rsplit('.',1)[0]
    return n2
DM={n:dmap(n) for n in mod}
dset=set(DM.values())
ddeps=collections.defaultdict(set); dusers=collections.defaultdict(set)
for n,ds in deps.items():
    a=DM[n]
    for d in ds:
        b=DM.get(d)
        if b and b!=a: ddeps[a].add(b); dusers[b].add(a)
dmod={}
for n in mod: dmod.setdefault(DM[n],mod[n])
COPY=re.compile(r'^Fl4Proofs[A-Z]+\.')
dmus=collections.defaultdict(set)
for k,v in dusers.items(): dmus[k]=set(v)
for D in dset:
    if COPY.match(D):
        o='Fl4Proofs.'+D.split('.',1)[1]
        if o in dset: dmus[o].add(D)
def drev(seeds):
    s=set();st=list(seeds)
    while st:
        x=st.pop()
        if x in s: continue
        s.add(x); st+=dusers.get(x,())
    return s
seeds=set();K=set();OLD={}
for l in open(b3f):
    p=l.split()
    if not p or p[0]=='#': continue
    if p[0]=='SEED': seeds.add(p[2])
    elif p[0]=='KEEP': K.add(p[3])
    elif p[0] in ('DEL','KEEP-UNDELETABLE'): OLD[p[3]]=p[0]
FREE={'Fl4Proofs.P3.JHole.mcsPPJI','Fl4Proofs.P3.JHole.mcsPPJU','Fl4Proofs.P3.kernel_entryJ33'}
prot=set(K) if '--old-keeps' in opts else K-FREE
FMODS={'Fl4Proofs.P3.SpecInvYieldScopeF%d'%i for i in range(1,5)}
if '--no-fprot' not in opts: prot|={x for x in dset if dmod.get(x) in FMODS}
miss=sorted(x for x in seeds|K if x not in dset)
R=seeds-prot
Dd=drev(R); bad=sorted(Dd&prot)
D=set(Dd); wl=list(D)
while wl:
    x=wl.pop()
    for y in ddeps.get(x,()):
        if y in D or y in prot: continue
        us=dmus.get(y)
        if us and us<=D: D.add(y); wl.append(y)
D={x for x in D if dmod[x].startswith('Fl4Proofs.')}
print('consts',len(mod),'decls',len(dset),'seeds',len(seeds),'prot',len(prot),'missing',len(miss),'prot-in-rev',bad)
print('dead decls',len(D))
json.dump(dict(D=sorted(D),dmod={x:dmod[x] for x in D},dkind={x:kind.get(x,'aux') for x in D},missing=miss,
  users={x:sorted(dmus.get(x,())) for x in D}),open(out,'w'))
