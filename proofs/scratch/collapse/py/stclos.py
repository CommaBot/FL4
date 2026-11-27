# statement-level closure: which kept tops' statements depend (through defs/structures) on each cone's narrowed defs
import gzip,collections,re,sys,json
exec(open('/private/tmp/claude-502/col/ana.py').read())
TD=sys.argv[1]   # tydump.tsv.gz path
mod,kind,deps=load('depdump.tsv.gz')
ty={}
for line in gzip.open(TD,'rt'):
    p=line.rstrip('\n').split('\t'); ty[p[0]]=p[2].split() if len(p)>2 and p[2] else []
def stdeps(n):
    k=kind.get(n)
    if k in ('thm',): return ty.get(n,[])
    return deps.get(n,[])   # defs / inductives / ctors: full (value + type)
memo={}
def sclos(n):
    seen=set();st=[n]
    while st:
        x=st.pop()
        if x in seen: continue
        seen.add(x); st+=stdeps(x)
    return seen
narrow={'N':['Fl4Proofs.P3.JEntryAt','Fl4Proofs.P3.JEntryAtR','Fl4Proofs.P3.JEntryAtR2','Fl4Proofs.P3.JEntryAtR3','Fl4Proofs.P3.JEntryAtR5','Fl4Proofs.P3.SInvR.G5.JEntryAtR6','Fl4Proofs.P3.SInvR.G5.JEntryAtR7'],
 'I':['Fl4Proofs.P3.ArchIrqRel'],
 'Q':['Fl4Proofs.P3.MachPlat','Fl4Proofs.P3.IrqPlatA','Fl4Proofs.P3.MaskMR','Fl4Proofs.P3.JDecMRLK','Fl4Proofs.P3.JDecMRL2'],
 'J':[n for n in mod if re.fullmatch(r'Fl4Proofs\.P3\.(SInvR\.G5\.)?JPathAtM(35E?|36E|U\d+)?',n)],
 'K':['Fl4Proofs.P3.ArchSwF','Fl4Proofs.P3.KFinAtR','Fl4Proofs.P3.KFinAtR27','Fl4Proofs.P3.KFinAtR31','Fl4Proofs.P3.SInvR.G5.KFinAtR5','Fl4Proofs.P3.KFinAtR5']}
narrow={k:[x for x in v if x in mod] for k,v in narrow.items()}
print({k:len(v) for k,v in narrow.items()}, narrow['K'])
dead=set(json.load(open('/private/tmp/claude-502/col/dead_x86.json'))['X'])
pre=re.compile(r'^Fl4Proofs[A-Z]+\.')
users=collections.defaultdict(set)
for n,ds in deps.items():
    for d in ds: users[d].add(n)
tops=[n for n in mod if kind[n]=='thm' and re.match(r'(serializable_|kernel_entry_reach)',n.split('.')[-1]) and not users.get(n) and n not in dead and not pre.match(n)]
print('kept unused tops',len(tops))
hit=collections.defaultdict(list)
for t in tops:
    c=sclos(t)
    for k,v in narrow.items():
        if any(x in c for x in v): hit[k].append(t)
for k in narrow:
    print(k,len(hit[k]),' '.join(x.split('.')[-1] for x in sorted(hit[k]))[:2500])
