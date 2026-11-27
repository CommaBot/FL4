exec(open('/private/tmp/claude-502/col/ana.py').read())
import subprocess
REPO='/Users/stillfail/.stillfail/sessions/claude-ember@d70ccd1321eaa3aa3390df77fb901ff2774a7cc3da926c3cf25ca287a3ba5f22/C0AQ0C0KVMH-1794890878-390829/workspace/FL4-collapse'
which=sys.argv[1]  # x86|a64
mod,kind,deps=load('depdump.tsv.gz' if which=='x86' else 'depdumpA64.tsv.gz')
users=collections.defaultdict(set)
for n,ds in deps.items():
    for d in ds: users[d].add(n)
pre=re.compile(r'^(Fl4Proofs)([A-Z]+)\.(.*)$')
for c in list(mod):
    m=pre.match(c)
    if m and which=='x86':
        o='Fl4Proofs.'+m.group(3)
        if o in mod: users[o].add(c)   # meta edge: a transport copy needs its original
def last(n): return n.split('.')[-1]
D=set()
for n in mod:
    if kind[n]!='thm' or users.get(n): continue
    l=last(n)
    if which=='x86':
        if re.fullmatch(r'kernel_entry_reachU(\d+)[A-Za-z]*',l):
            k=int(re.match(r'kernel_entry_reachU(\d+)',l).group(1))
            if 5<=k<=45: D.add(n)
        mm=re.fullmatch(r'serializable_fl4_local(W|U|VX)(\d+)([A-Za-z0-9]*)',l)
        if mm and 'of' not in mm.group(3) and 'via' not in mm.group(3):
            f,k,suf=mm.group(1),int(mm.group(2)),mm.group(3)
            if f=='W' and 1<=k<=16 and not suf.startswith('P'): D.add(n)
            if f=='U' and 1<=k<=15: D.add(n)
            if f=='VX' and 1<=k<=10: D.add(n)
    else:
        if re.fullmatch(r'entry_of(3|4|5A|6A|7A|7B|8A|9A|10A)',l) and n.startswith('Fl4ProofsA64.P1.kernel_entry.'): D.add(n)
if which=='x86':
    for n in mod:
        if (n.startswith('Fl4Proofs.P1.kernel_entry.entry_of') or n.startswith('Fl4Proofs.P1.X5.kernel_entry.entry_of')) and kind[n]=='thm': D.add(n)
# line-alive name roots
lineTok=set()
for b in ['p3J','a64','mmuAD']:
    for f in open(f'/private/tmp/claude-502/col/live_{b}.txt').read().split():
        if not f.endswith('.lean') or f.endswith('Fl4Proofs.lean') or f.endswith('Fl4ProofsA64.lean'): continue
        t=subprocess.run(['git','-C',REPO,'show',f'par/{b}:{f}'],capture_output=True,text=True).stdout
        lineTok|=set(re.findall(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*",t))
bylast=collections.defaultdict(set)
for n in mod: bylast[last(n)].add(n)
lineKeep=set()
for t in lineTok:
    for n in bylast.get(last(t),()):
        if n.endswith(t): lineKeep.add(n)
keptForLine=D&lineKeep
D-=lineKeep
Dmods={mod[n] for n in D}
# fixpoint: add constants all of whose users are dead
X=set(D); changed=True
while changed:
    changed=False
    for n in list(mod):
        if n in X or n in lineKeep: continue
        if re.match(r'(serializable_|kernel_entry_reach)',last(n)): continue
        isaux=bool(re.search(r'(\.(match_\d+|proof_\d+|_proof_\d+|_simp_\d+|eq_\d+|eq_def|_unfold|_sunfold|_cstage\d*|_sparseCasesOn_\d+)$)|^_private',n))
        if not isaux and mod[n] not in Dmods: continue
        us=users.get(n)
        if us and us<=X:
            X.add(n); changed=True
print('droppable tops',len(D),'kept for line',sorted(keptForLine))
print('dead total',len(X))
bym=collections.defaultdict(set)
for n in X: bym[mod[n]].add(n)
tot=collections.Counter(mod.values())
full=[m for m in bym if len(bym[m])==tot[m]]
print('modules fully dead',len(full)); print(sorted(full))
print('partially dead modules',len(bym)-len(full))
json.dump({'D':sorted(D),'X':sorted(X),'full':sorted(full),'bym':{m:sorted(v) for m,v in bym.items()},'kfl':sorted(keptForLine)},open(f'/private/tmp/claude-502/col/dead_{which}.json','w'))
