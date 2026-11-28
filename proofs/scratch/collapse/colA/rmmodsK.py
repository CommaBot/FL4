"""collapse A, K: remove the K transport / copy modules; each importer imports the removed module's surviving
imports instead (transitively, without duplicates)."""
import re,os,subprocess,sys
RM=sys.argv[1:]
def imps(m):
    p=m.replace('.','/')+'.lean'
    return [l.split()[1] for l in open(p) if l.startswith('import ')]
I={m:imps(m) for m in RM}
def repl(m,seen=None):
    out=[]
    for i in I[m]:
        if i in RM: out+=repl(i)
        else: out.append(i)
    return out
files=subprocess.check_output(['git','ls-files','Fl4Proofs','Fl4Proofs.lean'],text=True).split()
for f in files:
    if not f.endswith('.lean') or f[:-5].replace('/','.') in RM: continue
    L=open(f).read().split('\n')
    if not any(l.startswith('import ') and l.split()[1] in RM for l in L): continue
    have={l.split()[1] for l in L if l.startswith('import ')}
    out=[];added=set()
    for l in L:
        if l.startswith('import ') and l.split()[1] in RM:
            if f=='Fl4Proofs.lean': continue
            for r in repl(l.split()[1]):
                if r not in have and r not in added: out.append('import '+r); added.add(r)
            continue
        out.append(l)
    open(f,'w').write('\n'.join(out)); print('IMPORTS',f,sorted(added))
for m in RM: subprocess.check_call(['git','rm','-q',m.replace('.','/')+'.lean']); print('RM',m)
