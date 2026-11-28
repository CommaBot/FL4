"""collapse A / B3: git rm the emptied modules; in every live importer under Fl4Proofs/ replace `import M` by M's
own imports (expanded through other emptied modules, skipping ones the importer already has); drop M from the root.
usage (from proofs/): rmmods.py SRC.json"""
import json,re,subprocess,sys
E=json.load(open(sys.argv[1]))['empty']; ES=set(E)
own={m:[l.split()[1] for l in open(m.replace('.','/')+'.lean') if l.startswith('import ')] for m in E}
def expand(m,seen):
    out=[]
    for i in own[m]:
        if i in seen: continue
        seen.add(i)
        out+= expand(i,seen) if i in ES else [i]
    return out
files=set()
for m in E:
    r=subprocess.run(['git','grep','-l','-E','^import '+re.escape(m)+r'\s*$','--','Fl4Proofs','Fl4Proofs.lean','Fl4ProofsA64','Fl4ProofsA64.lean','Fl4Spec'],capture_output=True,text=True).stdout.split()
    files|=set(r)
log=[]
for f in sorted(files):
    if f.endswith('.lean') and f[:-5].replace('/','.') in ES: continue
    L=open(f).read().split('\n')
    have={l.split()[1] for l in L if l.startswith('import ')}
    out=[]
    for l in L:
        p=l.split()
        if len(p)==2 and p[0]=='import' and p[1] in ES:
            if f=='Fl4Proofs.lean': log.append(f'{f}: - {p[1]}'); continue
            add=[i for i in expand(p[1],set()) if i not in have]
            have|=set(add)
            out+=['import '+i for i in add]; log.append(f'{f}: {p[1]} -> {add}')
        else: out.append(l)
    open(f,'w').write('\n'.join(out))
subprocess.run(['git','rm','-q']+[m.replace('.','/')+'.lean' for m in E],check=True)
print('\n'.join(log))
