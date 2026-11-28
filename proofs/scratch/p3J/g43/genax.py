# usage: python3 genax.py OUT Mod1 Mod2 ...  -> AX file importing the last module(s), #print axioms for each decl
import sys,re
out=sys.argv[1]; mods=sys.argv[2:]
lines=[]
for m in mods: lines.append('import '+m)
names=[]
for m in mods:
    ns=[]
    for l in open(m.replace('.','/')+'.lean'):
        mm=re.match(r'^namespace (\S+)',l)
        if mm: ns.append(mm.group(1)); continue
        mm=re.match(r'^end (\S+)',l)
        if mm and ns and ns[-1]==mm.group(1): ns.pop(); continue
        mm=re.match(r'^(?:theorem|def|structure|abbrev) (\S+)',l)
        if mm:
            n=mm.group(1)
            names.append('.'.join(ns+[n]) if ns else n)
for n in names: lines.append('#print axioms '+n)
open(out,'w').write('\n'.join(lines)+'\n')
print(len(names))
