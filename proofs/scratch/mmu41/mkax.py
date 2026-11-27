import sys,re
out=sys.argv[1]; mods=sys.argv[2:]
L=[]
for m in mods:
    L.append('import '+m)
for m in mods:
    t=open(m.replace('.','/')+'.lean').read()
    ns='Fl4Proofs.P3'
    for line in t.split('\n'):
        mm=re.match(r'namespace (\S+)',line)
        if mm: ns=mm.group(1)
        mm=re.match(r'theorem (\S+)',line)
        if mm: L.append('#print axioms '+ns+'.'+mm.group(1))
open(out,'w').write('\n'.join(L)+'\n')
print(len([l for l in L if l.startswith('#print')]))
