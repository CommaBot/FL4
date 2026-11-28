import sys,re
out=sys.argv[1]; mods=sys.argv[2:]
L=['import '+m for m in mods]
for m in mods:
    t=open(m.replace('.','/')+'.lean').read()
    st=[]
    for line in t.split('\n'):
        mm=re.match(r'namespace (\S+)',line)
        if mm: st.append(mm.group(1)); continue
        mm=re.match(r'end (\S+)\s*$',line)
        if mm and st and st[-1]==mm.group(1): st.pop(); continue
        mm=re.match(r'(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(theorem|def|abbrev|structure) (\S+)',line)
        if mm: L.append('#print axioms '+'.'.join(st+[mm.group(2)]))
open(out,'w').write('\n'.join(L)+'\n')
print(len([l for l in L if l.startswith('#print')]))
