"""collapse A / B3: axint27.lean without the deleted names -> axint27b3.lean. usage: mkaxb3.py DEAD.json SRC.json"""
import json,sys,os
d=set(json.load(open(sys.argv[1]))['D']); rows={r[1] for r in json.load(open(sys.argv[2]))['rows']}
here=os.path.dirname(os.path.abspath(__file__))
src=os.path.join(here,'..','..','int27','axint27.lean'); out=[];drop=0
for l in open(src):
    p=l.split()
    if l.startswith('#print axioms') and (p[2] in d or any(p[2].startswith(r+'.') for r in rows if p[2].startswith(r))):
        drop+=1; continue
    out.append(l)
open(os.path.join(here,'axint27b3.lean'),'w').write(''.join(out))
print('kept',sum(1 for l in out if l.startswith('#print')),'dropped',drop)
