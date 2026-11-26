# rootunion.py THEIRS: write proofs/Fl4Proofs.lean = HEAD's import lines + THEIRS' missing import lines (order kept, deduped).
import sys,subprocess
f='proofs/Fl4Proofs.lean'
g=lambda r: subprocess.check_output(['git','show',f'{r}:{f}'],text=True).splitlines()
o=g('HEAD'); t=g(sys.argv[1])
assert all(l.startswith('import ') or not l.strip() for l in o+t), 'non-import line'
seen=set(); r=[]
for l in o+t:
  if not l.startswith('import ') or l in seen: continue
  seen.add(l); r.append(l)
open(f,'w').write('\n'.join(r)+'\n'); print(len(o),len(t),len(r))
