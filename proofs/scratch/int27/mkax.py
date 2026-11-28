# int27: build scratch/int27/axint27.lean (run in proofs/):
#   (a) thms.py over every Fl4Proofs / Fl4Spec module added or modified since BASE (main 5baf782fc) — every new name;
#   (b) thms.py --tops over every module reachable from the root Fl4Proofs.lean — every serializable_* / kernel_entry_reach* top.
# Dedup. The A64 side is swept by scratch/collapse/axallA64.lean (whole environment). Usage: python3 scratch/int27/mkax.py BASE
import sys,subprocess,os
base=sys.argv[1]
ch=[f[len('proofs/'):] for f in subprocess.check_output(['git','diff','--name-only','--diff-filter=AM',base,'HEAD','--',
    'Fl4Proofs','Fl4Spec'],text=True).split() if f.endswith('.lean')]
ch=[f for f in ch if f.startswith(('Fl4Proofs/','Fl4Spec/'))]
seen=set();st=[l.split()[1] for l in open('Fl4Proofs.lean') if l.startswith('import ')];reach=[]
while st:
  m=st.pop()
  if m in seen or not m.startswith(('Fl4Proofs.','Fl4Spec.')): continue
  p=m.replace('.','/')+'.lean'
  if not os.path.exists(p): continue
  seen.add(m); reach.append(p)
  st+=[l.split()[1] for l in open(p,errors='replace') if l.startswith('import ')]
rs=set(reach); chr_=[f for f in ch if f in rs]
open('scratch/int27/newmods.txt','w').write('\n'.join(sorted(chr_))+'\n')
th=lambda args: subprocess.check_output(['python3','scratch/int27/thms.py']+args,text=True).splitlines()
a=th(chr_); b=th(['--tops']+sorted(reach))
out=['import Fl4Proofs','']; s=set()
for l in a+b:
  if l in s: continue
  s.add(l); out.append(l)
open('scratch/int27/axint27.lean','w').write('\n'.join(out)+'\n')
print('changed',len(ch),'changed&reachable',len(chr_),'reachable',len(reach),'new-names',len(set(a)),'tops',len(set(b)),'total',len(s))
